
--===============================================
-- DCC831 Formal Methods
-- 2023.2
--
-- Miniproject 1
--
-- Name:  Guilherme de Oliveira Silva
-- ID: 2023671528
--
--===============================================

--------------
-- Signatures
--------------

abstract sig ObjectStatus {}
one sig InUse, Purged extends ObjectStatus {}

abstract sig Object {
  var status: lone ObjectStatus
}

sig Message extends Object {}

sig Mailbox extends Object {
  var messages: set Message
}

one sig MailApp {
  inbox: Mailbox,
  drafts: Mailbox,
  trash: Mailbox,
  sent: Mailbox,
  var userboxes: set Mailbox
}

-- added for convenience, to track the operators applied during
-- a system execution
abstract sig Operator {}

/*
	Operators map

	CMB:		create mailbox
	DMB: 	delete mailbox
	CM: 		create message
	GM: 		get message
	SM:		send message
	DM:		delete message
	MM:		move message
	ET: 		empty trash
*/

one sig CMB, DMB, CM, GM, SM, DM, MM, ET extends Operator {}
one sig Track {
  var op: lone Operator
}


-----------------------
-- Abbreviation macros
-----------------------

-- May be convenient to use

fun mInbox []: Mailbox { MailApp.inbox }
fun mDrafts []: Mailbox { MailApp.drafts }
fun mTrash []: Mailbox { MailApp.trash }
fun mSent []: Mailbox { MailApp.sent }

fun mUserBoxes []: set Mailbox { MailApp.userboxes }

-- Auxiliary predicates
pred objectIsPurged [o: Object] {
	o.status = Purged
}

pred objectIsInUse [o: Object] {
	o.status = InUse
}

pred noStatusChanged [Obj: set Object] {
	all o: Obj | o.status' = o.status
}

pred noMessagesChanged [Mb: set Mailbox] {
	all mb: Mb | mb.messages' = mb.messages
}

fact oncePurgedAlwaysPurged {
	always all o: Object | o.status = Purged => o.status' = Purged
}

fun predefinedMailBoxes [] : Mailbox {
	mInbox + mDrafts + mTrash + mSent
}

-------------
-- Operators
-------------


pred createMessage [m: Message] {
	/*
		Pre-conditions
		1. It must be put in the Drafts mailbox. Thus, this Mailbox must be active.
		2. It is a "fresh" object. Thus, it cannot be drawn from the set of messages
			that are currently active or purged.
	*/
	objectIsInUse[mDrafts]
	not objectIsPurged[m]
	not objectIsInUse[m]

	/*
		Post-conditions
		1. Add the message to the Drafts mailbox.
		2. Change the message status to active.
		3. Add the Create Message operation (CM) to the tracker.
	*/
	mDrafts.messages' = mDrafts.messages + m
	m.status' = InUse
	Track.op' = CM

	/*
		Frame conditions
		1. All the objects must retain its status.
		2. The contents of all the other mailboxes must be the same.
	*/
	noStatusChanged[Object - (m)]
	noMessagesChanged[Mailbox - (mDrafts)]
}

pred getMessage [m: Message] {
	/*
		Pre-conditions
		1. It must be put in the Inbox mailbox. Thus, this mailbox must be active.
		2. The message comes from "outside" the Mail App. Thus, its status must not be either
			InUse or Purged.
	*/
	objectIsInUse[mInbox]
	not objectIsPurged[m]
	not objectIsInUse[m]

	/*
		Post-conditions
		1. Add the message to the Inbox mailbox.
		2. Change the message status to active.
		3. Add the Get Message operation (GM) to the tracker.
	*/
	mInbox.messages' = mInbox.messages + m
	m.status' = InUse
	Track.op' = GM

	/*
		Frame conditions
		1. All the objects must retain its status.
		2. The contents of all the other mailboxes must be the same.
	*/
	noStatusChanged[Object - (m)]
	noMessagesChanged[Mailbox - (mInbox)]
}

pred moveMessage [m: Message, mb1: Mailbox] {
	/*
		Pre-conditions
		1. There exists a Mailbox, other than the destination Mailbox, that is active and contains
			the Message.
		2. The Mailbox to receive the Message must also be active.
		3. The Message to be moved must be active.
	*/
	after some mb: Mailbox - mb1 | (m in mb.messages) and (objectIsInUse[mb])
	objectIsInUse[mb1]
	objectIsInUse[m]

	/*
		Post-conditions
		1. The Message is in the destination Mailbox.
		2. No other Mailbox contains the Message.
		3. Add the Move Message operation (MM) to the tracker.
	*/
	mb1.messages' = mb1.messages + m
	all mb: Mailbox - mb1 | mb.messages' = mb.messages - m
	Track.op' = MM

	/*
		Frame conditions
		1. All the objects must retain its status.
		2. The contents of all the other mailboxes must be the same.
	*/
	noStatusChanged[Object]
	noMessagesChanged[Mailbox - (mb1 + m.~messages)]
}

pred deleteMessage [m: Message] {
	/*
		Pre-conditions
		1. The Message to be deleted must be active.
		2. The Message must not be already in the Trash Mailbox.
	*/
	objectIsInUse[m]
	m not in mTrash.messages

	/*
		Post-conditions
		1. The Message is sent to Trash.
		2. The Message must not be in any Mailbox other than Trash.
	*/
	mTrash.messages' = mTrash.messages + m
	all mb: Mailbox - mTrash | mb.messages' = mb.messages - m
	Track.op' = DM

	/*
		Frame conditions
		1. All the objects must retain its status.
		2. The contents of all the other mailboxes must be the same
			(except for the Trash and the Mailbox that originally contained
			the deleted message).
	*/
	noStatusChanged[Object]
	noMessagesChanged[Mailbox - (mTrash + m.~messages)]
}

pred sendMessage [m: Message] {
	/*
		Pre-conditions
		1. The Message must be active.
		2. The Message must be in the Drafts Mailbox.
	*/
	objectIsInUse[m]
	after m in mDrafts.messages

	/*
		Post-conditions
		1. The Message is in the Sent Mailbox.
		2. The Message is no longer in the Drafts Mailbox.
	*/
	mDrafts.messages' = mDrafts.messages - m
	mSent.messages' = mSent.messages + m
	Track.op' = SM

	/*
		Frame conditions
		1. All the objects must retain its status.
		2. The contents of all the other mailboxes must be the same.
	*/
	noStatusChanged[Object]
	noMessagesChanged[Mailbox - (mDrafts + mSent)]
}

pred emptyTrash [] {
	/*
		Pre-conditions
		1. The Trash Mailbox must contain some active Message.
	*/
	after some m: Message | (m in mTrash.messages) and (objectIsInUse[m])

	/*
		Post-conditions
		1. All the Messages in the Trash Mailbox have its status set to Purged.
		2. All the Messages in the Trash Mailbox are dissociated from this object.
	*/
	all m: Message | (m in mTrash.messages) and (m.status' = Purged)
	all m: Message | (m in mTrash.messages) and (mTrash.messages' = mTrash.messages - m)
	Track.op' = ET

	/*
		Frame conditions
		1. All the objects must retain its status.
		2. The contents of all the other mailboxes must be the same.
	*/
	noStatusChanged[Object - (mTrash.messages)]
	noMessagesChanged[Mailbox - (mTrash)]
}

pred createMailbox [mb: Mailbox] {
	/*
		Pre-conditions
		1. The new Mailbox must be a new, fresh object.
		2. The new Mailbox must be different from the other existing Mailboxes.
	*/
	not objectIsPurged[mb]
	all existingMailbox: (Mailbox - mb) | mb != existingMailbox

	/*
		Post-conditions
		1. The new Mailbox status is set to active.
		2. The new Mailbox is added to the user-created Mailboxes.
	*/
	mb.status' = InUse
	mUserBoxes' = mUserBoxes + mb
	Track.op' = CMB

	/*
		Frame conditions
		1. All the previously existing objects must retain its status.
		2. The contents of all the other mailboxes must be the same.
	*/
	noStatusChanged[Object - (mb)]
	noMessagesChanged[Mailbox]
}

pred deleteMailbox [mb: Mailbox] {
	/*
		Pre-conditions
		1. The Mailbox to be deleted must be active.
		2. The Mailbox to be deleted must be an user-created Mailbox.
		3. The Mailbox to be deleted must not be a predefined Mailbox.
	*/
	not objectIsPurged[mb]
	after mb in mUserBoxes
	mb not in predefinedMailBoxes

	/*
		Post-conditions
		1. The Mailbox is removed from the MailApp.
		2. All of its Messages and the Mailbox itself are Purged.
	*/
	all m: mb.messages | m.status' = Purged
	mb.status' = Purged
	mUserBoxes' = mUserBoxes - mb
	Track.op' = DMB

	/*
		Frame conditions
		1. All the previously existing objects must retain its status.
		2. The contents of all the other mailboxes must be the same.
	*/
	noStatusChanged[Object - (mb)]
	noMessagesChanged[Mailbox - (mb)]
}


----------------------------
-- Initial state conditions
----------------------------

pred init [] {
  -- There are no purged objects at all
	no o: Object | objectIsPurged[o]

  -- All mailboxes are empty
	all m: Mailbox | no m.messages

  -- The predefined mailboxes are mutually distinct
	always disj[mInbox, mDrafts, mSent, mTrash, mUserBoxes]

  -- The predefined mailboxes are the only active objects
	always mInbox.status = InUse
	always mDrafts.status = InUse
	always mTrash.status = InUse
	always mSent.status = InUse
	all o: Object | objectIsInUse[o] => o in predefinedMailBoxes

  -- The app has no user-created mailboxes
	no mUserBoxes

  -- For convenience, no tracked operation.
	no op
}

-----------------------
-- Transition relation
-----------------------

pred trans []  {
    (some mb: Mailbox | createMailbox [mb])
    or
    (some mb: Mailbox | deleteMailbox [mb])
    or
    (some m: Message | createMessage [m])
    or
    (some m: Message | getMessage [m])
    or
    (some m: Message | sendMessage [m])
    or
    (some m: Message | deleteMessage [m])
    or
    (some m: Message | some mb: Mailbox | moveMessage [m, mb])
    or
    emptyTrash []
}


--------------------
-- System predicate
--------------------

-- Denotes all possible executions of the system from a state
-- that satisfies the initial condition
pred System {
	init
   always trans
}

run execution { System } for 8


--------------
-- Properties
--------------

pred p1 {
-- Active mailboxes contain only active messages
	all mb: Mailbox | all m: Message |
		(mb.status = InUse) and (m in mb.messages) => m.status = InUse
}

pred p2 {
-- Every active message belongs to some active mailbox
	all m: Message | some mb: Mailbox |
		m.status = InUse => m in mb.messages
}

pred p3 {
-- Mailboxes do not share messages
	all mb1, mb2: Mailbox |
		mb1 != mb2 => no mb1.messages & mb2.messages
}

pred p4 {
-- The system mailboxes are always active
	always objectIsInUse[mSent]
	always objectIsInUse[mTrash]
	always objectIsInUse[mInbox]
	always objectIsInUse[mDrafts]
}

pred p5 {
-- User-created mailboxes are different from the system mailboxes
	all mb: mUserBoxes | mb not in predefinedMailBoxes
}

pred p6 {
-- An object can have Purged status only if it was once active
	before all o: Object | o.status = Purged => o.status = InUse
}

pred p7 {
-- Every sent message was once a draft message
	before all m: Message | m in mSent.messages => m in mDrafts.messages
}

--------------
-- Assertions
--------------

assert a1 { System => p1 }
check a1

assert a2 { System => p2 }
check a2

assert a3 { System => p3 }
check a3

assert a4 { System => p4 }
check a4

assert a5 { System => p5 }
check a5

assert a6 { System => p6 }
check a6

assert a7 { System => p7 }
check a7
