
--===============================================
-- DCC831 Formal Methods
-- 2022.2
--
-- Miniproject 1
--
-- Name:  <replace with your name>
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

-------------
-- Operators
-------------


pred createMessage [m: Message] {

}

pred getMessage [m: Message] {

}

pred moveMessage [m: Message, mb1: Mailbox] {

}

pred deleteMessage [m: Message] {

}

pred sendMessage [m: Message] {

}

pred emptyTrash [] {

}

pred createMailbox [mb: Mailbox] {

}

pred deleteMailbox [mb: Mailbox] {

}


----------------------------
-- Initial state conditions
----------------------------

pred init [] {
  -- There are no purged objects at all

  -- All mailboxes are empty

  -- The predefined mailboxes are mutually distinct

  -- The predefined mailboxes are the only active objects

  -- The app has no user-created mailboxes

  -- For convenience, no tracked operation.
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

}

pred p2 {
-- Every active message belongs to some active mailbox

}

pred p3 {
-- Mailboxes do not share messages

}

pred p4 {
-- The system mailboxes are always active

}

pred p5 {
-- User-created mailboxes are different from the system mailboxes

}

pred p6 {
-- An object can have Purged status only if it was once active

}

pred p7 {
-- Every sent message was once a draft message

}

--------------
-- Assertions
--------------

assert a1 { System => p1 }
assert a2 { System => p2 }
assert a3 { System => p3 }
assert a4 { System => p4 }
assert a5 { System => p5 }
assert a6 { System => p6 }
assert a7 { System => p7 }
