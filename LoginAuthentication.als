-- ============================================================
-- MODULE  : LoginAuthentication
-- TOPIC   : Login & Authentication System
-- COURSE  : Formal Method — Final Project 2025-2
-- TOOL    : Alloy Analyzer 4/5
-- ============================================================

module LoginAuthentication


-- ============================================================
-- SECTION 1 — SIGNATURES (System Entities)
-- ============================================================

-- Primitive identity atoms
sig Username {}
sig Password {}

-- A Credential pairs one Username with one Password
sig Credential {
    uname  : one Username,
    passwd : one Password
}

-- Roles available in the system
abstract sig Role {}
one sig Admin   extends Role {}
one sig Regular extends Role {}

-- A User holds exactly one credential and exactly one role
sig User {
    cred : one Credential,
    role : one Role
}

-- An authentication token tied to a session
sig Token {}

-- A Session represents an active authenticated context
sig Session {
    owner : one User,
    tok   : one Token
}

-- Possible outcomes of a login attempt
abstract sig Result {}
one sig Success extends Result {}
one sig Failure extends Result {}

-- A LoginAttempt records who tried to log in, what credential was provided,
-- and whether the attempt succeeded or failed
sig LoginAttempt {
    subject   : one User,
    inputCred : one Credential,
    outcome   : one Result
}


-- ============================================================
-- SECTION 2 — FACTS (Business Rules / Constraints)
-- ============================================================

-- [F1] No two users may share the same credential object
fact uniqueCredentialPerUser {
    all disj u1, u2 : User | u1.cred != u2.cred
}

-- [F2] No two credentials may share the same username
--      (usernames are system-wide unique identifiers)
fact uniqueUsername {
    all disj c1, c2 : Credential | c1.uname != c2.uname
}

-- [F3] Every credential in the system belongs to exactly one user
--      (no orphan credentials, no shared credentials)
fact credentialOwnedByExactlyOneUser {
    all c : Credential | one u : User | u.cred = c
}

-- [F4] No two sessions may carry the same authentication token
--      (each token uniquely identifies one session)
fact uniqueTokenPerSession {
    all disj s1, s2 : Session | s1.tok != s2.tok
}

-- [F5] A user may hold at most one active session at a time
--      (prevents session duplication / session fixation vulnerability)
fact singleSessionPerUser {
    all u : User | lone s : Session | s.owner = u
}

-- [F6] Every token in the system must be associated with exactly one session
--      (no orphan tokens floating in the system)
fact noOrphanToken {
    all t : Token | one s : Session | s.tok = t
}

-- [F7] A login attempt is successful if and only if the submitted credential
--      exactly matches the user's registered credential
fact loginAttemptCorrectness {
    all la : LoginAttempt |
        la.outcome = Success iff la.inputCred = la.subject.cred
}

-- [F8] A successful login attempt guarantees the user has an active session
fact successImpliesSession {
    all la : LoginAttempt | la.outcome = Success implies
        (some s : Session | s.owner = la.subject)
}

-- [F9] A user who has no successful login attempt must have no active session
--      (session cannot exist without a prior successful authentication)
fact noSessionWithoutSuccessfulLogin {
    all u : User |
        (no la : LoginAttempt | la.subject = u and la.outcome = Success)
            implies (no s : Session | s.owner = u)
}

-- [F10] The system allows at most one Admin-role user
--       (enforces principle of least privilege at the admin tier)
fact atMostOneAdmin {
    lone u : User | u.role = Admin
}

-- [F11] The system must always contain at least one Regular-role user
--       (ensures the system is meaningful and not purely administrative)
fact atLeastOneRegularUser {
    some u : User | u.role = Regular
}

-- [F12] The number of active sessions never exceeds the number of users
--       who have at least one successful login attempt on record
fact sessionCountIsConsistent {
    # Session <=
        # { u : User | some la : LoginAttempt |
                la.subject = u and la.outcome = Success }
}


-- ============================================================
-- SECTION 3 — PREDICATES (System Behaviors)
-- ============================================================

-- [P1] login
-- Models a valid login event:
--   · the submitted credential matches the user's registered credential
--   · the resulting session is owned by that user
--   · no other session for this user exists concurrently
pred login [u : User, c : Credential, s : Session] {
    c = u.cred
    s.owner = u
    no s2 : Session | s2.owner = u and s2 != s
}

-- [P2] logout
-- Models the post-logout state:
--   · no active session exists for user u in the current snapshot
pred logout [u : User] {
    no s : Session | s.owner = u
}

-- [P3] isAuthenticated
-- True if and only if user u currently holds an active session
pred isAuthenticated [u : User] {
    some s : Session | s.owner = u
}

-- [P4] validateCredential
-- True if the given credential c is the exact registered credential of user u
pred validateCredential [u : User, c : Credential] {
    u.cred = c
}

-- [P5] adminLogin
-- An admin-specific login: identical to login but restricted to Admin-role users
pred adminLogin [u : User, c : Credential, s : Session] {
    u.role = Admin
    login[u, c, s]
}


-- ============================================================
-- SECTION 4 — ASSERTIONS (Security Properties)
-- ============================================================

-- [A1] No user ever holds two simultaneous active sessions
assert noDoubleSession {
    no disj s1, s2 : Session | s1.owner = s2.owner
}

-- [A2] Authentication tokens are always unique across all sessions
assert noSharedToken {
    no disj s1, s2 : Session | s1.tok = s2.tok
}

-- [A3] A user all of whose login attempts failed must not be authenticated
assert failedLoginImpliesNoSession {
    all u : User |
        (all la : LoginAttempt | la.subject = u implies la.outcome = Failure)
            implies not isAuthenticated[u]
}

-- [A4] Usernames are globally unique across all registered users
assert globalUsernameUniqueness {
    all disj u1, u2 : User | u1.cred.uname != u2.cred.uname
}

-- [A5] Every session in the system is owned by a registered user
assert sessionsOwnedByRegisteredUsers {
    all s : Session | s.owner in User
}


-- ============================================================
-- SECTION 5 — RUN / CHECK SCENARIOS
-- ============================================================

-- [S1] Find a valid instance where a regular user logs in successfully
run login for 3

-- [S2] Find a valid instance of an admin user logging in
run adminLogin for 3

-- [S3] Find any general consistent model instance (sanity / consistency check)
run {} for 4

-- [S4] Verify: no user ever holds two simultaneous active sessions
check noDoubleSession for 5

-- [S5] Verify: authentication tokens are never shared between sessions
check noSharedToken for 5

-- [S6] Verify: all-failed login attempts produce no authenticated state
check failedLoginImpliesNoSession for 5

-- [S7] Verify: username uniqueness holds globally
check globalUsernameUniqueness for 5


-- ============================================================
-- SECTION 6 — ERROR ANALYSIS
-- ============================================================
-- The following block demonstrates an INCORRECT model version.
-- It intentionally removes Fact F5 (singleSessionPerUser), which
-- allows a single user to hold two or more active sessions — a
-- session duplication / session fixation security flaw.
--
-- To test this error version in Alloy Analyzer:
--   1. Comment out [F5] above (fact singleSessionPerUser {...})
--   2. Run: check noDoubleSession for 5
--   3. The Analyzer will report a COUNTEREXAMPLE showing one user
--      owning two different Session atoms simultaneously.
--   4. Restore [F5] to fix the model.
--
-- Violated assertion: noDoubleSession
-- Root cause: without [F5], the model permits
--             s1.owner = s2.owner for distinct s1, s2 : Session
-- Correction: re-add fact singleSessionPerUser as defined above.
-- ============================================================
