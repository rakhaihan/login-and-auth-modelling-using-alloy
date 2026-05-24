sig username {}
sig password {}
sig credential {
    uname  : one username,
    passwd : one password
}

abstract sig role {}
one sig admin   extends role {}
one sig regular extends role {}

sig user {
    cred : one credential,
    role : one role
}

sig token {}
sig session {
    owner : one user,
    tok   : one token
}

abstract sig result {}
one sig success extends result {}
one sig failure extends result {}

sig loginAttempt {
    subject   : one user,
    inputCred : one credential,
    outcome   : one result
}