sig Username {}
sig Password {}

sig Credential {
    uname  : one Username,
    passwd : one Password
}

sig User {
    cred : one Credential,
    role : one Role
}

abstract sig Role {}
one sig Admin   extends Role {}
one sig Regular extends Role {}

abstract sig Result {}
one sig Success extends Result {}
one sig Failure extends Result {}

sig Token {}

sig Session {
    owner : one User,
    tok   : one Token
}

sig LoginAttempt {
    subject   : one User,
    inputCred : one Credential,
    outcome   : one Result
}