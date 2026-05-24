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

pred login [u : User, c : Credential, s : Session] {
    c = u.cred
    s.owner = u
    no s2 : Session | s2.owner = u and s2 != s
}

pred logout [u : User] {
    no s : Session | s.owner = u
}

pred isAuthenticated [u : User] {
    some s : Session | s.owner = u
}

pred validateCredential [u : User, c : Credential] {
    u.cred = c
}

pred adminLogin [u : User, c : Credential, s : Session] {
    u.role = Admin
    login[u, c, s]
}