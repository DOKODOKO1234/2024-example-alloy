sig Role{}//ロールは管理者と一般ユーザーだけ
one sig Admin extends Role{}
one sig GeneralUser extends Role{}


sig User { // ユーザー情報
    havePass: set Password,  // ユーザーが登録しているパスワード
    friends: set User,       // 友だち登録しているユーザー
    role: one Role           // 一般ユーザーか管理者か
}

sig Password {
    content: String,         // パスワード文字列
    shared: set User,        // 共有した友達
    expirationFlag: one ExpirationFlag,  // パスワードの使用期限
    accessibleTeams: set Team   // アクセスできる部署
}

enum ExpirationFlag {//パスワードが有効か無効かのフラグ
    Valid,
    Invalid
}

sig Team {  // パスワードでアクセスできる場所
    members: set User  // 所属メンバー
}

fact EnsureShareRange{ // パスワードを持っているユーザーはそのパスワードを共有対象にできる
    all p: Password | p.shared = { u: User | p in u.havePass }
}

fact EnsureUsersHavePasswords { // パスワードを必ず持っている
    all u: User | some u.havePass
}

fact UniquePasswordContent {//それぞれのパスワードの内容は重複しない
    all disj p1, p2: Password | p1.content != p2.content
}

fact EnsureTeamHaveMembers{//部署には必ずメンバーが配属されている
    all t:Team | some t.members
}

fact NoSelfFriend {//自分自身は友達にできない
    all u: User | u !in u.friends
}

fact EnsurePasswordsHaveTeams{//有効なパスワードは必ず、どこかの部署で使える
    all p: Password |
    p.expirationFlag = Valid => some p.accessibleTeams

}
fact EnsureInvalidPasswordsCannotAccessTeams {//期限切れのパスワードは使えない
    all p: Password |
        p.expirationFlag = Invalid => no p.accessibleTeams
}

fact EnsureAdmin{//管理者が確実に存在する
    one u: User | u.role = Admin
}

fact EnsureExpirationFlag {//パスワードは期限の属性を持つ
    all p: Password | p.expirationFlag in Valid or p.expirationFlag in Invalid
}

fact SharingRule {  // 一般ユーザーが共有できるのは友達に入っている人だけ
    all u1, u2: User, p: Password |
    u1.role = GeneralUser and p in u1.havePass and u2 in u1.friends => u2 in p.shared
}


fact AdminPassSharing {  // 管理者はパスワードを所属している部署のメンバーと友達に共有できる
    all u: User, p: Password, t: Team |
    u.role in Admin and p in u.havePass and t in p.accessibleTeams =>
    p.shared = p.shared + t.members
}


fact EnsureGeneralUserExists {//一般ユーザーが必ず存在する
    some u: User | u.role = GeneralUser
}


fact GeneralUserCanOnlyUseOwnPasswords {// 一般ユーザーは自分が持っているパスワードのみ共有可能
    all u: User, p: Password |
    u.role = GeneralUser and p in u.havePass =>
    p.shared = p.shared + u.friends 
}

assert AdminCanSharePasswords {//管理者が共有できるのは自分のチームメンバーと友だちだけか？
    all u: User, p: Password, t: Team |
    u.role = Admin and p in u.havePass and t in p.accessibleTeams
    => p.shared = p.shared + t.members
}

assert InvalidPasswordCannotAccessTeams {//期限切れのパスワードは本当に使えないか？
    all u: User, p: Password |
    p in u.havePass and p.expirationFlag = Invalid =>
    no p.accessibleTeams
}

pred init {//前提条件
    some u: User, p: Password, s: String | 
    p in u.havePass and 
    p.content = s 
}

run {//検証条件
    init and some u: User | u.role = Admin
} for exactly 2 Role,exactly 10 User, exactly 5 Password, 5 Team, exactly 5 String




