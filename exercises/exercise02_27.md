
app-exp
    lambda-exp a
        app-exp
            var-exp a
            var-exp b
    var-exp c


lambda-exp x
    lambda-exp y
        app-exp
            lambda-exp x
                app-exp
                    var-exp x
                    var-exp y
            var-exp x