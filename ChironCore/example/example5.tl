:x = 5
:unusedvar = 10 
:total = 0

repeat :x [
    :total = :total + 1  
    :temp = :x * 2  
]

forward :total