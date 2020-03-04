function w $main() {
@B8
    %i =w copy 1
@B7
    %a =w copy -1
    %c =w copy 3
    jnz %a, @B6, @B5
@B6
    %b =w copy 4
    %c =w copy 5
    %d =w copy 6
@B5
    %a =w copy 7
    %d =w copy 8
    jnz %a, @B7, @En
@En
    ret
}
