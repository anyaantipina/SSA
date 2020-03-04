function w $main() {
@start
@loop
    %cond =w csgew 1, 200
    jnz %cond, @end, @loop
@end
    ret 0
}
