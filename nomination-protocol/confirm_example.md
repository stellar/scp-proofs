# How to use it.
`confirm_example.txt` contains a series of actions to check if the ivy scripts are sane.

Run it by `./nomination < confirm_example.txt`.
Alternatively, run `./nomination` and copy and paste the content line by line.

# The content
For convenience, I copied and pasted the content here.

```
node.vote(0, 10)
node.check_confirmed(0, 10)
node.check_confirmed(1, 10)
node.vote(1, 10)
node.check_confirmed(0, 10)
node.check_confirmed(1, 10)
network.deliver_vote(1, 0, 10)
node.check_confirmed(0, 10)
node.check_confirmed(1, 10)
network.deliver_accept(0, 1, 10)
node.check_confirmed(0, 10)
node.check_confirmed(1, 10)
network.deliver_accept(1, 0, 10)
node.check_confirmed(0, 10)
node.check_confirmed(1, 10)
```

# Explanation

* Only two nodes. `Node 0` and `Node 1`.
* Only one statement. `Statement 10`. (The number 10 is arbitrarily chosen. Could've been 5, or 102)
* The only quorum is `{0, 1}`.
* After each action, we check if `Node 0` and `Node 1` have confirmed `Statement 10`.

1. `node.vote(0, 10)` => No one should confirm anything.
1. `node.vote(1, 10)` => No one should confirm anything.
1. `node.deliver_vote(1, 0, 10)`
   => `Node 0` hears that `Node 1` voted for `Statement 10`.
      The set `{0, 1}` is a quorum, so `Node 0` accepts `Statement 10`.
1. `network.deliver_accept(0, 1, 10)`
   => `Node 1` hears that `Node 0` accepted `Statement 10`.
      Then `Node 1` can accept and confirm `Statement 10`.
1. `network.deliver_accept(1, 0, 10)`
   => `Node 0` hears that `Node 1` accepted `Statement 10`.
      Then `Node 0` can confirm `Statement 10`.
