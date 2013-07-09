## Prerequisites

(On windows: download and install msysgit.)

Generate keys (http://help.github.com/msysgit-key-setup/)

Upload public key on github account settings page

Line endings:
  * Linux: ```git config --global core.autocrlf input```
  * Windows: ```git config --global core.autocrlf true```

Username and email:
```
git config --global user.name "Your Name"
git config --global user.email "address you used to register on github"
```


## Workflow

(use ```gitk --all``` at any time to understand local repo state)


```
# initialization
git clone git@github.com:Vlad-Shcherbina/icfpc2013-tbd.git

git config branch.master.rebase true
git config merge.defaultToUpstream true

# while True:
    git pull
    
    [hack]
    git add, git commit (or just git gui)
    
    # if there are changes that did not fit into current commit:
        git stash
    
    git pull   # rebase by default
    # if you got "CONFLICT (content): Merge conflict in...":
        # merge is justified
        git rebase --abort
        git merge
        # if there are conflicts (which is likely):
            [resolve them]
            git add, git commit (or git gui)
            
    git push
    
    # if there were changes stashed:
        git stash pop
```

Never Never Never revert your published history!

Never do git ```commit --amend``` if you've already push-ed the previous commit!

Never do git rebase on published commits
