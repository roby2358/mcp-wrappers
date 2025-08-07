import pkgutil, src
for m in pkgutil.walk_packages(src.__path__, src.__name__ + "."):
    __import__(m.name)
