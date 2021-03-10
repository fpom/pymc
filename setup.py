from setuptools import setup, find_packages
import pathlib, inspect
import pymc

long_description = pathlib.Path("README.md").read_text(encoding="utf-8")
description = inspect.cleandoc(pymc.__doc__).splitlines()[0]

setup(name="pymc",
      description=description,
      long_description=long_description,
      url="https://forge.ibisc.univ-evry.fr/cthomas/pyits_model_checker",
      author="Colin Thomas",
      author_email="cthomas@ens-cachan.fr",
      classifiers=["Development Status :: 4 - Beta",
                   "Intended Audience :: Developers",
                   "Topic :: Scientific/Engineering",
                   "Programming Language :: Python :: 3",
                   "Operating System :: OS Independent"],
      packages=find_packages(where="."),
      python_requires=">=3.7",
)
