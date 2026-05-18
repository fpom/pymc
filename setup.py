from setuptools import setup, find_packages
import pathlib

long_description = pathlib.Path("README.md").read_text(encoding="utf-8")
description = "libDDD-based model-checker for (AR)CTL with(out) fairness"

setup(
    name="pymc",
    description=description,
    long_description=long_description,
    url="https://forge.ibisc.univ-evry.fr/cthomas/pyits_model_checker",
    author="Colin Thomas",
    author_email="cthomas@ens-cachan.fr",
    classifiers=[
        "Development Status :: 4 - Beta",
        "Intended Audience :: Developers",
        "Topic :: Scientific/Engineering",
        "Programming Language :: Python :: 3",
        "Operating System :: OS Independent",
    ],
    packages=find_packages(where="."),
    python_requires=">=3.7",
    install_requires=[
        "pytl @ git+https://github.com/fpom/pytl.git",
        "pyddd @ git+https://github.com/fpom/pyddd.git",
    ],
)
