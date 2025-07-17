import setuptools

setuptools.setup(
    name="dual_pairs",
    version="0.5",
    author="Peter Bruin",
    author_email="P.J.Bruin@math.leidenuniv.nl",
    description="SageMath package for computing with dual pairs of algebras",
    long_description=open("README.md", "r").read(),
    long_description_content_type="text/markdown",
    url="https://gitlab.com/pbruin/dual-pairs",
    packages=["dual_pairs"],
    package_data={"dual_pairs": ["example_data/*.gp"]},
    extras_require={"doc": "sphinx>=2",
                    "passagemath": ["passagemath-flint",
                                    "passagemath-modules",
                                    "passagemath-pari",
                                    "passagemath-repl"]},
    classifiers=[
        "Topic :: Scientific/Engineering :: Mathematics",
        "Intended Audience :: Science/Research",
        "Programming Language :: Python",
        "Operating System :: OS Independent",
        "Development Status :: 3 - Alpha",
        "License :: OSI Approved :: GNU General Public License v3 or later (GPLv3+)"
    ])
