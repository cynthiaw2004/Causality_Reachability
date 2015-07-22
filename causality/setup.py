from setuptools import setup

with open('README') as description:
    description = description.read()

execfile('causality/version.py') # Acquire version constants.

# Define some package entry points. These will be command-line scripts that get
# installed into the user's PATH
epoints = """
[console_scripts]
create-domain = causality.reachability:create_domain
create-codomain = causality.reachability:create_codomain
call-undersamples = causality.reachability:call_undersamples
"""

install_requires = []
tests_require = ['teamcity-messages'] + install_requires

setup(
    name='causality',
    description='',
    version=__version__,
    author='Ian Beaver, Cynthia Freeman, Sergey Plis',
    author_email='ibeaver@nextit.com',
    license='BSD 3-Clause',
    long_description=description,
    include_package_data=True, # Include files listed in MANIFEST.in
    packages=['causality'], # Sub-packages must be explicitly listed.
    #install_requires=['ConcurrentLogHandler>=0.8.3','lxml'], # List of dependencies.
    #entry_points=epoints,
    install_requires=install_requires, # List of dependencies.
    test_suite='tests.tests',
    tests_require=tests_require,
    zip_safe=False) # Override annoying default behavior of easy_install.