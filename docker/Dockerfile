FROM debian:bookworm

RUN echo 'debconf debconf/frontend select Noninteractive' | debconf-set-selections
RUN apt-get update && apt-get install -y apt-utils

# Install and configure locale `en_US.UTF-8`
RUN apt-get update && apt-get install -y locales && \
    sed -i 's/# en_US.UTF-8 UTF-8/en_US.UTF-8 UTF-8/g' /etc/locale.gen && \
    echo 'LANG=en_US.UTF-8' > /etc/default/locale && \
    locale-gen

ENV LANG=en_US.UTF-8

RUN apt-get update && apt-get install -y git python3 python3-pip g++ cmake python3-ply python3-pygraphviz git python3-tk tix pkg-config libssl-dev libreadline-dev

# create a user:
RUN useradd -ms /bin/bash user
USER user
WORKDIR /home/user

RUN git clone --recurse-submodules https://github.com/kenmcmil/ivy.git
WORKDIR /home/user/ivy/

# make sure it's using the right python:
RUN sed -i "s/'python /'python3 /g" build_submodules.py
RUN python3 build_submodules.py
USER root
RUN apt-get update && apt-get install -y python3-setuptools python3-venv
USER user
RUN python3 -m venv venv
ENV PATH="/home/user/ivy/venv/bin/:$PATH"
RUN pip install --upgrade setuptools
RUN python3 setup.py install
COPY . /home/user/scp-proofs/

WORKDIR /home/user/scp-proofs/
CMD ["ivy_check", "complete=fo", "SCP.ivy"]
