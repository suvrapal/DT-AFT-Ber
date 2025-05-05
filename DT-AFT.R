# R Code for Data Generation

data.Ber.RC = function(n,beta0,beta1,beta2,cens,setting){
  z1 = rnorm(n,mean=0,sd=1) # z1 and z2 are the two continuous covariates 
  # generated independently from standard normal distributions
  z2 = rnorm(n,mean=0,sd=1)
  
  piz = rep(NA,n) # this is the uncured probability pi(z)
  
  if(setting==1){ # linear classification boundary
    piz = (exp(0.3-(5*z1)-(3*z2))/(1+exp(0.3-(5*z1)-(3*z2))))
  }
  
  if(setting==2){ # non-linear classification boundary
    piz =  (exp(0.3-(5*z1*z2)-(3*z1*z2))/(1+exp(0.3-(5*z1*z2)-(3*z1*z2))))
  }
  if(setting==3){ # non-linear classification boundary 
    piz = exp(-exp(0.3-(5*z1*z2)-(3*cos(z2))))
  }
  
  C = runif(n,0,cens) # censoring time 
  U = runif(n,0,1)
  Y = rep(NA,n) # observed lifetime
  D = rep(NA,n) # censoring indicator
  J = rep(NA,n) # cured indicator (J=0 implies cured)
  Sp = rep(NA,n) # overall (population) survival function
  S1 = rep(NA,n) # susceptible survival function
  S0 = rep(NA,n) # baseline survival function
  
  for(i in 1:n){
    if(U[i]<= 1-piz[i]){
      Y[i] = C[i]
      D[i] = 0
      J[i] = 0
      
      Sp[i] = (1-piz[i]) + (piz[i]*exp(-(Y[i]*exp(-(beta0+(beta1*z1[i])
                                                    +(beta2*z2[i]))))))
      S1[i] = exp(-(Y[i]*exp(-(beta0+(beta1*z1[i])+(beta2*z2[i])))))
      S0[i] = exp(-(Y[i]))
    }else{
      T =  rexp(1,rate =exp(-(beta0+(beta1*z1[i])+(beta2*z2[i]))) )
      Y[i] = min(T,C[i])
      J[i] = 1
      
      Sp[i] = (1-piz[i]) + (piz[i]*exp(-(Y[i]*exp(-(beta0+(beta1*z1[i]) 
                                                    +(beta2*z2[i]))))))
      S1[i] = exp(-(Y[i]*exp(-(beta0+(beta1*z1[i])+(beta2*z2[i])))))
      S0[i] = exp(-(Y[i]))
      
      if(Y[i]==C[i]){
        D[i] = 0
      }else{
        D[i] = 1
      }
    }
  }
  return(data.frame(Y,D,z1,z2,J,uncure=piz,Sp=Sp,S1=S1,S0=S0))
} # function to generate data under 3 different classification boundaries


# R code for DT-based EM algorithm

library(smcure)
library(survival)
library(rpart)
library(caret)

smrank <-function(beta,Time,X,n,w,Status){
  error <- drop(log(Time)-beta%*%t(X))
  tp <- numeric()     
  for(i in 1:n){
    tp[i] <- sum(as.numeric((error[i]-error)<0)*abs(error[i]-error)*w*Status[i])
  }
  sum(tp)/n
}


smsurv <-function(Time,Status,X,beta,w,model){    
  death_point <- sort(unique(subset(Time, Status==1)))
  if(model=='ph') coxexp <- exp((beta)%*%t(X[,-1]))  
  lambda <- numeric()
  event <- numeric()
  for(i in 1: length(death_point)){
    event[i] <- sum(Status*as.numeric(Time==death_point[i]))
    if(model=='ph')  
      temp <- sum(as.numeric(Time>=death_point[i])*w*drop(coxexp))
    if(model=='aft')  
      temp <- sum(as.numeric(Time>=death_point[i])*w)
    temp1 <- event[i]
    lambda[i] <- temp1/temp
  }
  HHazard <- numeric()
  for(i in 1:length(Time)){
    HHazard[i] <- sum(as.numeric(Time[i]>=death_point)*lambda)
    if(Time[i]>max(death_point))
      HHazard[i] <- Inf
    if(Time[i]<min(death_point))
      HHazard[i] <- 0
  }
  survival <- exp(-HHazard)
  list(survival=survival)
}






em.dt <-function(Time,Time1,Status,Status1,X,X1,Z,Z1,offsetvar,uncureprob,
                 uncurepred,beta,emmax,eps,data,testdata) 
{
  w <- Status	
  w1<-Status1
  n <- length(Status)
  m <- length(Status1)
  
  if(!is.null(offsetvar)) 
    Time <- Time/exp(offsetvar)
  error <- drop(log(Time)-beta%*%t(X))
  error1 <- drop(log(Time1)-beta%*%t(X1))
  s <- smsurv(error,Status,X,beta,w,model="aft")$survival
  s1 <- smsurv(error1,Status1,X1,beta,w1,model="aft")$survival
  convergence<- 1000;i <-1
  while (convergence > eps & i < emmax){
    error <- drop(log(Time)-beta%*%t(X))
    error1 <- drop(log(Time1)-beta%*%t(X1))
    survival <- s
    survival1 <- s1
    
    ## E step 
    w <- Status+(1-Status)*(uncureprob*survival)/((1-uncureprob)
                                                  +uncureprob*survival)
    w1 <- Status1+(1-Status1)*(uncurepred*survival1)/((1-uncurepred)
                                                      +uncurepred*survival1)
    ## M step
    multipleuncureprob=matrix(1:5*n, nrow=n,ncol=5)
    for (j in 1:n){multipleuncureprob[j,]<-rbinom(5,size = 1,prob=w[j])}
    uncureprob1<-c(1,1)
    uncureprob2<-c(1,1)
    uncureprob3<-c(1,1)
    uncureprob4<-c(1,1)
    uncureprob5<-c(1,1)
    for (j in 1:n){uncureprob1[j]=multipleuncureprob[j,1]}
    for (j in 1:n){uncureprob2[j]=multipleuncureprob[j,2]}
    for (j in 1:n){uncureprob3[j]=multipleuncureprob[j,3]}
    for (j in 1:n){uncureprob4[j]=multipleuncureprob[j,4]}
    for (j in 1:n){uncureprob5[j]=multipleuncureprob[j,5]}
    for (j in 1:n){uncureprob1[j]=uncureprob1[j]}
    for (j in 1:n){uncureprob2[j]=uncureprob2[j]}
    for (j in 1:n){uncureprob3[j]=uncureprob3[j]}
    for (j in 1:n){uncureprob4[j]=uncureprob4[j]}
    for (j in 1:n){uncureprob5[j]=uncureprob5[j]}
    uncureprob1<-as.factor(uncureprob1)
    uncureprob2<-as.factor(uncureprob2)
    uncureprob3<-as.factor(uncureprob3)
    uncureprob4<-as.factor(uncureprob4)
    uncureprob5<-as.factor(uncureprob5)
    update_cureb<-c(1,1)
    update_pred<-c(1,1)
    
    daata=data.frame(uncureprob1,Z[,-1])
    obj3 <- tune.rpart(uncureprob1~z1+z2, data = daata, minsplit =c(11,20,25), 
                       cp = c(0.001,0.005,0.01))
    bc<-obj3$best.parameters[1]  
    bg<-obj3$best.parameters[2]
    
    mod1 <- rpart(formula = uncureprob1~z1+z2, data = data,method = "class",
                  control = rpart.control(minsplit = bc[[1]],minbucket = round(bc[[1]]/3), 
                                          cp = bg[[1]]),xval = 10,parms = list(split="gini"))
    cp.min1<-mod1$cptable[which.min(mod1$cptable[,"xerror"]),"CP"]
    tree1<-prune(mod1, cp=cp.min1)
    proba1 <- predict(tree1, newdata = data,type = "prob")
    cproba1 <- predict(tree1, newdata = testdata,type = "prob")
    update_cureb1<-c(1,1)
    update_pred1<-c(1,1)
    for (z in 1:n){update_cureb1[z]<-proba1[z,colnames(proba1)==1]}
    for (d in 1:m){update_pred1[d]<-cproba1[d,colnames(cproba1)==1]}
    uncureprob1<-as.numeric(as.character(uncureprob1))
    
    mod2 <- rpart(formula = uncureprob2~z1+z2, data = data,method = "class",
                  control = rpart.control(minsplit = bc[[1]],minbucket = round(bc[[1]]/3), 
                                          cp = bg[[1]]),xval = 10,parms = list(split="gini"))
    cp.min2<-mod2$cptable[which.min(mod2$cptable[,"xerror"]),"CP"]
    tree2<-prune(mod2, cp=cp.min2)
    proba2 <- predict(tree2, newdata = data,type = "prob")
    cproba2 <- predict(tree2, newdata = testdata,type = "prob")
    update_cureb2<-c(1,1)
    update_pred2<-c(1,1)
    for (z in 1:n){update_cureb2[z]<-proba2[z,colnames(proba2)==1]}
    for (d in 1:m){update_pred2[d]<-cproba2[d,colnames(cproba2)==1]}
    uncureprob2<-as.numeric(as.character(uncureprob2))
    
    mod3 <- rpart(formula = uncureprob3~z1+z2, data = data,method = "class",
                  control = rpart.control(minsplit = bc[[1]],minbucket = round(bc[[1]]/3), 
                                          cp = bg[[1]]),xval = 10,parms = list(split="gini"))
    cp.min3<-mod3$cptable[which.min(mod3$cptable[,"xerror"]),"CP"]
    tree3<-prune(mod3, cp=cp.min3)
    proba3 <- predict(tree3, newdata = data,type = "prob")
    cproba3 <- predict(tree3, newdata = testdata,type = "prob")
    update_cureb3<-c(1,1)
    update_pred3<-c(1,1)
    for (z in 1:n){update_cureb3[z]<-proba3[z,colnames(proba3)==1]}
    for (d in 1:m){update_pred3[d]<-cproba3[d,colnames(cproba3)==1]}
    uncureprob3<-as.numeric(as.character(uncureprob3))
    
    mod4 <- rpart(formula = uncureprob4~z1+z2, data = data,method = "class",
                  control = rpart.control(minsplit = bc[[1]],minbucket = round(bc[[1]]/3), 
                                          cp = bg[[1]]),xval = 10,parms = list(split="gini"))
    cp.min4<-mod4$cptable[which.min(mod4$cptable[,"xerror"]),"CP"]
    tree4<-prune(mod4, cp=cp.min4)
    proba4 <- predict(tree4, newdata = data,type = "prob")
    cproba4 <- predict(tree4, newdata = testdata,type = "prob")
    update_cureb4<-c(1,1)
    update_pred4<-c(1,1)
    for (z in 1:n){update_cureb4[z]<-proba4[z,colnames(proba4)==1]}
    for (d in 1:m){update_pred4[d]<-cproba4[d,colnames(cproba4)==1]}
    uncureprob4<-as.numeric(as.character(uncureprob4))
    
    mod5 <- rpart(formula = uncureprob5~z1+z2, data = data,method = "class",
                  control = rpart.control(minsplit = bc[[1]],minbucket = round(bc[[1]]/3), 
                                          cp = bg[[1]]),xval = 10,parms = list(split="gini"))
    cp.min5<-mod5$cptable[which.min(mod5$cptable[,"xerror"]),"CP"]
    tree5<-prune(mod5, cp=cp.min5)
    proba5 <- predict(tree5, newdata = data,type = "prob")
    cproba5 <- predict(tree5, newdata = testdata,type = "prob")
    update_cureb5<-c(1,1)
    update_pred5<-c(1,1)
    for (z in 1:n){update_cureb5[z]<-proba5[z,colnames(proba5)==1]}
    for (d in 1:m){update_pred5[d]<-cproba5[d,colnames(cproba5)==1]}
    uncureprob5<-as.numeric(as.character(uncureprob5))
    
    for (z in 1:n){update_cureb[z]<-(update_cureb1[z]+update_cureb2[z]
                                     +update_cureb3[z]+update_cureb4[z]+update_cureb5[z])/5}
    for (d in 1:m){update_pred[d]<-(update_pred1[d]+update_pred2[d]
                                    +update_pred3[d]+update_pred4[d]+update_pred5[d])/5}
    
    if(!is.null(offsetvar)) 
      update_cureb <- as.numeric(eval(parse(text = paste("glm", "(", "w~Z[,-1]
      +offset(offsetvar)",",family=quasibinomial(link='", link, "'",")",")",
                                                         sep = "")))$coef)
    
    update_beta <- optim(rep(0,ncol(X)), smrank, Time=Time,X=X,n=n,w=w,
                         Status=Status,method="Nelder-Mead",control=list(reltol=0.0001,
                                                                         maxit=500))$par
    update_s <- smsurv(error,Status,X,beta,w,model="aft")$survival
    update_s1 <-smsurv(error1,Status1,X1,beta,w1,model="aft")$survival
    
    convergence<-sum(c(mean(update_cureb)-mean(uncureprob),update_beta-beta,
                       mean(update_s)-mean(s))^2)
    uncureprob <- update_cureb
    uncurepred <- update_pred
    beta <- update_beta 
    s<-update_s
    s1<-update_s1
    i <- i+1
  }
  
  S1 = s # survival function of susceptible group
  S1.pred<-s1
  Sp = (1-uncureprob)+(uncureprob*S1)
  em.dt <- list(latencyfit=beta,Uncureprob=uncureprob,Uncurepred=uncurepred,
                S0=s,S1=S1,Sp=Sp,S1.pred=S1.pred,tau=convergence, Mod1=mod1, Mod2=mod2, 
                Mod3=mod3, Mod4=mod4, Mod5=mod5)
}




smcure.dt <-function(formula,cureform,offset=NULL,data,testdata,na.action=na.omit,
                     Var1=T,emmax=500,eps=1e-3,nboot=100)
{
  call <- match.call()
  #model <- match.arg(model)
  cat("Program is running..be patient...")
  ## prepare data
  n <- dim(data)[1]
  m <- dim(testdata)[1]
  mf <- model.frame(formula,data)
  mp <- model.frame(formula,testdata)
  cvars <- all.vars(cureform)
  Z <- as.matrix(cbind(rep(1,n),data[,cvars]))
  Z1 <- as.matrix(cbind(rep(1,m),testdata[,cvars]))
  colnames(Z) <- c("(Intercept)",cvars)
  if(!is.null(offset)) {
    offsetvar <- all.vars(offset)
    offsetvar<-data[,offsetvar]}
  else offsetvar <- NULL
  Y <- model.extract(mf,"response")
  Y1 <- model.extract(mp,"response")
  X <- model.matrix(attr(mf,"terms"), mf)
  X1 <- model.matrix(attr(mp,"terms"), mp)
  if (!inherits(Y, "Surv")) stop("Response must be a survival object")
  Time <- Y[,1]
  Time1 <- Y1[,1]
  Status <- Y[,2]
  Status1 <- Y1[,2]
  bnm <- colnames(Z)
  nb <- ncol(Z)
  betanm <- colnames(X)
  nbeta <- ncol(X)
  
  w <- Status
  nw<-c(1,1)
  for(i in 1: n) {
    nw[i]= w[i]
  }
  nw <- as.factor(nw)
  dataa=data.frame(nw,Z[,-1])
  obj3 <- tune.rpart(nw~z1+z2, data=dataa,minsplit = c(11,20,25), 
                     cp = c(0.001,0.005,0.01))
  bc<-obj3$best.parameters[1]
  bg<-obj3$best.parameters[2]
  
  mod <- rpart(formula = nw~z1+z2, data = data,method = "class",
               control = rpart.control(minsplit=bc[[1]],minbucket = round(bc[[1]]/3), 
                                       cp = bg[[1]]),xval =10,parms = list(split="gini"))
  cp.min<-mod$cptable[which.min(mod$cptable[,"xerror"]),"CP"]
  tree<-prune(mod, cp=cp.min)
  proba <- predict(tree, newdata = data,type = "prob")
  cproba <- predict(tree, newdata = testdata,type = "prob")
  
  uncureprob<-c(1,1)
  uncurepred<-c(1,1)
  for (i in 1:n){uncureprob[i]<-proba[i,colnames(proba)==1]}
  for (k in 1:m){uncurepred[k]<-cproba[k,colnames(cproba)==1]}
  nw<-as.numeric(as.character(nw))
  
  w <- as.factor(w)
  beta <- survreg(Surv(Time,Status)~X[,-1])$coef
  
  ## do EM algo
  emfit <- em.dt(Time,Time1,Status,Status1,X,X1,Z,Z1,offsetvar,uncureprob,
                 uncurepred,beta,emmax,eps,data,testdata)
  beta = emfit$latencyfit
  UN<-emfit$Uncureprob
  PRED<-emfit$Uncurepred
  MOD1<-emfit$Mod1
  MOD2<-emfit$Mod2
  MOD3<-emfit$Mod3
  MOD4<-emfit$Mod4
  MOD5<-emfit$Mod5
  S1 = emfit$S1
  S1.pred=emfit$S1.pred
  Sp = emfit$Sp
  S0 = emfit$S0
  if(Var1){
    uncure_boot<-matrix(rep(0,nboot*n), nrow=nboot)
    beta_boot<-matrix(rep(0,nboot*(nbeta)), nrow=nboot)
    
    iter <- matrix(rep(0,nboot),ncol=1)
    tempdata <- cbind(Time,Status,X,Z)
    data1<-subset(tempdata,Status==1);data0<-subset(tempdata,Status==0)
    n1<-nrow(data1);n0<-nrow(data0)  
    i<-1
    while (i<=nboot){
      print(i)
      id1<-sample(1:n1,n1,replace=TRUE);id0<-sample(1:n0,n0,replace=TRUE)
      bootdata<-rbind(data1[id1,],data0[id0,])
      
      
      bootX <- bootdata[,betanm]
      
      bootfit <- em.dt(bootdata[,1],bootdata[,2],bootX,bootZ,X1,Z1,offsetvar,UN,
                       PRED,beta,emmax,eps,data,testdata)
      beta_boot[i,] <- bootfit$latencyfit
      uncure_boot[i,] = bootfit$Uncureprob
      if (bootfit$tau<eps){
        i<-i+1}
    }#end of while
    beta_var <- apply(beta_boot, 2, var)
    uncure_var = apply(uncure_boot,2,var)
    beta_sd <- sqrt(beta_var)
    uncure_sd = sqrt(uncure_var)
    lower_uncure = UN - (1.96*uncure_sd)
    upper_uncure = UN + (1.96*uncure_sd)
  }
  
  fit<-list()
  class(fit) <- c("smcure.dt")
  fit$beta <- beta
  if(Var1){
    fit$beta_var <- beta_var
    fit$beta_sd <- beta_sd
    fit$beta_zvalue <- fit$beta/beta_sd
    fit$beta_pvalue <- (1-pnorm(abs(fit$beta_zvalue)))*2
    fit$lower_uncure = lower_uncure
    fit$upper_uncure = upper_uncure
  }
  
  cat("done.\n")
  fit$call <- call
  fit$bnm <- bnm
  fit$betanm <- betanm
  fit$UN<- UN
  fit$PRED<- PRED
  fit$Sp = Sp
  fit$S1 = S1
  fit$S1.pred=S1.pred
  fit$S0 = S0
  error=drop(log(Time)-beta%*%t(X))
  fit$error=error
  fit}



