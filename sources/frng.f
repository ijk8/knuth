      SUBROUTINE RNARRY(AA,N)
C       FORTRAN 77 version of "ran_array"
C       from Seminumerical Algorithms by D E Knuth, 3rd edition (1997)
C       including the MODIFICATIONS made in the 9th printing (2002)
C       and a bugfix to make this compatible with rng.c (2012)
C       ********* see the book for explanations and caveats! *********
      IMPLICIT INTEGER (A-Z)
      DIMENSION AA(*)
      PARAMETER (KK=100)
      PARAMETER (LL=37)
      PARAMETER (MM=2**30)
      COMMON /RSTATE/ RANX(KK)
      SAVE /RSTATE/
      DO 1 J=1,KK
 1       AA(J)=RANX(J)
      DO 2 J=KK+1,N
         AA(J)=AA(J-KK)-AA(J-LL)
         IF (AA(J) .LT. 0) AA(J)=AA(J)+MM
 2    CONTINUE
      DO 3 J=1,LL
         RANX(J)=AA(N+J-KK)-AA(N+J-LL)
         IF (RANX(J) .LT. 0) RANX(J)=RANX(J)+MM
 3    CONTINUE
      DO 4 J=LL+1,KK
         RANX(J)=AA(N+J-KK)-RANX(J-LL)
         IF (RANX(J) .LT. 0) RANX(J)=RANX(J)+MM
 4    CONTINUE
      END


      SUBROUTINE RNSTRT(SEED)
      IMPLICIT INTEGER (A-Z)
      PARAMETER (KK=100)
      PARAMETER (LL=37)
      PARAMETER (MM=2**30)
      PARAMETER (TT=70)
      PARAMETER (KKK=KK+KK-1)
      DIMENSION X(KKK)
      COMMON /RSTATE/ RANX(KK)
      SAVE /RSTATE/
      IF (SEED .LT. 0) THEN
         SSEED=MM-1-MOD(-1-SEED,MM)
      ELSE
         SSEED=MOD(SEED,MM)
      END IF
      SS=SSEED-MOD(SSEED,2)+2
      DO 1 J=1,KK
         X(J)=SS
         SS=SS+SS
         IF (SS .GE. MM) SS=SS-MM+2
 1    CONTINUE
      X(2)=X(2)+1
      SS=SSEED
      T=TT-1
 10   DO 12 J=KK,2,-1
         X(J+J-1)=X(J)
 12      X(J+J-2)=0
      DO 14 J=KKK,KK+1,-1
         X(J-(KK-LL))=X(J-(KK-LL))-X(J)
         IF (X(J-(KK-LL)) .LT. 0) X(J-(KK-LL))=X(J-(KK-LL))+MM
         X(J-KK)=X(J-KK)-X(J)
         IF (X(J-KK) .LT. 0) X(J-KK)=X(J-KK)+MM
 14   CONTINUE
      IF (MOD(SS,2) .EQ. 1) THEN
         DO 16 J=KK,1,-1
 16      X(J+1)=X(J)
         X(1)=X(KK+1)
         X(LL+1)=X(LL+1)-X(KK+1)
         IF (X(LL+1) .LT. 0) X(LL+1)=X(LL+1)+MM
       END IF
       IF (SS .NE. 0) THEN
          SS=SS/2
       ELSE
          T=T-1
       END IF
       IF (T .GT. 0) GO TO 10
       DO 20 J=1,LL
 20       RANX(J+KK-LL)=X(J)
       DO 21 J=LL+1,KK
 21       RANX(J-LL)=X(J)
       DO 22 J=1,10
 22       CALL RNARRY(X,KKK)
       END


       PROGRAM MAIN
C      a rudimentary test program:
       IMPLICIT INTEGER (A-Z)
       DIMENSION A(2009)
       EXTERNAL RNSTRT, RNARRY
       CALL RNSTRT(310952)
       DO 1 I=1,2009
          CALL RNARRY(A,1009)
 1     CONTINUE 
       PRINT '(I15)',A(1)
C                   the number should be 995235265
       CALL RNSTRT(310952)
       DO 2 I=1,1009
          CALL RNARRY(A,2009)
 2     CONTINUE 
       PRINT '(I15)',A(1)
C                                 again, 995235265
       END
