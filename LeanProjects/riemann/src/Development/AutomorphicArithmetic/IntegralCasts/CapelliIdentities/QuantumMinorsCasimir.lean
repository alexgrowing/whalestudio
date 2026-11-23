import Mathlib

noncomputable def UpperTheory.Reformulated.B.QuantumMinorsCasimir.GlRel.{u_1} :
    {A : Type u_1} → [Ring A] → {n : Nat} → (Fin n → Fin n → A) → Prop :=
    fun {A : Type u_1} [inst : Ring A] {n : Nat} (E : Fin n → Fin n → A) ↦
      ∀ (a b c d : Fin n),
        @Eq A
          (@HSub.hSub A A A
            (@instHSub A
              (@SubNegMonoid.toSub A
                (@AddGroup.toSubNegMonoid A (@AddGroupWithOne.toAddGroup A (@Ring.toAddGroupWithOne A inst)))))
            (@HMul.hMul A A A (@instHMul A (@Distrib.toMul A (@instDistribOfSemiring A (@Ring.toSemiring A inst)))) (E a b)
              (E c d))
            (@HMul.hMul A A A (@instHMul A (@Distrib.toMul A (@instDistribOfSemiring A (@Ring.toSemiring A inst)))) (E c d)
              (E a b)))
          (@HSub.hSub A A A
            (@instHSub A
              (@SubNegMonoid.toSub A
                (@AddGroup.toSubNegMonoid A (@AddGroupWithOne.toAddGroup A (@Ring.toAddGroupWithOne A inst)))))
            (@ite A (@Eq (Fin n) b c) (instDecidableEqFin n b c) (E a d)
              (@OfNat.ofNat A (nat_lit 0)
                (@Zero.toOfNat0 A (@MulZeroClass.toZero A (@instMulZeroClassOfSemiring A (@Ring.toSemiring A inst))))))
            (@ite A (@Eq (Fin n) d a) (instDecidableEqFin n d a) (E c b)
              (@OfNat.ofNat A (nat_lit 0)
                (@Zero.toOfNat0 A (@MulZeroClass.toZero A (@instMulZeroClassOfSemiring A (@Ring.toSemiring A inst)))))))

noncomputable def UpperTheory.Reformulated.B.QuantumMinorsCasimir.Tm.{u_1} :
    {A : Type u_1} →
      [inst : Ring A] →
        [@Algebra Complex A Complex.instCommSemiring (@Ring.toSemiring A inst)] →
          {n : Nat} → (Fin n → Fin n → A) → Complex → Fin n → Fin n → A :=
    fun {A : Type u_1} [inst : Ring A] [inst_1 : @Algebra Complex A Complex.instCommSemiring (@Ring.toSemiring A inst)]
        {n : Nat} (E : Fin n → Fin n → A) (u : Complex) (a b : Fin n) ↦
      @HAdd.hAdd A A A (@instHAdd A (@Distrib.toAdd A (@instDistribOfSemiring A (@Ring.toSemiring A inst))))
        (@ite A (@Eq (Fin n) a b) (instDecidableEqFin n a b)
          (@DFunLike.coe
            (@RingHom Complex A
              (@Semiring.toNonAssocSemiring Complex (@CommSemiring.toSemiring Complex Complex.instCommSemiring))
              (@Semiring.toNonAssocSemiring A (@Ring.toSemiring A inst)))
            Complex (fun (x : Complex) ↦ A)
            (@RingHom.instFunLike Complex A
              (@Semiring.toNonAssocSemiring Complex (@CommSemiring.toSemiring Complex Complex.instCommSemiring))
              (@Semiring.toNonAssocSemiring A (@Ring.toSemiring A inst)))
            (@Algebra.algebraMap Complex A Complex.instCommSemiring (@Ring.toSemiring A inst) inst_1) u)
          (@OfNat.ofNat A (nat_lit 0)
            (@Zero.toOfNat0 A (@MulZeroClass.toZero A (@instMulZeroClassOfSemiring A (@Ring.toSemiring A inst))))))
        (E a b)

noncomputable def UpperTheory.Reformulated.B.QuantumMinorsCasimir.qminor.{u_1} :
    {A : Type u_1} →
      [inst : Ring A] →
        [@Algebra Complex A Complex.instCommSemiring (@Ring.toSemiring A inst)] →
          {n t : Nat} → (Fin n → Fin n → A) → (Fin t → Fin n) → (Fin t → Fin n) → Complex → A :=
    fun {A : Type u_1} [inst : Ring A] [inst_1 : @Algebra Complex A Complex.instCommSemiring (@Ring.toSemiring A inst)]
        {n t : Nat} (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (u : Complex) ↦
      ∑ σ : Equiv.Perm (Fin t),
        @HMul.hMul A A A (@instHMul A (@Distrib.toMul A (@instDistribOfSemiring A (@Ring.toSemiring A inst))))
          (@Int.cast A (@AddGroupWithOne.toIntCast A (@Ring.toAddGroupWithOne A inst))
            (@Units.val Int Int.instMonoid
              (@DFunLike.coe
                (@MonoidHom (Equiv.Perm (Fin t)) (@Units Int Int.instMonoid)
                  (@MulOneClass.toMulOne (Equiv.Perm (Fin t))
                    (@Monoid.toMulOneClass (Equiv.Perm (Fin t))
                      (@DivInvMonoid.toMonoid (Equiv.Perm (Fin t))
                        (@Group.toDivInvMonoid (Equiv.Perm (Fin t)) (@Equiv.Perm.permGroup (Fin t))))))
                  (@MulOneClass.toMulOne (@Units Int Int.instMonoid) (@Units.instMulOneClass Int Int.instMonoid)))
                (Equiv.Perm (Fin t)) (fun (x : Equiv.Perm (Fin t)) ↦ @Units Int Int.instMonoid)
                (@MonoidHom.instFunLike (Equiv.Perm (Fin t)) (@Units Int Int.instMonoid)
                  (@MulOneClass.toMulOne (Equiv.Perm (Fin t))
                    (@Monoid.toMulOneClass (Equiv.Perm (Fin t))
                      (@DivInvMonoid.toMonoid (Equiv.Perm (Fin t))
                        (@Group.toDivInvMonoid (Equiv.Perm (Fin t)) (@Equiv.Perm.permGroup (Fin t))))))
                  (@MulOneClass.toMulOne (@Units Int Int.instMonoid) (@Units.instMulOneClass Int Int.instMonoid)))
                (@Equiv.Perm.sign (Fin t) (instDecidableEqFin t) (Fin.fintype t)) σ)))
          (@List.prod A (@Distrib.toMul A (@instDistribOfSemiring A (@Ring.toSemiring A inst)))
            (@AddMonoidWithOne.toOne A (@AddGroupWithOne.toAddMonoidWithOne A (@Ring.toAddGroupWithOne A inst)))
            (@List.ofFn A t fun (k : Fin t) ↦
              @UpperTheory.Reformulated.B.QuantumMinorsCasimir.Tm A inst inst_1 n E
                (@HSub.hSub Complex Complex Complex (@instHSub Complex Complex.instSub) u
                  (@Nat.cast Complex Complex.instNatCast (@Fin.val t k)))
                (a
                  (@DFunLike.coe (Equiv.Perm (Fin t)) (Fin t) (fun (x : Fin t) ↦ Fin t)
                    (@EquivLike.toFunLike (Equiv.Perm (Fin t)) (Fin t) (Fin t) (@Equiv.instEquivLike (Fin t) (Fin t))) σ k))
                (b k)))

noncomputable def UpperTheory.Reformulated.B.QuantumMinorsCasimir.qdet.{u_1} :
    {A : Type u_1} →
      [inst : Ring A] →
        [@Algebra Complex A Complex.instCommSemiring (@Ring.toSemiring A inst)] →
          {n : Nat} → (Fin n → Fin n → A) → Complex → A :=
    fun {A : Type u_1} [inst : Ring A] [inst_1 : @Algebra Complex A Complex.instCommSemiring (@Ring.toSemiring A inst)]
        {n : Nat} (E : Fin n → Fin n → A) (u : Complex) ↦
      @UpperTheory.Reformulated.B.QuantumMinorsCasimir.qminor A inst inst_1 n n E (@id (Fin n)) (@id (Fin n)) u

theorem UpperTheory.Reformulated.B.QuantumMinorsCasimir.casimir :
    ∀ {V : Type} [inst : AddCommGroup V]
      [inst_1 : @_root_.Module Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst)]
      (E :
        Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            @Module.End Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst) inst_1),
      @UpperTheory.Reformulated.B.QuantumMinorsCasimir.GlRel (@Module.End Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst) inst_1)
          (@Module.End.instRing Complex V Complex.instSemiring inst inst_1)
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) E →
        ∀ (k : Complex) (φ : V),
          @Eq V
              (@HAdd.hAdd V V V
                (@instHAdd V
                  (@AddCommMagma.toAdd V
                    (@AddCommSemigroup.toAddCommMagma V
                      (@AddCommMonoid.toAddCommSemigroup V (@AddCommGroup.toAddCommMonoid V inst)))))
                (@DFunLike.coe (@Module.End Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst) inst_1) V
                  (fun (x : V) ↦ V)
                  (@LinearMap.instFunLike Complex Complex V V Complex.instSemiring Complex.instSemiring
                    (@AddCommGroup.toAddCommMonoid V inst) (@AddCommGroup.toAddCommMonoid V inst) inst_1 inst_1
                    (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)))
                  (E
                    (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                      (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0)))
                    (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                      (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0))))
                  φ)
                (@DFunLike.coe (@Module.End Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst) inst_1) V
                  (fun (x : V) ↦ V)
                  (@LinearMap.instFunLike Complex Complex V V Complex.instSemiring Complex.instSemiring
                    (@AddCommGroup.toAddCommMonoid V inst) (@AddCommGroup.toAddCommMonoid V inst) inst_1 inst_1
                    (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)))
                  (E
                    (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
                      (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 1)))
                    (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
                      (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 1))))
                  φ))
              (@OfNat.ofNat V (nat_lit 0)
                (@Zero.toOfNat0 V
                  (@NegZeroClass.toZero V
                    (@SubNegZeroMonoid.toNegZeroClass V
                      (@SubtractionMonoid.toSubNegZeroMonoid V
                        (@SubtractionCommMonoid.toSubtractionMonoid V (@AddCommGroup.toDivisionAddCommMonoid V inst))))))) →
            @Eq V
                (@HSub.hSub V V V
                  (@instHSub V (@SubNegMonoid.toSub V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst))))
                  (@DFunLike.coe (@Module.End Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst) inst_1)
                    V (fun (x : V) ↦ V)
                    (@LinearMap.instFunLike Complex Complex V V Complex.instSemiring Complex.instSemiring
                      (@AddCommGroup.toAddCommMonoid V inst) (@AddCommGroup.toAddCommMonoid V inst) inst_1 inst_1
                      (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)))
                    (E
                      (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                        (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0)))
                      (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
                        (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 1))))
                    φ)
                  (@DFunLike.coe (@Module.End Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst) inst_1)
                    V (fun (x : V) ↦ V)
                    (@LinearMap.instFunLike Complex Complex V V Complex.instSemiring Complex.instSemiring
                      (@AddCommGroup.toAddCommMonoid V inst) (@AddCommGroup.toAddCommMonoid V inst) inst_1 inst_1
                      (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)))
                    (E
                      (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
                        (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 1)))
                      (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                        (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0))))
                    φ))
                (@HSMul.hSMul Complex V V
                  (@instHSMul Complex V
                    (@SMulZeroClass.toSMul Complex V
                      (@AddZero.toZero V
                        (@AddZeroClass.toAddZero V
                          (@AddMonoid.toAddZeroClass V
                            (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst))))))
                      (@DistribSMul.toSMulZeroClass Complex V
                        (@AddMonoid.toAddZeroClass V
                          (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst))))
                        (@DistribMulAction.toDistribSMul Complex V (@Semiring.toMonoid Complex Complex.instSemiring)
                          (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst)))
                          (@Module.toDistribMulAction Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst)
                            inst_1)))))
                  (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I k) φ) →
              @Eq V
                  (@HSub.hSub V V V
                    (@instHSub V (@SubNegMonoid.toSub V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst))))
                    (@DFunLike.coe
                      (@Module.End Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst) inst_1) V
                      (fun (x : V) ↦ V)
                      (@LinearMap.instFunLike Complex Complex V V Complex.instSemiring Complex.instSemiring
                        (@AddCommGroup.toAddCommMonoid V inst) (@AddCommGroup.toAddCommMonoid V inst) inst_1 inst_1
                        (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)))
                      (E
                        (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                          (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0)))
                        (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                          (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0))))
                      φ)
                    (@DFunLike.coe
                      (@Module.End Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst) inst_1) V
                      (fun (x : V) ↦ V)
                      (@LinearMap.instFunLike Complex Complex V V Complex.instSemiring Complex.instSemiring
                        (@AddCommGroup.toAddCommMonoid V inst) (@AddCommGroup.toAddCommMonoid V inst) inst_1 inst_1
                        (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)))
                      (E
                        (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
                          (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 1)))
                        (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
                          (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 1))))
                      φ))
                  (@HSMul.hSMul Complex V V
                    (@instHSMul Complex V
                      (@SMulZeroClass.toSMul Complex V
                        (@AddZero.toZero V
                          (@AddZeroClass.toAddZero V
                            (@AddMonoid.toAddZeroClass V
                              (@SubNegMonoid.toAddMonoid V
                                (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst))))))
                        (@DistribSMul.toSMulZeroClass Complex V
                          (@AddMonoid.toAddZeroClass V
                            (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst))))
                          (@DistribMulAction.toDistribSMul Complex V (@Semiring.toMonoid Complex Complex.instSemiring)
                            (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst)))
                            (@Module.toDistribMulAction Complex V Complex.instSemiring
                              (@AddCommGroup.toAddCommMonoid V inst) inst_1)))))
                    Complex.I
                    (@HAdd.hAdd V V V
                      (@instHAdd V
                        (@AddCommMagma.toAdd V
                          (@AddCommSemigroup.toAddCommMagma V
                            (@AddCommMonoid.toAddCommSemigroup V (@AddCommGroup.toAddCommMonoid V inst)))))
                      (@DFunLike.coe
                        (@Module.End Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst) inst_1) V
                        (fun (x : V) ↦ V)
                        (@LinearMap.instFunLike Complex Complex V V Complex.instSemiring Complex.instSemiring
                          (@AddCommGroup.toAddCommMonoid V inst) (@AddCommGroup.toAddCommMonoid V inst) inst_1 inst_1
                          (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)))
                        (E
                          (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                            (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0)))
                          (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
                            (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 1))))
                        φ)
                      (@DFunLike.coe
                        (@Module.End Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst) inst_1) V
                        (fun (x : V) ↦ V)
                        (@LinearMap.instFunLike Complex Complex V V Complex.instSemiring Complex.instSemiring
                          (@AddCommGroup.toAddCommMonoid V inst) (@AddCommGroup.toAddCommMonoid V inst) inst_1 inst_1
                          (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)))
                        (E
                          (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
                            (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 1)))
                          (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                            (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0))))
                        φ))) →
                ∀ (u : Complex),
                  @Eq V
                    (@DFunLike.coe
                      (@Module.End Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst) inst_1) V
                      (fun (x : V) ↦ V)
                      (@LinearMap.instFunLike Complex Complex V V Complex.instSemiring Complex.instSemiring
                        (@AddCommGroup.toAddCommMonoid V inst) (@AddCommGroup.toAddCommMonoid V inst) inst_1 inst_1
                        (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)))
                      (@UpperTheory.Reformulated.B.QuantumMinorsCasimir.qdet
                        (@Module.End Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst) inst_1)
                        (@Module.End.instRing Complex V Complex.instSemiring inst inst_1)
                        (@Module.End.instAlgebra Complex Complex V Complex.instCommSemiring Complex.instSemiring
                          (@AddCommGroup.toAddCommMonoid V inst) inst_1 inst_1
                          (@smulCommClass_self Complex V (@CommRing.toCommMonoid Complex Complex.commRing)
                            (@DistribMulAction.toMulAction Complex V
                              (@CommMonoid.toMonoid Complex (@CommRing.toCommMonoid Complex Complex.commRing))
                              (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst))
                              (@Module.toDistribMulAction Complex V Complex.instSemiring
                                (@AddCommGroup.toAddCommMonoid V inst) inst_1)))
                          (@instSMulOfMul Complex Complex.instMul)
                          (@IsScalarTower.left Complex V (@Semiring.toMonoid Complex Complex.instSemiring)
                            (@DistribMulAction.toMulAction Complex V (@Semiring.toMonoid Complex Complex.instSemiring)
                              (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst))
                              (@Module.toDistribMulAction Complex V Complex.instSemiring
                                (@AddCommGroup.toAddCommMonoid V inst) inst_1))))
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) E
                        (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) u
                          (@HDiv.hDiv Complex Complex Complex
                            (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))
                            (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
                            (@OfNat.ofNat Complex (nat_lit 2)
                              (@instOfNatAtLeastTwo Complex (nat_lit 2) Complex.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
                      φ)
                    (@HSMul.hSMul Complex V V
                      (@instHSMul Complex V
                        (@SMulZeroClass.toSMul Complex V
                          (@AddZero.toZero V
                            (@AddZeroClass.toAddZero V
                              (@AddMonoid.toAddZeroClass V
                                (@SubNegMonoid.toAddMonoid V
                                  (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst))))))
                          (@DistribSMul.toSMulZeroClass Complex V
                            (@AddMonoid.toAddZeroClass V
                              (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst))))
                            (@DistribMulAction.toDistribSMul Complex V (@Semiring.toMonoid Complex Complex.instSemiring)
                              (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst)))
                              (@Module.toDistribMulAction Complex V Complex.instSemiring
                                (@AddCommGroup.toAddCommMonoid V inst) inst_1)))))
                      (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
                        (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) u
                          (@HDiv.hDiv Complex Complex Complex
                            (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))
                            (@HSub.hSub Complex Complex Complex (@instHSub Complex Complex.instSub) k
                              (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne)))
                            (@OfNat.ofNat Complex (nat_lit 2)
                              (@instOfNatAtLeastTwo Complex (nat_lit 2) Complex.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                        (@HSub.hSub Complex Complex Complex (@instHSub Complex Complex.instSub) u
                          (@HDiv.hDiv Complex Complex Complex
                            (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))
                            (@HSub.hSub Complex Complex Complex (@instHSub Complex Complex.instSub) k
                              (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne)))
                            (@OfNat.ofNat Complex (nat_lit 2)
                              (@instOfNatAtLeastTwo Complex (nat_lit 2) Complex.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
                      φ) := by
  intro V _ _ E h k φ h1 h2 h3 u
  have hq : ∀ v : ℂ, UpperTheory.Reformulated.B.QuantumMinorsCasimir.qdet E v φ =
      (v * (v - 1)) • φ + v • E 1 1 φ + (v - 1) • E 0 0 φ + E 0 0 (E 1 1 φ) - E 1 0 (E 0 1 φ) := by
    intro v
    have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
    have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
    unfold UpperTheory.Reformulated.B.QuantumMinorsCasimir.qdet UpperTheory.Reformulated.B.QuantumMinorsCasimir.qminor UpperTheory.Reformulated.B.QuantumMinorsCasimir.Tm
    rw [hu, Finset.sum_pair hne]
    simp [List.ofFn_succ, Module.algebraMap_end_apply]
    module
  have c (a b c d : Fin 2) := congrArg (fun f : Module.End ℂ V => f φ) (h a b c d)
  have cad := c 0 0 1 1
  have cab := c 0 0 0 1
  have cac := c 0 0 1 0
  have cdb := c 1 1 0 1
  have cdc := c 1 1 1 0
  have cbc := c 0 1 1 0
  simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true, Fin.zero_eq_one_iff,
    Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, LinearMap.zero_apply] at cad cab cac cdb cdc cbc
  have z (a b : Fin 2) := congrArg (E a b) h1
  have w (a b : Fin 2) := congrArg (E a b) h2
  have g (a b : Fin 2) := congrArg (E a b) h3
  simp only [map_add, map_sub, map_smul, map_zero] at z w g
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [hq]
  linear_combination (norm := skip) u • h1 + (1 / 4 : ℂ) • (z 0 0 + z 1 1 - (g 0 0 - g 1 1)
    - Complex.I • (g 0 1 + g 1 0) - (2 * Complex.I) • h2 + (w 0 1 - w 1 0) + (Complex.I * k) • h2
    + (2 : ℂ) • cad - Complex.I • (cab + cac - cdb - cdc) + (2 : ℂ) • cbc)
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring
