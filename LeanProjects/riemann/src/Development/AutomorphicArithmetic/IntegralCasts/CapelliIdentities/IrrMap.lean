import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qi38.Irr :
    {R : Type} →
      [inst : CommRing R] →
        {H : Type} →
          [inst_1 : Group H] →
            {n : Type} →
              [inst_2 : Fintype n] →
                [inst_3 : DecidableEq n] →
                  @MonoidHom H (Matrix n n R)
                      (@MulOneClass.toMulOne H
                        (@Monoid.toMulOneClass H (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst_1))))
                      (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid n R inst_2 inst_3
                        (@MulOneClass.toMulOne R
                          (@MulZeroOneClass.toMulOneClass R
                            (@instMulZeroOneClassOfSemiring R
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                        (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))) →
                    Prop :=
    fun {R : Type} [inst : CommRing R] {H : Type} [inst_1 : Group H] {n : Type} [inst_2 : Fintype n]
        [inst_3 : DecidableEq n]
        (r :
          @MonoidHom H (Matrix n n R)
            (@MulOneClass.toMulOne H (@Monoid.toMulOneClass H (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst_1))))
            (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid n R inst_2 inst_3
              (@MulOneClass.toMulOne R
                (@MulZeroOneClass.toMulOneClass R
                  (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
              (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))) ↦
      @Eq
        (@Submodule R (Matrix n n R) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@Matrix.addCommMonoid n n R
            (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
          (@Matrix.module n n R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
        (@Submodule.span R (Matrix n n R) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@Matrix.addCommMonoid n n R
            (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
          (@Matrix.module n n R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
          (@Set.range (Matrix n n R) H
            (@DFunLike.coe
              (@MonoidHom H (Matrix n n R)
                (@MulOneClass.toMulOne H
                  (@Monoid.toMulOneClass H (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst_1))))
                (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid n R inst_2 inst_3
                  (@MulOneClass.toMulOne R
                    (@MulZeroOneClass.toMulOneClass R
                      (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                  (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
              H (fun (x : H) ↦ Matrix n n R)
              (@MonoidHom.instFunLike H (Matrix n n R)
                (@MulOneClass.toMulOne H
                  (@Monoid.toMulOneClass H (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst_1))))
                (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid n R inst_2 inst_3
                  (@MulOneClass.toMulOne R
                    (@MulZeroOneClass.toMulOneClass R
                      (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                  (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
              r)))
        (@Top.top
          (@Submodule R (Matrix n n R) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@Matrix.addCommMonoid n n R
              (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
            (@Matrix.module n n R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
              (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
          (@Submodule.instTop R (Matrix n n R) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@Matrix.addCommMonoid n n R
              (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
            (@Matrix.module n n R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
              (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi38.modFun :
    {O M ι : Type} →
      [inst : CommRing O] →
        [inst_1 : AddCommGroup M] →
          [@_root_.Module O M (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst))
                (@AddCommGroup.toAddCommMonoid M inst_1)] →
            @_root_.Module O (ι → M) (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst))
              (@Pi.addCommMonoid ι (fun (a : ι) ↦ M) fun (i : ι) ↦ @AddCommGroup.toAddCommMonoid M inst_1) :=
    fun {O M ι : Type} [inst : CommRing O] [inst_1 : AddCommGroup M]
        [inst_2 :
          @_root_.Module O M (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst))
            (@AddCommGroup.toAddCommMonoid M inst_1)] ↦
      @Pi.Function.module ι O M (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst))
        (@AddCommGroup.toAddCommMonoid M inst_1) inst_2
attribute [local instance] UpperTheory.Reformulated.B.Qi38.modFun

noncomputable def UpperTheory.Reformulated.B.Qi38.mapRep :
    {R R' : Type} →
      [inst : CommRing R] →
        [inst_1 : CommRing R'] →
          {H : Type} →
            [inst_2 : Group H] →
              {n : Type} →
                [inst_3 : Fintype n] →
                  [inst_4 : DecidableEq n] →
                    @RingHom R R'
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                        (@Semiring.toNonAssocSemiring R'
                          (@CommSemiring.toSemiring R' (@CommRing.toCommSemiring R' inst_1))) →
                      @MonoidHom H (Matrix n n R)
                          (@MulOneClass.toMulOne H
                            (@Monoid.toMulOneClass H (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst_2))))
                          (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid n R inst_3 inst_4
                            (@MulOneClass.toMulOne R
                              (@MulZeroOneClass.toMulOneClass R
                                (@instMulZeroOneClassOfSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                            (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))) →
                        @MonoidHom H (Matrix n n R')
                          (@MulOneClass.toMulOne H
                            (@Monoid.toMulOneClass H (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst_2))))
                          (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid n R' inst_3 inst_4
                            (@MulOneClass.toMulOne R'
                              (@MulZeroOneClass.toMulOneClass R'
                                (@instMulZeroOneClassOfSemiring R'
                                  (@CommSemiring.toSemiring R' (@CommRing.toCommSemiring R' inst_1)))))
                            (@Semiring.toAddCommMonoid R'
                              (@CommSemiring.toSemiring R' (@CommRing.toCommSemiring R' inst_1)))) :=
    fun {R R' : Type} [inst : CommRing R] [inst_1 : CommRing R'] {H : Type} [inst_2 : Group H] {n : Type}
        [inst_3 : Fintype n] [inst_4 : DecidableEq n]
        (f :
          @RingHom R R' (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (@Semiring.toNonAssocSemiring R' (@CommSemiring.toSemiring R' (@CommRing.toCommSemiring R' inst_1))))
        (r :
          @MonoidHom H (Matrix n n R)
            (@MulOneClass.toMulOne H (@Monoid.toMulOneClass H (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst_2))))
            (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid n R inst_3 inst_4
              (@MulOneClass.toMulOne R
                (@MulZeroOneClass.toMulOneClass R
                  (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
              (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))) ↦
      @MonoidHom.comp H (Matrix n n R) (Matrix n n R')
        (@MulOneClass.toMulOne H (@Monoid.toMulOneClass H (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst_2))))
        (@MulOneClass.toMulOne (Matrix n n R)
          (@MulZeroOneClass.toMulOneClass (Matrix n n R)
            (@NonAssocSemiring.toMulZeroOneClass (Matrix n n R)
              (@Matrix.nonAssocSemiring n R
                (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) inst_3
                inst_4))))
        (@MulOneClass.toMulOne (Matrix n n R')
          (@MulZeroOneClass.toMulOneClass (Matrix n n R')
            (@NonAssocSemiring.toMulZeroOneClass (Matrix n n R')
              (@Matrix.nonAssocSemiring n R'
                (@Semiring.toNonAssocSemiring R' (@CommSemiring.toSemiring R' (@CommRing.toCommSemiring R' inst_1))) inst_3
                inst_4))))
        (@RingHom.toMonoidHom (Matrix n n R) (Matrix n n R')
          (@Matrix.nonAssocSemiring n R
            (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) inst_3 inst_4)
          (@Matrix.nonAssocSemiring n R'
            (@Semiring.toNonAssocSemiring R' (@CommSemiring.toSemiring R' (@CommRing.toCommSemiring R' inst_1))) inst_3
            inst_4)
          (@RingHom.mapMatrix n R R' inst_3 inst_4
            (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (@Semiring.toNonAssocSemiring R' (@CommSemiring.toSemiring R' (@CommRing.toCommSemiring R' inst_1))) f))
        r

private theorem UpperTheory.Reformulated.B.Qi38.aux {Γ E E' : Type} [Field E] [Field E'] (f : E →+* E') {n : Nat}
    (r : Γ → Matrix (Fin n) (Fin n) E) (hr : Submodule.span E (Set.range r) = ⊤)
    (N : Submodule E' (Fin n → E'))
    (hN : ∀ g v, v ∈ N → ((r g).map f).mulVec v ∈ N) : N = ⊥ ∨ N = ⊤ := by
  have key : ∀ A : Matrix (Fin n) (Fin n) E, ∀ v ∈ N, (A.map f).mulVec v ∈ N := by
    intro A v hv
    have hA : A ∈ Submodule.span E (Set.range r) := by rw [hr]; exact Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hN g v hv
    | zero =>
      rw [Matrix.map_zero _ (map_zero f), Matrix.zero_mulVec]
      exact N.zero_mem
    | add x y _ _ hx hy =>
      rw [Matrix.map_add _ (map_add f), Matrix.add_mulVec]
      exact N.add_mem hx hy
    | smul a x _ hx =>
      have h : (a • x).map f = f a • x.map f := by
        ext i j
        simp
      rw [h, Matrix.smul_mulVec]
      exact N.smul_mem _ hx
  refine or_iff_not_imp_left.2 fun hne => ?_
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff N).1 hne
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
  have hj' : v j ≠ 0 := hj
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  refine N.sum_mem fun i _ => ?_
  have h1 := N.smul_mem (w i * (v j)⁻¹) (key (Matrix.single i j 1) v hv)
  have h2 : (w i * (v j)⁻¹) • ((Matrix.single i j (1 : E)).map f).mulVec v = Pi.single i (w i) := by
    rw [Matrix.map_single, map_one, Matrix.single_mulVec]
    ext k
    by_cases hk : k = i
    · subst hk
      simp [hj']
    · simp [hk]
  rwa [h2] at h1

theorem UpperTheory.Reformulated.B.Qi38.irr_map :
    ∀ {Γ E E' : Type} [inst : Group Γ] [inst_1 : Field E] [inst_2 : Field E']
      (f :
        @RingHom E E'
          (@Semiring.toNonAssocSemiring E
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
          (@Semiring.toNonAssocSemiring E'
            (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))))
      {n : Nat}
      (r :
        @MonoidHom Γ (Matrix (Fin n) (Fin n) E)
          (@MulOneClass.toMulOne Γ (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst))))
          (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Fin n) E (Fin.fintype n) (instDecidableEqFin n)
            (@MulOneClass.toMulOne E
              (@MulZeroOneClass.toMulOneClass E
                (@instMulZeroOneClassOfSemiring E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))))
            (@Semiring.toAddCommMonoid E
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))))),
      @UpperTheory.Reformulated.B.Qi38.Irr E (@Field.toCommRing E inst_1) Γ inst (Fin n) (Fin.fintype n) (instDecidableEqFin n) r →
        ∀
          (N :
            @Submodule E' (Fin n → E')
              (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid E'
                  (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
              (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                (@Semiring.toModule E'
                  (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2)))))),
          (∀ (g : Γ) (v : Fin n → E'),
              @Membership.mem (Fin n → E')
                  (@Submodule E' (Fin n → E')
                    (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                    (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                      @Semiring.toAddCommMonoid E'
                        (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                    (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                      (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                      (@Semiring.toModule E'
                        (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                  (@SetLike.instMembership
                    (@Submodule E' (Fin n → E')
                      (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                      (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                        @Semiring.toAddCommMonoid E'
                          (@DivisionSemiring.toSemiring E'
                            (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                      (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                        (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                        (@Semiring.toModule E'
                          (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                    (Fin n → E')
                    (@Submodule.setLike E' (Fin n → E')
                      (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                      (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                        @Semiring.toAddCommMonoid E'
                          (@DivisionSemiring.toSemiring E'
                            (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                      (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                        (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                        (@Semiring.toModule E'
                          (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2)))))))
                  N v →
                @Membership.mem (Fin n → E')
                  (@Submodule E' (Fin n → E')
                    (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                    (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                      @Semiring.toAddCommMonoid E'
                        (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                    (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                      (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                      (@Semiring.toModule E'
                        (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                  (@SetLike.instMembership
                    (@Submodule E' (Fin n → E')
                      (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                      (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                        @Semiring.toAddCommMonoid E'
                          (@DivisionSemiring.toSemiring E'
                            (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                      (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                        (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                        (@Semiring.toModule E'
                          (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                    (Fin n → E')
                    (@Submodule.setLike E' (Fin n → E')
                      (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                      (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                        @Semiring.toAddCommMonoid E'
                          (@DivisionSemiring.toSemiring E'
                            (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                      (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                        (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                        (@Semiring.toModule E'
                          (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2)))))))
                  N
                  (@Matrix.mulVec (Fin n) (Fin n) E'
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring E'
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing E'
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing E'
                          (@CommRing.toNonUnitalCommRing E' (@Field.toCommRing E' inst_2)))))
                    (Fin.fintype n)
                    (@DFunLike.coe
                      (@MonoidHom Γ (Matrix (Fin n) (Fin n) E')
                        (@MulOneClass.toMulOne Γ
                          (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst))))
                        (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Fin n) E' (Fin.fintype n)
                          (instDecidableEqFin n)
                          (@MulOneClass.toMulOne E'
                            (@MulZeroOneClass.toMulOneClass E'
                              (@instMulZeroOneClassOfSemiring E'
                                (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                          (@Semiring.toAddCommMonoid E'
                            (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                      Γ (fun (x : Γ) ↦ Matrix (Fin n) (Fin n) E')
                      (@MonoidHom.instFunLike Γ (Matrix (Fin n) (Fin n) E')
                        (@MulOneClass.toMulOne Γ
                          (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst))))
                        (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Fin n) E' (Fin.fintype n)
                          (instDecidableEqFin n)
                          (@MulOneClass.toMulOne E'
                            (@MulZeroOneClass.toMulOneClass E'
                              (@instMulZeroOneClassOfSemiring E'
                                (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                          (@Semiring.toAddCommMonoid E'
                            (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                      (@UpperTheory.Reformulated.B.Qi38.mapRep E E' (@Field.toCommRing E inst_1) (@Field.toCommRing E' inst_2) Γ inst
                        (Fin n) (Fin.fintype n) (instDecidableEqFin n) f r)
                      g)
                    v)) →
            Or
              (@Eq
                (@Submodule E' (Fin n → E')
                  (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                  (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                    @Semiring.toAddCommMonoid E'
                      (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                  (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                    (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                    (@Semiring.toModule E'
                      (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                N
                (@Bot.bot
                  (@Submodule E' (Fin n → E')
                    (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                    (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                      @Semiring.toAddCommMonoid E'
                        (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                    (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                      (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                      (@Semiring.toModule E'
                        (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                  (@Submodule.instBot E' (Fin n → E')
                    (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                    (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                      @Semiring.toAddCommMonoid E'
                        (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                    (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                      (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                      (@Semiring.toModule E'
                        (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))))
              (@Eq
                (@Submodule E' (Fin n → E')
                  (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                  (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                    @Semiring.toAddCommMonoid E'
                      (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                  (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                    (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                    (@Semiring.toModule E'
                      (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                N
                (@Top.top
                  (@Submodule E' (Fin n → E')
                    (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                    (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                      @Semiring.toAddCommMonoid E'
                        (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                    (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                      (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                      (@Semiring.toModule E'
                        (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                  (@Submodule.instTop E' (Fin n → E')
                    (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                    (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                      @Semiring.toAddCommMonoid E'
                        (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                    (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                      (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                      (@Semiring.toModule E'
                        (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2)))))))) := by
  intro Γ E E' _ _ _ f n r hr N hN
  exact UpperTheory.Reformulated.B.Qi38.aux f (fun g => r g) hr N hN
