import Mathlib

private theorem UpperTheory.Reformulated.B.FreeModuleQuotient.aux {R S M : Type} [CommRing R] [CommRing S] [AddCommGroup M]
    [Module R M] (s : S →+* R) (I K : Ideal S) (hIK : I ≤ K) (c : ℕ)
    (e : M ≃+ (Fin c → S ⧸ I)) (he : ∀ (z : S) (x : M), e (s z • x) = z • e x) :
    ∃ e' : (M ⧸ (Ideal.map s K • ⊤ : Submodule R M)) ≃+ (Fin c → S ⧸ K),
      ∀ (a : S) (x : M ⧸ (Ideal.map s K • ⊤ : Submodule R M)), e' (s a • x) = a • e' x := by
  classical
  let φ : M →+ (Fin c → S ⧸ K) :=
    { toFun := fun x i => Ideal.Quotient.factor hIK (e x i)
      map_zero' := by funext i; simp
      map_add' := by intro x y; funext i; simp }
  have hφ : ∀ x i, φ x i = Ideal.Quotient.factor hIK (e x i) := fun _ _ => rfl
  have hsm : ∀ (a : S) (x : M), φ (s a • x) = a • φ x := by
    intro a x
    funext i
    rw [Pi.smul_apply, hφ, hφ, he, Pi.smul_apply]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e x i)
    rw [← hy]
    rfl
  have hsurj : Function.Surjective φ := by
    intro y
    choose t ht using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨e.symm (fun i => Ideal.Quotient.mk I (t i)), ?_⟩
    funext i
    rw [hφ, e.apply_symm_apply, Ideal.Quotient.factor_mk, ht]
  have h1 : ∀ r ∈ Ideal.map s K, ∀ x : M, φ (r • x) = 0 := by
    intro r hr
    refine Submodule.span_induction (p := fun r _ => ∀ x : M, φ (r • x) = 0) ?_ ?_ ?_ ?_ hr
    · rintro _ ⟨k, hk, rfl⟩ x
      rw [hsm]
      funext i
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (φ x i)
      rw [Pi.smul_apply, ← hy]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (K.mul_mem_right y hk)
    · intro x; simp
    · intro a b _ _ ha hb x
      rw [add_smul, map_add, ha, hb, add_zero]
    · intro a b _ hb x
      rw [smul_eq_mul, mul_comm, mul_smul, hb]
  have hker : ∀ x : M, x ∈ (Ideal.map s K • ⊤ : Submodule R M) ↔ φ x = 0 := by
    intro x
    constructor
    · intro hx
      refine Submodule.smul_induction_on (p := fun x => φ x = 0) hx ?_ ?_
      · intro r hr n _; exact h1 r hr n
      · intro a b ha hb; rw [map_add, ha, hb, add_zero]
    · intro hx
      choose t ht using fun i => Ideal.Quotient.mk_surjective (e x i)
      have htK : ∀ i, t i ∈ K := by
        intro i
        have := congrFun hx i
        rw [hφ, ← ht, Ideal.Quotient.factor_mk] at this
        exact Ideal.Quotient.eq_zero_iff_mem.1 this
      have hxe : x = ∑ i, s (t i) • e.symm (Pi.single i 1) := by
        apply e.injective
        rw [map_sum]
        simp only [he, e.apply_symm_apply]
        rw [← Finset.univ_sum_single (e x)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Pi.single_smul, ← ht, ← Algebra.algebraMap_eq_smul_one]
        rfl
      rw [hxe]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem_smul (Ideal.mem_map_of_mem s (htK i)) Submodule.mem_top
  let ψ : (M ⧸ (Ideal.map s K • ⊤ : Submodule R M)) →+ (Fin c → S ⧸ K) :=
    QuotientAddGroup.lift (Ideal.map s K • ⊤ : Submodule R M).toAddSubgroup φ
      (fun x hx => (hker x).1 hx)
  have hψ : ∀ x : M, ψ (Submodule.Quotient.mk x) = φ x := fun _ => rfl
  have hbij : Function.Bijective ψ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [hψ] at hx
      exact (Submodule.Quotient.mk_eq_zero _).2 ((hker y).2 hx)
    · intro y
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨Submodule.Quotient.mk x, hψ x⟩
  refine ⟨AddEquiv.ofBijective ψ hbij, fun a x => ?_⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul]
  exact hsm a y

theorem UpperTheory.Reformulated.B.FreeModuleQuotient.freeN_quot :
    ∀ {R S M : Type} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : AddCommGroup M]
      [inst_3 :
        @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid M inst_2)]
      (s :
        @RingHom S R (@Semiring.toNonAssocSemiring S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
      (I K : @Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))),
      @LE.le (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
          (@Preorder.toLE (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
            (@PartialOrder.toPreorder (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
              (@Submodule.instPartialOrder S S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                (@Semiring.toAddCommMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                (@Semiring.toModule S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))))))
          I K →
        ∀ (c : Nat)
          (e :
            @AddEquiv M
              (Fin c →
                @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                  (@Ideal.instHasQuotient_1 S inst_1) I)
              (@AddCommMagma.toAdd M
                (@AddCommSemigroup.toAddCommMagma M
                  (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_2))))
              (@Pi.instAdd (Fin c)
                (fun (a : Fin c) ↦
                  @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                    (@Ideal.instHasQuotient_1 S inst_1) I)
                fun (i : Fin c) ↦
                @Distrib.toAdd
                  (@HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                    (@Ideal.instHasQuotient_1 S inst_1) I)
                  (@instDistribOfSemiring
                    (@HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                      (@Ideal.instHasQuotient_1 S inst_1) I)
                    (@Ideal.Quotient.semiring S inst_1 I)))),
          (∀ (z : S) (x : M),
              @Eq
                (Fin c →
                  @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                    (@Ideal.instHasQuotient_1 S inst_1) I)
                (@DFunLike.coe
                  (@AddEquiv M
                    (Fin c →
                      @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                        (@Ideal.instHasQuotient_1 S inst_1) I)
                    (@AddCommMagma.toAdd M
                      (@AddCommSemigroup.toAddCommMagma M
                        (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_2))))
                    (@Pi.instAdd (Fin c)
                      (fun (a : Fin c) ↦
                        @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                          (@Ideal.instHasQuotient_1 S inst_1) I)
                      fun (i : Fin c) ↦
                      @Distrib.toAdd
                        (@HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                          (@Ideal.instHasQuotient_1 S inst_1) I)
                        (@instDistribOfSemiring
                          (@HasQuotient.Quotient S
                            (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Ideal.instHasQuotient_1 S inst_1) I)
                          (@Ideal.Quotient.semiring S inst_1 I))))
                  M
                  (fun (x : M) ↦
                    Fin c →
                      @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                        (@Ideal.instHasQuotient_1 S inst_1) I)
                  (@EquivLike.toFunLike
                    (@AddEquiv M
                      (Fin c →
                        @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                          (@Ideal.instHasQuotient_1 S inst_1) I)
                      (@AddCommMagma.toAdd M
                        (@AddCommSemigroup.toAddCommMagma M
                          (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_2))))
                      (@Pi.instAdd (Fin c)
                        (fun (a : Fin c) ↦
                          @HasQuotient.Quotient S
                            (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Ideal.instHasQuotient_1 S inst_1) I)
                        fun (i : Fin c) ↦
                        @Distrib.toAdd
                          (@HasQuotient.Quotient S
                            (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Ideal.instHasQuotient_1 S inst_1) I)
                          (@instDistribOfSemiring
                            (@HasQuotient.Quotient S
                              (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Ideal.instHasQuotient_1 S inst_1) I)
                            (@Ideal.Quotient.semiring S inst_1 I))))
                    M
                    (Fin c →
                      @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                        (@Ideal.instHasQuotient_1 S inst_1) I)
                    (@AddEquiv.instEquivLike M
                      (Fin c →
                        @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                          (@Ideal.instHasQuotient_1 S inst_1) I)
                      (@AddCommMagma.toAdd M
                        (@AddCommSemigroup.toAddCommMagma M
                          (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_2))))
                      (@Pi.instAdd (Fin c)
                        (fun (a : Fin c) ↦
                          @HasQuotient.Quotient S
                            (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Ideal.instHasQuotient_1 S inst_1) I)
                        fun (i : Fin c) ↦
                        @Distrib.toAdd
                          (@HasQuotient.Quotient S
                            (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Ideal.instHasQuotient_1 S inst_1) I)
                          (@instDistribOfSemiring
                            (@HasQuotient.Quotient S
                              (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Ideal.instHasQuotient_1 S inst_1) I)
                            (@Ideal.Quotient.semiring S inst_1 I)))))
                  e
                  (@HSMul.hSMul R M M
                    (@instHSMul R M
                      (@SMulZeroClass.toSMul R M
                        (@AddZero.toZero M
                          (@AddZeroClass.toAddZero M
                            (@AddMonoid.toAddZeroClass M
                              (@SubNegMonoid.toAddMonoid M
                                (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_2))))))
                        (@DistribSMul.toSMulZeroClass R M
                          (@AddMonoid.toAddZeroClass M
                            (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_2))))
                          (@DistribMulAction.toDistribSMul R M
                            (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_2)))
                            (@Module.toDistribMulAction R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                    (@DFunLike.coe
                      (@RingHom S R
                        (@Semiring.toNonAssocSemiring S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                      S (fun (x : S) ↦ R)
                      (@RingHom.instFunLike S R
                        (@Semiring.toNonAssocSemiring S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                      s z)
                    x))
                (@HSMul.hSMul S
                  (Fin c →
                    @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                      (@Ideal.instHasQuotient_1 S inst_1) I)
                  (Fin c →
                    @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                      (@Ideal.instHasQuotient_1 S inst_1) I)
                  (@instHSMul S
                    (Fin c →
                      @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                        (@Ideal.instHasQuotient_1 S inst_1) I)
                    (@Function.hasSMul (Fin c) S
                      (@HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                        (@Ideal.instHasQuotient_1 S inst_1) I)
                      (@Submodule.Quotient.instSMul S S (@CommRing.toRing S inst_1)
                        (@Ring.toAddCommGroup S (@CommRing.toRing S inst_1))
                        (@Semiring.toModule S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))) I)))
                  z
                  (@DFunLike.coe
                    (@AddEquiv M
                      (Fin c →
                        @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                          (@Ideal.instHasQuotient_1 S inst_1) I)
                      (@AddCommMagma.toAdd M
                        (@AddCommSemigroup.toAddCommMagma M
                          (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_2))))
                      (@Pi.instAdd (Fin c)
                        (fun (a : Fin c) ↦
                          @HasQuotient.Quotient S
                            (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Ideal.instHasQuotient_1 S inst_1) I)
                        fun (i : Fin c) ↦
                        @Distrib.toAdd
                          (@HasQuotient.Quotient S
                            (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Ideal.instHasQuotient_1 S inst_1) I)
                          (@instDistribOfSemiring
                            (@HasQuotient.Quotient S
                              (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Ideal.instHasQuotient_1 S inst_1) I)
                            (@Ideal.Quotient.semiring S inst_1 I))))
                    M
                    (fun (x : M) ↦
                      Fin c →
                        @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                          (@Ideal.instHasQuotient_1 S inst_1) I)
                    (@EquivLike.toFunLike
                      (@AddEquiv M
                        (Fin c →
                          @HasQuotient.Quotient S
                            (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Ideal.instHasQuotient_1 S inst_1) I)
                        (@AddCommMagma.toAdd M
                          (@AddCommSemigroup.toAddCommMagma M
                            (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_2))))
                        (@Pi.instAdd (Fin c)
                          (fun (a : Fin c) ↦
                            @HasQuotient.Quotient S
                              (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Ideal.instHasQuotient_1 S inst_1) I)
                          fun (i : Fin c) ↦
                          @Distrib.toAdd
                            (@HasQuotient.Quotient S
                              (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Ideal.instHasQuotient_1 S inst_1) I)
                            (@instDistribOfSemiring
                              (@HasQuotient.Quotient S
                                (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Ideal.instHasQuotient_1 S inst_1) I)
                              (@Ideal.Quotient.semiring S inst_1 I))))
                      M
                      (Fin c →
                        @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                          (@Ideal.instHasQuotient_1 S inst_1) I)
                      (@AddEquiv.instEquivLike M
                        (Fin c →
                          @HasQuotient.Quotient S
                            (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Ideal.instHasQuotient_1 S inst_1) I)
                        (@AddCommMagma.toAdd M
                          (@AddCommSemigroup.toAddCommMagma M
                            (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_2))))
                        (@Pi.instAdd (Fin c)
                          (fun (a : Fin c) ↦
                            @HasQuotient.Quotient S
                              (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Ideal.instHasQuotient_1 S inst_1) I)
                          fun (i : Fin c) ↦
                          @Distrib.toAdd
                            (@HasQuotient.Quotient S
                              (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Ideal.instHasQuotient_1 S inst_1) I)
                            (@instDistribOfSemiring
                              (@HasQuotient.Quotient S
                                (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Ideal.instHasQuotient_1 S inst_1) I)
                              (@Ideal.Quotient.semiring S inst_1 I)))))
                    e x))) →
            ∃ (e' :
              @AddEquiv
                (@HasQuotient.Quotient M
                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                  (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                  (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                    (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                      (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                        (@IsScalarTower.left R M
                          (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                          (@DistribMulAction.toMulAction R M
                            (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                            (@Module.toDistribMulAction R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                    (@Ideal.map S R
                      (@RingHom S R
                        (@Semiring.toNonAssocSemiring S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@RingHom.instFunLike S R
                        (@Semiring.toNonAssocSemiring S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                      s K)
                    (@Top.top
                      (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                      (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                (Fin c →
                  @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                    (@Ideal.instHasQuotient_1 S inst_1) K)
                (@AddCommMagma.toAdd
                  (@HasQuotient.Quotient M
                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                    (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                    (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                      (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                      (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                        (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                        (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                          (@IsScalarTower.left R M
                            (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@DistribMulAction.toMulAction R M
                              (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                              (@Module.toDistribMulAction R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                      (@Ideal.map S R
                        (@RingHom S R
                          (@Semiring.toNonAssocSemiring S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@RingHom.instFunLike S R
                          (@Semiring.toNonAssocSemiring S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                        s K)
                      (@Top.top
                        (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                        (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                  (@AddCommSemigroup.toAddCommMagma
                    (@HasQuotient.Quotient M
                      (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                      (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                      (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                        (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                        (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                        (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                            (@IsScalarTower.left R M
                              (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@DistribMulAction.toMulAction R M
                                (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                (@Module.toDistribMulAction R M
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                        (@Ideal.map S R
                          (@RingHom S R
                            (@Semiring.toNonAssocSemiring S
                              (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                          (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@RingHom.instFunLike S R
                            (@Semiring.toNonAssocSemiring S
                              (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                          s K)
                        (@Top.top
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                    (@AddCommMonoid.toAddCommSemigroup
                      (@HasQuotient.Quotient M
                        (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                        (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                        (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                              (@IsScalarTower.left R M
                                (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@DistribMulAction.toMulAction R M
                                  (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                  (@Module.toDistribMulAction R M
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                          (@Ideal.map S R
                            (@RingHom S R
                              (@Semiring.toNonAssocSemiring S
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.instFunLike S R
                              (@Semiring.toNonAssocSemiring S
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            s K)
                          (@Top.top
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                      (@Submodule.Quotient.addCommMonoid R M (@CommRing.toRing R inst) inst_2 inst_3
                        (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                              (@IsScalarTower.left R M
                                (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@DistribMulAction.toMulAction R M
                                  (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                  (@Module.toDistribMulAction R M
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                          (@Ideal.map S R
                            (@RingHom S R
                              (@Semiring.toNonAssocSemiring S
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.instFunLike S R
                              (@Semiring.toNonAssocSemiring S
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            s K)
                          (@Top.top
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))))
                (@Pi.instAdd (Fin c)
                  (fun (a : Fin c) ↦
                    @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                      (@Ideal.instHasQuotient_1 S inst_1) K)
                  fun (i : Fin c) ↦
                  @Distrib.toAdd
                    (@HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                      (@Ideal.instHasQuotient_1 S inst_1) K)
                    (@instDistribOfSemiring
                      (@HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                        (@Ideal.instHasQuotient_1 S inst_1) K)
                      (@Ideal.Quotient.semiring S inst_1 K)))),
              ∀ (a : S)
                (x :
                  @HasQuotient.Quotient M
                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                    (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                    (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                      (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                      (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                        (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                        (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                          (@IsScalarTower.left R M
                            (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@DistribMulAction.toMulAction R M
                              (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                              (@Module.toDistribMulAction R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                      (@Ideal.map S R
                        (@RingHom S R
                          (@Semiring.toNonAssocSemiring S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@RingHom.instFunLike S R
                          (@Semiring.toNonAssocSemiring S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                        s K)
                      (@Top.top
                        (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                        (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))),
                @Eq
                  (Fin c →
                    @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                      (@Ideal.instHasQuotient_1 S inst_1) K)
                  (@DFunLike.coe
                    (@AddEquiv
                      (@HasQuotient.Quotient M
                        (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                        (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                        (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                              (@IsScalarTower.left R M
                                (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@DistribMulAction.toMulAction R M
                                  (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                  (@Module.toDistribMulAction R M
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                          (@Ideal.map S R
                            (@RingHom S R
                              (@Semiring.toNonAssocSemiring S
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.instFunLike S R
                              (@Semiring.toNonAssocSemiring S
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            s K)
                          (@Top.top
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                      (Fin c →
                        @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                          (@Ideal.instHasQuotient_1 S inst_1) K)
                      (@AddCommMagma.toAdd
                        (@HasQuotient.Quotient M
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                          (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                (@IsScalarTower.left R M
                                  (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@DistribMulAction.toMulAction R M
                                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                    (@Module.toDistribMulAction R M
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                            (@Ideal.map S R
                              (@RingHom S R
                                (@Semiring.toNonAssocSemiring S
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.instFunLike S R
                                (@Semiring.toNonAssocSemiring S
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              s K)
                            (@Top.top
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                        (@AddCommSemigroup.toAddCommMagma
                          (@HasQuotient.Quotient M
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                            (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                  (@IsScalarTower.left R M
                                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@DistribMulAction.toMulAction R M
                                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                      (@Module.toDistribMulAction R M
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                              (@Ideal.map S R
                                (@RingHom S R
                                  (@Semiring.toNonAssocSemiring S
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@RingHom.instFunLike S R
                                  (@Semiring.toNonAssocSemiring S
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                s K)
                              (@Top.top
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                          (@AddCommMonoid.toAddCommSemigroup
                            (@HasQuotient.Quotient M
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                              (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                    (@IsScalarTower.left R M
                                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@DistribMulAction.toMulAction R M
                                        (@Semiring.toMonoid R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                        (@Module.toDistribMulAction R M
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                (@Ideal.map S R
                                  (@RingHom S R
                                    (@Semiring.toNonAssocSemiring S
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@RingHom.instFunLike S R
                                    (@Semiring.toNonAssocSemiring S
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  s K)
                                (@Top.top
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                            (@Submodule.Quotient.addCommMonoid R M (@CommRing.toRing R inst) inst_2 inst_3
                              (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                    (@IsScalarTower.left R M
                                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@DistribMulAction.toMulAction R M
                                        (@Semiring.toMonoid R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                        (@Module.toDistribMulAction R M
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                (@Ideal.map S R
                                  (@RingHom S R
                                    (@Semiring.toNonAssocSemiring S
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@RingHom.instFunLike S R
                                    (@Semiring.toNonAssocSemiring S
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  s K)
                                (@Top.top
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))))
                      (@Pi.instAdd (Fin c)
                        (fun (a : Fin c) ↦
                          @HasQuotient.Quotient S
                            (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Ideal.instHasQuotient_1 S inst_1) K)
                        fun (i : Fin c) ↦
                        @Distrib.toAdd
                          (@HasQuotient.Quotient S
                            (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Ideal.instHasQuotient_1 S inst_1) K)
                          (@instDistribOfSemiring
                            (@HasQuotient.Quotient S
                              (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Ideal.instHasQuotient_1 S inst_1) K)
                            (@Ideal.Quotient.semiring S inst_1 K))))
                    (@HasQuotient.Quotient M
                      (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                      (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                      (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                        (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                        (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                        (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                            (@IsScalarTower.left R M
                              (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@DistribMulAction.toMulAction R M
                                (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                (@Module.toDistribMulAction R M
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                        (@Ideal.map S R
                          (@RingHom S R
                            (@Semiring.toNonAssocSemiring S
                              (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                          (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@RingHom.instFunLike S R
                            (@Semiring.toNonAssocSemiring S
                              (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                          s K)
                        (@Top.top
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                    (fun
                        (x :
                          @HasQuotient.Quotient M
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                            (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                  (@IsScalarTower.left R M
                                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@DistribMulAction.toMulAction R M
                                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                      (@Module.toDistribMulAction R M
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                              (@Ideal.map S R
                                (@RingHom S R
                                  (@Semiring.toNonAssocSemiring S
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@RingHom.instFunLike S R
                                  (@Semiring.toNonAssocSemiring S
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                s K)
                              (@Top.top
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))) ↦
                      Fin c →
                        @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                          (@Ideal.instHasQuotient_1 S inst_1) K)
                    (@EquivLike.toFunLike
                      (@AddEquiv
                        (@HasQuotient.Quotient M
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                          (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                (@IsScalarTower.left R M
                                  (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@DistribMulAction.toMulAction R M
                                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                    (@Module.toDistribMulAction R M
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                            (@Ideal.map S R
                              (@RingHom S R
                                (@Semiring.toNonAssocSemiring S
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.instFunLike S R
                                (@Semiring.toNonAssocSemiring S
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              s K)
                            (@Top.top
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                        (Fin c →
                          @HasQuotient.Quotient S
                            (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Ideal.instHasQuotient_1 S inst_1) K)
                        (@AddCommMagma.toAdd
                          (@HasQuotient.Quotient M
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                            (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                  (@IsScalarTower.left R M
                                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@DistribMulAction.toMulAction R M
                                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                      (@Module.toDistribMulAction R M
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                              (@Ideal.map S R
                                (@RingHom S R
                                  (@Semiring.toNonAssocSemiring S
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@RingHom.instFunLike S R
                                  (@Semiring.toNonAssocSemiring S
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                s K)
                              (@Top.top
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                          (@AddCommSemigroup.toAddCommMagma
                            (@HasQuotient.Quotient M
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                              (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                    (@IsScalarTower.left R M
                                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@DistribMulAction.toMulAction R M
                                        (@Semiring.toMonoid R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                        (@Module.toDistribMulAction R M
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                (@Ideal.map S R
                                  (@RingHom S R
                                    (@Semiring.toNonAssocSemiring S
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@RingHom.instFunLike S R
                                    (@Semiring.toNonAssocSemiring S
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  s K)
                                (@Top.top
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                            (@AddCommMonoid.toAddCommSemigroup
                              (@HasQuotient.Quotient M
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                                (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      M (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                      (@IsScalarTower.left R M
                                        (@Semiring.toMonoid R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        (@DistribMulAction.toMulAction R M
                                          (@Semiring.toMonoid R
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                          (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                          (@Module.toDistribMulAction R M
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                  (@Ideal.map S R
                                    (@RingHom S R
                                      (@Semiring.toNonAssocSemiring S
                                        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@RingHom.instFunLike S R
                                      (@Semiring.toNonAssocSemiring S
                                        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    s K)
                                  (@Top.top
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                              (@Submodule.Quotient.addCommMonoid R M (@CommRing.toRing R inst) inst_2 inst_3
                                (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      M (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                      (@IsScalarTower.left R M
                                        (@Semiring.toMonoid R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        (@DistribMulAction.toMulAction R M
                                          (@Semiring.toMonoid R
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                          (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                          (@Module.toDistribMulAction R M
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                  (@Ideal.map S R
                                    (@RingHom S R
                                      (@Semiring.toNonAssocSemiring S
                                        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@RingHom.instFunLike S R
                                      (@Semiring.toNonAssocSemiring S
                                        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    s K)
                                  (@Top.top
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))))
                        (@Pi.instAdd (Fin c)
                          (fun (a : Fin c) ↦
                            @HasQuotient.Quotient S
                              (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Ideal.instHasQuotient_1 S inst_1) K)
                          fun (i : Fin c) ↦
                          @Distrib.toAdd
                            (@HasQuotient.Quotient S
                              (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Ideal.instHasQuotient_1 S inst_1) K)
                            (@instDistribOfSemiring
                              (@HasQuotient.Quotient S
                                (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Ideal.instHasQuotient_1 S inst_1) K)
                              (@Ideal.Quotient.semiring S inst_1 K))))
                      (@HasQuotient.Quotient M
                        (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                        (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                        (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                              (@IsScalarTower.left R M
                                (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@DistribMulAction.toMulAction R M
                                  (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                  (@Module.toDistribMulAction R M
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                          (@Ideal.map S R
                            (@RingHom S R
                              (@Semiring.toNonAssocSemiring S
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.instFunLike S R
                              (@Semiring.toNonAssocSemiring S
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            s K)
                          (@Top.top
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                      (Fin c →
                        @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                          (@Ideal.instHasQuotient_1 S inst_1) K)
                      (@AddEquiv.instEquivLike
                        (@HasQuotient.Quotient M
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                          (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                (@IsScalarTower.left R M
                                  (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@DistribMulAction.toMulAction R M
                                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                    (@Module.toDistribMulAction R M
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                            (@Ideal.map S R
                              (@RingHom S R
                                (@Semiring.toNonAssocSemiring S
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.instFunLike S R
                                (@Semiring.toNonAssocSemiring S
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              s K)
                            (@Top.top
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                        (Fin c →
                          @HasQuotient.Quotient S
                            (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Ideal.instHasQuotient_1 S inst_1) K)
                        (@AddCommMagma.toAdd
                          (@HasQuotient.Quotient M
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                            (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                  (@IsScalarTower.left R M
                                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@DistribMulAction.toMulAction R M
                                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                      (@Module.toDistribMulAction R M
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                              (@Ideal.map S R
                                (@RingHom S R
                                  (@Semiring.toNonAssocSemiring S
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@RingHom.instFunLike S R
                                  (@Semiring.toNonAssocSemiring S
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                s K)
                              (@Top.top
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                          (@AddCommSemigroup.toAddCommMagma
                            (@HasQuotient.Quotient M
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                              (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                    (@IsScalarTower.left R M
                                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@DistribMulAction.toMulAction R M
                                        (@Semiring.toMonoid R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                        (@Module.toDistribMulAction R M
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                (@Ideal.map S R
                                  (@RingHom S R
                                    (@Semiring.toNonAssocSemiring S
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@RingHom.instFunLike S R
                                    (@Semiring.toNonAssocSemiring S
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  s K)
                                (@Top.top
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                            (@AddCommMonoid.toAddCommSemigroup
                              (@HasQuotient.Quotient M
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                                (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      M (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                      (@IsScalarTower.left R M
                                        (@Semiring.toMonoid R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        (@DistribMulAction.toMulAction R M
                                          (@Semiring.toMonoid R
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                          (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                          (@Module.toDistribMulAction R M
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                  (@Ideal.map S R
                                    (@RingHom S R
                                      (@Semiring.toNonAssocSemiring S
                                        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@RingHom.instFunLike S R
                                      (@Semiring.toNonAssocSemiring S
                                        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    s K)
                                  (@Top.top
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                              (@Submodule.Quotient.addCommMonoid R M (@CommRing.toRing R inst) inst_2 inst_3
                                (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      M (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                      (@IsScalarTower.left R M
                                        (@Semiring.toMonoid R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        (@DistribMulAction.toMulAction R M
                                          (@Semiring.toMonoid R
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                          (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                          (@Module.toDistribMulAction R M
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                  (@Ideal.map S R
                                    (@RingHom S R
                                      (@Semiring.toNonAssocSemiring S
                                        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@RingHom.instFunLike S R
                                      (@Semiring.toNonAssocSemiring S
                                        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    s K)
                                  (@Top.top
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))))
                        (@Pi.instAdd (Fin c)
                          (fun (a : Fin c) ↦
                            @HasQuotient.Quotient S
                              (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Ideal.instHasQuotient_1 S inst_1) K)
                          fun (i : Fin c) ↦
                          @Distrib.toAdd
                            (@HasQuotient.Quotient S
                              (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Ideal.instHasQuotient_1 S inst_1) K)
                            (@instDistribOfSemiring
                              (@HasQuotient.Quotient S
                                (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Ideal.instHasQuotient_1 S inst_1) K)
                              (@Ideal.Quotient.semiring S inst_1 K)))))
                    e'
                    (@HSMul.hSMul R
                      (@HasQuotient.Quotient M
                        (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                        (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                        (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                              (@IsScalarTower.left R M
                                (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@DistribMulAction.toMulAction R M
                                  (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                  (@Module.toDistribMulAction R M
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                          (@Ideal.map S R
                            (@RingHom S R
                              (@Semiring.toNonAssocSemiring S
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.instFunLike S R
                              (@Semiring.toNonAssocSemiring S
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            s K)
                          (@Top.top
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                      (@HasQuotient.Quotient M
                        (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                        (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                        (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                              (@IsScalarTower.left R M
                                (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@DistribMulAction.toMulAction R M
                                  (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                  (@Module.toDistribMulAction R M
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                          (@Ideal.map S R
                            (@RingHom S R
                              (@Semiring.toNonAssocSemiring S
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.instFunLike S R
                              (@Semiring.toNonAssocSemiring S
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            s K)
                          (@Top.top
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                      (@instHSMul R
                        (@HasQuotient.Quotient M
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                          (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                (@IsScalarTower.left R M
                                  (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@DistribMulAction.toMulAction R M
                                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                    (@Module.toDistribMulAction R M
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                            (@Ideal.map S R
                              (@RingHom S R
                                (@Semiring.toNonAssocSemiring S
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.instFunLike S R
                                (@Semiring.toNonAssocSemiring S
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              s K)
                            (@Top.top
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                        (@Submodule.Quotient.instSMul R M (@CommRing.toRing R inst) inst_2 inst_3
                          (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                (@IsScalarTower.left R M
                                  (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@DistribMulAction.toMulAction R M
                                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                    (@Module.toDistribMulAction R M
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                            (@Ideal.map S R
                              (@RingHom S R
                                (@Semiring.toNonAssocSemiring S
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.instFunLike S R
                                (@Semiring.toNonAssocSemiring S
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              s K)
                            (@Top.top
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                      (@DFunLike.coe
                        (@RingHom S R
                          (@Semiring.toNonAssocSemiring S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                        S (fun (x : S) ↦ R)
                        (@RingHom.instFunLike S R
                          (@Semiring.toNonAssocSemiring S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                        s a)
                      x))
                  (@HSMul.hSMul S
                    (Fin c →
                      @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                        (@Ideal.instHasQuotient_1 S inst_1) K)
                    (Fin c →
                      @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                        (@Ideal.instHasQuotient_1 S inst_1) K)
                    (@instHSMul S
                      (Fin c →
                        @HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                          (@Ideal.instHasQuotient_1 S inst_1) K)
                      (@Function.hasSMul (Fin c) S
                        (@HasQuotient.Quotient S (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                          (@Ideal.instHasQuotient_1 S inst_1) K)
                        (@Submodule.Quotient.instSMul S S (@CommRing.toRing S inst_1)
                          (@Ring.toAddCommGroup S (@CommRing.toRing S inst_1))
                          (@Semiring.toModule S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))) K)))
                    a
                    (@DFunLike.coe
                      (@AddEquiv
                        (@HasQuotient.Quotient M
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                          (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                (@IsScalarTower.left R M
                                  (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@DistribMulAction.toMulAction R M
                                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                    (@Module.toDistribMulAction R M
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                            (@Ideal.map S R
                              (@RingHom S R
                                (@Semiring.toNonAssocSemiring S
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.instFunLike S R
                                (@Semiring.toNonAssocSemiring S
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              s K)
                            (@Top.top
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                        (Fin c →
                          @HasQuotient.Quotient S
                            (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Ideal.instHasQuotient_1 S inst_1) K)
                        (@AddCommMagma.toAdd
                          (@HasQuotient.Quotient M
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                            (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                  (@IsScalarTower.left R M
                                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@DistribMulAction.toMulAction R M
                                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                      (@Module.toDistribMulAction R M
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                              (@Ideal.map S R
                                (@RingHom S R
                                  (@Semiring.toNonAssocSemiring S
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@RingHom.instFunLike S R
                                  (@Semiring.toNonAssocSemiring S
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                s K)
                              (@Top.top
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                          (@AddCommSemigroup.toAddCommMagma
                            (@HasQuotient.Quotient M
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                              (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                    (@IsScalarTower.left R M
                                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@DistribMulAction.toMulAction R M
                                        (@Semiring.toMonoid R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                        (@Module.toDistribMulAction R M
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                (@Ideal.map S R
                                  (@RingHom S R
                                    (@Semiring.toNonAssocSemiring S
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@RingHom.instFunLike S R
                                    (@Semiring.toNonAssocSemiring S
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  s K)
                                (@Top.top
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                            (@AddCommMonoid.toAddCommSemigroup
                              (@HasQuotient.Quotient M
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                                (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      M (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                      (@IsScalarTower.left R M
                                        (@Semiring.toMonoid R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        (@DistribMulAction.toMulAction R M
                                          (@Semiring.toMonoid R
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                          (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                          (@Module.toDistribMulAction R M
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                  (@Ideal.map S R
                                    (@RingHom S R
                                      (@Semiring.toNonAssocSemiring S
                                        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@RingHom.instFunLike S R
                                      (@Semiring.toNonAssocSemiring S
                                        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    s K)
                                  (@Top.top
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                              (@Submodule.Quotient.addCommMonoid R M (@CommRing.toRing R inst) inst_2 inst_3
                                (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      M (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                      (@IsScalarTower.left R M
                                        (@Semiring.toMonoid R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        (@DistribMulAction.toMulAction R M
                                          (@Semiring.toMonoid R
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                          (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                          (@Module.toDistribMulAction R M
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                  (@Ideal.map S R
                                    (@RingHom S R
                                      (@Semiring.toNonAssocSemiring S
                                        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@RingHom.instFunLike S R
                                      (@Semiring.toNonAssocSemiring S
                                        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    s K)
                                  (@Top.top
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))))
                        (@Pi.instAdd (Fin c)
                          (fun (a : Fin c) ↦
                            @HasQuotient.Quotient S
                              (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Ideal.instHasQuotient_1 S inst_1) K)
                          fun (i : Fin c) ↦
                          @Distrib.toAdd
                            (@HasQuotient.Quotient S
                              (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Ideal.instHasQuotient_1 S inst_1) K)
                            (@instDistribOfSemiring
                              (@HasQuotient.Quotient S
                                (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Ideal.instHasQuotient_1 S inst_1) K)
                              (@Ideal.Quotient.semiring S inst_1 K))))
                      (@HasQuotient.Quotient M
                        (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                        (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                        (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                              (@IsScalarTower.left R M
                                (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@DistribMulAction.toMulAction R M
                                  (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                  (@Module.toDistribMulAction R M
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                          (@Ideal.map S R
                            (@RingHom S R
                              (@Semiring.toNonAssocSemiring S
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.instFunLike S R
                              (@Semiring.toNonAssocSemiring S
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            s K)
                          (@Top.top
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                      (fun
                          (x :
                            @HasQuotient.Quotient M
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                              (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                    (@IsScalarTower.left R M
                                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@DistribMulAction.toMulAction R M
                                        (@Semiring.toMonoid R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                        (@Module.toDistribMulAction R M
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                (@Ideal.map S R
                                  (@RingHom S R
                                    (@Semiring.toNonAssocSemiring S
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@RingHom.instFunLike S R
                                    (@Semiring.toNonAssocSemiring S
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  s K)
                                (@Top.top
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))) ↦
                        Fin c →
                          @HasQuotient.Quotient S
                            (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Ideal.instHasQuotient_1 S inst_1) K)
                      (@EquivLike.toFunLike
                        (@AddEquiv
                          (@HasQuotient.Quotient M
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                            (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                  (@IsScalarTower.left R M
                                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@DistribMulAction.toMulAction R M
                                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                      (@Module.toDistribMulAction R M
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                              (@Ideal.map S R
                                (@RingHom S R
                                  (@Semiring.toNonAssocSemiring S
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@RingHom.instFunLike S R
                                  (@Semiring.toNonAssocSemiring S
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                s K)
                              (@Top.top
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                          (Fin c →
                            @HasQuotient.Quotient S
                              (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Ideal.instHasQuotient_1 S inst_1) K)
                          (@AddCommMagma.toAdd
                            (@HasQuotient.Quotient M
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                              (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                    (@IsScalarTower.left R M
                                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@DistribMulAction.toMulAction R M
                                        (@Semiring.toMonoid R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                        (@Module.toDistribMulAction R M
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                (@Ideal.map S R
                                  (@RingHom S R
                                    (@Semiring.toNonAssocSemiring S
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@RingHom.instFunLike S R
                                    (@Semiring.toNonAssocSemiring S
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  s K)
                                (@Top.top
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                            (@AddCommSemigroup.toAddCommMagma
                              (@HasQuotient.Quotient M
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                                (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      M (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                      (@IsScalarTower.left R M
                                        (@Semiring.toMonoid R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        (@DistribMulAction.toMulAction R M
                                          (@Semiring.toMonoid R
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                          (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                          (@Module.toDistribMulAction R M
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                  (@Ideal.map S R
                                    (@RingHom S R
                                      (@Semiring.toNonAssocSemiring S
                                        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@RingHom.instFunLike S R
                                      (@Semiring.toNonAssocSemiring S
                                        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    s K)
                                  (@Top.top
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                              (@AddCommMonoid.toAddCommSemigroup
                                (@HasQuotient.Quotient M
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                                  (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                      (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@Semiring.toModule R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        M (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                        (@IsScalarTower.left R M
                                          (@Semiring.toMonoid R
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                          (@DistribMulAction.toMulAction R M
                                            (@Semiring.toMonoid R
                                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                            (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                            (@Module.toDistribMulAction R M
                                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                    (@Ideal.map S R
                                      (@RingHom S R
                                        (@Semiring.toNonAssocSemiring S
                                          (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                        (@Semiring.toNonAssocSemiring R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@RingHom.instFunLike S R
                                        (@Semiring.toNonAssocSemiring S
                                          (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                        (@Semiring.toNonAssocSemiring R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                      s K)
                                    (@Top.top
                                      (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                      (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                                (@Submodule.Quotient.addCommMonoid R M (@CommRing.toRing R inst) inst_2 inst_3
                                  (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                      (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@Semiring.toModule R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        M (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                        (@IsScalarTower.left R M
                                          (@Semiring.toMonoid R
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                          (@DistribMulAction.toMulAction R M
                                            (@Semiring.toMonoid R
                                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                            (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                            (@Module.toDistribMulAction R M
                                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                    (@Ideal.map S R
                                      (@RingHom S R
                                        (@Semiring.toNonAssocSemiring S
                                          (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                        (@Semiring.toNonAssocSemiring R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@RingHom.instFunLike S R
                                        (@Semiring.toNonAssocSemiring S
                                          (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                        (@Semiring.toNonAssocSemiring R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                      s K)
                                    (@Top.top
                                      (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                      (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))))
                          (@Pi.instAdd (Fin c)
                            (fun (a : Fin c) ↦
                              @HasQuotient.Quotient S
                                (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Ideal.instHasQuotient_1 S inst_1) K)
                            fun (i : Fin c) ↦
                            @Distrib.toAdd
                              (@HasQuotient.Quotient S
                                (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Ideal.instHasQuotient_1 S inst_1) K)
                              (@instDistribOfSemiring
                                (@HasQuotient.Quotient S
                                  (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                  (@Ideal.instHasQuotient_1 S inst_1) K)
                                (@Ideal.Quotient.semiring S inst_1 K))))
                        (@HasQuotient.Quotient M
                          (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                          (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                (@IsScalarTower.left R M
                                  (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@DistribMulAction.toMulAction R M
                                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                    (@Module.toDistribMulAction R M
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                            (@Ideal.map S R
                              (@RingHom S R
                                (@Semiring.toNonAssocSemiring S
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.instFunLike S R
                                (@Semiring.toNonAssocSemiring S
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              s K)
                            (@Top.top
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                        (Fin c →
                          @HasQuotient.Quotient S
                            (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                            (@Ideal.instHasQuotient_1 S inst_1) K)
                        (@AddEquiv.instEquivLike
                          (@HasQuotient.Quotient M
                            (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                            (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                            (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                  (@IsScalarTower.left R M
                                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@DistribMulAction.toMulAction R M
                                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                      (@Module.toDistribMulAction R M
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                              (@Ideal.map S R
                                (@RingHom S R
                                  (@Semiring.toNonAssocSemiring S
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@RingHom.instFunLike S R
                                  (@Semiring.toNonAssocSemiring S
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                s K)
                              (@Top.top
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                          (Fin c →
                            @HasQuotient.Quotient S
                              (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                              (@Ideal.instHasQuotient_1 S inst_1) K)
                          (@AddCommMagma.toAdd
                            (@HasQuotient.Quotient M
                              (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                              (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                              (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) M
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                    (@IsScalarTower.left R M
                                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@DistribMulAction.toMulAction R M
                                        (@Semiring.toMonoid R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                        (@Module.toDistribMulAction R M
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                (@Ideal.map S R
                                  (@RingHom S R
                                    (@Semiring.toNonAssocSemiring S
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@RingHom.instFunLike S R
                                    (@Semiring.toNonAssocSemiring S
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  s K)
                                (@Top.top
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                            (@AddCommSemigroup.toAddCommMagma
                              (@HasQuotient.Quotient M
                                (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                                (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      M (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                      (@IsScalarTower.left R M
                                        (@Semiring.toMonoid R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        (@DistribMulAction.toMulAction R M
                                          (@Semiring.toMonoid R
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                          (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                          (@Module.toDistribMulAction R M
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                  (@Ideal.map S R
                                    (@RingHom S R
                                      (@Semiring.toNonAssocSemiring S
                                        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@RingHom.instFunLike S R
                                      (@Semiring.toNonAssocSemiring S
                                        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    s K)
                                  (@Top.top
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                              (@AddCommMonoid.toAddCommSemigroup
                                (@HasQuotient.Quotient M
                                  (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                  (@Submodule.hasQuotient R M (@CommRing.toRing R inst) inst_2 inst_3)
                                  (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                      (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@Semiring.toModule R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        M (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                        (@IsScalarTower.left R M
                                          (@Semiring.toMonoid R
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                          (@DistribMulAction.toMulAction R M
                                            (@Semiring.toMonoid R
                                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                            (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                            (@Module.toDistribMulAction R M
                                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                    (@Ideal.map S R
                                      (@RingHom S R
                                        (@Semiring.toNonAssocSemiring S
                                          (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                        (@Semiring.toNonAssocSemiring R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@RingHom.instFunLike S R
                                        (@Semiring.toNonAssocSemiring S
                                          (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                        (@Semiring.toNonAssocSemiring R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                      s K)
                                    (@Top.top
                                      (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                      (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))
                                (@Submodule.Quotient.addCommMonoid R M (@CommRing.toRing R inst) inst_2 inst_3
                                  (@HSMul.hSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                    (@instHSMul (@Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                      (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                      (@Submodule.instSMul R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@Semiring.toModule R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                        M (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                                        (@IsScalarTower.left R M
                                          (@Semiring.toMonoid R
                                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                          (@DistribMulAction.toMulAction R M
                                            (@Semiring.toMonoid R
                                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                            (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_2))
                                            (@Module.toDistribMulAction R M
                                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                                    (@Ideal.map S R
                                      (@RingHom S R
                                        (@Semiring.toNonAssocSemiring S
                                          (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                        (@Semiring.toNonAssocSemiring R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1))
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@RingHom.instFunLike S R
                                        (@Semiring.toNonAssocSemiring S
                                          (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                        (@Semiring.toNonAssocSemiring R
                                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                      s K)
                                    (@Top.top
                                      (@Submodule R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                                      (@Submodule.instTop R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))))
                          (@Pi.instAdd (Fin c)
                            (fun (a : Fin c) ↦
                              @HasQuotient.Quotient S
                                (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Ideal.instHasQuotient_1 S inst_1) K)
                            fun (i : Fin c) ↦
                            @Distrib.toAdd
                              (@HasQuotient.Quotient S
                                (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                (@Ideal.instHasQuotient_1 S inst_1) K)
                              (@instDistribOfSemiring
                                (@HasQuotient.Quotient S
                                  (@Ideal S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_1)))
                                  (@Ideal.instHasQuotient_1 S inst_1) K)
                                (@Ideal.Quotient.semiring S inst_1 K)))))
                      e' x)) := by
  intro R S M _ _ _ _ s I K hIK c e he
  exact UpperTheory.Reformulated.B.FreeModuleQuotient.aux s I K hIK c e he
