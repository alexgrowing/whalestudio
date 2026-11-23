import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LocGraded

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem lc_of_fib {Γ A B : Type} [TopologicalSpace Γ] {f : Γ → A} {g : Γ → B} (hf : IsLocallyConstant f)
    (h : ∀ x y, f x = f y → g x = g y) : IsLocallyConstant g := by
  rw [IsLocallyConstant.iff_eventually_eq] at hf ⊢
  exact fun x => (hf x).mono fun y hy => h _ _ hy

private theorem exists_grpTop (Γ : Type) [Group Γ] (T : TopologicalSpace Γ) :
    ∃ T' : TopologicalSpace Γ, @IsTopologicalGroup Γ T' _ ∧
      ∀ (M : Type) [Monoid M] (φ : Γ →* M), @IsLocallyConstant Γ M T φ ↔ @IsLocallyConstant Γ M T' φ := by
  classical
  let S := {K : Subgroup Γ // K.Normal ∧ @IsLocallyConstant Γ (Γ ⧸ K) T (fun x => (x : Γ ⧸ K))}
  let ρ : ∀ K : S, Γ →* Equiv.Perm (Γ ⧸ K.1) := fun K => MulAction.toPermHom Γ (Γ ⧸ K.1)
  let T' : TopologicalSpace Γ := ⨅ K : S, TopologicalSpace.induced (ρ K) ⊥
  have htg : ∀ K : S, @IsTopologicalGroup Γ (TopologicalSpace.induced (ρ K) ⊥) _ := by
    intro K
    letI : TopologicalSpace (Equiv.Perm (Γ ⧸ K.1)) := ⊥
    haveI : DiscreteTopology (Equiv.Perm (Γ ⧸ K.1)) := ⟨rfl⟩
    exact topologicalGroup_induced (ρ K)
  refine ⟨T', topologicalGroup_iInf htg, ?_⟩
  intro M _ φ
  have hρT : ∀ K : S, @IsLocallyConstant Γ _ T (ρ K) := by
    intro K
    refine @lc_of_fib Γ _ _ T _ _ K.2.2 ?_
    intro x y hxy
    ext c
    induction c using QuotientGroup.induction_on with
    | H z =>
      simp only [ρ, MulAction.toPermHom_apply, MulAction.toPerm_apply, MulAction.Quotient.smul_coe]
      rw [QuotientGroup.eq] at hxy ⊢
      have := K.2.1.conj_mem _ hxy z⁻¹
      simpa [mul_assoc] using this
  have hρT' : ∀ K : S, @IsLocallyConstant Γ _ T' (ρ K) := by
    intro K
    letI : TopologicalSpace (Equiv.Perm (Γ ⧸ K.1)) := ⊥
    haveI : DiscreteTopology (Equiv.Perm (Γ ⧸ K.1)) := ⟨rfl⟩
    rw [@IsLocallyConstant.iff_continuous Γ _ T']
    apply continuous_iInf_dom (i := K)
    exact continuous_induced_dom
  constructor
  · intro hφ
    let K : Subgroup Γ := φ.ker
    have hK : ∀ x y : Γ, (x : Γ ⧸ K) = y ↔ φ x = φ y := by
      intro x y
      rw [QuotientGroup.eq, MonoidHom.mem_ker, map_mul]
      constructor
      · intro e
        calc φ x = φ x * (φ x⁻¹ * φ y) := by rw [e, mul_one]
          _ = φ y := by rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
      · intro e
        rw [← e, ← map_mul, inv_mul_cancel, map_one]
    have hmk : @IsLocallyConstant Γ (Γ ⧸ K) T (fun x => (x : Γ ⧸ K)) :=
      @lc_of_fib Γ _ _ T _ _ hφ fun x y e => (hK x y).2 e
    let K' : S := ⟨K, MonoidHom.normal_ker φ, hmk⟩
    refine @lc_of_fib Γ _ _ T' _ _ (hρT' K') ?_
    intro x y hxy
    have := congrArg (fun e : Equiv.Perm (Γ ⧸ K) => e ((1 : Γ) : Γ ⧸ K)) hxy
    simp only [ρ, K', MulAction.toPermHom_apply, MulAction.toPerm_apply, MulAction.Quotient.smul_coe, mul_one] at this
    rw [smul_eq_mul, smul_eq_mul, mul_one, mul_one] at this
    exact (hK x y).1 this
  · intro hφ
    have hid : @Continuous Γ Γ T T' id := by
      apply continuous_iInf_rng.2
      intro K
      apply continuous_induced_rng.2
      letI : TopologicalSpace (Equiv.Perm (Γ ⧸ K.1)) := ⊥
      haveI : DiscreteTopology (Equiv.Perm (Γ ⧸ K.1)) := ⟨rfl⟩
      exact (@IsLocallyConstant.iff_continuous Γ _ T _ _ _).1 (hρT K)
    exact @IsLocallyConstant.comp_continuous Γ Γ M T T' φ id hφ hid

private def tr {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [Fintype ι] [DecidableEq ι]
    {rbar : Γ →* Matrix ι ι (ResidueField O)} (T T' : TopologicalSpace Γ)
    (h : ∀ (M : Type) [Monoid M] (φ : Γ →* M), @IsLocallyConstant Γ M T φ → @IsLocallyConstant Γ M T' φ)
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : @Lift O _ _ Γ ι _ T _ _ rbar R _ _ _) :
    @Lift O _ _ Γ ι _ T' _ _ rbar R _ _ _ :=
  @Lift.mk O _ _ Γ ι _ T' _ _ rbar R _ _ _ (@Lift.hom O _ _ Γ ι _ T _ _ rbar R _ _ _ r)
    (fun a b N => by
      let φ : Γ →* Matrix ι ι (R ⧸ maximalIdeal R ^ N) :=
        (Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix.toMonoidHom.comp
          (@Lift.hom O _ _ Γ ι _ T _ _ rbar R _ _ _ r)
      have h1 : @IsLocallyConstant Γ _ T φ := by
        rw [@IsLocallyConstant.iff_eventually_eq Γ _ T]
        intro x
        have h2 := fun a b => (@IsLocallyConstant.iff_eventually_eq Γ _ T _).1
          (@Lift.cont O _ _ Γ ι _ T _ _ rbar R _ _ _ r a b N) x
        have h3 := Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => h2 a b
        exact h3.mono fun y hy => Matrix.ext fun a b => hy a b
      exact @lc_of_fib _ _ _ T' _ _ (h _ φ h1) fun x y e => congrFun (congrFun e a) b)
    (@Lift.red O _ _ Γ ι _ T _ _ rbar R _ _ _ r)

theorem UpperTheory.V.Alg.loc_graded_top :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (N : Subgroup Γ) (L : Cond O rbar), Φ.IsLocCond r0.hom N L →
          ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (p : R →ₐ[O] R'), Function.Surjective p → maximalIdeal R * RingHom.ker p = ⊥ → ∀ (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → IsHomog O W.wt (RingHom.ker (p.comp W.π)) →
          ∀ r' : Lift O rbar R', Φ.InH r0.hom R' r' → L R' r' → (∀ s a b, r'.hom s a b ∈ (W.part (w a - w b)).map p.toLinearMap) →
          ∃ r : Lift O rbar R, Φ.InH r0.hom R r ∧ L R r ∧ r.map p = r' ∧ ∀ s a b, r.hom s a b ∈ W.part (w a - w b) := by
  intro O _ _ _ _ ι X _ _ _ _ _ w Φ h2 Γ _ T rbar r0 hbar hr0 N L hL R _ _ _ R' _ _ _ p hp hker W hz hW r' hr' hLr' hpart
  obtain ⟨U, hU, hiff⟩ : ∃ U : PLift (TopologicalSpace Γ), @IsTopologicalGroup Γ U.down _ ∧
      ∀ (M : Type) [Monoid M] (φ : Γ →* M), @IsLocallyConstant Γ M T φ ↔ @IsLocallyConstant Γ M U.down φ := by
    obtain ⟨T', h1, h2⟩ := exists_grpTop Γ T
    exact ⟨⟨T'⟩, h1, h2⟩
  have hf : ∀ (M : Type) [Monoid M] (φ : Γ →* M), @IsLocallyConstant Γ M T φ → @IsLocallyConstant Γ M U.down φ :=
    fun M _ φ => (hiff M φ).1
  have hb : ∀ (M : Type) [Monoid M] (φ : Γ →* M), @IsLocallyConstant Γ M U.down φ → @IsLocallyConstant Γ M T φ :=
    fun M _ φ => (hiff M φ).2
  let L' : @Cond O _ _ Γ ι _ U.down _ _ rbar := fun S _ _ _ r => L S (tr U.down T hb r)
  have hL' : @FormData.IsLocCond O _ ι X _ _ _ w Φ _ Γ _ U.down rbar r0.hom N L' := by
    refine @FormData.IsLocCond.mk O _ ι X _ _ _ w Φ _ Γ _ U.down rbar r0.hom N L' ?_ ?_ ?_ ?_ ?_
    · intro S _ _ _ r hr
      obtain ⟨I, hI⟩ := hL.closed S (tr U.down T hb r) hr
      refine ⟨I, fun S' _ _ _ f => ?_⟩
      convert hI S' f using 2
      exact Lift.ext rfl
    · intro S _ _ _ r r2 h hr hh hc hLr
      exact hL.conj S (tr U.down T hb r) (tr U.down T hb r2) h hr hh hc hLr
    · intro S _ _ _ r r2 t hr ht htc hLr
      exact hL.torus S (tr U.down T hb r) (tr U.down T hb r2) t hr ht htc hLr
    · intro S S' _ _ _ _ _ _ q hq hk s hs hLs
      obtain ⟨r1, hr1, hL1, hm1⟩ := hL.lift S S' q hq hk (tr U.down T hb s) hs hLs
      refine ⟨tr T U.down hf r1, hr1, ?_, ?_⟩
      · exact (congrArg (L S) (Lift.ext rfl : tr U.down T hb (tr T U.down hf r1) = r1)).mpr hL1
      · have e := congrArg (@Lift.hom O _ _ Γ ι _ T _ _ rbar S' _ _ _) hm1
        exact Lift.ext e
    · intro S S' _ _ _ _ _ _ q hq hk r1 r2 hr1 hr2 hm hL1
      have e := congrArg (@Lift.hom O _ _ Γ ι _ U.down _ _ rbar S' _ _ _) hm
      exact hL.tangent S S' q hq hk (tr U.down T hb r1) (tr U.down T hb r2) hr1 hr2 (Lift.ext e) hL1
  have hLr'' : L' R' (tr T U.down hf r') := by
    exact (congrArg (L R') (Lift.ext rfl : tr U.down T hb (tr T U.down hf r') = r')).mpr hLr'
  obtain ⟨r, hr, hLr, hmap, hpart'⟩ := @loc_graded O _ _ _ _ ι X _ _ _ _ _ w Φ h2 Γ _ U.down hU rbar
    (tr T U.down hf r0) hbar hr0 N L' hL' R _ _ _ R' _ _ _ p hp hker W hz hW (tr T U.down hf r') hr' hLr'' hpart
  have e := congrArg (@Lift.hom O _ _ Γ ι _ U.down _ _ rbar R' _ _ _) hmap
  exact ⟨tr U.down T hb r, hr, hLr, Lift.ext e, hpart'⟩
