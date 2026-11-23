import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ChartLeadingWeightTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Latfil
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Satfil
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.NegWeightLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FgHolds

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem length_localization_bound {O B L P I : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing B]
    [Algebra O B] (x : B →ₐ[O] O) [AddCommGroup L] [Module B L] [Module O L] [IsScalarTower O B L]
    [Module.Finite B L] [AddCommGroup P] [Module B P] [Finite I] (lc : L →ₗ[O] (I → FractionRing O))
    (hlc : ∀ (b : B) (f : L), lc (b • f) = x b • lc f)
    (hsp : ∀ i, ∃ f, lc f i ≠ 0 ∧ ∀ j, j ≠ i → lc f j = 0)
    (ϖ : O) (hϖ : Irreducible ϖ) (π : L →ₗ[B] P) (hπ : Function.Surjective π)
    (hk : ∀ f, π f = 0 ↔ ∃ g, lc f = ϖ • lc g) : Module.length B P = Nat.card I := by
  classical
  have := Fintype.ofFinite I
  have hfin : Module.Finite O (LinearMap.range lc) := by
    obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := B) (M := L)
    rw [Module.Finite.iff_fg]
    refine ⟨S.image lc, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le, Finset.coe_image]
      rintro _ ⟨f, -, rfl⟩
      exact ⟨f, rfl⟩
    · rintro _ ⟨f, rfl⟩
      have hf : f ∈ Submodule.span B (S : Set L) := hS ▸ Submodule.mem_top
      induction hf using Submodule.span_induction with
      | mem f hf => exact Submodule.subset_span (by rw [Finset.coe_image]; exact ⟨f, hf, rfl⟩)
      | zero => rw [map_zero]; exact zero_mem _
      | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
      | smul b f _ hf => rw [hlc]; exact Submodule.smul_mem _ _ hf
  have hfree : Module.Free O (LinearMap.range lc) := inferInstance
  have hrk : Module.finrank O (LinearMap.range lc) = Fintype.card I := by
    apply le_antisymm
    · have h1 : Module.rank O (LinearMap.range lc) ≤ Module.rank O (I → FractionRing O) := Submodule.rank_le _
      rw [← IsLocalization.rank_eq (FractionRing O) (nonZeroDivisors O) le_rfl (N := I → FractionRing O),
        rank_fun'] at h1
      exact Module.finrank_le_of_rank_le h1
    · choose f hf hf' using hsp
      have h2 : LinearIndependent O fun i => lc.rangeRestrict (f i) := by
        rw [Fintype.linearIndependent_iff]
        intro c hc i
        have h3 := congrArg (fun z : LinearMap.range lc => z.1 i) hc
        simp only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply,
          LinearMap.codRestrict_apply, LinearMap.rangeRestrict, ZeroMemClass.coe_zero, Pi.zero_apply] at h3
        rw [Finset.sum_eq_single i (fun j _ hj => by rw [hf' j i (Ne.symm hj), smul_zero]) (by simp)] at h3
        exact (smul_eq_zero.1 h3).resolve_right (hf i)
      exact h2.fintype_card_le_finrank
  let e : LinearMap.range lc ≃ₗ[O] (I → O) := LinearEquiv.ofFinrankEq _ _ (by rw [hrk, Module.finrank_fintype_fun_eq_card])
  let ρ : L →ₗ[O] (I → O ⧸ Ideal.span {ϖ}) :=
    ((Ideal.span {ϖ}).mkQ.compLeft I) ∘ₗ e.toLinearMap ∘ₗ lc.rangeRestrict
  have hρ : Function.Surjective ρ := by
    intro y
    choose z hz using fun i => Submodule.mkQ_surjective (Ideal.span {ϖ}) (y i)
    obtain ⟨f, hf⟩ := lc.surjective_rangeRestrict (e.symm z)
    refine ⟨f, funext fun i => ?_⟩
    show (Ideal.span {ϖ}).mkQ (e (lc.rangeRestrict f) i) = y i
    rw [hf, e.apply_symm_apply, hz]
  have hρk : ∀ f, ρ f = 0 ↔ ∃ g, lc f = ϖ • lc g := by
    intro f
    constructor
    · intro h
      have h1 : ∀ i, ∃ c, c * ϖ = e (lc.rangeRestrict f) i := fun i =>
        Ideal.mem_span_singleton'.1 ((Submodule.Quotient.mk_eq_zero _).1 (congrFun h i))
      choose c hc using h1
      obtain ⟨g, hg⟩ := lc.surjective_rangeRestrict (e.symm c)
      refine ⟨g, ?_⟩
      have h2 : lc.rangeRestrict f = ϖ • lc.rangeRestrict g := by
        apply e.injective
        rw [map_smul, hg, e.apply_symm_apply]
        funext i
        rw [← hc, Pi.smul_apply, smul_eq_mul, mul_comm]
      exact congrArg Subtype.val h2
    · rintro ⟨g, hg⟩
      have h2 : lc.rangeRestrict f = ϖ • lc.rangeRestrict g := Subtype.ext hg
      funext i
      show (Ideal.span {ϖ}).mkQ (e (lc.rangeRestrict f) i) = 0
      rw [h2, map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)
  letI : Module O P := Module.compHom P (algebraMap O B)
  haveI : IsScalarTower O B P := ⟨fun a b p => by
    show _ = algebraMap O B a • b • p
    rw [Algebra.smul_def, mul_smul]⟩
  have hact : ∀ (b : B) (p : P), b • p = x b • p := by
    intro b p
    obtain ⟨f, rfl⟩ := hπ p
    show _ = algebraMap O B (x b) • π f
    rw [← sub_eq_zero, ← map_smul, ← map_smul, ← map_sub, hk]
    exact ⟨0, by rw [map_sub, hlc, hlc, AlgHom.commutes, map_zero, smul_zero]; exact sub_self _⟩
  have h1 : Module.length B P = Module.length O P := by
    letI : Algebra B O := x.toRingHom.toAlgebra
    haveI : IsScalarTower B O P := ⟨fun b a p => by
      rw [hact]
      exact mul_smul (x b) a p⟩
    exact Module.length_eq_of_surjective fun a => ⟨algebraMap O B a, x.commutes a⟩
  have hker : LinearMap.ker (π.restrictScalars O) = LinearMap.ker ρ := by
    ext f
    exact (hk f).trans (hρk f).symm
  have e2 : P ≃ₗ[O] (I → O ⧸ Ideal.span {ϖ}) :=
    (((π.restrictScalars O).quotKerEquivOfSurjective hπ).symm.trans (Submodule.quotEquivOfEq _ _ hker)).trans
      (ρ.quotKerEquivOfSurjective hρ)
  haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  haveI : IsSimpleModule O (O ⧸ Ideal.span {ϖ}) := isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 inferInstance)
  rw [h1, e2.length_eq, Module.length_pi_of_fintype]
  simp [Module.length_eq_one]

private theorem weight_eq {τ : Type} (wt : τ → ℤ) (ν : τ →₀ ℕ) :
    Finsupp.weight wt ν = (Finsupp.weight (posW wt) ν : ℤ) - (Finsupp.weight (negW wt) ν : ℤ) := by
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Nat.cast_sum, Nat.cast_mul, ← Finset.sum_sub_distrib,
    nsmul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_sub, posW, negW, Int.toNat_sub_toNat_neg]

private theorem pullback_fin_relation {τ : Type} [Fintype τ] (wt : τ → ℤ) (h : ∀ i, wt i ≠ 0) (a b : ℕ) :
    Finite {ν : τ →₀ ℕ // Finsupp.weight (negW wt) ν = a ∧ Finsupp.weight (posW wt) ν = b} := by
  have h1 := Finsupp.finite_of_nat_weight_le (fun i => negW wt i + posW wt i)
    (fun i => by have := h i; simp only [negW, posW]; omega) (a + b)
  refine Set.Finite.to_subtype (s := {ν | Finsupp.weight (negW wt) ν = a ∧ Finsupp.weight (posW wt) ν = b})
    (h1.subset ?_)
  rintro ν ⟨h2, h3⟩
  show Finsupp.weight (fun i => negW wt i + posW wt i) ν ≤ a + b
  rw [← h2, ← h3]
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, mul_add, Finset.sum_add_distrib, le_refl]

private noncomputable def monoL {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ}
    (N : Fin k → Submodule B A) (m : Fin k →₀ ℕ) : lat N m →ₗ[B] rees N where
  toFun f := mono N m f.1 f.2
  map_add' f g := Subtype.ext (by
    show MvPolynomial.monomial m (f.1 + g.1) = MvPolynomial.monomial m f.1 + MvPolynomial.monomial m g.1
    rw [map_add])
  map_smul' c f := Subtype.ext (by
    show MvPolynomial.monomial m (c • f.1) = c • MvPolynomial.monomial m f.1
    rw [MvPolynomial.smul_monomial])

private theorem gr_eq_range {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ}
    (N : Fin k → Submodule B A) (m : Fin k →₀ ℕ) : reesGr N (toDeg m) = LinearMap.range (monoL N m) := by
  classical
  apply le_antisymm
  · intro p hp
    refine ⟨⟨_, p.2 m⟩, Subtype.ext ?_⟩
    ext n
    show MvPolynomial.coeff n (MvPolynomial.monomial m _) = _
    rw [MvPolynomial.coeff_monomial]
    split_ifs with h
    · rw [← h]
    · exact (hp n fun h' => h (toDeg_injective h').symm).symm
  · rintro _ ⟨f, rfl⟩
    exact mono_mem N m f.1 f.2

private theorem piece_gen {B R L : Type} [CommRing B] [CommRing R] [Algebra B R] [AddCommGroup L] [Module B L]
    {k : ℕ} (𝒢 : Deg k → Submodule B R) (d : Deg k) (ι : L →ₗ[B] R) (hι : 𝒢 d = LinearMap.range ι) (𝔮 : Ideal R)
    (β : B) : ∃ π : L →ₗ[B] ((((GMod.self 𝒢).quo 𝔮).quot (algebraMap B R β)).gr d),
      Function.Surjective π ∧ ∀ f, π f = 0 ↔ ∃ p : R, ι f - β • p ∈ 𝔮 := by
  let M := LinearMap.range (LinearMap.lsmul R (R ⧸ 𝔮) (algebraMap B R β))
  let π0 : L →ₗ[B] (R ⧸ 𝔮) ⧸ M := M.mkQ.restrictScalars B ∘ₗ (Submodule.mkQ 𝔮).restrictScalars B ∘ₗ ι
  have hgr : (((GMod.self 𝒢).quo 𝔮).quot (algebraMap B R β)).gr d = LinearMap.range π0 := by
    rw [LinearMap.range_comp, LinearMap.range_comp, ← hι]
    rfl
  refine ⟨π0.codRestrict _ fun f => hgr ▸ LinearMap.mem_range_self π0 f, fun y => ?_, fun f => ?_⟩
  · obtain ⟨f, hf⟩ : y.1 ∈ LinearMap.range π0 := hgr ▸ y.2
    exact ⟨f, Subtype.ext hf⟩
  · rw [Subtype.ext_iff]
    show M.mkQ (Submodule.mkQ 𝔮 (ι f)) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective 𝔮 y
      rw [LinearMap.lsmul_apply, ← map_smul, algebraMap_smul, eq_comm, Submodule.mkQ_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq] at hy
      exact ⟨p, hy⟩
    · rintro ⟨p, hp⟩
      refine ⟨Submodule.mkQ 𝔮 p, ?_⟩
      rwa [LinearMap.lsmul_apply, ← map_smul, algebraMap_smul, eq_comm, Submodule.mkQ_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq]

private theorem rees_graded_piece_surjection {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ}
    (N : Fin k → Submodule B A) (μ : Fin k →₀ ℕ) (𝔮 : Ideal (rees N)) (β : B) (T : (Fin k →₀ ℕ) → AddSubgroup A)
    (hq : ∀ p, p ∈ 𝔮 ↔ ∀ m, MvPolynomial.coeff m p.1 ∈ T m) :
    ∃ π : lat N μ →ₗ[B] ((((GMod.self (reesGr N)).quo 𝔮).quot (algebraMap B (rees N) β)).gr (toDeg μ)),
      Function.Surjective π ∧ ∀ f, π f = 0 ↔ ∃ g : lat N μ, (f - β • g).1 ∈ T μ := by
  classical
  obtain ⟨π, hπ, hk⟩ := piece_gen (reesGr N) (toDeg μ) (monoL N μ) (gr_eq_range N μ) 𝔮 β
  refine ⟨π, hπ, fun f => (hk f).trans ⟨?_, ?_⟩⟩
  · rintro ⟨p, hp⟩
    refine ⟨⟨_, p.2 μ⟩, ?_⟩
    have h1 : MvPolynomial.coeff μ (MvPolynomial.monomial μ f.1 - β • p.1) ∈ T μ := (hq _).1 hp μ
    rwa [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_pos rfl, MvPolynomial.coeff_smul] at h1
  · rintro ⟨g, hg⟩
    refine ⟨monoL N μ g, ?_⟩
    rw [← map_smul, ← map_sub, hq]
    intro m
    show MvPolynomial.coeff m (MvPolynomial.monomial μ (f - β • g).1) ∈ _
    rw [MvPolynomial.coeff_monomial]
    split_ifs with h
    · exact h ▸ hg
    · exact zero_mem _

theorem UpperTheory.V.Alg.M.hf_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
    Q.F (Fin.last r) ∈ satSq x → ∀ 𝔮 : Ideal (mR Q), (𝔮 : Set (mR Q)) = leadKer Q wt φ → ∀ ϖ : O, Irreducible ϖ →
      ∀ d : Deg 3, 0 ≤ d → hilb ((mQ Q 𝔮).quot (algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) ϖ))) d =
        cnt wt (2 * d 0 + 4 * d 2) (2 * d 1 + 2 * d 2) := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q τ _ wt φ hφ hF 𝔮 h𝔮 ϖ hϖ d hd
  classical
  obtain ⟨μ, rfl⟩ : ∃ μ : Fin 3 →₀ ℕ, toDeg μ = d :=
    ⟨Finsupp.equivFunOnFinite.symm fun j => (d j).toNat, funext fun j => by simpa [toDeg] using hd j⟩
  set F := Q.F (Fin.last r) with hFd
  obtain ⟨π, hπ, hk⟩ := rees_graded_piece_surjection (mN 𝒜 F) μ 𝔮 (algebraMap O (𝒜 0) ϖ)
    (fun ν => ((fil (FractionRing O) wt (2 * ν 0 + 4 * ν 2 + 1)).toAddSubgroup).comap φ.toRingHom.toAddMonoidHom)
    (fun p => by rw [← SetLike.mem_coe, h𝔮]; rfl)
  let I := {ν : τ →₀ ℕ // Finsupp.weight (negW wt) ν = 2 * μ 0 + 4 * μ 2 ∧ Finsupp.weight (posW wt) ν = 2 * μ 1 + 2 * μ 2}
  haveI : Finite I := pullback_fin_relation wt (fun i => by have := hφ.wts i; omega) _ _
  let lc : lat (mN 𝒜 F) μ →ₗ[O] (I → FractionRing O) :=
    { toFun := fun f ν => MvPowerSeries.coeff ν.1 (φ f.1)
      map_add' := fun f g => funext fun ν => by simp
      map_smul' := fun c f => funext fun ν => by
        show MvPowerSeries.coeff ν.1 (φ (c • f.1)) = c • MvPowerSeries.coeff ν.1 (φ f.1)
        rw [map_smul, LinearMap.map_smul_of_tower] }
  have hlat := latfil_holds O A 𝒜 x hW τ wt φ hφ F (Q.hF _) hF μ
  have hz : ∀ f : lat (mN 𝒜 F) μ, φ f.1 ∈ fil (FractionRing O) wt (2 * μ 0 + 4 * μ 2 + 1) ↔ lc f = 0 := by
    intro f
    refine ⟨fun h => funext fun ν => h ν.1 (by rw [ν.2.1]; omega), fun h ν hν => ?_⟩
    obtain ⟨h1, h2⟩ := hlat f.1 f.2
    by_cases h3 : Finsupp.weight (negW wt) ν < 2 * μ 0 + 4 * μ 2
    · exact h2 ν h3
    by_cases h4 : Finsupp.weight (posW wt) ν = 2 * μ 1 + 2 * μ 2
    · exact congrFun h ⟨ν, by omega, h4⟩
    · exact hφ.graded _ _ h1 ν (by rw [weight_eq]; omega)
  have hfg : ∀ i, (mN 𝒜 F i).FG := by
    have h := fg_holds O A 𝒜 x hW
    intro i
    fin_cases i
    · exact h _
    · exact h _
    · exact (Submodule.fg_span_singleton _).sup (((h _).mul (h _)).mul (h _))
  have hl : lat (mN 𝒜 F) μ = mN 𝒜 F 0 ^ μ 0 * mN 𝒜 F 1 ^ μ 1 * mN 𝒜 F 2 ^ μ 2 := Fin.prod_univ_three _
  haveI : Module.Finite (𝒜 0) (lat (mN 𝒜 F) μ) := by
    rw [Module.Finite.iff_fg, hl]
    exact (((hfg _).pow _).mul ((hfg _).pow _)).mul ((hfg _).pow _)
  have key := length_localization_bound (res0 𝒜 x) lc (fun b f => ?_) (fun i => ?_) ϖ hϖ π hπ (fun f => ?_)
  · show ((Module.length _ _).toNat : ℤ) = (Nat.card _ : ℕ)
    rw [key, ENat.toNat_coe]
    congr 1
    refine Nat.card_congr (Equiv.subtypeEquivRight fun ν => ?_)
    simp only [toDeg]
    omega
  · rw [← sub_eq_zero, ← map_smul, ← map_sub, ← hz, ← algebraMap_smul (𝒜 0) (res0 𝒜 x b) f, ← sub_smul]
    show φ (((b - algebraMap O (𝒜 0) (res0 𝒜 x b) : 𝒜 0) : A) * f.1) ∈ _
    rw [map_mul, add_comm _ 1]
    refine (fil_holds _ _ wt _ _ _ _ ((satfil_holds O A 𝒜 x hW τ wt φ hφ).2 _ (Subtype.property _) ?_)
      (hlat f.1 f.2).2).1
    show res0 𝒜 x (b - algebraMap O (𝒜 0) (res0 𝒜 x b)) = 0
    rw [map_sub, AlgHom.commutes]
    exact sub_self _
  · obtain ⟨f, hf, h1, h2⟩ := exists_mem_oz_pow_coeff_ne_zero_unique O A 𝒜 x hW τ wt φ hφ (μ 0 + 2 * μ 2) (μ 1 + μ 2) i.1 (by rw [i.2.1]; ring)
      (by rw [i.2.2]; ring)
    have hle : oz 𝒜 (-2) ^ (μ 0 + 2 * μ 2) * oz 𝒜 2 ^ (μ 1 + μ 2) ≤ lat (mN 𝒜 F) μ := by
      have h3 : oz 𝒜 (-2) ^ (μ 0 + 2 * μ 2) * oz 𝒜 2 ^ (μ 1 + μ 2) =
          oz 𝒜 (-2) ^ μ 0 * oz 𝒜 2 ^ μ 1 * (oz 𝒜 (-2) * oz 𝒜 (-2) * oz 𝒜 2) ^ μ 2 := by ring
      rw [h3, hl]
      exact mul_le_mul' le_rfl (pow_le_pow_left' (le_sup_right : _ ≤ mN 𝒜 F 2) _)
    exact ⟨⟨f, hle hf⟩, h1, fun j hj => h2 j.1 (by rw [j.2.1]; ring) fun h => hj (Subtype.ext h)⟩
  · rw [hk]
    refine exists_congr fun g => ?_
    rw [← sub_eq_zero, ← map_smul, ← map_sub, ← hz, algebraMap_smul]
    rfl
