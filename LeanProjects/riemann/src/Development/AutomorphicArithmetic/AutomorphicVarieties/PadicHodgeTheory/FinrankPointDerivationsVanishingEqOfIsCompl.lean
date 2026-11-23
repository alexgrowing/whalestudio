import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

section SlopeTestRemainingChoices
open MvPowerSeries

private theorem low_mem {R σ : Type} [CommRing R] [Finite σ] (m : Ideal (MvPowerSeries σ R))
    (hF : ∀ s, (MvPowerSeries.X s : MvPowerSeries σ R) ∈ m) (n : ℕ) (g : MvPowerSeries σ R)
    (hg : truncTotal n g = 0) : g ∈ m ^ n := by
  have hI : MvPolynomial.idealOfVars σ R ≤ m.comap (MvPolynomial.coeToMvPowerSeries.ringHom) := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    simpa using hF s
  have hIn : MvPolynomial.idealOfVars σ R ^ n ≤
      (m ^ n).comap (MvPolynomial.coeToMvPowerSeries.ringHom) :=
    (Ideal.pow_right_mono hI n).trans (Ideal.le_comap_pow _ n)
  let e := toAdicCompletionAlgEquiv σ R
  have key : ∀ y ∈ (MvPolynomial.idealOfVars σ R ^ n • ⊤ : Submodule (MvPolynomial σ R)
      (AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R))), (e.symm y) ∈ m ^ n := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun p hp z _ => ?_) (fun a b ha hb => ?_)
    · rw [map_smul, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (hIn hp)
    · rw [map_add]; exact add_mem ha hb
  have h := key (e g) (by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (MvPolynomial.idealOfVars_fg σ R), LinearMap.mem_ker,
      AdicCompletion.eval_apply, toAdicCompletionAlgEquiv_apply, toAdicCompletion_apply_eq_mk_truncTotal]
    rw [hg]
    rfl)
  rwa [AlgEquiv.symm_apply_apply] at h

private theorem mem_max {E σ : Type} [Field E] (a : MvPowerSeries σ E) :
    a ∈ maximalIdeal _ ↔ MvPowerSeries.constantCoeff a = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]

private theorem coeff_single_mul {E σ : Type} [CommRing E] (i : σ) (f g : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
      MvPowerSeries.constantCoeff g * MvPowerSeries.coeff (Finsupp.single i 1) f := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, mul_comm]

private theorem mem_sq {E σ : Type} [Field E] [Finite σ] (g : MvPowerSeries σ E)
    (h0 : MvPowerSeries.constantCoeff g = 0) (h1 : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) g = 0) :
    g ∈ maximalIdeal (MvPowerSeries σ E) ^ 2 := by
  refine low_mem _ (fun s => (mem_max _).2 (by simp)) 2 g ?_
  ext d
  rw [coeff_truncTotal_eq_ite]
  split_ifs with hd
  · have : d.degree = 0 ∨ d.degree = 1 := by omega
    rcases this with h | h
    · rw [Finsupp.degree_eq_zero_iff] at h
      subst h
      simpa using h0
    · obtain ⟨i, rfl⟩ : ∃ i, Finsupp.single i 1 = d := by
        have : d ∈ Set.range (fun i : σ => Finsupp.single i 1) := by
          rw [Finsupp.range_single_one]; exact h
        exact this
      simpa using h1 i
  · simp

private theorem of_mem_sq {E σ : Type} [Field E] (g : MvPowerSeries σ E)
    (h : g ∈ maximalIdeal (MvPowerSeries σ E) ^ 2) (i : σ) :
    MvPowerSeries.coeff (Finsupp.single i 1) g = 0 := by
  rw [pow_two] at h
  refine Submodule.mul_induction_on h (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [coeff_single_mul, (mem_max _).1 ha, (mem_max _).1 hb]; simp
  · rw [map_add, ha, hb, add_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.finrank_pointDerivations_vanishing_eq_of_isCompl :
    ∀ {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (n : ℕ) (P : Ideal R) (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries (Fin n) E), UpperTheory.V.Loc.IsCompl P x φ → ∀ T : Submodule E (R →ₗ[O] E), (∀ δ, δ ∈ T ↔ (∀ a b, δ (a * b) = algebraMap O E (x a) * δ b + algebraMap O E (x b) * δ a) ∧ ∀ a ∈ P, δ a = 0) → Module.finrank E ↥T = n := by
  intro O R E _ _ _ _ _ _ _ n P x φ H T hT
  classical
  have hinj : Function.Injective (algebraMap O E) := IsFractionRing.injective O E
  have hne : ∀ c : O, c ≠ 0 → algebraMap O E c ≠ 0 := fun c hc h => hc (hinj (by simpa using h))
  let D : Fin n → (R →ₗ[O] E) := fun i =>
    ((MvPowerSeries.coeff (Finsupp.single i 1) : MvPowerSeries (Fin n) E →ₗ[E] E).restrictScalars O).comp
      φ.toLinearMap
  have hD : ∀ i a, D i a = MvPowerSeries.coeff (Finsupp.single i 1) (φ a) := fun i a => rfl
  have hDT : ∀ i, D i ∈ T := fun i => (hT _).2 ⟨fun a b => by
      rw [hD, hD, hD, map_mul, coeff_single_mul, H.const, H.const], fun a ha => by
      rw [← H.ker, RingHom.mem_ker] at ha
      rw [hD, ha, map_zero]⟩

  have hex : ∀ i : Fin n, ∃ (a : R) (c : O), c ≠ 0 ∧ ∀ j, D j a = if j = i then algebraMap O E c else 0 := by
    intro i
    obtain ⟨a, c, hc, h⟩ := H.dense 2 (MvPowerSeries.X i)
    refine ⟨a, c, hc, fun j => ?_⟩
    have := of_mem_sq _ h j
    rw [map_sub, sub_eq_zero, ← hD, ← algebraMap_smul E c, map_smul, MvPowerSeries.coeff_X] at this
    rw [← this]
    simp [Finsupp.single_left_inj]
  choose a c hc ha using hex
  have h1 : ∀ δ ∈ T, δ 1 = 0 := fun δ hδ => by
    have := ((hT δ).1 hδ).1 1 1
    simpa using this
  have hker : ∀ δ ∈ T, ∀ r, (∀ i, D i r = 0) → δ r = 0 := by
    intro δ hδ r hr
    have hsub : ∀ δ ∈ T, δ (r - x r • 1) = δ r := fun δ hδ => by
      rw [map_sub, map_smul, h1 δ hδ, smul_zero, sub_zero]
    have hm : φ (r - x r • 1) ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2 := by
      refine mem_sq _ ?_ fun i => ?_
      · rw [H.const]; simp
      · rw [← hD, hsub _ (hDT i), hr]
    obtain ⟨k, hk, hmem⟩ := H.inj 2 _ hm
    have hz : ∀ s ∈ RingHom.ker x ^ 2 ⊔ P, δ s = 0 := by
      intro s hs
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hs
      rw [map_add, ((hT δ).1 hδ).2 v hv, add_zero]
      rw [pow_two] at hu
      refine Submodule.mul_induction_on hu (fun p hp q hq => ?_) (fun p q hp hq => ?_)
      · rw [RingHom.mem_ker] at hp hq
        rw [((hT δ).1 hδ).1, hp, hq]; simp
      · rw [map_add, hp, hq, add_zero]
    have := hz _ hmem
    rw [map_smul, hsub δ hδ, Algebra.smul_def] at this
    exact (mul_eq_zero.1 this).resolve_left (hne k hk)
  let ev : T →ₗ[E] (Fin n → E) := LinearMap.pi fun i => (LinearMap.applyₗ' E (a i)).comp T.subtype
  have hev : ∀ (δ : T) i, ev δ i = (δ : R →ₗ[O] E) (a i) := fun _ _ => rfl
  have hbij : Function.Bijective ev := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro δ hδ
      ext r
      obtain ⟨k, hk⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ
        (fun i => D i r / algebraMap O E (c i))
      choose! b hb using hk
      have hz := hker δ δ.2 ((k : O) • r - ∑ i, b i • a i) (fun j => by
        rw [map_sub, map_sum, map_smul]
        simp only [map_smul, ha, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [Algebra.smul_def, Algebra.smul_def, hb j (Finset.mem_univ _), Algebra.smul_def]
        have := hne _ (hc j)
        field_simp
        ring)
      rw [map_sub, map_sum, map_smul] at hz
      simp only [map_smul, ← hev, hδ, Pi.zero_apply, smul_zero, Finset.sum_const_zero, sub_zero] at hz
      rw [Algebra.smul_def] at hz
      exact (mul_eq_zero.1 hz).resolve_left (hne k (nonZeroDivisors.coe_ne_zero k))
    · intro v
      refine ⟨∑ j, (v j / algebraMap O E (c j)) • ⟨D j, hDT j⟩, ?_⟩
      ext i
      rw [map_sum, Finset.sum_apply]
      simp only [hev, Submodule.coe_smul, LinearMap.smul_apply, ha, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [smul_eq_mul, div_mul_cancel₀ _ (hne _ (hc i))]
  rw [(LinearEquiv.ofBijective ev hbij).finrank_eq]
  simp
