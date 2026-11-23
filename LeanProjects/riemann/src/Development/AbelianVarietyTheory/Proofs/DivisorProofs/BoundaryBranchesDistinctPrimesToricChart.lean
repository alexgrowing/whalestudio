import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryFormNonlocalDvr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitelyManyIsoClassesProjectiveNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeAtOfToricChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonSemiAbelianPullbackTwoUnitaryTraits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdClassGroupMk0EqOfLinearEquivPiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinitzPiIdealsLinearEquivOfClassGroupProdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomCompleteDVRPrincipalMaximalIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalPushoutUnramifiedCharZeroStatement

noncomputable section
open scoped nonZeroDivisors

namespace GlobalTheory.BranchSep

section Cancel

variable {O : Type} [CommRing O] [IsDedekindDomain O]

theorem exists_split_ker {X X' : Type} [AddCommGroup X] [Module O X] [AddCommGroup X'] [Module O X']
    [Module.Projective O X'] (ρ : X →ₗ[O] X') (hρ : Function.Surjective ρ) :
    ∃ e : X ≃ₗ[O] (LinearMap.ker ρ) × X', ∀ x, (e x).2 = ρ x := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property ρ LinearMap.id hρ
  let q := (LinearMap.exact_subtype_ker_map ρ).splitSurjectiveEquiv (LinearMap.ker ρ).injective_subtype ⟨s, hs⟩
  exact ⟨q.1, fun x => (LinearMap.congr_fun q.2.2 x).symm⟩

def piSumEquiv {ι μ : Type} (B : ι → (Ideal O)⁰) (A : μ → (Ideal O)⁰) :
    ((i : ι ⊕ μ) → ((Sum.elim B A i : (Ideal O)⁰) : Ideal O)) ≃ₗ[O] ((i : ι) → (B i : Ideal O)) × ((i : μ) → (A i : Ideal O)) :=
  LinearEquiv.sumPiEquivProdPi O ι μ (fun i => ((Sum.elim B A i : (Ideal O)⁰) : Ideal O))

theorem exists_equiv_comp_eq {X X' : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.IsTorsionFree O X]
    [AddCommGroup X'] [Module O X'] [Module.IsTorsionFree O X'] (ρ ρ' : X →ₗ[O] X') (hρ : Function.Surjective ρ)
    (hρ' : Function.Surjective ρ') : ∃ e : X ≃ₗ[O] X, ∀ x, ρ (e x) = ρ' x := by
  classical
  haveI : Module.Finite O X' := Module.Finite.of_surjective ρ hρ
  haveI := GlobalTheory.ProjModFinIso.projective_of_isTorsionFree (R := O) X'
  obtain ⟨e₁, he₁⟩ := exists_split_ker ρ hρ
  obtain ⟨e₂, he₂⟩ := exists_split_ker ρ' hρ'
  have r1 := e₁.finrank_eq
  have r2 := e₂.finrank_eq
  rw [GlobalTheory.ProjModFinIso.finrank_prod_eq] at r1 r2
  obtain ⟨ι, _, B, hB, ⟨eB⟩⟩ := GlobalTheory.ProjModFinIso.exists_equiv_pi (R := O) _ (LinearMap.ker ρ) rfl
  obtain ⟨ι', _, B', hB', ⟨eB'⟩⟩ := GlobalTheory.ProjModFinIso.exists_equiv_pi (R := O) _ (LinearMap.ker ρ') rfl
  obtain ⟨μ, _, A, -, ⟨eA⟩⟩ := GlobalTheory.ProjModFinIso.exists_equiv_pi (R := O) _ X' rfl
  have hc : Fintype.card ι' = Fintype.card ι := by rw [hB, hB']; omega
  let σ : ι' ≃ ι := Fintype.equivOfCardEq hc
  let B'' : ι → (Ideal O)⁰ := fun i => B' (σ.symm i)
  let eB'' : (LinearMap.ker ρ') ≃ₗ[O] ((i : ι) → (B'' i : Ideal O)) :=
    eB'.trans (LinearEquiv.piCongrLeft O (fun i' : ι' => (B' i' : Ideal O)) σ.symm).symm
  let E₁ : X ≃ₗ[O] ((i : ι ⊕ μ) → ((Sum.elim B A i : (Ideal O)⁰) : Ideal O)) :=
    e₁.trans ((eB.prodCongr eA).trans (piSumEquiv B A).symm)
  let E₂ : X ≃ₗ[O] ((i : ι ⊕ μ) → ((Sum.elim B'' A i : (Ideal O)⁰) : Ideal O)) :=
    e₂.trans ((eB''.prodCongr eA).trans (piSumEquiv B'' A).symm)
  have h1 := GlobalTheory.T.prod_classGroup_mk0_eq_of_linearEquiv_pi O (ι ⊕ μ) (Sum.elim B A) (Sum.elim B'' A) ⟨E₁.symm.trans E₂⟩
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type] at h1
  simp only [Sum.elim_inl, Sum.elim_inr] at h1
  obtain ⟨eBB⟩ := GlobalTheory.T.steinitz_pi_ideals_linearEquiv_of_classGroup_prod O ι B B'' (mul_right_cancel h1)
  let κ : (LinearMap.ker ρ) ≃ₗ[O] (LinearMap.ker ρ') := eB.trans (eBB.trans eB''.symm)
  refine ⟨e₂.trans ((κ.symm.prodCongr (LinearEquiv.refl O X')).trans e₁.symm), fun x => ?_⟩
  rw [← he₁, ← he₂, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

end Cancel
end GlobalTheory.BranchSep

noncomputable section
open IsLocalRing ReciprocityTheory.AnForm.R GlobalTheory.Toroidal

namespace GlobalTheory.BranchSep

section Ring

theorem injective_of_ker_le_span {R W : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing W] [IsDomain W] (φ : R →+* W) {t : R} (ht : t ∈ maximalIdeal R) (h0 : φ t ≠ 0)
    (h : ∀ r, r ∉ Ideal.span {t} → φ r ≠ 0) : Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  have key : ∀ n : ℕ, ∀ x, φ x = 0 → x ∈ Ideal.span {t} ^ n := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      have hx' : x ∈ Ideal.span {t} := by by_contra hc; exact h x hc hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx'
      have hy : φ y = 0 := by
        rw [map_mul] at hx
        exact (mul_eq_zero.1 hx).resolve_right h0
      rw [pow_succ']
      exact Ideal.mul_mem_mul (ih y hy) (Ideal.mem_span_singleton_self t) |> fun h' => by
        simpa [mul_comm] using h'
  intro x hx
  have hne : Ideal.span {t} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact fun hu => (mem_maximalIdeal t).1 ht hu
  have := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {t}) hne
  have hm : x ∈ ⨅ i, Ideal.span {t} ^ i := Ideal.mem_iInf.2 fun n => key n x hx
  rw [this] at hm
  exact hm

theorem not_X_dvd_X {σ k : Type} [Field k] {a b : σ} (hab : a ≠ b) :
    ¬ (MvPowerSeries.X a : MvPowerSeries σ k) ∣ MvPowerSeries.X b := by
  classical
  intro h
  have := MvPowerSeries.X_dvd_iff.1 h (Finsupp.single b 1) (by simp [Finsupp.single_apply, hab])
  simp [MvPowerSeries.coeff_X] at this

variable (k : Type) [Field k] (m e : ℕ)

theorem prime_mvX {σ k : Type} [CommRing k] [IsDomain k] (s : σ) : Prime (MvPowerSeries.X s : MvPowerSeries σ k) := by
  classical
  let ρ := MvPowerSeries.rescale (σ := σ) (R := k) (fun i => if i = s then 0 else 1)
  have key : ∀ g, MvPowerSeries.X s ∣ g ↔ ρ g = 0 := by
    intro g
    rw [MvPowerSeries.X_dvd_iff, MvPowerSeries.ext_iff]
    refine forall_congr' fun n => ?_
    rw [MvPowerSeries.coeff_rescale, map_zero]
    by_cases hn : n s = 0
    · have : (n.prod fun i m => (if i = s then (0 : k) else 1) ^ m) = 1 := by
        refine Finset.prod_eq_one fun i hi => ?_
        have : i ≠ s := fun h => (Finsupp.mem_support_iff.1 hi) (h ▸ hn)
        simp [this]
      simp [hn, this]
    · have : (n.prod fun i m => (if i = s then (0 : k) else 1) ^ m) = 0 :=
        Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hn) (by simp [hn])
      simp [hn, this]
  refine ⟨?_, ?_, fun a b h => ?_⟩
  · intro h
    have := congrArg (MvPowerSeries.coeff (Finsupp.single s 1)) h
    simp [MvPowerSeries.coeff_X] at this
  · intro h
    have := h.map (MvPowerSeries.constantCoeff (σ := σ) (R := k))
    simp at this
  · rw [key, map_mul, mul_eq_zero, ← key, ← key] at h
    exact h

instance isPrime_span_bdParam (i : Fin m) : (Ideal.span {bdParam k m e i}).IsPrime :=
  (Ideal.span_singleton_prime (prime_mvX (k := k) _).ne_zero).2 (prime_mvX _)

theorem side {A : Type} [CommRing A] [CharZero k] (θ : A →+* ChartRing k m e)
    (hθ : θ.Flat) (D : Ideal A) (hD : D.map θ = Ideal.span {∏ i, bdParam k m e i}) (i : Fin m) :
    let V := Localization.AtPrime (Ideal.span {bdParam k m e i})
    let f : A →+* V := (algebraMap (ChartRing k m e) V).comp θ
    f.Flat ∧ (maximalIdeal V).comap f = (Ideal.span {bdParam k m e i}).comap θ ∧
      ((maximalIdeal V).comap f).map f = maximalIdeal V ∧ CharZero (ResidueField V) ∧
      maximalIdeal V = Ideal.span {algebraMap (ChartRing k m e) V (bdParam k m e i)} ∧
      (∀ j, j ≠ i → IsUnit (algebraMap (ChartRing k m e) V (bdParam k m e j))) ∧
      ∀ r, r ∉ Ideal.span {bdParam k m e i} → IsUnit (algebraMap (ChartRing k m e) V r) := by
  intro V f
  set t := bdParam k m e i
  have hunit : ∀ r, r ∉ Ideal.span {t} → IsUnit (algebraMap (ChartRing k m e) V r) := fun r hr =>
    (IsLocalization.AtPrime.isUnit_to_map_iff V (Ideal.span {t}) r).2 hr
  have hj : ∀ j, j ≠ i → IsUnit (algebraMap (ChartRing k m e) V (bdParam k m e j)) := fun j hj =>
    hunit _ fun h => not_X_dvd_X (k := k) (Sum.inl_injective.ne hj.symm) (Ideal.mem_span_singleton.1 h)
  have hm : maximalIdeal V = Ideal.span {algebraMap (ChartRing k m e) V t} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hc : (maximalIdeal V).comap f = (Ideal.span {t}).comap θ := by
    rw [← Ideal.comap_comap]
    congr 1
    exact Localization.AtPrime.comap_maximalIdeal
  refine ⟨?_, hc, ?_, ?_, hm, hj, hunit⟩
  · exact RingHom.Flat.comp hθ (by rw [RingHom.flat_algebraMap_iff]; exact IsLocalization.flat _ (Ideal.span {t}).primeCompl)
  · rw [hc]
    refine le_antisymm ?_ ?_
    · rw [← Ideal.map_map, ← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_mono (Ideal.map_comap_le)
    · rw [hm, Ideal.span_le, Set.singleton_subset_iff]
      have hDle : D ≤ (Ideal.span {t}).comap θ := by
        intro x hx
        have h1 : θ x ∈ D.map θ := Ideal.mem_map_of_mem θ hx
        rw [hD, Ideal.mem_span_singleton] at h1
        exact Ideal.mem_span_singleton.2 ((Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans h1)
      have hprod : algebraMap (ChartRing k m e) V (∏ j, bdParam k m e j) ∈ ((Ideal.span {t}).comap θ).map f := by
        refine Ideal.map_mono hDle ?_
        rw [← Ideal.map_map, hD]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul] at hprod
      have hu : IsUnit (algebraMap (ChartRing k m e) V (∏ j ∈ Finset.univ.erase i, bdParam k m e j)) := by
        rw [map_prod]
        exact (IsUnit.prod_iff (s := Finset.univ.erase i)).2 fun j hjm => hj j (Finset.ne_of_mem_erase hjm)
      obtain ⟨u, hu'⟩ := hu
      have := Ideal.mul_mem_right (↑u⁻¹ : V) _ hprod
      rwa [← hu', mul_assoc, Units.mul_inv, mul_one] at this
  · exact (RingHom.charZero_iff ((residue V).comp ((algebraMap (ChartRing k m e) V).comp
      (MvPowerSeries.C (σ := Fin m ⊕ Fin e) (R := k)))).injective).1 inferInstance

theorem exists_two_traits {A : Type} [CommRing A] [CharZero k] (θ : A →+* ChartRing k m e) (hθ : θ.Flat) (D : Ideal A)
    (hD : D.map θ = Ideal.span {∏ i, bdParam k m e i}) (i i' : Fin m)
    (hc : (Ideal.span {bdParam k m e i}).comap θ = (Ideal.span {bdParam k m e i'}).comap θ) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (g g' : ChartRing k m e →+* W),
      GlobalTheory.LN.CDvr W ∧ Function.Injective g ∧ Function.Injective g' ∧ g.comp θ = g'.comp θ ∧
      Associated (g (bdParam k m e i)) (g' (bdParam k m e i')) ∧ g (bdParam k m e i) ≠ 0 ∧
      ¬ IsUnit (g (bdParam k m e i)) ∧ (∀ j, j ≠ i → IsUnit (g (bdParam k m e j))) ∧
      ∀ j, j ≠ i' → IsUnit (g' (bdParam k m e j)) := by
  obtain ⟨hf, hcm, hmap, hch, hm, hj, hu⟩ := side k m e θ hθ D hD i
  obtain ⟨hf', hcm', hmap', -, hm', hj', hu'⟩ := side k m e θ hθ D hD i'
  set V := Localization.AtPrime (Ideal.span {bdParam k m e i})
  set V' := Localization.AtPrime (Ideal.span {bdParam k m e i'})
  set a := algebraMap (ChartRing k m e) V
  set a' := algebraMap (ChartRing k m e) V'
  obtain ⟨B, _, _, g0, g0', hcomp, hg0, hgm, hgm'⟩ :=
    GlobalTheory.T.exists_local_pushout_unramified_charZero A V V' (a.comp θ) (a'.comp θ) hf' (hcm.trans (hc.trans hcm'.symm)) hmap hmap' hch
  set ϖ := g0 (a (bdParam k m e i))
  set ϖ' := g0' (a' (bdParam k m e i'))
  have hB : maximalIdeal B = Ideal.span {ϖ} := by
    rw [← hgm, hm, Ideal.map_span, Set.image_singleton]
  have hB' : maximalIdeal B = Ideal.span {ϖ'} := by
    rw [← hgm', hm', Ideal.map_span, Set.image_singleton]
  have hl0 : IsLocalHom g0 := ((IsLocalRing.local_hom_TFAE g0).out 0 2).2 hgm.le
  have hreg : ϖ ∈ nonZeroDivisors B := by
    letI := g0.toAlgebra
    haveI : Module.Flat V B := hg0
    have ha0 : a (bdParam k m e i) ≠ 0 := by
      rw [Ne, ← map_zero a]
      exact fun h => (prime_mvX (k := k) _).ne_zero
        (IsLocalization.injective V (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {bdParam k m e i})) h)
    have h1 : IsSMulRegular V (a (bdParam k m e i)) :=
      IsLeftRegular.isSMulRegular (mul_right_injective₀ ha0)
    have h2 := IsSMulRegular.of_flat (S := B) h1
    have key : ∀ x : B, ϖ * x = 0 → x = 0 := fun x hx => h2 (show ϖ * x = ϖ * 0 by rw [mul_zero]; exact hx)
    exact mem_nonZeroDivisors_iff.2 ⟨key, fun x hx => key x (by rw [mul_comm]; exact hx)⟩
  have hchB : CharZero (ResidueField B) :=
    (RingHom.charZero_iff (ResidueField.map g0).injective).1 hch
  obtain ⟨W, _, _, _, h, hW, hloc, hϖ⟩ := GlobalTheory.T.exists_localHom_completeDVR_principal_maximalIdeal B ϖ hB hreg hchB
  have hmem : ∀ j, bdParam k m e j ∈ maximalIdeal (ChartRing k m e) := fun j =>
    (mem_maximalIdeal _).2 (prime_mvX (k := k) _).not_unit
  have hϖn : ¬ IsUnit ϖ := (mem_maximalIdeal ϖ).1 (hB ▸ Ideal.mem_span_singleton_self ϖ)
  have hdvd1 : ϖ ∣ ϖ' := Ideal.mem_span_singleton.1 (hB ▸ hB' ▸ Ideal.mem_span_singleton_self ϖ')
  have hdvd2 : ϖ' ∣ ϖ := Ideal.mem_span_singleton.1 (hB' ▸ hB ▸ Ideal.mem_span_singleton_self ϖ)
  have hϖ' : h ϖ' ≠ 0 := fun h0 => hϖ (by
    obtain ⟨c, hc⟩ := hdvd2
    rw [hc, map_mul, h0, zero_mul])
  have hϖ'n : ¬ IsUnit ϖ' := fun hu => hϖn (isUnit_of_dvd_unit hdvd1 hu)
  refine ⟨W, inferInstance, inferInstance, inferInstance, h.comp (g0.comp a), h.comp (g0'.comp a'), hW, ?_, ?_, ?_,
    associated_of_dvd_dvd (map_dvd h hdvd1) (map_dvd h hdvd2), hϖ, fun hu => hϖn (hloc.map_nonunit _ hu),
    fun j hji => (hj j hji).map (h.comp g0), fun j hji => (hj' j hji).map (h.comp g0')⟩
  · refine injective_of_ker_le_span _ (hmem i) hϖ fun r hr => ?_
    exact ((hu r hr).map (h.comp g0)).ne_zero
  · refine injective_of_ker_le_span _ (hmem i') hϖ' fun r hr => ?_
    exact ((hu' r hr).map (h.comp g0')).ne_zero
  · ext x
    exact congrArg h (RingHom.congr_fun hcomp x)

end Ring
end GlobalTheory.BranchSep

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BranchSep

section SlopeTestRemainingChoices

theorem isTorsionFree_of_free (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Free ℤ X] : Module.IsTorsionFree (𝓞 E) X := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun c x h => ?_
  by_contra hcx
  push_neg at hcx
  obtain ⟨r, hr, α, hα⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) c).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hcx.1)
  have : r • x = 0 := by
    rw [← algebraMap_smul (𝓞 E) r x, hα, mul_comm, mul_smul, h, smul_zero]
  exact hcx.2 ((smul_eq_zero.1 this).resolve_left hr)

theorem pow_eq_of_associated {W : Type} [CommRing W] [IsDomain W] {w : W} (h0 : w ≠ 0) (hu : ¬ IsUnit w) {a b : ℕ}
    (h : Associated (w ^ a) (w ^ b)) : a = b := by
  have key : ∀ {a b : ℕ}, Associated (w ^ a) (w ^ b) → a ≤ b → a = b := by
    intro a b h hab
    by_contra hne
    have hlt : 0 < b - a := by omega
    have h1 : Associated (w ^ a * 1) (w ^ a * w ^ (b - a)) := by
      rw [_root_.mul_one, ← pow_add, Nat.add_sub_cancel' hab]; exact h
    have h2 : Associated 1 (w ^ (b - a)) := Associated.of_mul_left h1 (Associated.refl _) (pow_ne_zero _ h0)
    exact hu ((isUnit_pow_iff hlt.ne').1 (associated_one_iff_isUnit.1 h2.symm))
  rcases le_total a b with hab | hab
  · exact key h hab
  · exact (key h.symm hab).symm

theorem associated_map_monomial {R W : Type} [CommRing R] [CommRing W] (ψ : R →+* W) {M : ℕ} (s : Fin M → R)
    (a : Fin M) (hs : ∀ b, b ≠ a → IsUnit (ψ (s b))) (u : Rˣ) (n : Fin M → ℕ) :
    Associated (ψ (u * ∏ b, s b ^ n b)) (ψ (s a) ^ n a) := by
  classical
  rw [map_mul, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ a), map_pow]
  have h1 : IsUnit (ψ u) := u.isUnit.map ψ
  have h2 : IsUnit (∏ b ∈ Finset.univ.erase a, ψ (s b ^ n b)) :=
    (IsUnit.prod_iff (s := Finset.univ.erase a)).2 fun b hb => by
      rw [map_pow]; exact (hs b (Finset.ne_of_mem_erase hb)).pow _
  obtain ⟨v, hv⟩ := h1.mul h2
  refine ⟨v⁻¹, ?_⟩
  calc ψ u * (ψ (s a) ^ n a * ∏ b ∈ Finset.univ.erase a, ψ (s b ^ n b)) * ↑v⁻¹
      = ψ (s a) ^ n a * ((ψ u * ∏ b ∈ Finset.univ.erase a, ψ (s b ^ n b)) * ↑v⁻¹) := by ring
    _ = ψ (s a) ^ n a := by rw [← hv, Units.mul_inv, _root_.mul_one]

theorem eq_of_diag {X : Type} [AddCommGroup X] {β β' : LinearMap.BilinForm ℤ X} (hβ : ∀ y z, β y z = β z y)
    (hγ : ∀ y z, β' y z = β' z y) (h : ∀ y, β y y = β' y y) : β = β' := by
  refine LinearMap.ext₂ fun y z => ?_
  have h1 := h (y + z)
  simp only [map_add, LinearMap.add_apply] at h1
  rw [h y, h z, hβ z y, hγ z y] at h1
  linarith

end SlopeTestRemainingChoices
end GlobalTheory.BranchSep

namespace GlobalTheory.BranchSep

theorem branch_sep : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (k : Type) [Field k] (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S), IsTaut C → C.y ≫ j = jK _ ≫ ξ → ξ (closedPoint _) ∉ Set.range j → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, C.s i} → (∀ p : Sp (ChartRing k m e), ξ p ∈ Set.range j ↔ ∏ i, C.s i ∉ p.asIdeal) → ∀ i i' : Fin m, (Ideal.span {bdParam k m e i}).comap (Scheme.stalkClosedPointTo ξ).hom = (Ideal.span {bdParam k m e i'}).comap (Scheme.stalkClosedPointTo ξ).hom → i = i' := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hnsi Z zs i OZ N d J S π j _ BD hU hSep hUP k _ m e C ξ hT hy hx hEt hidl hrng
    ii ii' hcomp
  by_contra hne

  obtain ⟨hm, hs, -, -, -, -, -⟩ := hT

  haveI : CharZero k := (RingHom.charZero_iff ((MvPowerSeries.constantCoeff (σ := Fin m ⊕ Fin e) (R := k)).comp
    C.b).injective).1 inferInstance
  haveI : CharZero (ChartRing k m e) := (RingHom.charZero_iff
    (MvPowerSeries.C (σ := Fin m ⊕ Fin e) (R := k)).injective).1 inferInstance
  have hCN : GlobalTheory.TorRef.IsCN (ChartRing k m e) := GlobalTheory.ChartCone.isCN_chartRing k m e
  have hTI : C.P.TorsionIso := GlobalTheory.FlatTors.torsionIso_holds E H (ChartRing k m e) _
    ⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩ C.t C.P
  have hsb : ∀ a : Fin C.m, C.s a = bdParam k m e (Fin.cast hm a) := hs
  have hprod : ∏ a, C.s a = ∏ b, bdParam k m e b := by
    rw [Finset.prod_congr rfl fun a _ => hsb a]
    exact Fintype.prod_equiv (finCongr hm) _ _ fun _ => rfl
  set θ := (Scheme.stalkClosedPointTo ξ).hom
  obtain ⟨W, _, _, _, g, g', hW, hg, hg', hgg, hass, hg0, hgu, hgj, hgj'⟩ :=
    exists_two_traits k m e θ hEt.1 _ (by rw [← hprod]; exact hidl) ii ii' hcomp

  have hjW : Function.Injective ((algebraMap W (FractionRing W)).comp g) := (IsFractionRing.injective W _).comp hg
  have hjW' : Function.Injective ((algebraMap W (FractionRing W)).comp g') := (IsFractionRing.injective W _).comp hg'
  let κ : Sp (FractionRing W) ⟶ Sp (FractionRing (ChartRing k m e)) := spMap (IsFractionRing.lift hjW)
  let κ' : Sp (FractionRing W) ⟶ Sp (FractionRing (ChartRing k m e)) := spMap (IsFractionRing.lift hjW')
  have hκ : κ ≫ jK _ = jK W ≫ spMap g :=
    (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap hjW)).trans (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).symm
  have hκ' : κ' ≫ jK _ = jK W ≫ spMap g' :=
    (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap hjW')).trans (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).symm
  have hξ : ∀ h : ChartRing k m e →+* W, spMap h ≫ ξ = spMap (h.comp θ) ≫ S.fromSpecStalk _ := by
    intro h
    conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
    rw [← Category.assoc]
    congr 1
    exact GlobalTheory.Ex.UnifModel.spMap_comp (a := θ) fun _ => rfl
  have hy' : κ ≫ C.y = κ' ≫ C.y := by
    rw [← cancel_mono j]
    simp only [Category.assoc]
    rw [hy, ← Category.assoc, hκ, ← Category.assoc κ', hκ', Category.assoc, Category.assoc, hξ g, hξ g', hgg]

  obtain ⟨tW, ⟨m1⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap g) C.t
  obtain ⟨tW', ⟨m2⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap g') C.t
  obtain ⟨tKR, ⟨n1⟩, ⟨n2⟩⟩ := C.gen
  obtain ⟨uK, ⟨n⟩⟩ := GlobalTheory.TraitOrder.exists_pull (κ ≫ C.y ≫ pullback.fst _ _) Xo.univ.t
  obtain ⟨c1⟩ := GlobalTheory.TraitOrder.cancel rfl n2 n
  have e' : κ' ≫ C.y ≫ pullback.fst _ _ = κ ≫ C.y ≫ pullback.fst _ _ := by
    rw [← Category.assoc, ← hy', Category.assoc]
  obtain ⟨c2⟩ := GlobalTheory.TraitOrder.cancel e' n2 n
  obtain ⟨d1⟩ := GlobalTheory.TraitOrder.comp hκ n1 c1
  obtain ⟨d2⟩ := GlobalTheory.TraitOrder.comp hκ' n1 c2
  obtain ⟨x1⟩ := GlobalTheory.TraitOrder.cancel rfl m1 d1
  obtain ⟨x2⟩ := GlobalTheory.TraitOrder.cancel rfl m2 d2
  haveI := hW.1
  obtain ⟨ψ, -⟩ := GlobalTheory.ModelUniqueChecks.existsUnique_map W (FractionRing W) tW tW' uK x1 x2
  obtain ⟨m2'⟩ := GlobalTheory.TraitOrder.comp (Category.id_comp _) m2 ψ

  have hpol : GlobalTheory.LN.PolAt tW (jK W) := GlobalTheory.DatUniq.polAt_pull m1 (GlobalTheory.DatUniq.polAt_of_unif C.P) (jK W) κ hκ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨V', _, _, _, f, hV', hf, hfl, hfϖ, t', m', ⟨P'⟩⟩ := GlobalTheory.T.exists_unramified_uniformisation_polarisedTriple E H W hW ϖ hϖ tW hpol
  obtain ⟨n3⟩ := GlobalTheory.TraitOrder.comp (GlobalTheory.Ex.UnifModel.spMap_comp (d := f.comp g) fun _ => rfl) m1 m'
  obtain ⟨n4⟩ := GlobalTheory.TraitOrder.comp (GlobalTheory.Ex.UnifModel.spMap_comp (d := f.comp g') fun _ => rfl) m2' m'

  have hml : ∀ b, bdParam k m e b ∈ maximalIdeal (ChartRing k m e) := fun b =>
    (mem_maximalIdeal _).2 (prime_mvX (k := k) _).not_unit
  have hnl : ¬ IsLocalHom (f.comp g) := fun hl =>
    (mem_maximalIdeal _).1 (hml ii') (hl.map_nonunit _ ((hgj ii' fun h => hne h.symm).map f))
  have hnl' : ¬ IsLocalHom (f.comp g') := fun hl =>
    (mem_maximalIdeal _).1 (hml ii) (hl.map_nonunit _ ((hgj' ii hne).map f))
  obtain ⟨ρ, hρs, hρ⟩ := GlobalTheory.TraitCmp.main E H _ C.t C.P hCN hTI V' hV' (f.comp g) (hf.comp hg) hnl t' n3 P'
  obtain ⟨ρ', hρs', hρ'⟩ := GlobalTheory.TraitCmp.main E H _ C.t C.P hCN hTI V' hV' (f.comp g') (hf.comp hg') hnl' t' n4 P'

  haveI : Module.IsTorsionFree (𝓞 E) C.P.D.toPre.X := isTorsionFree_of_free E _
  haveI : Module.IsTorsionFree (𝓞 E) P'.D.toPre.X := isTorsionFree_of_free E _
  haveI : Module.Finite (𝓞 E) C.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI := GlobalTheory.ProjModFinIso.projective_of_isTorsionFree (R := 𝓞 E) C.P.D.toPre.X
  obtain ⟨ε, hε⟩ := exists_equiv_comp_eq ρ ρ' hρs hρs'
  obtain ⟨hd, hcp, hz⟩ := hV'
  obtain ⟨be, -, hmon, -⟩ := GlobalTheory.TorRef.exists_periodForm P' hfϖ
  have hsa : C.s (Fin.cast hm.symm ii) = bdParam k m e ii := by rw [hsb]; rfl
  have hsa' : C.s (Fin.cast hm.symm ii') = bdParam k m e ii' := by rw [hsb]; rfl
  have hπ0 : f (g (bdParam k m e ii)) ≠ 0 := fun h0 => hg0 (hf (by rw [h0, map_zero]))
  have hπu : ¬ IsUnit (f (g (bdParam k m e ii))) := fun h0 => hgu (hfl.map_nonunit _ h0)
  have hM : (l.M' : ℤ) ≠ 0 := by exact_mod_cast (GlobalTheory.LevelExist.M'_pos l).ne'
  have key : ∀ y, C.δ (Fin.cast hm.symm ii') y y = C.δ (Fin.cast hm.symm ii) (ε y) (ε y) := by
    intro y
    obtain ⟨u, n, hn, hc⟩ := C.mono y
    obtain ⟨u2, n2, hn2, hc2⟩ := C.mono (ε y)
    obtain ⟨u3, n3', -, hc3⟩ := hmon (ρ' y)
    have h1 := hρ' y _ _ hc hc3
    have h2 := hρ (ε y) _ _ hc2 (by rw [hε]; exact hc3)
    have h3 := associated_map_monomial (f.comp g') C.s (Fin.cast hm.symm ii') (fun b hb => by
      rw [hsb]
      exact (hgj' _ fun h0 => hb (by rw [← h0]; rfl)).map f) u n
    have h4 := associated_map_monomial (f.comp g) C.s (Fin.cast hm.symm ii) (fun b hb => by
      rw [hsb]
      exact (hgj _ fun h0 => hb (by rw [← h0]; rfl)).map f) u2 n2
    have h5 : Associated ((f.comp g') (C.s (Fin.cast hm.symm ii'))) (f (g (bdParam k m e ii))) := by
      rw [hsa']; exact (hass.map f).symm
    have h6 : (f.comp g) (C.s (Fin.cast hm.symm ii)) = f (g (bdParam k m e ii)) := by rw [hsa]; rfl
    rw [h6] at h4
    have hexp := pow_eq_of_associated hπ0 hπu
      ((h5.pow_pow (n := n (Fin.cast hm.symm ii'))).symm.trans (h3.symm.trans (h1.trans (h2.symm.trans h4))))
    have e1 := hn (Fin.cast hm.symm ii')
    have e2 := hn2 (Fin.cast hm.symm ii)
    simp only [LinearMap.smul_apply, smul_eq_mul] at e1 e2
    rw [hexp] at e1
    exact mul_left_cancel₀ hM (e1.trans e2.symm)
  have hpull : pull ε.toLinearMap (C.δ (Fin.cast hm.symm ii)) = C.δ (Fin.cast hm.symm ii') :=
    eq_of_diag (fun y z => by simp only [pull_apply]; exact (C.cone.mem _).1 _ _) (C.cone.mem _).1
      fun y => by simp only [pull_apply]; exact (key y).symm
  have hrays := hnsi C.P.D.toPre.X C.rank C.m C.δ C.cone ε _ _ hpull
  apply hne
  have := congrArg (Fin.cast hm) hrays
  simpa using this

end GlobalTheory.BranchSep
