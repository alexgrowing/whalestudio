import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StChartPrimElt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocAwaySpec
import GroundTheory.HeightsAndTheta.Heights.Intersections.StChartSpecCount
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Polynomial

namespace ChartSpecCount

theorem exists_pow_mul_eq_map {R : Type*} [CommRing R] (E : R) {Q : Type*}
    (F : MvPolynomial Q (Localization.Away E)) :
    ∃ (n : ℕ) (F' : MvPolynomial Q R),
      MvPolynomial.map (algebraMap R (Localization.Away E)) F' =
        MvPolynomial.C (algebraMap R (Localization.Away E) (E ^ n)) * F := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj E a
    refine ⟨n, MvPolynomial.C b, ?_⟩
    rw [MvPolynomial.map_C, ← MvPolynomial.C_mul, map_pow, mul_comm, hb]
  | add F G hF hG =>
    obtain ⟨n, F', hF'⟩ := hF
    obtain ⟨k, G', hG'⟩ := hG
    refine ⟨n + k, MvPolynomial.C (E ^ k) * F' + MvPolynomial.C (E ^ n) * G', ?_⟩
    simp only [map_add, map_mul, MvPolynomial.map_C, hF', hG', pow_add, map_pow]
    ring
  | mul_X F i hF =>
    obtain ⟨n, F', hF'⟩ := hF
    exact ⟨n, F' * MvPolynomial.X i, by rw [map_mul, MvPolynomial.map_X, hF', mul_assoc]⟩

theorem eval₂_mvEval₂_C {A K Q : Type*} [CommRing A] [CommRing K] (k : A →+* K) (x : K) (G : Q → A[X])
    (F : MvPolynomial Q A) :
    (MvPolynomial.eval₂ C G F).eval₂ k x = MvPolynomial.eval₂ k (fun q => (G q).eval₂ k x) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add F G' hF hG => simp [Polynomial.eval₂_add, hF, hG]
  | mul_X F i hF => simp [Polynomial.eval₂_mul, hF]

theorem mvEval₂_eval₂_C {A K Q : Type*} [CommRing A] [CommRing K] (k : A →+* K) (y : Q → K)
    (τ : MvPolynomial Q A) (p : A[X]) :
    MvPolynomial.eval₂ k y (p.eval₂ MvPolynomial.C τ) = p.eval₂ k (MvPolynomial.eval₂ k y τ) := by
  induction p using Polynomial.induction_on' with
  | add p p' hp hp' => simp [Polynomial.eval₂_add, hp, hp']
  | monomial n a => simp [Polynomial.eval₂_monomial]

theorem dvd_map_of_dvd_map {A Φ K : Type*} [CommRing A] [Field Φ] [CommRing K] (fA : A →+* Φ) (σ : A →+* K)
    (hker : RingHom.ker fA ≤ RingHom.ker σ) {mA : A[X]} (hm : mA.Monic) {p : A[X]}
    (hp : mA.map fA ∣ p.map fA) : mA.map σ ∣ p.map σ := by
  have h0 : (p %ₘ mA).map fA = 0 := by
    rw [map_modByMonic fA hm]
    exact (modByMonic_eq_zero_iff_dvd (hm.map fA)).2 hp
  have h1 : (p %ₘ mA).map σ = 0 := by
    ext n
    rw [coeff_map, coeff_zero]
    exact RingHom.mem_ker.mp (hker (RingHom.mem_ker.mpr (by rw [← coeff_map, h0, coeff_zero])))
  refine ⟨(p /ₘ mA).map σ, ?_⟩
  conv_lhs => rw [← modByMonic_add_div p mA]
  rw [Polynomial.map_add, Polynomial.map_mul, h1, zero_add]

end ChartSpecCount

open ChartSpecCount in

theorem ChartSpecCount.proof (hPE : ChartPrimElt.Statement) (hLA : LocAwaySpec.Statement) :
    ChartSpecCount.Statement := by
  classical
  intro R _ Φ _ _ Φ' _ _ φ Q _ r hfrac hfin
  obtain ⟨τ, g, u, hdeg, hg, hu, -, hh⟩ := hPE Φ Φ' Q r hfin
  set θ : Φ' := MvPolynomial.aeval r τ with hθ
  have hint : IsIntegral Φ θ := by
    by_contra hni
    have h0 : minpoly Φ θ = 0 := minpoly.eq_zero hni
    rw [h0, natDegree_zero] at hdeg
    exact (Module.finrank_pos (R := Φ) (M := IntermediateField.adjoin Φ (Set.range r))).ne hdeg
  set m : Φ[X] := minpoly Φ θ with hm
  let hq : Q → Φ[X] := fun q => if hq : r q ≠ 0 then (hh q hq).choose else 0
  have hhq : ∀ q, r q ≠ 0 → m ∣ hq q * g q - 1 := by
    intro q hq0
    simp only [hq, dif_pos hq0]
    exact (hh q hq0).choose_spec
  let S : Finset Φ := m.coeffs ∪ u.coeffs ∪ τ.coeffs ∪ Finset.univ.biUnion (fun q => (g q).coeffs ∪ (hq q).coeffs)
  obtain ⟨E, hE, hS, hker⟩ := hLA R Φ φ S hfrac
  set φA : Localization.Away E →+* Φ := IsLocalization.Away.lift E hE with hφA
  have hφAR : φA.comp (algebraMap R (Localization.Away E)) = φ := by
    ext x
    exact IsLocalization.Away.lift_eq E hE x
  have hlift : ∀ p : Φ[X], p.coeffs ⊆ S → p ∈ lifts φA := by
    intro p hp
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : p.coeff n = 0
    · exact ⟨0, by rw [hn, map_zero]⟩
    · exact hS _ (hp (coeff_mem_coeffs hn))
  obtain ⟨mA, hmA, hmAdeg, hmAmon⟩ := lifts_and_natDegree_eq_and_monic
    (hlift m (fun c hc => by
      simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact Or.inl (Or.inl (Or.inl hc)))) (minpoly.monic hint)
  obtain ⟨uA, huA⟩ := (mem_lifts u).1 (hlift u (fun c hc => by
      simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact Or.inl (Or.inl (Or.inr hc))))
  have hgl : ∀ q, ∃ gq : (Localization.Away E)[X], gq.map φA = g q := fun q => (mem_lifts _).1
    (hlift (g q) (fun c hc => by
      simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact Or.inr ⟨q, Or.inl hc⟩))
  choose gA hgA using hgl
  have hhl : ∀ q, ∃ hq' : (Localization.Away E)[X], hq'.map φA = hq q := fun q => (mem_lifts _).1
    (hlift (hq q) (fun c hc => by
      simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact Or.inr ⟨q, Or.inr hc⟩))
  choose hA hhA using hhl
  obtain ⟨τA, hτA⟩ := MvPolynomial.mem_range_map_iff_coeffs_subset.2 (fun c hc => hS c (by
      simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact Or.inl (Or.inr (Finset.mem_coe.1 hc))) : (τ.coeffs : Set Φ) ⊆ Set.range φA)
  set f : Localization.Away E →+* Φ' := (algebraMap Φ Φ').comp φA with hf
  have hfφ : f.comp (algebraMap R (Localization.Away E)) = (algebraMap Φ Φ').comp φ := by
    rw [hf, RingHom.comp_assoc, hφAR]

  have hevθ : ∀ p : (Localization.Away E)[X], p.eval₂ f θ = aeval θ (p.map φA) := by
    intro p
    rw [aeval_def, eval₂_map]
  have hτθ : MvPolynomial.eval₂ f r τA = θ := by
    rw [hθ, hf, ← MvPolynomial.eval₂_map, hτA]
    rfl
  have hθm : mA.eval₂ f θ = 0 := by rw [hevθ, hmA, hm, minpoly.aeval]
  have hθg : ∀ q, (gA q).eval₂ f θ = r q := fun q => by rw [hevθ, hgA, hg q]
  have hθτ : (MvPolynomial.eval₂ C gA τA - X).eval₂ f θ = 0 := by
    rw [Polynomial.eval₂_sub, eval₂_mvEval₂_C, Polynomial.eval₂_X]
    simp only [hθg]
    rw [hτθ, sub_self]
  have hθu : (uA * derivative mA - 1).eval₂ f θ = 0 := by
    obtain ⟨c, hc⟩ := hu
    rw [hevθ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one, ← derivative_map, huA, hmA, hc,
      map_mul, hm, minpoly.aeval, zero_mul]
  have hθh : ∀ q, r q ≠ 0 → (hA q * gA q - 1).eval₂ f θ = 0 := by
    intro q hq0
    obtain ⟨c, hc⟩ := hhq q hq0
    rw [hevθ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one, hhA, hgA, hc, map_mul, hm,
      minpoly.aeval, zero_mul]
  refine ⟨E, fun h => hE.ne_zero h, ?_⟩
  intro ψ hkerψ hψ0
  have hψu : IsUnit (ψ E) := hψ0.isUnit
  have hσ := hker ℂ ψ hψu hkerψ
  have hσψ : (IsLocalization.Away.lift E hψu : Localization.Away E →+* ℂ).comp
      (algebraMap R (Localization.Away E)) = ψ := by
    ext x
    simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq]
  generalize (IsLocalization.Away.lift E hψu : Localization.Away E →+* ℂ) = σ at hσ hσψ

  have hD : ∀ p : (Localization.Away E)[X], p.eval₂ f θ = 0 → mA.map σ ∣ p.map σ := by
    intro p hp
    refine dvd_map_of_dvd_map φA σ hσ hmAmon ?_
    rw [hmA, hm]
    exact minpoly.dvd Φ θ (by rw [← hevθ]; exact hp)
  have hDr : ∀ p : (Localization.Away E)[X], p.eval₂ f θ = 0 → ∀ t : ℂ, mA.eval₂ σ t = 0 →
      p.eval₂ σ t = 0 := by
    intro p hp t ht
    obtain ⟨c, hc⟩ := hD p hp
    have := congrArg (eval t) hc
    rw [eval_mul, eval_map, eval_map, ht, zero_mul] at this
    exact this

  have hZA : ∀ y : Q → ℂ, (∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
      MvPolynomial.eval₂ ψ y F = 0) →
      ∀ F : MvPolynomial Q (Localization.Away E), MvPolynomial.eval₂ f r F = 0 → MvPolynomial.eval₂ σ y F = 0 := by
    intro y hy F hF
    obtain ⟨n, F', hF'⟩ := exists_pow_mul_eq_map E F
    have h1 : MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F' = 0 := by
      rw [← hfφ, ← MvPolynomial.eval₂_map, hF', MvPolynomial.eval₂_mul, hF, mul_zero]
    have h2 := hy F' h1
    rw [← hσψ, ← MvPolynomial.eval₂_map, hF', MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C] at h2
    have hEn : σ (algebraMap R (Localization.Away E) (E ^ n)) ≠ 0 := by
      rw [← RingHom.comp_apply, hσψ, map_pow]
      exact pow_ne_zero _ hψ0
    exact (mul_eq_zero.1 h2).resolve_left hEn
  let G : ℂ → Q → ℂ := fun t q => (gA q).eval₂ σ t
  let T : Set ℂ := {t | mA.eval₂ σ t = 0}

  have hb : ∀ t ∈ T, ∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
      MvPolynomial.eval₂ ψ (G t) F = 0 := by
    intro t ht F hF
    have hp : (MvPolynomial.eval₂ C gA (MvPolynomial.map (algebraMap R (Localization.Away E)) F)).eval₂ f θ = 0 := by
      rw [eval₂_mvEval₂_C]
      simp only [hθg]
      rw [MvPolynomial.eval₂_map, hfφ]
      exact hF
    have := hDr _ hp t ht
    rw [eval₂_mvEval₂_C, MvPolynomial.eval₂_map, hσψ] at this
    exact this

  have ha : ∀ y : Q → ℂ, (∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
      MvPolynomial.eval₂ ψ y F = 0) → MvPolynomial.eval₂ σ y τA ∈ T ∧ G (MvPolynomial.eval₂ σ y τA) = y := by
    intro y hy
    have hyA := hZA y hy
    refine ⟨?_, ?_⟩
    · have := hyA (mA.eval₂ MvPolynomial.C τA) (by rw [mvEval₂_eval₂_C, hτθ, hθm])
      rw [mvEval₂_eval₂_C] at this
      exact this
    · funext q
      have := hyA (MvPolynomial.X q - (gA q).eval₂ MvPolynomial.C τA)
        (by rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X, mvEval₂_eval₂_C, hτθ, hθg, sub_self])
      rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X, mvEval₂_eval₂_C, sub_eq_zero] at this
      exact this.symm

  have hc : ∀ t ∈ T, MvPolynomial.eval₂ σ (G t) τA = t := by
    intro t ht
    have := hDr _ hθτ t ht
    rw [Polynomial.eval₂_sub, eval₂_mvEval₂_C, Polynomial.eval₂_X, sub_eq_zero] at this
    exact this
  have hZ : {y : Q → ℂ | ∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
      MvPolynomial.eval₂ ψ y F = 0} = G '' T := by
    ext y
    constructor
    · intro hy
      exact ⟨_, (ha y hy).1, (ha y hy).2⟩
    · rintro ⟨t, ht, rfl⟩
      exact hb t ht
  have hinj : Set.InjOn G T := by
    intro t₁ h₁ t₂ h₂ h
    rw [← hc t₁ h₁, ← hc t₂ h₂, h]
  have hmw0 : mA.map σ ≠ 0 := (hmAmon.map σ).ne_zero
  have hT : T = ↑(mA.map σ).roots.toFinset := by
    ext t
    simp [T, mem_roots hmw0, eval_map]
  have hsep : (mA.map σ).Separable := by
    obtain ⟨c, hc'⟩ := hD _ hθu
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one, ← derivative_map] at hc'
    exact ⟨-c, uA.map σ, by linear_combination hc'⟩
  have hcard : T.ncard = Module.finrank Φ (IntermediateField.adjoin Φ (Set.range r)) := by
    rw [hT, Set.ncard_coe_finset, Multiset.toFinset_card_of_nodup (nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree, hmAmon.natDegree_map, hmAdeg, ← hdeg]
  refine ⟨?_, ?_, ?_⟩
  · rw [hZ, hT]
    exact (Finset.finite_toSet _).image G
  · rw [hZ, hinj.ncard_image, hcard]
  · intro y hy q hq0
    obtain ⟨hyT, hyG⟩ := ha y hy
    have := hDr _ (hθh q hq0) _ hyT
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_one, sub_eq_zero] at this
    intro h0
    rw [← hyG] at h0
    simp only [G] at h0
    rw [h0, mul_zero] at this
    exact zero_ne_one this

end GroundTheory.Heights₂.Heights.Inter
