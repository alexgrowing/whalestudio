import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.FrobeniusEigenvaluesTraceZeroAdjoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusPowerCompatibility

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GroundTheory.Global.SemiLocal
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd

open private Ad3P.SEGAux.frobenius_eigenvalues_trace_zero_adjoint Ad3P.SEGAux.charEig_cyc_inv Ad3P.SEGAux.algSat_eq from PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.FrobeniusEigenvaluesTraceZeroAdjoint

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.AdjointSystem

private theorem unif_val {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (μ : kˣ →* ℂˣ) (hμ : GroundTheory.LocalField.IsUnramifiedChar μ) : μ (unif k) = μ (GroundTheory.LocalField.unifUnit k) := by
  obtain ⟨⟨h1, h2⟩, -⟩ := polFacts k
  have hord := GroundTheory.LocalField.ord_unifUnit (K := k)
  have hle : ∀ {x : k}, x ≠ 0 → (ValuativeRel.valuation k x ≤ 1 ↔ 0 ≤ GroundTheory.LocalField.ord x) := fun {x} hx => by
    have h0 := GroundTheory.LocalField.mem_valBall_iff_le_ord (n := 0) hx
    rwa [GroundTheory.LocalField.mem_valBall_zero_iff, Valuation.mem_integer_iff] at h0
  have hlt : ∀ {x : k}, x ≠ 0 → (ValuativeRel.valuation k x < 1 ↔ 1 ≤ GroundTheory.LocalField.ord x) := fun {x} hx => by
    have h0 := GroundTheory.LocalField.mem_valBall_iff_le_ord (n := 1) hx
    rwa [GroundTheory.LocalField.mem_valBall_one_iff] at h0
  have a1 := (hlt (unif k).ne_zero).1 h1
  have a2 := h2 _ ((hlt (GroundTheory.LocalField.unifUnit k).ne_zero).2 hord.ge)
  have a3 : ValuativeRel.valuation k ((GroundTheory.LocalField.unifUnit k * (unif k)⁻¹ : kˣ) : k) ≤ 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ a2 zero_le'
  have a4 := (hle (Units.ne_zero _)).1 a3
  rw [GroundTheory.LocalField.ord_units_mul, GroundTheory.LocalField.ord_units_inv, hord] at a4
  have a5 : GroundTheory.LocalField.ord ((unif k : kˣ) : k) = 1 := by omega
  have a6 := GroundTheory.LocalField.isUnramifiedChar_iff.1 hμ (unif k * (GroundTheory.LocalField.unifUnit k)⁻¹) (by
    rw [GroundTheory.LocalField.ord_units_mul, GroundTheory.LocalField.ord_units_inv, hord, a5]; simp)
  rwa [map_mul, map_inv, mul_inv_eq_one] at a6

private theorem charpoly_inv {M M' : Matrix (Fin 2) (Fin 2) ℂ} (h : M * M' = 1) {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : M.charpoly = X ^ 2 - C (a + b) * X + C (a * b)) : M'.charpoly = (X - C b⁻¹) * (X - C a⁻¹) := by
  rw [Matrix.charpoly_fin_two] at hc
  have e0 := congrArg (eval 0) hc
  have e1 := congrArg (eval 1) hc
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
  have hd : M.det = a * b := by simpa using e0
  have ht : M.trace = a + b := by
    rw [hd] at e1
    linear_combination -e1
  have hi : M' = (a * b)⁻¹ • M.adjugate := by
    rw [← Matrix.inv_eq_right_inv h, Matrix.inv_def, hd, Ring.inverse_eq_inv']
  have t' : M'.trace = b⁻¹ + a⁻¹ := by
    rw [hi, Matrix.trace_smul, Matrix.adjugate_fin_two, Matrix.trace_fin_two]
    rw [Matrix.trace_fin_two] at ht
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul]
    field_simp
    linear_combination ht
  have d' : M'.det = b⁻¹ * a⁻¹ := by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_one, hd] at this
    field_simp
    linear_combination this
  rw [Matrix.charpoly_fin_two, t', d']
  simp only [map_add, map_mul]
  ring

private theorem frobEig_unique {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l n : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 F)} {B B' : Multiset ℂ}
    (h : FrobEig ι r w B) (h' : FrobEig ι r w B') : B = B' := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have e := ((h A hA).2 σ hσ).symm.trans ((h' A hA).2 σ hσ)
  have e2 := congrArg Polynomial.roots e
  rwa [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at e2

private theorem ev_under (K : Type) [Field K] [NumberField K] {Q : HeightOneSpectrum (𝓞 K) → Prop}
    (h : ∀ᶠ w in Filter.cofinite, Q w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∀ w : PlacesOver K v, Q w.1 := by
  refine Filter.eventually_cofinite.2 (((Filter.eventually_cofinite.1 h).image fun w => w.under (𝓞 ℚ)).subset fun v hv => ?_)
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨w.1, hw, HeightOneSpectrum.ext w.2.over.symm⟩

private theorem frobEig_geom {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (v : HeightOneSpectrum (𝓞 ℚ)) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ A : ValuationSubring Ω, IsPlaceOver A v → (∀ s ∈ Ine (F := ℚ) A, ρ s = 1) ∧ ∀ σ : G ℚ Ω, IsFrob A (normV v) σ →
      (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.map ι.toRingHom = X ^ 2 - C (a + b) * X + C (a * b)) :
    FrobEig ι ρ v {b⁻¹, a⁻¹} := fun A hA => by
  obtain ⟨h1, h2⟩ := h A hA
  refine ⟨h1, fun σ hσ => ?_⟩
  have e := h2 σ hσ
  rw [← Matrix.charpoly_map] at e ⊢
  have hm : (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)).map ι.toRingHom * (ρ σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).map ι.toRingHom = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [charpoly_inv hm ha hb e]
  simp

private theorem algSat_inj (n q : ℕ) (hq : q ≠ 0) {B B' : Multiset ℂˣ} (h : algSat n q B = algSat n q B') : B = B' := by
  have hc : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hq)) _).ne'
  rw [Ad3P.SEGAux.algSat_eq, Ad3P.SEGAux.algSat_eq] at h
  exact Multiset.map_injective (fun x y e => Units.ext (mul_left_cancel₀ hc e)) h

private theorem algSat_three (q : ℕ) (t : ℂˣ) : algSat 3 q {t, 1, t⁻¹} = {(q : ℂ) * t, (q : ℂ), (q : ℂ) * (t⁻¹ : ℂˣ)} := by
  have h : ((((q : ℝ) ^ (((3 : ℝ) - 1) / 2) : ℝ)) : ℂ) = q := by
    have : (((3 : ℝ) - 1) / 2) = 1 := by norm_num
    rw [this, Real.rpow_one]
    simp
  simp [algSat, h]

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.AdjointSystem

open UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.AdjointSystem in
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.adSysOf :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.AdSysOf := by
  intro l _ Ω _ _ _ ι N _ χ D g ρ hR hS K _ _ _ _ P hA
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  have h0 : Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hb : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, v ∉ D.bad :=
    Filter.eventually_cofinite.2 (by simpa using D.bad.finite_toSet)
  filter_upwards [hR, hl, hb, ev_under K hA.2] with v h1 h2 h3 h4 w
  obtain ⟨B, hB, hF⟩ := h4 w
  obtain ⟨α, β, e1, e2, e3⟩ := hS.2 v h3
  have hp : Ad3.pOf v = normV v := by
    simp [Ad3.pOf, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hq' : Ideal.absNorm w.1.asIdeal = Ideal.absNorm v.asIdeal ^ fdeg w := (normVal ℚ K v w (1 : _ →* ℂˣ)).2.2.2
  have hnq : normV w.1 = normV v ^ fdeg w := by
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hq'
  have hu : w.1.under (𝓞 ℚ) = v := HeightOneSpectrum.ext w.2.over.symm
  have e4 : D.ν v (unif (v.adicCompletion ℚ)) = α / β := (unif_val (D.ν v) (D.unr v h3)).trans e3
  have g1 : FrobEig ι ρ v {(β : ℂ)⁻¹, (α : ℂ)⁻¹} := by
    refine frobEig_geom ι ρ v α β α.ne_zero β.ne_zero fun A hA' => ?_
    refine ⟨(h1 A hA').1, fun σ hσ => ?_⟩
    rw [(h1 A hA').2 σ hσ, e1, e2, hp]
  have g2 := Ad3P.SEGAux.frobenius_eigenvalues_trace_zero_adjoint ι ρ v _ _ (inv_ne_zero β.ne_zero) (inv_ne_zero α.ne_zero) g1
  have g3 := UpperTheory.frobenius_eigenvalues_twist ℚ Ω l ι 3 _ _ v _ _ g2 (Ad3P.SEGAux.charEig_cyc_inv ι v h2)
  have g4 := (UpperTheory.frobenius_power_compatibility ℚ K Ω l ι w.1 (fdeg w) (by rw [hu]; exact hnq)).1 3 _ _ (by rw [hu]; exact g3)
  have g5 := frobEig_unique hF g4
  have hnz : normV w.1 ≠ 0 := by
    have := Ideal.absNorm_eq_zero_iff.not.2 w.1.ne_bot
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this
  rw [e4]
  have hfin : B = {(α / β) ^ fdeg w, 1, ((α / β) ^ fdeg w)⁻¹} := by
    refine algSat_inj 3 (normV w.1) hnz (g5.trans ?_)
    rw [algSat_three, hnq]
    have hα := α.ne_zero
    have hβ := β.ne_zero
    have x1 : (((β : ℂ)⁻¹ / (α : ℂ)⁻¹) * (normV v : ℂ)) ^ fdeg w =
        ((normV v ^ fdeg w : ℕ) : ℂ) * (((α / β) ^ fdeg w : ℂˣ) : ℂ) := by
      push_cast
      rw [mul_pow, mul_comm]
      congr 2
      field_simp
    have x3 : (((α : ℂ)⁻¹ / (β : ℂ)⁻¹) * (normV v : ℂ)) ^ fdeg w =
        ((normV v ^ fdeg w : ℕ) : ℂ) * ((((α / β) ^ fdeg w)⁻¹ : ℂˣ) : ℂ) := by
      push_cast
      rw [mul_pow, mul_comm, ← inv_pow]
      congr 2
      field_simp
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    rw [x1, x3]
    simp
  rw [← hfin]
  exact hB
