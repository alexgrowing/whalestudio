import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldLP
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModerateGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormAdelicThetaSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalDarbouxFixesThetaDistributionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianTwistToHermitian
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.LiftPair
open scoped Matrix TensorProduct NNReal

namespace GlobalTheory.ThK.PairConv

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_herm_of_skew (hCM : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = -J i j)
    (hd : J.det ≠ 0) : ∃ c₀ : E, c₀ ≠ 0 ∧ IsHermND σ (c₀ • J.map σ) := by
  obtain ⟨x, hx⟩ := GlobalTheory.SkewToHerm.exists_sigma_ne σ hCM
  have hss := GlobalTheory.SiegelSet.sigma_sigma hCM
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_sub, hss]
    rw [hJ j i]
    ring
  · have hdet : (J.map σ).det = σ J.det := by rw [AlgHom.map_det]; rfl
    rw [Matrix.det_smul, hdet]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hx))) ((map_ne_zero_iff σ σ.toRingHom.injective).2 hd)

theorem exists_rat_ht_le {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : UA σ J) :
    ∃ γ ∈ ratU σ J, (ht (γ * h) : ℝ) ≤ 2 * qht h := by
  have h1 : (1 : ℝ≥0) ≤ qht h := le_ciInf fun γ => one_le_heightGL F _
  have h2 : qht h < 2 * qht h := by
    rw [two_mul]; exact lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one h1)
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt h2
  exact ⟨γ.1, γ.2, by exact_mod_cast hγ.le⟩

theorem thetaSum_moderateGrowth (hcm : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {n m : ℕ}
    {JX : Matrix (Fin n) (Fin n) E} {JY : Matrix (Fin m) (Fin m) E}
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JY)) (Fin n × Fin m)) {χX χY : Chr F E}
    {om : UA σ JX × UA σ JY →* Module.End ℂ ((Fin n × Fin m → AF F) → ℂ)}
    (hW : IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JY) co χX χY om)
    {Φ : (Fin n × Fin m → AF F) → ℂ} (hΦ : Φ ∈ schA F (Fin n × Fin m)) :
    ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖thetaSum F (om (g, h) Φ)‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  obtain ⟨v, -, ⟨τ⟩⟩ := GlobalTheory.Orb.exists_split_place_notMem hcm ∅
  let B : Base F E := ⟨ψ, fun w => Classical.choice inferInstance, 0, 0, ∅, fun v => absurd v.2 (Finset.notMem_empty _), v, τ⟩
  let X : Spc F E n := ⟨JX, ⊥, 0, 1⟩
  let Y : Spc F E m := ⟨JY, ⊥, 0, 1⟩
  exact GlobalTheory.ThetaFree.theta_moderateGrowth F E σ B n m X Y ⟨co, fun _ => 0, 0, ∅⟩ χX χY om ⟨hψ, hW⟩ Φ hΦ

end

theorem integrableOn_mul_conj_theta : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.ThK.KP → ∀ (hcm : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (n m : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JY : Matrix (Fin m) (Fin m) E), (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → ∀ (hY : ∀ i j, σ (JY j i) = -JY i j) (hYd : JY.det ≠ 0) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JY)) (Fin n × Fin m)), (∀ x : Matrix (Fin n) (Fin m) E, ∃ y z : Fin n × Fin m → F, co.e (incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) → ∀ χX χY : Chr F E, IsHecke F E χX → IsHecke F E χY → ∀ om : UA σ JX × UA σ JY →* Module.End ℂ ((Fin n × Fin m → AF F) → ℂ), IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JY) co χX χY om → ∀ f : UA σ JY → ℂ, Continuous f → (∀ γ ∈ ratU σ JY, ∀ h, f (γ * h) = f h) → (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) → ∀ Φ ∈ schA F (Fin n × Fin m), ∀ (g : UA σ JX) (μ : Measure (UA σ JY)) (𝓕 : Set (UA σ JY)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ JY) 𝓕 μ → IntegrableOn (fun h => f h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ))) 𝓕 μ := by
  intro F E _ _ _ _ _ σ hK hcm ψ hψ n m JX JY hX hXd hY hYd co hco χX χY hχX hχY om hW f hfc _ hdec Φ hΦ g μ 𝓕 hμ h𝓕
  have hS := hW.isUSplitting
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨c₀, hc₀, hJ⟩ := exists_herm_of_skew hcm hY hYd
  have heq := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := JY) hσ hc₀
  haveI : BorelSpace (UA σ JY) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.ThKContSmall.measure_fundamental_domain_lt_top hK.siegelSetUnitary hcm hJ _ heq μ hμ 𝓕 h𝓕).ne
  have hcont : Continuous fun h : UA σ JY => thetaSum F (om (g, h) Φ) := by
    obtain ⟨l, hl, hlt⟩ := GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact F (Fin n × Fin m)
    have h1 : Continuous fun x : UA σ JX × UA σ JY => thetaSum F (om x Φ) :=
      (hS.cont l hl Φ hΦ).congr fun x => hlt _ (hS.pres _ _ hΦ)
    exact h1.comp (continuous_const.prodMk continuous_id)
  have hinv : ∀ γ ∈ ratU σ JY, ∀ h, thetaSum F (om (g, γ * h) Φ) = thetaSum F (om (g, h) Φ) := by
    intro γ hγ h
    have e : om (g, γ * h) Φ = om (1, γ) (om (g, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e]
    exact GlobalTheory.T.weilRep_rationalDarboux_fixes_thetaDistribution F E σ hcm ψ hψ n m JX JY hX hXd hY hYd co hco χX χY hχX hχY om hW 1 (one_mem _) γ hγ _
      (hS.pres _ _ hΦ)
  obtain ⟨C, k, hC⟩ := thetaSum_moderateGrowth hcm hψ co hW hΦ
  obtain ⟨D, hD⟩ := hdec k
  refine Integrable.of_bound (hfc.mul (Complex.continuous_conj.comp hcont)).aestronglyMeasurable
    (max C 0 * ((ht g : ℝ) * 2) ^ k * D) (.of_forall fun h => ?_)
  obtain ⟨γ, hγ, hγh⟩ := exists_rat_ht_le h
  have hg0 : (0 : ℝ) ≤ ht g := NNReal.coe_nonneg _
  have b : ‖thetaSum F (om (g, h) Φ)‖ ≤ max C 0 * ((ht g : ℝ) * (2 * qht h)) ^ k := by
    rw [← hinv γ hγ h]
    refine (hC g _).trans ?_
    have h0 : (0 : ℝ) ≤ (ht g : ℝ) * ht (γ * h) := mul_nonneg hg0 (NNReal.coe_nonneg _)
    exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ h0 (mul_le_mul_of_nonneg_left hγh hg0) k) (pow_nonneg h0 _)
      (le_max_right _ _)
  rw [norm_mul, Complex.norm_conj]
  calc ‖f h‖ * ‖thetaSum F (om (g, h) Φ)‖ ≤ ‖f h‖ * (max C 0 * ((ht g : ℝ) * (2 * qht h)) ^ k) :=
        mul_le_mul_of_nonneg_left b (norm_nonneg _)
    _ = max C 0 * ((ht g : ℝ) * 2) ^ k * (‖f h‖ * (qht h : ℝ) ^ k) := by
        rw [← mul_assoc (ht g : ℝ), mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hD h) (mul_nonneg (le_max_right _ _) (pow_nonneg (by linarith) _))

end GlobalTheory.ThK.PairConv

end
