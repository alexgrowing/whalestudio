import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulConjSelf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelIsometryHalfLatticeVolumeOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfIpEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentBaseFunctionIdentityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPlaceModelLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchwartzBruhatHalfIffPullbackMatrix

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitCoordModel

variable {D : D7}

theorem exists_haar (v : FinPl D) : ∃ ν : Measure (Fv D.host.F v), ν.IsAddHaarMeasure := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  exact ⟨MeasureTheory.Measure.addHaar, inferInstance⟩

theorem pull_sub {S T : HSp D} {v : FinPl D} {m n : ℕ} (a : AE D)
    (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)) (Φ₁ Φ₂ : Matrix (Fin m) (Fin n) (Fv D.host.F v) → ℂ) :
    pull a κ (Φ₁ - Φ₂) = pull a κ Φ₁ - pull a κ Φ₂ := by
  funext t
  simp only [pull, Pi.sub_apply]
  split_ifs <;> simp

theorem ipO_smul_smul {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (c : ℂ) (f : Mx D m n → ℂ) :
    ipO μ 𝓕 (c • f) (c • f) = (c * (starRingEnd ℂ) c) * ipO μ 𝓕 f f := by
  unfold ipO
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext w
  ring

theorem bijOn_and_om_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (e a : AE D), IsSplitIdem D e → e + cA D e = idem D (.inl v) → (a = e ∨ a = cA D e) → ∀ (m n : ℕ) (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsCoord a (latO S T ΛS ΛT fun _ => True) κ → ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → Set.BijOn (fun Φ => Tm (pull a κ Φ)) (GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v))) {f | IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) f} ∧ ∀ g h, SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ∀ (γ : GL (Fin n) (Fv D.host.F v)) (δ : GL (Fin m) (Fv D.host.F v)), (∀ t, κ (actO S T g⁻¹ h⁻¹ t) = (δ⁻¹).val * κ t * γ.val) → ∀ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), om (g, h) (Tm (pull a κ Φ)) = ((splitFacO χS χT x y : Circle) : ℂ) • Tm (pull a κ (linOm v γ δ Φ)) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hC v e a he hev ha m n κ hκ Tm hTm

  obtain ⟨haS, haI⟩ : IsSplitIdem D a ∧ a + cA D a = idem D (.inl v) := by
    rcases ha with rfl | rfl
    · exact ⟨he, hev⟩
    · obtain ⟨h1, h2, w, ε, hε, h3⟩ := he
      refine ⟨⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm]; exact h2, w, ε, hε, by rw [cA_cA, add_comm]; exact h3⟩, ?_⟩
      rw [cA_cA, add_comm]; exact hev
  obtain ⟨-, hloc, hsurj⟩ : _ ∧ _ ∧ _ := by
    have := GlobalTheory.T.split_idempotent_base_function_identity D ψ θ S T sS sT ΛS ΛT f₀ hB v a haS haI
    exact ⟨this.1, this.2 Tm hTm⟩
  have hP := GlobalTheory.HalfCoordSB.isSBHalf_iff_pull D S T v m n a _ κ hκ
  obtain ⟨ν, hν⟩ := exists_haar (D := D) v
  obtain ⟨hv0, hvT, hIso⟩ := GlobalTheory.T.schrodingerModel_halfLatticeVolume_mul_inner_eq_inner D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC v a haS m n κ hκ Tm hTm ν hν
  have hvol : ((GlobalTheory.SplitWeil.volM ν (Fin m) (Fin n)
      (κ '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf a t})).toReal : ℂ) ≠ 0 := by
    exact_mod_cast ENNReal.toReal_ne_zero.mpr ⟨hv0, hvT⟩
  have hU := GlobalTheory.LinUnit.linOm_unitary D v m n
  have hdef : ∀ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)),
      GlobalTheory.SplitWeil.ip ν Φ Φ = 0 → Φ = 0 := fun Φ hΦ => ((hU 1 1).2 Φ hΦ).2 ν hν |>.2
  refine ⟨⟨fun Φ hΦ => hloc _ (hP.1 Φ hΦ), ?_, ?_⟩, ?_⟩
  · intro Φ₁ h₁ Φ₂ h₂ heq
    have hd : Φ₁ - Φ₂ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)) :=
      Submodule.sub_mem _ h₁ h₂
    have h0 : Tm (pull a κ (Φ₁ - Φ₂)) = 0 := by
      rw [pull_sub, map_sub, sub_eq_zero]; exact heq
    have hi := hIso _ hd _ hd
    rw [h0] at hi
    refine sub_eq_zero.mp (hdef _ hd ?_)
    rw [← hi]; simp [ipO]
  · intro x hx
    obtain ⟨Ψ, hΨ, rfl⟩ := hsurj x hx
    obtain ⟨Φ, hΦ, rfl⟩ := hP.2 Ψ hΨ
    exact ⟨Φ, hΦ, rfl⟩
  · intro g h hg hh x y hx hy γ δ hκa Φ hΦ
    obtain ⟨r, hr, hom⟩ := GlobalTheory.PlaceTensor.om_placeModel_linear D ψ θ S T χS χT om sS sT ΛS ΛT f₀ hW hB v e a he hev
      ha Tm hTm g h hg hh x y hx hy
    obtain ⟨r', hr', hlin⟩ := (hU γ δ).1
    have hr'0 : (r' : ℂ) ≠ 0 := by exact_mod_cast hr'.ne'

    have hsub : (fun t => pull a κ Φ (actO S T g⁻¹ h⁻¹ t)) = ((r' : ℂ)⁻¹) • pull a κ (linOm v γ δ Φ) := by
      funext t
      simp only [pull, Pi.smul_apply, smul_eq_mul, hlin]
      by_cases ht : IsHalf a t
      · rw [if_pos (GlobalTheory.SplitHecke.isHalf_actO g⁻¹ h⁻¹ ht), if_pos ht, hκa]
        field_simp
      · have ht' : ¬ IsHalf a (actO S T g⁻¹ h⁻¹ t) := by
          intro h'
          apply ht
          have h2 := GlobalTheory.SplitHecke.isHalf_actO g h h'
          have h3 := GlobalTheory.SplitHecke.actO_inv_actO g⁻¹ h⁻¹ t
          rw [inv_inv, inv_inv] at h3
          rwa [h3] at h2
        rw [if_neg ht', if_neg ht, mul_zero]
    have hmain : om (g, h) (Tm (pull a κ Φ)) =
        (((r : ℂ) * (r' : ℂ)⁻¹) * ((splitFacO χS χT x y : Circle) : ℂ)) • Tm (pull a κ (linOm v γ δ Φ)) := by
      rw [hom _ (hP.1 Φ hΦ), hsub, map_smul, smul_smul]
      congr 1; ring
    by_cases hΦ0 : GlobalTheory.SplitWeil.ip ν Φ Φ = 0
    ·
      have hz := hdef Φ hΦ hΦ0
      subst hz
      have hG0 : pull a κ (linOm v γ δ 0) = 0 := by
        funext t; simp [pull, hlin]
      rw [hmain, hG0]; simp
    ·
      have hF : IsThetaFunO ψ S T (Tm (pull a κ Φ)) := (hloc _ (hP.1 Φ hΦ)).1
      have h1 : ipO μ 𝓕 (om (g, h) (Tm (pull a κ Φ))) (om (g, h) (Tm (pull a κ Φ))) =
          ipO μ 𝓕 (Tm (pull a κ Φ)) (Tm (pull a κ Φ)) := by
        unfold ipO
        exact GlobalTheory.WeilInner.om_inner D ψ S T χS χT om hW μ 𝓕 hC (g, h) _ _ hF hF
      rw [hmain, ipO_smul_smul] at h1
      have hΦL := ((hU γ δ).2 Φ hΦ).1
      have hunit := (((hU γ δ).2 Φ hΦ).2 ν hν).1
      have e1 := hIso Φ hΦ Φ hΦ
      have e2 := hIso _ hΦL _ hΦL
      rw [hunit] at e2
      have hGF := mul_left_cancel₀ hvol (e2.trans e1.symm)
      have hI : ipO μ 𝓕 (Tm (pull a κ Φ)) (Tm (pull a κ Φ)) ≠ 0 := by
        intro h0; apply hΦ0; rw [← e1, h0, mul_zero]
      rw [hGF] at h1
      have hc := mul_right_cancel₀ hI (h1.trans (one_mul _).symm)
      have hχ : ((splitFacO χS χT x y : Circle) : ℂ) * (starRingEnd ℂ) ((splitFacO χS χT x y : Circle) : ℂ) = 1 := by
        rw [Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
      rw [map_mul, map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_ofReal] at hc
      have hsq : ((r : ℂ) * (r' : ℂ)⁻¹) ^ 2 = 1 := by
        linear_combination hc - ((r : ℂ) * (r' : ℂ)⁻¹) ^ 2 * hχ
      have hsqR : (r * r'⁻¹) ^ 2 = (1 : ℝ) := by exact_mod_cast hsq
      have hq : r * r'⁻¹ = 1 := (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).mp hsqR
      have hqC : (r : ℂ) * (r' : ℂ)⁻¹ = 1 := by exact_mod_cast hq
      rw [hmain, hqC, one_mul]

end GlobalTheory.SplitCoordModel
