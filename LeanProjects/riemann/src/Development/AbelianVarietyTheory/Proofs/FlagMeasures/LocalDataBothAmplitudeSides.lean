import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcTypeWIrreducibleAndSchurAverage
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiffQuotientBesselMapTendstoStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOnStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentEqLebesgueStatement

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Side

theorem urep_irred_of_ds {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    (h : IsDSHpk k r ε lam σ) : IsURepOn (GG k r) σ ∧ IsIrredOn (GG k r) σ := by
  obtain ⟨P, ⟨⟨hP, hH⟩, -⟩, -, -, ⟨⟨h1, hm⟩, hn, hc⟩, hi, -⟩ := h
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hPi : P * P⁻¹ = 1 := mul_nonsing_inv _ hd
  have hiP : P⁻¹ * P = 1 := nonsing_inv_mul _ hd
  have mem : ∀ g, g ∈ GG k r ↔ P * g * P⁻¹ ∈ UJset ε := uHConj _ ε _ P hd hH
  have back : ∀ g : Mat k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hiP]; simp
  have forth : ∀ g : Mat k r, P * (P⁻¹ * g * P) * P⁻¹ = g := fun g => by
    calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hPi]; simp
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · simpa [hiP] using h1
  · intro a ha b hb
    have := hm _ ((mem a).1 ha) _ ((mem b).1 hb)
    have e : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
      calc P * a * P⁻¹ * (P * b * P⁻¹) = P * a * (P⁻¹ * P) * b * P⁻¹ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hiP]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    simpa only [e, back] using this
  · intro g hg v
    have := hn _ ((mem g).1 hg) v
    simpa only [back] using this
  · intro v
    have hcont : Continuous fun g : Mat k r => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := (hc v).comp hcont.continuousOn (s := GG k r) (fun g hg => (mem g).1 hg)
    refine this.congr fun g _ => ?_
    simp only [Function.comp, back]
  · intro S hS hst
    refine hi S hS fun g hg v hv => hst _ ((mem _).2 ?_) v hv
    rw [forth]; exact hg

theorem isHaarOn_smul {k r : ℕ} {S : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn S μ) {c : ℝ}
    (hc : 0 < c) : IsHaarOn S (ENNReal.ofReal c • μ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : ENNReal.ofReal c • μ = c.toNNReal • μ := rfl
    rw [this]; infer_instance
  · intro h0
    rcases Measure.ennreal_smul_eq_zero.1 h0 with h | h
    · exact (ENNReal.ofReal_pos.2 hc).ne' h
    · exact h2 h
  · rw [Measure.smul_apply, h3, smul_zero]
  · intro s hs
    rw [Measure.map_smul, h4 s hs]

theorem oneSide_of_bessel {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {σ : Mat k r → (H →L[ℂ] H)} {z : Fin (2 * r + k + 1) → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} {u : Fin k → ℝ}
    {s : ℂ} {μG μW μN νS : Measure (Mt k r)} {B : H → Wp} {v : H} {c : ℝ}
    (hσ : IsURepOn (GG k r) σ) (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : IsHCTypeW k r z u π)
    (hG : IsHaarOn (GG k r) μG) (hW : IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1)
    (hN : IsHaarOn (Nset k r) μN) (hq : IsQuotMeas μG (muS μW μN) νS)
    (hB : IsBesselMapSm z (psi k r z s) σ π B) (hv : IsSmoothVec σ v) (hc : 0 < c)
    (hl : l2SG νS (fun g => B (σ g v)) = ENNReal.ofReal (c * Module.finrank ℂ Wp)) :
    OneSide z π (psi k r z s) μG μW μN νS (fun g => B (σ g v)) c := by
  have := FiniteDimensional.complete ℂ Wp
  obtain ⟨hnt, hu, hi⟩ := (GlobalTheory.Amp.Schur.type_irred_and_avg k r z π hz hT).1 u hπ
  refine ⟨hz, hT, hnt, hu, hi, hG, hW, hW1, hN, hq, fun n hn => (psiChar k r z s hz n hn).2, ?_, ?_, hc, hl⟩
  · intro h hh m hm g hg
    have hdet : IsUnit (Hpk k r).det :=
      Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1
    have hhm : h * m ∈ GG k r := (uHGroup _ _ hdet).2.1 h hh.1 m hm.1
    have hs : IsSmoothVec σ (σ g v) := ((GlobalTheory.T.smooth_vectors_dense_invariant k r σ v hσ).2.2.2.1 v hv).1 g hg
    have := hB.2.2.1 h hh m hm (σ g v) hs
    show B (σ (h * m * g) v) = _
    rw [hσ.1.2 _ hhm _ hg]
    exact this
  · exact (GlobalTheory.T.diffQuotient_besselMap_tendsto k r σ z _ π B v 0 hσ hB hv (by simp [InLieHpk])).2.1

theorem both_sides : ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) lam (A : LocS W), 0 < θ → 0 < D.host.v → HypTT D w w' → GoodW D τ w w' θ W → GoodS D lam A → IsURepOn (GG D.R.k D.R.rS) A.σ ∧ IsIrredOn (GG D.R.k D.R.rS) A.σ ∧ W.μN = ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS ∧ OneSide W.z W.π (psiS D W.z) W.μG W.μW W.μN W.νS A.Φ A.cN ∧ OneSide W.z' W.π' (psiS D W.z') W.μG W.μW' W.μN W.νS' A.Φ' A.cN := by
  intro D τ w w' θ W lam A hθ hv hTT hW hA
  obtain ⟨c1, c2, z1, z2, t1, t2, hG, w1, w1', w2, w2', hN, q1, q2⟩ := hW
  obtain ⟨-, hds, b1, b2, hsm, -, -, hc, l1, l2, -⟩ := hA
  obtain ⟨hu, hi⟩ := urep_irred_of_ds hds
  have hpos : 0 < (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ := by positivity
  have hμ : W.μN = ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ *
      2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS := by
    have e : haarLie (Nset D.R.k D.R.rS) (kapN D θ) = kapN D θ • haarLie (Nset D.R.k D.R.rS) 1 := by
      unfold haarLie; rw [one_smul]
    rw [hN, e, GlobalTheory.T.haar_lie_nilpotent_eq_lebesgue, smul_smul, ENNReal.ofReal_mul hpos.le, ENNReal.ofReal_pow (by norm_num)]
    simp [kapN]
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hμ]; exact isHaarOn_smul (GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn _ _) (by positivity)
  have hT1 : 0 < Tz D.R.k D.R.rS W.z := by
    rw [t1]; unfold Tr; exact_mod_cast hTT.1.pos
  have hT2 : 0 < Tz D.R.k D.R.rS W.z' := by
    rw [t2]; unfold Tr; exact_mod_cast hTT.2.1.pos
  exact ⟨hu, hi, hμ, oneSide_of_bessel hu z1 hT1 c1 hG w1 w1' hNH q1 b1 hsm hc l1,
    oneSide_of_bessel hu z2 hT2 c2 hG w2 w2' hNH q2 b2 hsm hc l2⟩

end GlobalTheory.Amp.Side
