import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevTransportHer
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RankOneEmbeddings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TLFinal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature

theorem haarSmul {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hcT : c ≠ ∞) : B.IsHaarOn U (c • μ) where
  conc := by rw [Measure.smul_apply, h.conc, smul_zero]
  left a ha := by rw [Measure.map_smul, h.left a ha]
  right a ha := by rw [Measure.map_smul, h.right a ha]
  finite_compact K hK := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hcT) (h.finite_compact K hK)
  ne_zero := by
    intro h0
    apply h.ne_zero
    have := congrArg (fun ν : Measure (Mt k r) => c⁻¹ • ν) h0
    simpa [smul_smul, ENNReal.inv_mul_cancel hc0 hcT] using this

section norm

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem massW_ne_zero (Bs : B.RealPlaceData k r Wp Wq) : Bs.μW Set.univ ≠ 0 :=
  Measure.measure_univ_ne_zero.2 Bs.haarW.ne_zero

theorem massW'_ne_zero (Bs : B.RealPlaceData k r Wp Wq) : Bs.μW' Set.univ ≠ 0 :=
  Measure.measure_univ_ne_zero.2 Bs.haarW'.ne_zero

theorem massW_ne_top (Bs : B.RealPlaceData k r Wp Wq) : Bs.μW Set.univ ≠ ∞ := by
  have := Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.haar_finite Formalism.FourierDecayAlt.P.B2x3.compactW Bs.z_mem Bs.T_pos Bs.haarW
  exact measure_ne_top _ _

theorem massW'_ne_top (Bs : B.RealPlaceData k r Wp Wq) : Bs.μW' Set.univ ≠ ∞ := by
  have := Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.haar_finite Formalism.FourierDecayAlt.P.B2x3.compactW Bs.z'_mem Bs.T'_pos Bs.haarW'
  exact measure_ne_top _ _

def normS (Bs : B.RealPlaceData k r Wp Wq) : B.RealPlaceData k r Wp Wq :=
  { Bs with
    μW := (Bs.μW Set.univ)⁻¹ • Bs.μW
    μW' := (Bs.μW' Set.univ)⁻¹ • Bs.μW'
    μN := D.muN k r
    haarW := haarSmul Bs.haarW (ENNReal.inv_ne_zero.2 (massW_ne_top Bs)) (ENNReal.inv_ne_top.2 (massW_ne_zero Bs))
    haarN := Formalism.FourierDecayAlt.P.Dx2.MN.haar r
    haarW' := haarSmul Bs.haarW' (ENNReal.inv_ne_zero.2 (massW'_ne_top Bs))
      (ENNReal.inv_ne_top.2 (massW'_ne_zero Bs)) }

theorem normS_μW_univ_eq_one (Bs : B.RealPlaceData k r Wp Wq) : (normS Bs).μW Set.univ = 1 := by
  show ((Bs.μW Set.univ)⁻¹ • Bs.μW) Set.univ = 1
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel (massW_ne_zero Bs) (massW_ne_top Bs)]

theorem normS_μW'_univ_eq_one (Bs : B.RealPlaceData k r Wp Wq) : (normS Bs).μW' Set.univ = 1 := by
  show ((Bs.μW' Set.univ)⁻¹ • Bs.μW') Set.univ = 1
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel (massW'_ne_zero Bs) (massW'_ne_top Bs)]

end norm

theorem towerAt : Formalism.FourierDecayAlt.P.PTie.TowerAt := by
  intro k r Wp Wq _ _ _ _ Bs
  obtain ⟨T, hT, hN⟩ := Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq (normS Bs) (normS_μW_univ_eq_one Bs) (normS_μW'_univ_eq_one Bs) rfl
  exact ⟨T, by rw [hT]; rfl, by rw [hT]; rfl, by rw [hT]; rfl, by rw [hT]; rfl, hN⟩

section frame

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem herm_mulVec' {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * H * g = H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hg]

theorem frameVec_facts (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (hF : D.IsBaseFrame Bs ν' m₀) :
    inWb k r (m₀ *ᵥ ν') ∧ herm (Hpk k r) (m₀ *ᵥ ν') Bs.z = 0 ∧ herm (Hpk k r) (m₀ *ᵥ ν') (m₀ *ᵥ ν') = 1 := by
  obtain ⟨hw, hz, hn, hm, hmz⟩ := hF
  have hU : m₀ᴴ * Hpk k r * m₀ = Hpk k r := hm.1
  refine ⟨Formalism.FourierDecayAlt.P.Qx8.inWb_mulVec hm hw, ?_, by rw [herm_mulVec' hU]; exact hn⟩
  have h0 : herm (Hpk k r) (m₀ *ᵥ ν') (m₀ *ᵥ Bs.z') = 0 := by rw [herm_mulVec' hU]; exact hz
  rw [hmz] at h0
  set c : ℂ := ((√(Tz k r Bs.z' / Tz k r Bs.z) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact_mod_cast (Real.sqrt_pos.mpr (div_pos Bs.T'_pos Bs.T_pos)).ne'
  have e : herm (Hpk k r) (m₀ *ᵥ ν') (c • Bs.z) = star c * herm (Hpk k r) (m₀ *ᵥ ν') Bs.z := by
    unfold herm
    rw [star_smul, smul_dotProduct, smul_eq_mul]
  rw [e] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (star_eq_zero.mp h) hc0
  · exact h

theorem frame_of (Bs : B.RealPlaceData k r Wp Wq) : ∃ (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r),
    D.IsBaseFrame Bs ν' m₀ := by
  obtain ⟨Fb, hBw, hBo, hBz⟩ := Formalism.FourierDecayAlt.P.Qx8.frame_exists Bs.z'_mem Bs.T'_pos
  set T : ℝ := Tz k r Bs.z with hTdef
  set T' : ℝ := Tz k r Bs.z' with hT'def
  have hT : 0 < T := Bs.T_pos
  have hT' : 0 < T' := Bs.T'_pos
  set c : ℝ := √(T' / T) with hc
  have hcc : c * c = T' / T := Real.mul_self_sqrt (div_pos hT' hT).le
  have hcw : inWb k r ((c : ℂ) • Bs.z) := Formalism.FourierDecayAlt.P.Qx8.inWb_smul Bs.z_mem _
  have hz' : herm (Hpk k r) Bs.z' Bs.z' = ((-T' : ℝ) : ℂ) := by
    rw [Formalism.FourierDecayAlt.P.Qx8.herm_self']; push_cast; rfl
  have hcz : herm (Hpk k r) ((c : ℂ) • Bs.z) ((c : ℂ) • Bs.z) = ((-T' : ℝ) : ℂ) := by
    rw [Formalism.FourierDecayAlt.P.Qx8.herm_smul_left', Formalism.FourierDecayAlt.P.Qx8.herm_smul_right', Formalism.FourierDecayAlt.P.Qx8.herm_self']
    have hs : star (c : ℂ) = c := Complex.conj_ofReal c
    rw [hs, ← hTdef]
    have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have e1 : (c : ℂ) * (c : ℂ) = (T' : ℂ) / (T : ℂ) := by
      rw [← Complex.ofReal_mul, hcc]; push_cast; rfl
    rw [show (c : ℂ) * ((c : ℂ) * -(T : ℂ)) = -((c : ℂ) * (c : ℂ)) * (T : ℂ) by ring, e1]
    push_cast
    field_simp
  obtain ⟨m, hm, hmz, -⟩ := Formalism.FourierDecayAlt.P.Qx8.move Bs.z'_mem hcw (-T') (by linarith) hz' hcz
  refine ⟨Fb ⟨0, by have := Bs.k_pos; omega⟩, m, hBw _, hBz _ _ (List.mem_singleton_self _), ?_, hm, hmz⟩
  rw [hBo, if_pos rfl]

end frame

end Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature

namespace Formalism.FourierDecayAlt.P

theorem exists_normalized_tower : Formalism.FourierDecayAlt.P.PTie.TowerAt := HaarMassHermitianCurvature.towerAt

end Formalism.FourierDecayAlt.P
