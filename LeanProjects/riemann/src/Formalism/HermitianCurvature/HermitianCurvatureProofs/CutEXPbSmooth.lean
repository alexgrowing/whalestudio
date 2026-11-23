import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialBesselSmoothCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProperDomP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkCpt

noncomputable section

open Matrix MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX

open Formalism.FourierDecayAlt.P.PBI.Sm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section lemmas

variable {k : ℕ}

theorem contDiff_castM {a b : ℕ} (e : a = b) : ContDiff ℝ ∞ (fun g : B.Mat k a => D.castM e g) := by
  subst e
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact contDiff_id

theorem ms_mMap {r : ℕ} (q₀ : (Fin r → Fin r → ℂ) × Mt k (r - r)) (h₀ : (Matrix.of q₀.1).det ≠ 0) :
    MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => U.mMap k r (r - r) (Matrix.of q.1) (Matrix.of q.2)) q₀ := by
  have hZ : MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => Matrix.of q.1) q₀ :=
    Formalism.FourierDecayAlt.P.PBI.ms_ofC contDiffAt_fst
  have hμ : MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => Matrix.of q.2) q₀ :=
    Formalism.FourierDecayAlt.P.PBI.ms_ofC contDiffAt_snd
  have hZi : MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => (Matrix.of q.1)ᴴ⁻¹) q₀ :=
    ms_inv (ms_conjT hZ) (by rw [Matrix.det_conjTranspose]; exact star_ne_zero.mpr h₀)
  unfold U.mMap
  exact Formalism.FourierDecayAlt.P.PBI.measurable_block_three (ms_const _) (ms_const _) (ms_mul hZi (ms_const _)) (ms_const _) hμ (ms_const _)
    (ms_mul (ms_const _) hZ) (ms_const _) (ms_const _)

theorem contDiffOn_xT (r : ℕ) :
    ContDiffOn ℝ ∞ (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => xT k r (Matrix.of q.1) (Matrix.of q.2))
      {q | (Matrix.of q.1).det ≠ 0} := by
  intro q₀ h₀
  have hm := ms_mMap q₀ h₀
  have hc : ContDiffAt ℝ ∞ (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) =>
      U.mMap k r (r - r) (Matrix.of q.1) (Matrix.of q.2)) q₀ :=
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun l => hm i l
  exact ((contDiff_castM (k := k) (by omega : r + (r - r) = r)).contDiffAt.comp q₀ hc).contDiffWithinAt

theorem dmin_xT (r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Z : Matrix (Fin r) (Fin r) ℂ) (μ : B.Mat k (r - r)) :
    Dmin k r z z' (xT k r Z μ) ⟨r, by omega⟩ = Z.det := by
  unfold xT
  rw [Formalism.FourierDecayAlt.P.PBI.dmin_castM (by omega) z z' _ r (by omega) (by omega),
    Formalism.FourierDecayAlt.P.hat_z_minimum_degree k r (r - r)]
  have e := Formalism.FourierDecayAlt.P.hat_z_on_slice k r (r - r) 0 0 Z μ
  rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e
  unfold U.DjU
  rw [e]

theorem xT_GV (r : ℕ) {Z : Matrix (Fin r) (Fin r) ℂ} {μ : B.Mat k (r - r)} (hZ : Z.det ≠ 0) (hμ : μ ∈ B.GV k (r - r)) :
    xT k r Z μ ∈ B.GV k r :=
  Formalism.FourierDecayAlt.P.PBE.castM_GV _ ((Formalism.FourierDecayAlt.P.slice_membership k r (r - r)).1 Z μ hZ hμ)

theorem gf_castM {a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) :
    Gf k b z z' (D.castM e g) = Gf k a (D.castV e.symm z) (D.castV e.symm z') g := by
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

theorem inWb_castV {a b : ℕ} (e : a = b) {z : Fin (2 * a + k + 1) → ℂ} (h : inWb k a z) : inWb k b (D.castV e z) := by
  subst e
  rwa [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

end lemmas

theorem pullback_smooth_formula : PbSmooth := by
  intro Wp Wq _ _ _ _ _ _ P p G hG q₀ hq₀ hG₀
  obtain ⟨⟨hsm, ⟨R, hR⟩, -⟩, -⟩ := hG
  have hCs : IsCompact {g : B.Mat P.k P.r | B.gN g ≤ R} := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R
  have hHC : ∀ g ∈ B.GV P.k P.r, g ∉ {g : B.Mat P.k P.r | B.gN g ≤ R} → G g = 0 := by
    intro g hg hn
    by_contra hne
    exact hn (hR g hg hne)
  have hΩ := PBQ.isOpen_domP P.k P.r P.r p.T.base.z p.T.base.z'
  have hP := proper_left_variables_domain Wp Wq P p P.r le_rfl _ hCs
  have hG₀' : Matrix.of q₀.2 ∈ B.GV P.k (P.r - P.r) := hG₀.1
  have hgf : 0 < Gf P.k P.r p.T.base.z p.T.base.z' (xT P.k P.r (Matrix.of q₀.1) (Matrix.of q₀.2)) := by
    unfold xT
    rw [gf_castM]
    have e := Formalism.FourierDecayAlt.P.level_function_slice P.k P.r (P.r - P.r)
      (D.castV (by omega : P.r = P.r + (P.r - P.r)) p.T.base.z) (D.castV (by omega : P.r = P.r + (P.r - P.r)) p.T.base.z')
      (inWb_castV _ p.T.base.z_mem) (inWb_castV _ p.T.base.z'_mem) 0 0 (Matrix.of q₀.1) (Matrix.of q₀.2)
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e
    rw [e, MkCptPf.lowV_top p.T _, MkCptPf.lowV_top' p.T _, MkCptPf.gf_eq_ggl (by omega)]
    exact mul_pos (Complex.normSq_pos.2 hq₀.1) hq₀.2
  have hyΩ : xT P.k P.r (Matrix.of q₀.1) (Matrix.of q₀.2) ∈ PBQ.domP P.k P.r P.r p.T.base.z p.T.base.z' := by
    refine ⟨fun l hl1 hl2 => ?_, hgf⟩
    have hl : l = ⟨P.r, by omega⟩ := Fin.ext (by show (l : ℕ) = P.r; omega)
    rw [hl, dmin_xT]; exact hq₀.1
  have hyG := xT_GV P.r hq₀.1 hG₀'
  have hz : p.T.base.z = D.castV (by omega : P.r + (P.r - P.r) = P.r) (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) :=
    (p.T.z_lev P.r le_rfl).symm
  obtain ⟨V, f', hV, hyV, hf', hag⟩ := partial_bessel_smooth_compact_support P.k P.r (P.r - P.r) P.r Wp Wq (p.T.bs P.r) p.T.base
    (by omega) hz G _ hsm hCs hHC _ hΩ hP _ hyΩ hyG
  have hxc := contDiffOn_xT (k := P.k) P.r
  have hOD : IsOpen {q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) | (Matrix.of q.1).det ≠ 0} :=
    isOpen_ne_fun (Continuous.matrix_det (continuous_fst)) continuous_const
  refine ⟨{q | (Matrix.of q.1).det ≠ 0} ∩
      (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => xT P.k P.r (Matrix.of q.1) (Matrix.of q.2)) ⁻¹' V,
    fun q => f' (xT P.k P.r (Matrix.of q.1) (Matrix.of q.2)), hxc.continuousOn.isOpen_inter_preimage hOD hV,
    ⟨hq₀.1, hyV⟩, hf'.comp (hxc.mono Set.inter_subset_left) (fun q hq => hq.2), fun q hq hqG => ?_⟩
  exact hag _ hq.2 (xT_GV P.r hq.1 hqG.1)

end Formalism.FourierDecayAlt.P.CutEX

namespace Formalism.FourierDecayAlt.P

theorem pullback_smooth : CutEX.PbSmooth := CutEX.pullback_smooth_formula

end Formalism.FourierDecayAlt.P
