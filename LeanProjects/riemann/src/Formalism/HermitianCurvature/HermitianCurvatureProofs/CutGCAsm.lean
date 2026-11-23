import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem toSm_of_mem (P : M.Par) {u : MA.Qp P.r P.TT → ℂ} (h : u ∈ MA.smSub P.r P.TT) (q : MA.Qp P.r P.TT) :
    (MA.toSm P u : MA.Qp P.r P.TT → ℂ) q = u q := by
  unfold MA.toSm
  rw [dif_pos h]

theorem assumption_on_sections_holds : AsmSec := by
  intro hFL hGQ hML hRS hRaw hQL Wp Wq _ _ _ _ _ _ P Bs hPl hk hsec
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hPl
  obtain ⟨e, he, hQQ⟩ := hGQ Wp Wq P Bs hPl hk hsec X
  refine ⟨e, he, fun Dc Φ hΦ Y a b ρ => ?_⟩
  apply Subtype.ext
  funext q
  have hLsm := hRaw Wp Wq P Bs hPl hk e he Dc _ (hQL Wp Wq P Bs hPl hk Dc Φ hΦ Y a b) ρ
  rw [toSm_of_mem P hLsm q]
  obtain ⟨Φt, V, hV, hagree⟩ := hFL Wp Wq P Bs hPl hk X Dc Φ hΦ q
  have h1 : rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ q =
      rawR P Bs.μsec e ((X.t (Y : ℂ) a b Φt : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
        Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q := by
    unfold rawR
    rw [((hagree q.1.2 (mem_of_mem_nhds hV)).2 (Y : ℂ) a b).symm]
  rw [h1, ← toSm_of_mem P (hRS Wp Wq P Bs hPl hk e he (X.t (Y : ℂ) a b Φt) ρ) q]
  show (trR P Bs e (X.t (Y : ℂ) a b Φt) ρ : MA.Qp P.r P.TT → ℂ) q = _
  rw [hQQ Φt (Y : ℂ) a b]
  refine hML P (trR P Bs e Φt) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) q.1.1 (interior V) isOpen_interior
    (fun ρ' q' hq'c hq'V => ?_) (Y : ℂ) a b ρ q rfl (mem_interior_iff_mem_nhds.2 hV)
  show (MA.toSm P (rawR P Bs.μsec e (Φt : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ') : MA.Qp P.r P.TT → ℂ) q' =
    (MA.toSm P (rawR P Bs.μsec e Φ ρ') : MA.Qp P.r P.TT → ℂ) q'
  rw [toSm_of_mem P (hRS Wp Wq P Bs hPl hk e he Φt ρ') q',
    toSm_of_mem P (hRaw Wp Wq P Bs hPl hk e he Dc Φ hΦ ρ') q']
  unfold rawR
  rw [hq'c, (hagree q'.1.2 (interior_subset hq'V)).1]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
