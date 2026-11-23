import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LinkSFinalP
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopRowSF
import Formalism.SharpRestriction.SmoothDesignExistence.FirstSectionHypothesesAtFamilyConstants

noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.ThmSOwn

def CT (𝒞 : FamClass) : FamClass := fun Fm => 𝒞 Fm ∧ TuSize Fm

def selT {𝒞 : FamClass} (sel : SSel 𝒞) : SSel (CT 𝒞) := fun Fm h => sel Fm h.1

theorem gapRowT {𝒞 : FamClass} (hRes : Closed 𝒞 fun Fm _ => ResidEv Fm) :
    Closed (CT 𝒞) fun Fm _ => CT 𝒞 Fm → Formalism.L2.SG.LoopsTies.GapEv Fm := by
  obtain ⟨ε1, hε1, hK⟩ := hRes
  refine ⟨ε1, hε1, fun eps he he1 => ?_⟩
  obtain ⟨K0, hK0⟩ := hK eps he he1
  refine ⟨⟨K0.pre, K0.t, K0.mid, fun l => max (K0.last l) (max 29 (8 * (l.map abs).sum))⟩,
    fun Fm CH hC hL _ => ?_⟩
  have hL0 : Fm.Large K0 CH :=
    ⟨hL.1, trivial, hL.2.2.1, fun c hc => le_trans (le_max_left _ _) (hL.2.2.2 c hc)⟩
  have hRes' : ResidEv Fm := hK0 Fm CH hC.1 hL0
  have hCG : 8 * Fm.CGam ≤ 8 * ((Fm.cOut ++ Fm.cMid CH).map abs).sum := by
    have hmem : |Fm.CGam| ∈ (Fm.cOut ++ Fm.cMid CH).map abs :=
      List.mem_map.mpr ⟨Fm.CGam, List.mem_append_right _ (by simp [FamP.cMid]), rfl⟩
    have h1 := List.single_le_sum (fun x hx => by
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      exact abs_nonneg y) _ hmem
    linarith [le_abs_self Fm.CGam]
  have hlast : ∀ c ∈ Fm.cLast, 29 ≤ c ∧ 8 * Fm.CGam ≤ c := by
    intro c hc
    have h := hL.2.2.2 c hc
    have h1 := le_max_left (29 : ℝ) (8 * ((Fm.cOut ++ Fm.cMid CH).map abs).sum)
    have h2 := le_max_right (29 : ℝ) (8 * ((Fm.cOut ++ Fm.cMid CH).map abs).sum)
    have h3 := le_max_right (K0.last (Fm.cOut ++ Fm.cMid CH))
      (max 29 (8 * ((Fm.cOut ++ Fm.cMid CH).map abs).sum))
    exact ⟨by linarith, by linarith⟩
  have g : ∀ c ∈ Fm.cLast, 29 ≤ c := fun c hc => (hlast c hc).1
  have hCk : 8 * Fm.CGam ≤ Fm.CkLow := (hlast Fm.CkLow (by simp [FamP.cLast])).2
  have hC'29 : 29 ≤ sC' Fm := g Fm.CkLow (by simp [FamP.cLast])
  have hCl16 : 16 ≤ sCl Fm := by
    unfold sCl
    have e1 := g Fm.CfL (by simp [FamP.cLast])
    have e2 := g Fm.Cw (by simp [FamP.cLast])
    have e3 := g Fm.CDel (by simp [FamP.cLast])
    have e4 := g Fm.CCount (by simp [FamP.cLast])
    have e5 := g Fm.Ch0r (by simp [FamP.cLast])
    have e6 := g Fm.Cgap (by simp [FamP.cLast])
    refine le_min (by linarith) (le_min (by linarith) (le_min (by linarith)
      (le_min (by linarith) (le_min (by linarith) (by linarith)))))
  obtain ⟨x0, hx0⟩ := Formalism.MainNotions.Pk.SD.first_section_hypotheses_at_family_constants Fm ⟨hCk, hC.2, hRes'⟩
  unfold Formalism.L2.SG.LoopsTies.GapEv
  exact ⟨x0, fun x hx i => gap_hypothesis_of_hypotheses (hx0 x hx i) hCl16 hC'29⟩

end Formalism.L2.SG.ThmSOwn
