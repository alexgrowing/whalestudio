import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrOfNotMem
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem keeps_of_refine {n a b : ℕ} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a}
    {p : Fin (a + 1) → Fin (b + 1)} (hW' : Monotone W') (hp : ∀ i, W' (p i) = W i)
    (hl : W' (Fin.last b) = W (Fin.last a))
    (hβ : ∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ)
    {g : Matrix (Fin n) (Fin n) ℂ} {c : Fin a → ℂ}
    (hstep : ∀ i : Fin a, ∀ y ∈ W i.succ, g *ᵥ y - c i • y ∈ W i.castSucc)
    (hlast : ∀ y ∈ W (Fin.last a), g *ᵥ y ∈ W (Fin.last a)) :
    ∀ l, ∀ y ∈ W' l, g *ᵥ y ∈ W' l := by
  intro l
  induction l using Fin.lastCases with
  | last => rw [hl]; exact hlast
  | cast l =>
    intro y hy
    obtain ⟨h1, h2⟩ := (hβ l (β l)).1 rfl
    have hy' : y ∈ W (β l).succ := by
      rw [← hp]; exact hW' h2.le hy
    have hs : g *ᵥ y - c (β l) • y ∈ W' l.castSucc := hW' h1 ((hp _).symm ▸ hstep _ y hy')
    have := (W' _).add_mem hs ((W' _).smul_mem (c (β l)) hy)
    rwa [sub_add_cancel] at this

theorem isSplit_of_refine {n a b : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a} {W' : Flag n b}
    {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)} (hW : IsIsoFlag ε j W)
    (hW' : IsIsoFlag ε (fun _ => 1) W') (hp : ∀ i, W' (p i) = W i) (hl : W' (Fin.last b) = W (Fin.last a))
    (hβ : ∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) {x : Fin a → ℝ} {t : UJ ε}
    (ht : IsSplit ε W x t) : IsSplit ε W' (x ∘ β) t := by
  have k1 := keeps_of_refine hW'.2.1 hp hl hβ ht.2.1 (fun y hy => (ht.1 _ y hy).1)
  have ht' := ht.opp hW
  have hoM : Monotone (opp ε W') := fun _ _ h => Submodule.map_mono (hW'.2.1 h)
  have k2 := keeps_of_refine (W := opp ε W) (W' := opp ε W') hoM
    (fun i => congrArg (fun V => V.map (Jm ε).mulVecLin) (hp i))
    (congrArg (fun V => V.map (Jm ε).mulVecLin) hl) hβ ht'.2.1 (fun y hy => (ht'.1 _ y hy).1)
  refine ⟨fun l y hy => ⟨k1 l y hy, ?_⟩, fun l y hy => ?_, ?_⟩
  · have hJ : (uMat t)ᴴ = Jm ε * uMat t⁻¹ * Jm ε := by
      rw [mul_assoc, inv_mul_Jm, ← mul_assoc, Jm_mul_self, one_mul]
    have hi := GlobalTheory.FlagLeviGroup.inv_keeps (GlobalTheory.FlagLeviGroup.uMat_inv_mul t) _ (k2 l)
    obtain ⟨z, hz, e⟩ := hi _ ⟨y, hy, rfl⟩
    rw [mulVecLin_apply, mulVecLin_apply] at e
    rw [hJ, ← mulVec_mulVec, ← mulVec_mulVec, ← e, mulVec_mulVec, Jm_mul_self, one_mulVec]
    exact hz
  · obtain ⟨h1, h2⟩ := (hβ l (β l)).1 rfl
    have hy' : y ∈ W (β l).succ := by
      rw [← hp]; exact hW'.2.1 (Fin.castSucc_lt_iff_succ_le.1 h2) hy
    have hs := ht.2.1 (β l) y hy'
    rw [← hp] at hs
    exact hW'.2.1 h1 hs
  · rw [hl]; exact ht.2.2

end GlobalTheory.RealInd.Stages
