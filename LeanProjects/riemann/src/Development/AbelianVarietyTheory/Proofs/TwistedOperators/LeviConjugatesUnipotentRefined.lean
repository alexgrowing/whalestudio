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

namespace GlobalTheory.RealInd.Stages.UnipConj

variable {n : ℕ} {ε : Fin n → Bool}

private lemma unitaryMatrix_mul_inv_eq_one (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  rw [← show uMat (g * g⁻¹) = uMat g * uMat g⁻¹ from rfl, mul_inv_cancel]
  rfl

private lemma unitaryMatrix_inv_eq_conj_transpose (g : Formalism.REAL.UJ ε) :
    uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
  have hf : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : (Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε) * uMat g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (uMat g)ᴴ, hf,
      Formalism.REAL.Jm_mul_self]
  calc uMat g⁻¹
      = ((Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε) * uMat g) * uMat g⁻¹ := by
        rw [h1, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, unitaryMatrix_mul_inv_eq_one, Matrix.mul_one]

theorem conj_mem_flagN {a : ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    (m : Formalism.REAL.UJ ε) (hm : m ∈ flagM ε W) (u : Formalism.REAL.UJ ε) (hu : u ∈ flagN ε W) :
    m * u * m⁻¹ ∈ flagN ε W := by
  have hmk : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i := fun i y hy => (hm i y hy).1
  have hmik : ∀ i, ∀ y ∈ W i, uMat m⁻¹ *ᵥ y ∈ W i := fun i =>
    UnipRad.inv_keeps m (W i) (hmk i)
  have key : ∀ y : Fin n → ℂ, uMat (m * u * m⁻¹) *ᵥ y - y =
      uMat m *ᵥ (uMat u *ᵥ (uMat m⁻¹ *ᵥ y) - uMat m⁻¹ *ᵥ y) := by
    intro y
    have e := unitaryMatrix_mul_inv_eq_one m
    rw [show uMat (m * u * m⁻¹) = uMat m * uMat u * uMat m⁻¹ from rfl]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec, e, Matrix.one_mulVec, Matrix.mul_assoc]
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · rw [key]
    exact hmk _ _ (hu.1 i _ (hmik _ _ hy))
  · rw [key]
    refine hmk _ _ (hu.2 _ fun x hx => ?_)
    have hx' := hmk _ x hx
    have h0 := hy _ hx'
    rw [unitaryMatrix_inv_eq_conj_transpose, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec _ (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε),
      Formalism.REAL.Jm_mul_self, Matrix.one_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    exact h0

theorem flagN_le_refine {a b : ℕ} {W : Flag n a} {W' : Flag n b} (hW' : Monotone W')
    {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)} (hp : ∀ i, W' (p i) = W i)
    (hlast : W' (Fin.last b) = W (Fin.last a))
    (hβ : ∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ)
    (g : Formalism.REAL.UJ ε) (hg : g ∈ flagN ε W) : g ∈ flagN ε W' := by
  refine ⟨fun l y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨h1, h2⟩ := (hβ l (β l)).1 rfl
    have hs : l.succ ≤ p (β l).succ := by
      rw [Fin.le_def]; rw [Fin.lt_def] at h2; simp only [Fin.val_succ, Fin.coe_castSucc] at h2 ⊢; omega
    have hy' : y ∈ W (β l).succ := by rw [← hp]; exact hW' hs hy
    have := hg.1 (β l) y hy'
    rw [← hp] at this
    exact hW' h1 this
  · rw [hlast] at hy ⊢
    exact hg.2 y hy

end GlobalTheory.RealInd.Stages.UnipConj

theorem GlobalTheory.RealInd.Stages.unip_conj_refine : ∀ {n a b : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)}, IsIsoFlag ε j W → IsIsoFlag ε (fun _ => 1) W' → (∀ i, W' (p i) = W i) → W' (Fin.last b) = W (Fin.last a) → (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) → ∀ m ∈ flagM ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W' := by
  intro n a b ε j W W' β p hW hW' hp hlast hβ m hm u hu
  exact GlobalTheory.RealInd.Stages.UnipConj.flagN_le_refine hW'.2.1 hp hlast hβ _
    (GlobalTheory.RealInd.Stages.UnipConj.conj_mem_flagN m hm u hu)
