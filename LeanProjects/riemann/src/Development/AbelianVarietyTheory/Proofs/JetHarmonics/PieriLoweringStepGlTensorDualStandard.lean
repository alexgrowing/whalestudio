import Mathlib
import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IrreducibleCapelliModules
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.Jets.Imports
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenspaceIrreducibleDualStandardStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ReducedWignerCoefficientLoweringStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerExtremeNeZero

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

noncomputable section

namespace GlobalTheory.WigSh

def splitCasimirDual {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) :
    Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)) where
  toFun y := WithLp.toLp 2 (fun a => ∑ c, E a c (y c))
  map_add' x y := by
    ext a
    simp [Finset.sum_add_distrib]
  map_smul' t y := by
    ext a
    simp [Finset.smul_sum]

theorem splitCasimirDual_apply {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (y : PiLp 2 (fun _ : Fin (n + 1) => V))
    (a : Fin (n + 1)) : splitCasimirDual E y a = ∑ c, E a c (y c) := rfl

theorem pieri_step_lowering : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ j, L j ≠ L l - 1) → ∃ S : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), Stab Et S ∧ S ≠ ⊥ ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' → S' = ⊥ ∨ S' = S) ∧ S ≤ CapSp Et (shf β (Function.update L l (L l - 1))) ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → S.starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wM L M l : ℂ) • v := by
  intro V _ _ _ n E Et β L l hH hadj hEt hL
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.splitCasimir_eigenspace_irreducible_dualStandard V n E Et (splitCasimirDual E) β L l hH hadj hEt
    (splitCasimirDual_apply E)
  have h4 := GlobalTheory.T.reducedWignerCoefficient_lowering V n E Et (splitCasimirDual E) β L l hH hadj hEt
    (splitCasimirDual_apply E)
  refine ⟨_, h1, ?_, h2, h3, h4⟩
  intro hbot
  have hbox : Box L (fun j : Fin n => L j.succ + 1) := by
    intro j
    have := hH.anti (show j.castSucc < j.succ from Fin.castSucc_lt_succ)
    constructor <;> simp only <;> omega
  have hne := (Formalism.FourierDecayAlt.P.branching_decomposition V n E β L hH).1 _ hbox
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h5 := h4 _ v hv
  have hw := (wigner_extreme_ne_zero n L l hH.anti).2 hL
  have hz : (Module.End.eigenspace (splitCasimirDual E) (β + L l + (n : ℂ))).starProjection
      (PiLp.single 2 (Fin.last n) v) = 0 := by
    have hm := (Module.End.eigenspace (splitCasimirDual E) (β + L l + (n : ℂ))).starProjection_apply_mem
      (PiLp.single 2 (Fin.last n) v)
    exact (Submodule.eq_bot_iff _).1 hbot _ hm
  rw [hz] at h5
  have h6 : ((wM L (fun j : Fin n => L j.succ + 1) l : ℝ) : ℂ) • v = 0 := by
    rw [← h5]; rfl
  rcases smul_eq_zero.1 h6 with h | h
  · exact hw (by exact_mod_cast h)
  · exact hv0 h

end GlobalTheory.WigSh
