import Mathlib
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnFoldRev
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem capelli_eigenSum_linearCombination : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (ι : Type) (S : Finset ι) (co : ι → ℂ) (Fs : ι → B.Mat k r → (Wq →L[ℂ] Wp)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ x ∈ S, ∃ (d' : ℕ) (A' : ℝ), d' ≤ d ∧ A ≤ A' ∧ (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d' : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A') m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (Fs x) g = ∑ i, Fi i g)) → (∀ g ∈ B.GV k r, F g = ∑ x ∈ S, co x • Fs x g) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g) := by
  intro k r Wp Wq _ _ _ _ _ _ lam d A ι S co Fs F h hF
  classical
  have h' : ∀ x : S, _ := fun x => h x.1 x.2
  choose d' A' hd hA N Fi ν hν hC hE hS using h'
  let e := (Fintype.equivFin (Σ x : S, Fin (N x))).symm
  refine ⟨_, fun j g => co (e j).1 • Fi (e j).1 (e j).2 g, fun j => ν (e j).1 (e j).2, ?_, ?_, ?_, ?_⟩
  · intro j s
    exact (hν _ _ s).trans (by exact_mod_cast hd _)
  · intro j
    refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul _ (hC _ _).1, fun m => ?_⟩
    obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.sInCC_mono (hA (e j).1) le_rfl ((hC _ (e j).2).2 m)
    exact ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul _ hc⟩
  · intro j Y g hg
    have h1 := Formalism.FourierDecayAlt.P.CutMP.En.cV_smul (k := k) (r := r) (Y : ℂ) (co (e j).1) (Fi (e j).1 (e j).2)
    have h2 := congrFun h1 g
    have h3 : (fun g => co (e j).1 • Fi (e j).1 (e j).2 g) = co (e j).1 • Fi (e j).1 (e j).2 := rfl
    beta_reduce
    rw [h3, h2, Pi.smul_apply, hE _ _ Y g hg, smul_comm]
  · intro g hg
    rw [hF g hg, Equiv.sum_comp e (fun y : (Σ x : S, Fin (N x)) => co y.1 • Fi y.1 y.2 g),
      Fintype.sum_sigma, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hS x g hg, Finset.smul_sum]

end GlobalTheory
