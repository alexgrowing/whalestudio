import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem gram_form_eq {m n : ℕ} (G : Matrix (Fin m) (Fin m) ℂ) (y : Matrix (Fin m) (Fin n) ℂ)
    (w : Fin n → ℂ) :
    star w ⬝ᵥ (y.conjTranspose * G * y).mulVec w = star (y.mulVec w) ⬝ᵥ G.mulVec (y.mulVec w) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

theorem exists_posOn_of_gram (m n : ℕ) (G : Matrix (Fin m) (Fin m) ℂ)
    (y : Matrix (Fin m) (Fin n) ℂ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ))
    (h : PosOn ε (y.conjTranspose * G * y) S) :
    ∃ T : Submodule ℂ (Fin m → ℂ), PosOn ε G T ∧ Module.finrank ℂ T = Module.finrank ℂ S := by
  have key : ∀ w ∈ S, w ≠ 0 → 0 < ε * (star (y.mulVec w) ⬝ᵥ G.mulVec (y.mulVec w)).re := by
    intro w hw hw0
    have hpos := h w hw hw0
    rwa [gram_form_eq] at hpos
  have hinj : Function.Injective ((Matrix.mulVecLin y).domRestrict S) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have hw0 : (w : Fin n → ℂ) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    have h1 := key w w.2 hw0
    have h2 : y.mulVec (w : Fin n → ℂ) = 0 := by simpa using hw
    simp [h2] at h1
  refine ⟨S.map (Matrix.mulVecLin y), ?_, ?_⟩
  · intro v hv hv0
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact hv0 (map_zero _)
    rw [Matrix.mulVecLin_apply]
    exact key w hw hw0
  · rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
