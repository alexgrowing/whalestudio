import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSecRdUNeZero
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverNZ

theorem exists_sec_ne_zero_each_comp : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ n : ℕ, Even n → ∃ a : (D.host.E →+* ℂ) × ℕ → ℕ, Dom a n ∧ ∀ k : (T.U j σ).Comp, ∃ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∃ x ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) f k x ≠ 0 := by
  intro D T hT j hj σ hσ n hn
  refine ⟨0, ⟨fun _ => antitone_const, hn⟩, fun k => ?_⟩
  have hU : IsUnf (T.U j σ) := hT.unf j hj σ hσ
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  obtain ⟨x, hx⟩ : ((T.U j σ).X k).dom.Nonempty := GlobalTheory.OrbitScalar.exists_mem_dom _
  obtain ⟨x₀, hx₀, -⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU).1 k ⟨x, hx⟩
  obtain ⟨f, hf, h0⟩ := GlobalTheory.DictLevel.exists_sec_rdU_ne_zero (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU hr k n hn x₀ hx₀
  exact ⟨f, hf, x₀.1, x₀.2, h0⟩

end GlobalTheory.CoverNZ
