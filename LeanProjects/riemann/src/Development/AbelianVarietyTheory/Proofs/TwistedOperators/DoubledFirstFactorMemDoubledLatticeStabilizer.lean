import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

theorem GlobalTheory.InertDbl.inlD_mem_KAtD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl F),
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, GlobalTheory.InertDbl.inlD σ W k ∈ GlobalTheory.InertDbl.KAtD σ W v := by
  intro F E _ _ _ _ _ σ d W v k hk
  refine ⟨?_, fun z hz => ?_⟩
  · intro u hu
    rw [GlobalTheory.InertDbl.matD_inlD]
    have h1 := hk.1 u hu
    have h1' : u • (mat k - 1) = 0 := h1
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · have := congrFun (congrFun h1' i) j
      simpa [Matrix.fromBlocks, Matrix.one_apply] using this
    all_goals simp [Matrix.fromBlocks, Matrix.one_apply]
  · have hinv : GlobalTheory.InertDbl.matD (GlobalTheory.InertDbl.inlD σ W k)⁻¹ = Matrix.fromBlocks (mat k⁻¹) 0 0 1 := by
      rw [← map_inv]; rfl
    rw [hinv, GlobalTheory.InertDbl.matD_inlD]
    obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨a1, a2⟩ := hk.2 _ hz1
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simp only [Matrix.fromBlocks_mulVec]; convert a1 using 1; funext i; simp [Function.comp_def]
    · simpa [Matrix.fromBlocks_mulVec] using hz2
    · simp only [Matrix.fromBlocks_mulVec]; convert a2 using 1; funext i; simp [Function.comp_def]
    · simpa [Matrix.fromBlocks_mulVec] using hz2
