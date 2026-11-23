import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerFiniteIndexChain
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_finite_index_chain : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n n₁ : ℕ) (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (V₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n₁)
    (r s i₀ i₁ : ℕ) (H : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane E n n₁), B.IsGood σ → V.IsHerm σ B r s → H.IsAdapted σ B V V₁ i₀ i₁ →
    ∀ K : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ V.J), GlobalTheory.ThK.IsStab (X := V) B K →
      ∃ (m : ℕ) (X Y : Matrix (Fin n) (Fin (m + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E))
        (c : GAd σ ((1 : E) • V.J.map σ)),
        IsWittFrame σ ((1 : E) • V.J.map σ) X Y ∧ GlobalTheory.EisLine.IsAdapted σ ((1 : E) • V.J.map σ) X Y L a ∧
        col0 X = Matrix.of (fun i (_ : Fin 1) => H.x i) ∧
        ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ V.J, g ∈ K ↔ ∃ k ∈ levelAll σ ((1 : E) • V.J.map σ) L a,
          (g : GL (Fin n) (AF F ⊗[F] E)) = matHom _ σ _ c * matHom _ σ _ k * (matHom _ σ _ c)⁻¹ := by
  first | exact @GlobalTheory.GoodPos.stab_conj_levelAll | exact GlobalTheory.GoodPos.stab_conj_levelAll | (intros; apply GlobalTheory.GoodPos.stab_conj_levelAll <;> assumption)
