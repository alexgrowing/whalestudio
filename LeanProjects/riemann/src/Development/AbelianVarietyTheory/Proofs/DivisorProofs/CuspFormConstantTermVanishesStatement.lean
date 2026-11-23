import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormConstantTermVanishes
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_constant_term_vanishes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
    ∀ (K : Subgroup (GAd σ J)) (S : Finset (Fin r)), (∀ k ∈ S, ∀ i ≤ k, i ∈ S) → ∀ i ∈ S,
    ∀ (φc : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J X Y S K φc → ∀ (s : Fin r → ℂ), GlobalTheory.StdPar.IsExponent σ J X Y S φc s →
    ∀ (e : (AF F ⊗[F] E)ˣ) (h : GAd σ J), GlobalTheory.LeviBlockRealization.IsBlockCentre σ J X Y i e h →
    ∀ (L : List ℂ), polyAt (GlobalTheory.LeviBlockRealization.leftTr σ J h)
        (L.map fun c => c * (((GlobalTheory.Doubling.absE F E e : ℝ) ^ (((n : ℝ) - 1) / 2 - (i : ℝ)) : ℝ) : ℂ)) φc = 0 →
      ∃ c ∈ L, ‖c‖ = (GlobalTheory.Doubling.absE F E e : ℝ) ^ (s i).re := by
  first | exact @GlobalTheory.PositionPeel.abs_root_eq | exact GlobalTheory.PositionPeel.abs_root_eq | (intros; apply GlobalTheory.PositionPeel.abs_root_eq <;> assumption)
