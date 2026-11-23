import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetSubquotientCharExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDetProdConstAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSignatureSum
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.DetProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_subquotient_char_exists : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.GeometricLemmaFiltration →
    ∀ (a a' l n : ℕ) (h : l + n ≤ a + a') (α β : kˣ →* ℂˣ), GlobalTheory.SplitWeil.IsUnram α → GlobalTheory.SplitWeil.IsUnram β →
    ∀ ρ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) k),
      GlobalTheory.SmGL.IsSubquotient ρ.ρ (GlobalTheory.ThK.MidJac.midJac l n (a + a') h (GlobalTheory.ThK.MidJac.detInd a a' α β)) →
      ∃ x x' j j' : ℕ, x + x' = n ∧ j + j' = l ∧ j + x ≤ a ∧ j' + x' ≤ a' ∧
        GlobalTheory.ThK.DetProd.IsDetProdConst x x'
          (α * GlobalTheory.SmGL.absPow k ((((1 : ℝ) - a) / 2 + j + ((x : ℝ) - 1) / 2 : ℝ) : ℂ))
          (β * GlobalTheory.SmGL.absPow k ((((1 : ℝ) - a') / 2 + j' + ((x' : ℝ) - 1) / 2 : ℝ) : ℂ)) ρ.ρ := by
  first | exact @GlobalTheory.ThK.MidJacCell.midJac_detInd | exact GlobalTheory.ThK.MidJacCell.midJac_detInd | (intros; apply GlobalTheory.ThK.MidJacCell.midJac_detInd <;> assumption)
