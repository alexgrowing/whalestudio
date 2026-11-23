import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartStarInvT
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD

noncomputable section

namespace GlobalTheory.CompanionTheory.DualMapAct

theorem act_dual : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}, ∀ (o : Op E a) (φ : Sm E a)
    (h1 : (fun g => star (φ.1 (invA E a g))) ∈ Sm E a)
    (h2 : (fun g => star ((act (invTOp o) φ).1 (invA E a g))) ∈ Sm E a),
    act o (⟨fun g => star (φ.1 (invA E a g)), h1⟩ : Sm E a) =
      ⟨fun g => star ((act (invTOp o) φ).1 (invA E a g)), h2⟩ :=
  fun o φ _ _ => GlobalTheory.CompanionTheory.DualAct.act_star_invT o φ _ _ (fun _ => rfl) (fun _ => rfl)

end GlobalTheory.CompanionTheory.DualMapAct

end
