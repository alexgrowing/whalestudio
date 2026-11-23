import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QxFstInj

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def qx_colFam {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
    {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
    {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ} (hd : IsStripData B be Str ps)
    {M M' : GLMod n} (e : M'.ι ≃ M.ι × κ) (hT : IsTensor M M' B e) (CF : ColFam M) : ColFam M' where
  J := qx_J Str CF
  mu := fun x => (x.2 : Fin n → ℤ)
  dom := fun x => hd.2.2.1 _ (CF.dom x.1) _ x.2.2
  ph := qx_ph ps e CF
  equiv := fun x => by
    ext i I
    exact qx_equiv hd e hT CF x i I
  indepP := fun p hp nu => by
    have := Fact.mk hp
    exact qx_indep hd e CF (ZMod p) nu
  indepQ := fun nu => qx_indep hd e CF ℚ nu
  rank := qx_rank hd e CF

theorem strip_data_tensor_holds : StripDataTensorColumnFamilies := by
  intro n _ κ _ _ B be Str ps hd M M' e hT ⟨CF⟩
  exact ⟨qx_colFam hd e hT CF⟩

end Formalism.InvariantFactorPaths.ColumnFamilies
