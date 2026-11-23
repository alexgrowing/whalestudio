import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardClProdFiniteAlgebraWithInvolution
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_cl_prod_finiteAlgebraWithInvolution : ∀ (K : UQ) (B₁ B₂ : InvAlg K), Nat.card (B₁.prod B₂).Cl = Nat.card B₁.Cl * Nat.card B₂.Cl := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.ClProd.card_cl_prod | exact GlobalTheory.UnitLemma.InvAlg.ClProd.card_cl_prod | (intros; apply GlobalTheory.UnitLemma.InvAlg.ClProd.card_cl_prod <;> assumption)
