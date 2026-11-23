import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFunctionTotalTensorInvariantLastArrows
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productFunction_totalTensor_invariant_lastArrows : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ k : FinPt G (.grid D.R.m D.R.m), finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
    ∀ (w : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
      (v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
    (τ.sum fun d a => a *
      (∏ j, Function.update (fun j => S.Z.vec (d.1 j)) (lastIx D)
        (colShift S t (finEmb G.sp.topDec k) (S.Z.vec (d.1 (lastIx D)))) j (w j)) *
      ∏ i, Function.update (fun i => S.Z.vec (d.2 i)) (lastIx D) (rowShift S k (S.Z.vec (d.2 (lastIx D)))) i (v i)) =
    τ.sum fun d a => a * (∏ j, S.Z.vec (d.1 j) (w j)) * ∏ i, S.Z.vec (d.2 i) (v i) := by
  first | exact @GlobalTheory.LastVertexTensor.productFn_invariant | exact GlobalTheory.LastVertexTensor.productFn_invariant | (intros; apply GlobalTheory.LastVertexTensor.productFn_invariant <;> assumption)
