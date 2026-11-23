import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

namespace GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isKAct_of_stable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (hs : ∀ x ∈ kFin M τ, x ∈ GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ))
    (hd : ∀ X ∈ lieAt V τ, ∀ x ∈ kFin M τ, dRep (M.rep τ) X x ∈ kFin M τ) :
    ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ), IsKAct M τ a := by
  have hU : IsUnit (M.fr τ) := M.fr_unit τ
  have hG : IsUnit (gramAt D V τ) := GlobalTheory.SmVec.gram_unit hU (M.fr_gram τ)
  have hπ := GlobalTheory.SmVec.isURepOn_trRep hU (M.fr_gram τ) (M.ds τ).2.2.1
  refine ⟨fun X => if hX : X ∈ lieAt V τ then
    { toFun := fun v => ⟨dRep (M.rep τ) X v, hd X hX v v.2⟩
      map_add' := fun v w => Subtype.ext (GlobalTheory.SmVec.dRep_add (hs v v.2) (hs w w.2) hX)
      map_smul' := fun c v => Subtype.ext (GlobalTheory.SmVec.dRep_smul c (hs v v.2) hX) } else 0, ⟨?_, ?_⟩⟩
  · intro X hX v
    rw [dif_pos hX]
    exact GlobalTheory.SmVec.hasDerivAt_dRep (hs v v.2) hX
  · intro X hX v w
    rw [dif_pos hX, Submodule.coe_inner, Submodule.coe_inner]
    have key : ⟪(v : M.H τ), dRep (M.rep τ) X w⟫_ℂ = -⟪dRep (M.rep τ) X v, (w : M.H τ)⟫_ℂ :=
      GlobalTheory.SmVec.inner_dRep hG hπ (hs v v.2) (hs w w.2) hX
    change ⟪dRep (M.rep τ) X v, (w : M.H τ)⟫_ℂ + ⟪(v : M.H τ), dRep (M.rep τ) X w⟫_ℂ = 0
    linear_combination key

theorem kFin_smooth_isKAct : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ) (m : ℤ) (U : M.H τ → R.U.H), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R M τ φ m U → kFin M τ ≤ M.sm τ ∧ ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ), IsKAct M τ a := by
  intro D V S M τ p q T R φ m U hM
  have hk : ∀ y : M.H τ, y ∈ kFin M τ ↔ U y ∈ Set.range R.ι := fun y => hM.kfin y
  have hsm : ∀ y ∈ kFin M τ, y ∈ GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ) := fun y hy =>
    GlobalTheory.SmVec.mem_smSub.2 (hM.smooth y ((hk y).1 hy))
  refine ⟨fun y hy => Submodule.subset_span (hM.smooth y ((hk y).1 hy)), exists_isKAct_of_stable M τ hsm ?_⟩
  intro X hX y hy
  rw [← hM.lie] at hX
  obtain ⟨Z, hZ, rfl⟩ := hX
  obtain ⟨v, hv⟩ := (hk y).1 hy
  exact (hk _).2 ⟨_, (hM.der Z hZ v y hv.symm).symm⟩

end GlobalTheory.Chain.IoLift

end
