import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiExteriorTensorIsSubquotientOfForall
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenMulti

theorem multiProd_isSubquotient_of_forall (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} (N : Fin d → ℕ) (M : ℕ) (hM : ∑ i, N i = M)
    (X Y : Fin d → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)]
    (ρ : ∀ i, Representation ℂ (GL (Fin (N i)) k) (X i))
    (ρ' : ∀ i, Representation ℂ (GL (Fin (N i)) k) (Y i))
    (hs : ∀ i, IsSmooth (ρ' i)) (hq : ∀ i, IsSubquotient (ρ i) (ρ' i)) :
    IsSubquotient (multiProd (stdBlocks N hM) ρ) (multiProd (stdBlocks N hM) ρ') :=
  GlobalTheory.ParIndSubquot.parInd_isSubquotient k _ _ _ (GlobalTheory.SmGL.stdBlocks N hM) _ _ _ _
    (GlobalTheory.SmGL.isSmooth_piTensor hs)
    (GlobalTheory.piTensor_isSubquotient_of_forall _ _ X Y ρ ρ' hq)

end GlobalTheory.CompanionTheory.GenMulti
