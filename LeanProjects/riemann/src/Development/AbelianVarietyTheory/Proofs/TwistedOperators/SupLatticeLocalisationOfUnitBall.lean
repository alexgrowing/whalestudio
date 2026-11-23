import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmulMemSupLattice

open NumberField IsDedekindDomain Formalism.IndefR.Arith

namespace GlobalTheory

theorem supLattice_localisation_of_unitBall (LL Ks WL G : Type) [Field LL] [NumberField LL] [Field Ks]
    [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)]
    [∀ σ, InnerProductSpace ℂ (W σ)] [Group G] (Φ : FormsL LL Ks WL W G)
    (hspan : Submodule.span Ks (Φ.MK : Set WL) = Φ.WK) (la : HeightOneSpectrum (𝓞 Ks)) (f : Φ.WK)
    (hf : ∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1) :
    ∃ s : 𝓞 Ks, s ∉ la.asIdeal ∧ s • (f : WL) ∈ Φ.MK := by
  first
  | exact @_root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice
  | exact _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice
  | (apply _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice ..)

end GlobalTheory
