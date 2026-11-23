import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicHyperplaneAverageSupportResidueGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankWeightComponentEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolicHyperplaneAverage_support_residueGL : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (PP : Pl D.host.E) (hPP : PP ∈ R.Pg) (v : FinPl D) (ρk : IsLocalRing.ResidueField (OI v) ≃+* kP PP) (a : Fin D.R.r → IsLocalRing.ResidueField (OI v)) (F : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) → ℂ), (∑ᶠ g ∈ {g : G | mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0}, F (Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g ⟨PP, hPP⟩))) = ∑ᶠ g ∈ {g : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) | ∀ w, a ⬝ᵥ w = 0 → (g : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (OI v))).mulVec w = w}, F g := by
  first | exact @GlobalTheory.DownLift.GenSplit.mirC_hyperplane_reindex | exact GlobalTheory.DownLift.GenSplit.mirC_hyperplane_reindex | (intros; apply GlobalTheory.DownLift.GenSplit.mirC_hyperplane_reindex <;> assumption)
