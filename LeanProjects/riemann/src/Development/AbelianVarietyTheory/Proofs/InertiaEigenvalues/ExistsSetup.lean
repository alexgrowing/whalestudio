import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLadicCoefficientFieldEmbeddingsComplexStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastMemUnder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatePlacesDistinct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodFrameRealisationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBaseDataIsGoodTwistStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepGoodTwistStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinTwistingCharacterDeltaGoodStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlacesTwistPlacesGoodPositionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterLadicGaloisCharacterEqHeckeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlacesMemPlacesOverGeneratorsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeriesTie.Complex

variable {D : D7}

def castG (Pg : Finset (Pl D.host.E)) {r r' : ℕ} (h : r' = r) : G0 Pg r ≃* G0 Pg r' :=
  MulEquiv.piCongrRight fun P => Units.mapEquiv
    (Matrix.reindexAlgEquiv (kP P.1) (kP P.1) (finCongr h.symm)).toMulEquiv

def levOf {G H : Type} [Group G] [Group H] (eG : G ≃* H) (U : Subgroup G) (χ : U →* ℂˣ) : Subgroup H × (U.map eG.toMonoidHom →* ℂˣ) :=
  (U.map eG.toMonoidHom, χ.comp (eG.subgroupMap U).symm.toMonoidHom)

theorem levOf_mem {G H : Type} [Group G] [Group H] (eG : G ≃* H) (U : Subgroup G) (χ : U →* ℂˣ) (g : G) :
    eG g ∈ (levOf eG U χ).1 ↔ g ∈ U := by
  simp [levOf, Subgroup.mem_map]

theorem levOf_chi {G H : Type} [Group G] [Group H] (eG : G ≃* H) (U : Subgroup G) (χ : U →* ℂˣ) (u : U)
    (hu : eG u ∈ (levOf eG U χ).1) : (levOf eG U χ).2 ⟨eG u, hu⟩ = χ u := by
  change χ ((eG.subgroupMap U).symm ⟨eG u, hu⟩) = χ u
  congr 1
  apply (eG.subgroupMap U).injective
  rw [MulEquiv.apply_symm_apply]
  rfl

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def eGc (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (j : Fin D.R.m) : G0g D.nd ≃* G0 Rl.Pg (Wc D j).rank :=
  cG.symm.trans (castG Rl.Pg (FWT.rank_Wc j))

end GlobalTheory.SeriesTie.Complex

end
