import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.EdgesRouteSmall
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.WeilRepresentationSplittingsDiffer
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumTensorProduct
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.RationalUnitsHaarCharacterOneStatement
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.SplitQuadraticAlgebraOrder
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FiniteNonunitMatrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.CompanionTheory.Ar.RT
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix
open scoped NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RT.ArchRing

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

def splitAE : AE F E ≃ₐ[F] (Ainf F ⊗[F] E) × (Af F ⊗[F] E) :=
  ((Algebra.TensorProduct.comm F (AF F) E).trans
    (Algebra.TensorProduct.prodRight F F E (Ainf F) (Af F))).trans
    (AlgEquiv.prodCongr (Algebra.TensorProduct.comm F E (Ainf F))
      (Algebra.TensorProduct.comm F E (Af F)))

theorem splitAE_tmul (a : AF F) (e : E) :
    splitAE F E (a ⊗ₜ[F] e) = (a.1 ⊗ₜ[F] e, a.2 ⊗ₜ[F] e) := by
  have h : (Algebra.TensorProduct.comm F (AF F) E) (a ⊗ₜ[F] e) = e ⊗ₜ[F] a := rfl
  simp only [splitAE, AlgEquiv.trans_apply, h, Algebra.TensorProduct.prodRight_tmul]
  rfl

theorem splitAE_smul (u : AF F) (x : AE F E) :
    splitAE F E (u • x) = (u.1 • (splitAE F E x).1, u.2 • (splitAE F E x).2) := by
  induction x using TensorProduct.induction_on with
  | zero => simp; rfl
  | tmul a e =>
    rw [TensorProduct.smul_tmul', splitAE_tmul, splitAE_tmul]
    simp [TensorProduct.smul_tmul']
  | add x y hx hy =>
    rw [smul_add, map_add, hx, hy, map_add]
    simp [smul_add]

theorem isArtinian_inf : IsArtinianRing (Ainf F) :=
  inferInstanceAs (IsArtinianRing ((v : InfinitePlace F) → v.Completion))

theorem isArtinian_E₁ (h : Module.finrank F E = 2) : IsArtinianRing (Ainf F ⊗[F] E) := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  haveI : IsArtinianRing (Ainf F) := isArtinian_inf
  exact IsArtinianRing.of_finite (Ainf F) _

theorem sigma_invol {σ : E →ₐ[F] E} (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_moved {σ : E →ₐ[F] E} (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) : ∃ x, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hr : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := h.2.2.2 τ x
    rw [hc x] at this
    exact this.symm
  have hR : (InfinitePlace.mk τ).IsReal := ⟨τ, hr, rfl⟩
  have := h.2.1.isComplex (InfinitePlace.mk τ)
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr this) hR

def c₁ (σ : E →ₐ[F] E) : Ainf F ⊗[F] E →ₐ[F] Ainf F ⊗[F] E :=
  Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ

def c₂ (σ : E →ₐ[F] E) : Af F ⊗[F] E →ₐ[F] Af F ⊗[F] E :=
  Algebra.TensorProduct.map (AlgHom.id F (Af F)) σ

theorem c₁_invol {σ : E →ₐ[F] E} (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (x : Ainf F ⊗[F] E) :
    c₁ σ (c₁ σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h' : ∀ (a : Ainf F) (e : E), c₁ σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := fun _ _ => rfl
    rw [h', h', sigma_invol h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem at_iff (x : AE F E) : At (evI F) x ↔ (splitAE F E x).2 = 0 := by
  constructor
  · intro hx
    obtain ⟨u, hu1, hu2⟩ : ∃ u : AF F, u.1 = 0 ∧ u.2 = 1 := ⟨(0, 1), rfl, rfl⟩
    have h0 : evI F u = 0 := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0
      rw [hu1]
      exact map_zero _
    have h2 : u • x = 0 := hx _ h0
    have h1 := congrArg (splitAE F E) h2
    rw [splitAE_smul, map_zero, hu2] at h1
    simpa using congrArg Prod.snd h1
  · intro hx u hu
    have h0 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by
      rw [map_zero]; exact hu)
    show u • x = 0
    apply (splitAE F E).injective
    rw [splitAE_smul, map_zero, h0, hx]
    simp

end GlobalTheory.CompanionTheory.Ar.RT.ArchRing
