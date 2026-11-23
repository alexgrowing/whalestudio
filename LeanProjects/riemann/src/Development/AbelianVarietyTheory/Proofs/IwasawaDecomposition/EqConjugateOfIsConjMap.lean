import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryOfFrameNormConj
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

namespace GlobalTheory.ConjExph

variable {F : Type} [Field F] [NumberField F]

theorem eq_conjugate_of_isConjMap (Y : Var F) {σ σ' : F →+* ℂ} {ι : Pts Y σ' → Pts Y σ} (h : IsConjMap ι)
    (z : Pts Y σ') : σ = ComplexEmbedding.conjugate σ' := by
  have h1 := (ι z).2
  rw [h z, Category.assoc, z.2] at h1
  have e : spMap (ComplexEmbedding.conjugate σ') = spMap σ := by
    rw [← h1, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  exact (congrArg CommRingCat.Hom.hom (Spec.map_injective e)).symm

theorem isConjMap_unique (Y : Var F) {σ σ' : F →+* ℂ} {ι ι' : Pts Y σ' → Pts Y σ} (h : IsConjMap ι)
    (h' : IsConjMap ι') : ι = ι' :=
  funext fun z => Subtype.ext ((h z).trans (h' z).symm)

theorem exists_isConjMap (Y : Var F) {σ σ' : F →+* ℂ} (h : σ = ComplexEmbedding.conjugate σ') :
    ∃ ι : Pts Y σ' → Pts Y σ, IsConjMap ι := by
  subst h
  exact ⟨CxPts.conjEquiv Y.str σ', fun _ => rfl⟩

theorem conjugate_conjugate (σ : F →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
  star_star σ

end GlobalTheory.ConjExph
