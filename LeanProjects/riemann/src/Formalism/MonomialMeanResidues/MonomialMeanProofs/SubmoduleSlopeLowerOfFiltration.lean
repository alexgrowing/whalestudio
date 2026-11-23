import Mathlib
import Formalism.MonomialMeanResidues.FilteredDegree
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.MeanHeightDescent.AverageDegreeBounds.GoodBadCut
import Formalism.MeanHeightDescent.AverageDegreeBounds.SpanMuMin

open Module NumberField Finset

noncomputable section

namespace Formalism.HermiteSiegelSlopes

open Formalism.HN

namespace GradedDegree

theorem denseRange_embedding {K : Type} [Field K] [NumberField K] (v : InfinitePlace K)
    (hv : v.IsComplex) : DenseRange (v.embedding : K → ℂ) := by
  have hcl := Complex.subfield_eq_of_closed
    (Subfield.isClosed_topologicalClosure (v.embedding.fieldRange))
  rcases hcl with h | h
  · exfalso
    have hreal : ComplexEmbedding.IsReal v.embedding := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      have hx : v.embedding x ∈ (v.embedding.fieldRange).topologicalClosure :=
        Subfield.le_topologicalClosure _ ⟨x, rfl⟩
      rw [h] at hx
      obtain ⟨r, hr⟩ := hx
      simp only [ComplexEmbedding.conjugate_coe_eq]
      rw [← hr]
      exact Complex.conj_ofReal r
    exact (InfinitePlace.not_isReal_iff_isComplex.2 hv)
      ((InfinitePlace.isReal_iff).2 hreal)
  · intro z
    have hz : z ∈ (v.embedding.fieldRange).topologicalClosure := by rw [h]; trivial
    have hz' : z ∈ _root_.closure ((v.embedding.fieldRange : Subfield ℂ) : Set ℂ) := hz
    rwa [RingHom.coe_fieldRange] at hz'

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  {W κ : Type} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]

section Alg

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

end Alg

end GradedDegree

namespace FiltrationSlope

open Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas

section

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
  [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

end

end FiltrationSlope

namespace PositionDegree

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def unc (K σ κ : Type) [Field K] [NumberField K] : (σ → κ → K) →ₗ[𝓞 K] (σ × κ → K) where
  toFun g p := g p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def emb (K σ κ : Type) [Field K] [DecidableEq σ] (α : σ) : (κ → K) →ₗ[K] (σ × κ → K) where
  toFun x p := if p.1 = α then x p.2 else 0
  map_add' x y := by
    funext p
    by_cases h : p.1 = α <;> simp [h]
  map_smul' a x := by
    funext p
    by_cases h : p.1 = α <;> simp [h]

end PositionDegree

end Formalism.HermiteSiegelSlopes
