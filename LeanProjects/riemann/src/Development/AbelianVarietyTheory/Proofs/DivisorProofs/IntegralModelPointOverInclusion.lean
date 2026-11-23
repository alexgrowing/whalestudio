import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.GenChartAlg

theorem exists_algebra_of_genPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β →
    ∀ (L : Type) [CommRing L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∃ (_ : Algebra c.F L), (yL ≫ r ≫ pullback.fst _ _) ≫ Xo.s = sOf c L ∧
      (∀ z : FrPt Xo c L, z.x = yL ≫ r ≫ pullback.fst _ _ → ptF z = yL ≫ r) ∧
      ∀ (σ : E →+* ℂ) (a : 𝓞 E), algebraMap c.F L (embK c σ a) = io (β (embV c' W σ a)) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r hle hr A _ ξ β hβ L _ io yL hyL
  obtain ⟨f', hf'⟩ : ∃ f' : c'.F →+* L, yL ≫ pullback.snd _ _ = spMap f' :=
    ⟨(Spec.preimage (yL ≫ pullback.snd _ _)).hom, by simp [spMap]⟩
  letI alg : Algebra c.F L := (f'.comp (IntermediateField.inclusion hle).toRingHom).toAlgebra
  have hsnd : yL ≫ r ≫ pullback.snd _ _ = spMap (algebraMap c.F L) := by
    rw [hr, ← Category.assoc, hf']
    simp only [spMap, ← Spec.map_comp]
    rfl
  have e1 : yL ≫ Y.j ≫ Y.s = spMap (io.comp β) := by
    rw [← Category.assoc, hyL, Category.assoc, hβ]
    simp only [spMap, ← Spec.map_comp]
    rfl
  have e2 : yL ≫ Y.j ≫ Y.s = spMap (f'.comp (c'.V W).subtype) := by
    simp only [Model.j, Category.assoc]
    rw [pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hf']
    simp only [spMap, ← Spec.map_comp]
    rfl
  have key : f'.comp (c'.V W).subtype = io.comp β := by
    have h := e2.symm.trans e1
    simp only [spMap] at h
    have h2 := Spec.map_injective h
    exact congrArg CommRingCat.Hom.hom h2
  refine ⟨alg, ?_, ?_, ?_⟩
  · simp only [Category.assoc, pullback.condition]
    rw [← Category.assoc r, ← Category.assoc yL, hsnd]
    simp only [sOf, spMap, ← Spec.map_comp]
    rfl
  · intro z hz
    apply pullback.hom_ext
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_fst, hz, Category.assoc]
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_snd, Category.assoc, hsnd]
  · intro σ a
    exact RingHom.congr_fun key (embV c' W σ a)

end GlobalTheory.GenChartAlg
