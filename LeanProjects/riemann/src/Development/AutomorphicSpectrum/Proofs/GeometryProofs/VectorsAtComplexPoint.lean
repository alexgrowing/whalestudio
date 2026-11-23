import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEigenTangentsPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.LocFn.Transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem isEigFrame_of_sameVec (Y : Model Xo c β) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) (κ : 𝓞 E →+* F) {n : ℕ}
    (v : Fin n → (epsAt (under y) ⟶ Xo.univ.t.G)) (v₀ : Fin n → (epsAt (y ≫ Y.j) ⟶ Y.t.G))
    (hs : ∀ i, SameVec Y y (v i) (v₀ i)) (hf : IsEigFrame Y.t.act (y ≫ Y.j) κ v₀) :
    IsEigFrame Xo.univ.t.act (under y) κ v := by
  have hq : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ := Y.m.cart
  have hp : IsGrpPullback Y.oF.t.G Xo.univ.t.G (pullback.fst _ _) Y.m0.toSABMap.φ := Y.m0.cart
  choose u hu₀ hu₁ hu₂ using hs
  let a : Fin n → (epsAt y ⟶ Y.oF.t.G) := fun i => Over.homMk (u i) (hu₀ i)
  have e₀ : (fun i => tanMap hq y (a i)) = v₀ := funext fun i => Over.OverMorphism.ext (hu₂ i)
  have e₁ : (fun i => tanMap hp y (a i)) = v := funext fun i => Over.OverMorphism.ext (hu₁ i)
  have h₁ : IsEigFrame Y.oF.t.act y κ a :=
    (isEigFrame_iff hq Y.oF.t.act Y.t.act Y.m.act y κ a).1 (by rw [e₀]; exact hf)
  have h₂ := (isEigFrame_iff hp Y.oF.t.act Xo.univ.t.act Y.m0.act y κ a).2 h₁
  rw [e₁] at h₂
  exact h₂

theorem isFramed_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (v₀ : Fin D.p → (epsAt (y ≫ Y.j) ⟶ Y.t.G)) (w₀ : Fin D.q → (epsAt (y ≫ Y.j) ⟶ Y.t.G)), y ≫ pullback.snd _ _ = spMap σ → (∀ i, SameVec Y y (v i) (v₀ i)) → (∀ j, SameVec Y y (w j) (w₀ j)) → IsEigFrame Y.t.act (y ≫ Y.j) (σ.comp (tauIn c τ)) v₀ → IsEigFrame Y.t.act (y ≫ Y.j) (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w₀ → IsFramed Set.univ τ σ y v w := by
  intro E _ _ _ H D l Xo c O _ β Y τ σ y v w v₀ w₀ hy hv hw fv fw
  exact ⟨hy, Set.subset_univ _, isEigFrame_of_sameVec Y y _ v v₀ hv fv, isEigFrame_of_sameVec Y y _ w w₀ hw fw⟩

end GlobalTheory.CompanionTheory.Ar.Flat
