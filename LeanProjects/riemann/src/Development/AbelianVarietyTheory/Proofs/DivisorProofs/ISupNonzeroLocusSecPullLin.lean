import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChange
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SpanVA

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj O1 coord)

variable {R : Type} [CommRing R] {m N : ℕ}

def lin (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) : Fin (m + 1) → (O1 R N).Sec :=
  fun i => ∑ j, GlobalTheory.AbLaw.cst (PSpace.str R N) ⊤ (a i j) • coord R N j

def dom (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) : (PSpace R N).Opens := ⨆ i, nonzeroLocus (lin a i)

theorem iSup_nonzeroLocus_secPull_lin (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) :
    ⨆ i, nonzeroLocus (GlobalTheory.Cartier.secPull (lin a i) (dom a).ι) = ⊤ := by
  simp only [GlobalTheory.Cartier.nonzeroLocus_secPull]
  rw [← Scheme.Hom.preimage_iSup]
  exact (dom a).ι_preimage_self

def proj (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) : (dom a).toScheme ⟶ PSpace R m :=
  toProj ((dom a).ι ≫ PSpace.str R N) (fun i => GlobalTheory.Cartier.secPull (lin a i) (dom a).ι)
    (iSup_nonzeroLocus_secPull_lin a)

def liftDom {X : Scheme.{0}} (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) (φ : X ⟶ PSpace R N)
    (h : φ ⁻¹ᵁ dom a = ⊤) : X ⟶ (dom a).toScheme :=
  IsOpenImmersion.lift (dom a).ι φ (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hx : x ∈ φ ⁻¹ᵁ dom a := h.ge trivial
    exact hx)

theorem liftDom_fac {X : Scheme.{0}} (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) (φ : X ⟶ PSpace R N)
    (h : φ ⁻¹ᵁ dom a = ⊤) : liftDom a φ h ≫ (dom a).ι = φ :=
  IsOpenImmersion.lift_fac _ _ _

end GlobalTheory.SpanVA
