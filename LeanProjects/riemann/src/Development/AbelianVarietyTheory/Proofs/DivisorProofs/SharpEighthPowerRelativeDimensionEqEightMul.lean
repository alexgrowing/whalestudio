import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimUniqueOfIsoGrp
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmoothOfRelativeDimensionPowObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem sharpRef_relDim : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → D.P.g = 8 * Q.g := by
  intro W V V₁ _ _ _ _ Q ρ D e h
  obtain ⟨pr, w, hmon, huniv, -⟩ := h
  have lim : IsLimit (Fan.mk D.P.A pr) :=
    mkFanLimit _ (fun s => (huniv s.pt s.proj).choose)
      (fun s i => (huniv s.pt s.proj).choose_spec.1 i)
      (fun s m hm => (huniv s.pt s.proj).unique hm (huniv s.pt s.proj).choose_spec.1)
  let eI : D.P.A ≅ powObj ((Over.pullback (spMap ρ)).obj Q.B) 8 :=
    lim.conePointUniqueUpToIso (powIsLimit _ 8)
  have hB : SmoothOfRelativeDimension Q.g ((Over.pullback (spMap ρ)).obj Q.B).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback Q.B.hom (spMap ρ)) Q.smoothDim
  have h8 := GlobalTheory.smoothOfRelativeDimension_powObj _ Q.g hB 8
  have hne : Nonempty (Sp V₁) := inferInstance
  exact GlobalTheory.relDim_unique_of_iso_grp (Sp V₁) hne D.P.A _ eI.hom inferInstance _ _ D.P.smoothDim h8

end GlobalTheory.Poinc.Sep
