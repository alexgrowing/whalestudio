import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoGrpPullbackIdentityTransport
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_iso_grpPullback_identity_transport : ∀ (V V₁ K : Type) [CommRing V] [CommRing V₁] [Field K] (B : Over (Sp V)) [GrpObj B] (ρ : V →+* V₁) (ev : V₁ →+* K) (σ : K ≃+* K) (f₁ : (Over.pullback (spMap ev)).obj ((Over.pullback (spMap ρ)).obj B) ⟶ (Over.pullback (spMap (σ.toRingHom.comp ev))).obj ((Over.pullback (spMap ρ)).obj B)), IsMonHom f₁ → IsIso f₁ → ∃ f : ((Over.pullback (spMap (ev.comp ρ))).obj B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj B) (𝟙 _) f ∧ ∀ (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj ((Over.pullback (spMap ρ)).obj B)).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj B).left), y ≫ pullback.fst B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst ((Over.pullback (spMap ρ)).obj B).hom (spMap ev) ≫ pullback.fst B.hom (spMap ρ) → y ≫ pullback.snd B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd ((Over.pullback (spMap ρ)).obj B).hom (spMap ev) → x ≫ f₁.left ≫ pullback.fst ((Over.pullback (spMap ρ)).obj B).hom (spMap (σ.toRingHom.comp ev)) ≫ pullback.fst B.hom (spMap ρ) = y ≫ f ≫ pullback.fst B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) := by
  first | exact @GlobalTheory.FibreTransport.transport | exact GlobalTheory.FibreTransport.transport | (intros; apply GlobalTheory.FibreTransport.transport <;> assumption)
