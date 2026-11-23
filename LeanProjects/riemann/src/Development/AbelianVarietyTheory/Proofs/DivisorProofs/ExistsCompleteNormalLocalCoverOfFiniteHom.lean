import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteLocalDomainCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCompleteOfFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocExt

theorem exists_isCN_cover_of_finite : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : Type) [CommRing C] (φ : R →+* C), IsCN R → Function.Injective φ → φ.Finite → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (σ : C →+* R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ σ.comp φ = ρ := by
  first
  | exact @_root_.GlobalTheory.FiniteLocalCompleteness.main
  | exact _root_.GlobalTheory.FiniteLocalCompleteness.main
  | (apply _root_.GlobalTheory.FiniteLocalCompleteness.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteLocalCompleteness.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteLocalCompleteness.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteLocalCompleteness.main ..)

end GlobalTheory.LocExt
