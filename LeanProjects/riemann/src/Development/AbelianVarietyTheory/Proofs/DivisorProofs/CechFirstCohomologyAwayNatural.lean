import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulEqZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechAway

theorem cech_one_away_natural : ∀ (R : Type) [CommRing R] (D : Type) [CommRing D] [Algebra R D] (n : ℕ) (s : Fin n → D), Ideal.span (Set.range s) = ⊤ → ∀ d : Fin n → Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, (∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E' (θ.comp ψ) = θ (d a b E ψ)) → (∀ (a b c : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → IsUnit (ψ (s c)) → d a b E ψ + d b c E ψ = d a c E ψ) → ∃ e : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, (∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → e a E' (θ.comp ψ) = θ (e a E ψ)) ∧ ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E ψ = e b E ψ - e a E ψ := by
  first
  | exact @_root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary
  | exact _root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary
  | (apply _root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary <;> assumption)
  | (intros; apply _root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary ..)

end GlobalTheory.CechAway
