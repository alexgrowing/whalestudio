import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
namespace GlobalTheory.KeyKa
open GlobalTheory.KeyPow

def KaRule (g c M : ℕ) : Prop :=
  ∃ ka : ∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K], KeyIn K → Kˣ,
    (∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
      (Mx : Matrix (Fin P.g) (Fin P.g) K), P.g = g → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (Mx i) v (v' i)) →
      a ^ (8 * c) * (ka K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = Mx.det ^ (4 * c) * ka K ⟨P, hg, rig, hr, th, hth, v, hv⟩) ∧
    (∀ (K K' : Type) [Field K] [CharZero K] [IsAlgClosed K] [Field K'] [CharZero K'] [IsAlgClosed K'] (f : K →+* K')
      (x : KeyIn K) (x' : KeyIn K'), x.P.g = g → KeyPB x' x f → (ka K' x' : K') = f (ka K x)) ∧
    (∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (x : KeyIn R), x.P.g = g → IsUnit (M : R) →
      ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (j : R →+* R') (u : R'ˣ),
        Function.Injective j ∧ IsLocalHom j ∧
        ∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (f : R' →+* K) (xK : KeyIn K),
          KeyPB xK x (f.comp j) → (ka K xK : K) = f u) ∧
    ∀ a b : Fin g → ℂ, charHalf g a b → ∃ U : Matrix (Fin g) (Fin g) ℂ → ℂ, Key.IsHoloSiegel g U ∧
      ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
        NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 →
        (ka ℂ x : ℂ) = U (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm))

def KaSt : Prop := ∀ g p : ℕ, 1 ≤ g → p.Prime → ∃ c M : ℕ, 1 ≤ c ∧ 1 ≤ M ∧ ¬ p ∣ M ∧ KaRule g c M

def KeyDesc : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K), ∃ (K₀ : Subfield K) (x₀ : KeyIn K₀), Countable K₀ ∧ KeyPB x x₀ K₀.subtype

def KaRuleK (g c M : ℕ) (ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ) : Prop :=
    (∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
      (Mx : Matrix (Fin P.g) (Fin P.g) K), P.g = g → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (Mx i) v (v' i)) →
      a ^ (8 * c) * (ka K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = Mx.det ^ (4 * c) * ka K ⟨P, hg, rig, hr, th, hth, v, hv⟩) ∧
    (∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (f : K →+* K')
      (x : KeyIn K) (x' : KeyIn K'), x.P.g = g → KeyPB x' x f → (ka K' x' : K') = f (ka K x)) ∧
    (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
      [IsFractionRing R K] (x : KeyIn R) (xK : KeyIn K), x.P.g = g → IsUnit (M : R) → KeyPB xK x (algebraMap R K) →
      ∃ u : Rˣ, (ka K xK : K) = algebraMap R K u ∧
        ∀ (k : Type) [Field k] [CharZero k] (r : R →+* k) (xk : KeyIn k), Function.Surjective r → KeyPB xk x r →
          (ka k xk : k) = r u) ∧
    ∀ a b : Fin g → ℂ, charHalf g a b → ∃ U : Matrix (Fin g) (Fin g) ℂ → ℂ, Key.IsHoloSiegel g U ∧
      ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
        NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 →
        (ka ℂ x : ℂ) = U (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm))

end GlobalTheory.KeyKa
end
