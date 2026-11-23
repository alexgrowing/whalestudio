import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticDatumTorsionLevelExt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_datum_torsion_level_ext : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (ρ : o), Odd k → 3 ≤ k → (∃ N' : ℕ, k = N' ^ 2) → em ρ = H.rt0 → em (b.ζ : o) = zeta k → ArBase em → ∀ (X : Scheme.{0}) (s : X ⟶ Sp o) (t : TObj g k J b s) (τ : SAB H X), PELRep D a bas ρ t → IsPEL D a bas ρ t τ → ∀ (p : ℕ) (Ag : SiegelFamily g p k), p.Prime → k.Coprime p → SRep Ag → ∀ (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La), (∀ x y, D.EF (bas' x) (bas' y) = omegaStd x y) → ∀ (O : Type) [CommRing O] (i : O →+* ℂ) (z : ZP p k →+* O) (bb : o →+* O), Function.Injective i → GlobalTheory.Models.IsInc (ZP p k).subtype i z → GlobalTheory.Models.IsInc em i bb → IsNoetherianRing O → ∀ (T : Scheme.{0}) (sT : T ⟶ Sp O) (f : T ⟶ X), IsPullback f sT s (spMap bb) → ∀ (tT : TObj g k J b (sT ≫ spMap bb)) (c : SiegPre g k (zetaZP p k) (sT ≫ spMap z)) (u : T ⟶ pullback Ag.s (spMap z)), TMap tT t f → TSieg bas bas' tT c → u ≫ pullback.snd _ _ = sT → SiegPB c Ag.univ (u ≫ pullback.fst _ _) → IsProper u := by
  first | exact @GlobalTheory.SiegelMapProper.isProper_toSiegel | exact GlobalTheory.SiegelMapProper.isProper_toSiegel | (intros; apply GlobalTheory.SiegelMapProper.isProper_toSiegel <;> assumption)
