import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerPresentationEndomorphismsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStable
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPowerPresentation_endomorphisms_pullback : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left) (c : SiegPre g n ζ (u ≫ F.s)), SiegPB c F.univ u → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T₁ : Over T) (y : Fin 8 → (T₁ ⟶ c.A)), ∃! x : T₁ ⟶ P.A, ∀ a, x ≫ pr a = y a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → ∃ c' : SiegPre g n ζ ((f ≫ u) ≫ F.s), SiegPB c' F.univ (f ≫ u) ∧ ∃ pr' : Fin 8 → (P'.A ⟶ c'.A), (∀ a, IsMonHom (pr' a)) ∧ (∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ c'.A)), ∃! x : T₁ ⟶ P'.A, ∀ a, x ≫ pr' a = y a) ∧ LBIso P'.L (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2)) ∧ ∀ (b : P.A ⟶ P.A) (k : Fin 8 → Fin 8 → ℤ), (∀ a, b ≫ pr a = (List.ofFn fun v => pr v ^ k a v).prod) → ∃ b' : P'.A ⟶ P'.A, (∀ a, b' ≫ pr' a = (List.ofFn fun v => pr' v ^ k a v).prod) ∧ b'.left ≫ φ = φ ≫ b.left := by
  first | exact @GlobalTheory.Poinc.sharpOver_pullback_end | exact GlobalTheory.Poinc.sharpOver_pullback_end | (intros; apply GlobalTheory.Poinc.sharpOver_pullback_end <;> assumption)
