import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelChangeBySymplecticSimilitude
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_level_change_by_symplectic_similitude : ∀ (h N : ℕ) (B : Type) [CommRing B] (b : TBase B N), Odd N → (∀ (S : Scheme.{0}) (s : S ⟶ Sp B) (C : SiegPre h N (b.ζ : B) s) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (m : ℕ), m.Coprime N → (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) → ∃ (C' : SiegPre h N ((b.ζ : B) ^ m) s) (φ : C'.A.left ⟶ C.A.left) (φ₂ : (G2 C'.A).left ⟶ (G2 C.A).left), IsGrpPullback C'.A C.A (𝟙 S) φ ∧ IsSquare φ φ₂ ∧ LBIso C'.P (C.P.pull φ₂) ∧ ∀ x, (C'.lev x).left ≫ φ = (C.lev (T x)).left) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (β : B →+* R) (m : ℕ) (β' : B →+* R) (C : SiegPre h N (b.ζ : B) (spMap β)) (C' : SiegPre h N (b.ζ : B) (spMap β')) (φ : C'.A.left ⟶ C.A.left) (φ₂ : (G2 C'.A).left ⟶ (G2 C.A).left), β' (b.ζ : B) = β (b.ζ : B) ^ m → IsGrpPullback C'.A C.A (𝟙 _) φ → IsSquare φ φ₂ → LBIso C'.P (C.P.pull φ₂) → ∃ T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ), (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) ∧ ∀ x, (C'.lev x).left ≫ φ = (C.lev (T x)).left := by
  first | exact @GlobalTheory.siegel_level_change_by_similitude | exact GlobalTheory.siegel_level_change_by_similitude | (intros; apply GlobalTheory.siegel_level_change_by_similitude <;> assumption)
