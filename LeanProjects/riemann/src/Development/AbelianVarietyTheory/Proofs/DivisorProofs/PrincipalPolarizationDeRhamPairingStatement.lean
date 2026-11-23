import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarizationDeRhamPairing
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
open CategoryTheory AlgebraicGeometry MonoidalCategory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_polarization_de_rham_pairing : GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CubeTheorem → GlobalTheory.CovTop.Hypotheses2 →
    GlobalTheory.Published.PoincareDeRhamDuality → ∀ {T : Scheme.{0}} (A : Over T) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → (∃ c, GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A c) → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∃ b : ∀ (V : T.Opens), IsAffineOpen V → (Γ(H, V) →ₗ[Γ(T, V)] Γ(H, V) →ₗ[Γ(T, V)] Γ(T, V)),
      (∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V) (s t : Γ(H, V)),
        b V' hV' (GlobalTheory.Twist.resM H h s) (GlobalTheory.Twist.resM H h t) = resG T h (b V hV s t)) ∧
      (∀ (V : T.Opens) (hV : IsAffineOpen V), (b V hV).IsPerfPair) ∧
      ∀ (V : T.Opens) (hV : IsAffineOpen V), ∃ P : LB ((onAff A hV) ⊗ (onAff A hV)).left,
        GlobalTheory.AbDual.IsDual (onAff A hV) (onAff A hV) P ∧
        ∃ φ : HdR (onAff A hV) →ₗ[Γ(T, V)] HdR (onAff A hV) →ₗ[Γ(T, V)] Γ(T, V),
          GlobalTheory.AbDual.IsCorrForm (GlobalTheory.Cris.dp0 Γ(T, V)) (𝟙 _) (onAff A hV) (onAff A hV) P φ ∧
          ∀ (x y : HdR (onAff A hV)) (u v : Γ(H, V)), (∀ w, x (e V hV w) = b V hV w u) →
            (∀ w, y (e V hV w) = b V hV w v) → φ x y = b V hV u v := by
  first | exact @GlobalTheory.PrincipalPolPairing.exists_affine_pairings | exact GlobalTheory.PrincipalPolPairing.exists_affine_pairings | (intros; apply GlobalTheory.PrincipalPolPairing.exists_affine_pairings <;> assumption)
