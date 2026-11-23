import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductSmallTwistedFunctionalEqnFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.ZmPow

theorem pow_mul_small : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N k : ℕ) (g : ∀ β, SecT D.toPre a N (-1) β) (ρ : ∀ β, SecT D.toPre a 0 k β), Small (maximalIdeal R) (w := id) g → Small (maximalIdeal R) (w := id) ρ → TFE h h' g → TFE h h' ρ → ∃ F : ∀ β, SecT D.toPre a ((N * k : ℕ) : ℤ) 0 β, Small (maximalIdeal R) (w := id) F ∧ TFE h h' F ∧ ∀ (e : ℕ) (τ : SecE U.toUnifPre (b e) N (-1)) (τ' : SecE U.toUnifPre (b e) 0 k), TExp U.toUnifPre τ (w := id) g → TExp U.toUnifPre τ' (w := id) ρ → ∃ τ'' : SecE U.toUnifPre (b e) ((N * k : ℕ) : ℤ) 0, (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' ^ k * sval τ' x z J') ∧ TExp U.toUnifPre τ'' (w := id) F := by
  intro R _ _ _ hAdm D a a' h h' hE A G _ _ hG U b hb N k g ρ hgS hρS hgT hρT
  have key : ∀ m : ℕ, ∀ n j : ℤ, n = (N : ℤ) * m → j = (k : ℤ) - m →
      ∃ F : ∀ β, SecT D.toPre a n j β, Small (maximalIdeal R) (w := id) F ∧ TFE h h' F ∧
        ∀ (e : ℕ) (τ : SecE U.toUnifPre (b e) N (-1)) (τ' : SecE U.toUnifPre (b e) 0 k),
          TExp U.toUnifPre τ (w := id) g → TExp U.toUnifPre τ' (w := id) ρ →
          ∃ τ'' : SecE U.toUnifPre (b e) n j,
            (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'),
              Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' ^ m * sval τ' x z J') ∧
            TExp U.toUnifPre τ'' (w := id) F := by
    intro m
    induction m with
    | zero =>
      intro n j hn hj
      have hn' : n = 0 := by simp [hn]
      have hj' : j = (k : ℤ) := by simp [hj]
      subst hn' hj'
      refine ⟨ρ, hρS, hρT, fun e τ τ' _ hτ' => ⟨τ', fun Z x z J' _ => by simp, hτ'⟩⟩
    | succ m ih =>
      intro n j hn hj
      obtain ⟨Fm, hFS, hFT, hFm⟩ := ih ((N : ℤ) * m) ((k : ℤ) - m) rfl rfl
      obtain ⟨F, hS, hT, hP⟩ := GlobalTheory.T.exists_product_small_twistedFunctionalEqn_family R hAdm D a a' h h' hE A G hG U b hb
        (N : ℤ) (-1) ((N : ℤ) * m) ((k : ℤ) - m) n j (by rw [hn]; push_cast; ring)
        (by rw [hj]; push_cast; ring) g Fm hgS hFS hgT hFT
      refine ⟨F, hS, hT, fun e τ τ' hτ hτ' => ?_⟩
      obtain ⟨τm, hτmv, hτmE⟩ := hFm e τ τ' hτ hτ'
      obtain ⟨τ'', hv, hE''⟩ := hP e τ τm hτ hτmE
      refine ⟨τ'', fun Z x z J' hJ => ?_, hE''⟩
      rw [hv Z x z J' hJ, hτmv Z x z J' hJ]
      ring
  exact key k _ _ (by push_cast; ring) (by simp)

end GlobalTheory.ZmPow
