import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatMatTransposeMulGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthLetters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointExtensionSplit

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.HalfGeo
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EqHalf.InducedProof

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

def actPt (t : SAB H X) (α : 𝓞 E) (T : Over X) : (T ⟶ t.G) →* (T ⟶ t.G) :=
  haveI := t.act.hom α
  IsMonHom.monoidHom (t.act.act α) T

theorem actPt_apply (α : 𝓞 E) {T : Over X} (w : T ⟶ t.G) : actPt t α T w = w ≫ t.act.act α := rfl

theorem act_mul (α : 𝓞 E) {T : Over X} (w w' : T ⟶ t.G) :
    (w * w') ≫ t.act.act α = (w ≫ t.act.act α) * (w' ≫ t.act.act α) :=
  map_mul (actPt t α T) w w'

theorem act_tors (α : 𝓞 E) {T : Over X} {w : T ⟶ t.G} {q : ℕ} (hw : w ^ q = 1) : (w ≫ t.act.act α) ^ q = 1 := by
  rw [← actPt_apply, ← map_pow, hw, map_one]

def actChar {O : Type} [CommRing O] {x : Sp O ⟶ X} {q : ℕ} (c : TorsChar t x q) (α : 𝓞 E) : TorsChar t x q where
  χ B _ _ _ w := c.χ B (w ≫ t.act.act α)
  mul B _ _ _ w w' hw hw' := by
    rw [act_mul, c.mul B _ _ (act_tors α hw) (act_tors α hw')]
  nat B B' _ _ _ _ _ _ φ g g' hg hg' :=
    c.nat B B' φ _ _ (act_tors α hg) (by rw [Over.comp_left, Over.comp_left, hg', Category.assoc])

def zprodChar {O : Type} [CommRing O] {x : Sp O ⟶ X} {q N : ℕ} (c : Fin N → TorsChar t x q) (n : Fin N → ℤ) :
    TorsChar t x q where
  χ B _ _ _ w := ∏ m, (c m).χ B w ^ n m
  mul B _ _ _ w w' hw hw' := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun m _ => by rw [(c m).mul B w w' hw hw', _root_.mul_zpow]
  nat B B' _ _ _ _ _ _ φ g g' hg hg' := by
    have h : ∀ m, (c m).χ B' g' = Units.map (φ : B →* B') ((c m).χ B g) := fun m =>
      Units.ext ((c m).nat B B' φ g g' hg hg')
    have h2 : ∏ m, (c m).χ B' g' ^ n m = Units.map (φ : B →* B') (∏ m, (c m).χ B g ^ n m) := by
      rw [map_prod]
      exact Finset.prod_congr rfl fun m _ => by rw [map_zpow, h]
    exact congrArg Units.val h2

theorem equivar_induced : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (K : Type) [Field K] [CharZero K]
    (ξ : Sp K ⟶ X) (q : ℕ), q ≠ 0 → (∃ ζ : K, IsPrimitiveRoot ζ q) → SplitK t ξ q →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] [Algebra R K] [IsFractionRing R K]
    (x : Sp R ⟶ X), spMap (algebraMap R K) ≫ x = ξ →
    ∀ (p : ℕ) [Fact p.Prime] (ψ : R →+* ↥(intO ℂ_[p])) (z : Sp ↥(intO ℂ_[p]) ⟶ X), IsLocalHom ψ → spMap ψ ≫ x = z →
    ∀ (N : ℕ) (χ : Fin N → (TorsK t ξ q →* Kˣ)) (ch : Fin N → TorsChar t z q) (ρ : 𝓞 E →+* Matrix (Fin N) (Fin N) ℤ),
    (∀ (α : 𝓞 E) (k k' : TorsK t ξ q), k'.1 = k.1 ≫ t.act.act α → ∀ m, χ m k' = ∏ m', χ m' k ^ ρ α m m') →
    (∀ m, InducedBy (χ m) x (algebraMap R K) ψ (ch m)) → GlobalTheory.EqHalf.Equivar t ch ρ := by
  intro E _ _ _ H X _ t K _ _ ξ q hq hζ hs R _ _ _ _ _ _ x hx p _ ψ z hψ hz N χ ch ρ hχ hch α B _ _ _ w hw m
  obtain ⟨-, h⟩ := GlobalTheory.HtChar.induced_chars E H X t K ξ q hq hζ hs R x hx
  obtain ⟨-, -, h3⟩ := h p ψ z hψ hz
  have hev : ∀ k : TorsK t ξ q, (∏ m', χ m' ^ ρ α m m') k = ∏ m', χ m' k ^ ρ α m m' := fun k => by
    rw [MonoidHom.finset_prod_apply]
    exact Finset.prod_congr rfl fun m' _ => MonoidHom.zpow_apply _ _ _
  refine h3 (∏ m', χ m' ^ ρ α m m') (actChar (ch m) α) (zprodChar ch (ρ α m)) (fun σ k a w hσ hk hw ha => ?_)
    (fun σ k a w hσ hk hw ha => ?_) B w hw
  · refine hch m (σ ≫ t.act.act α) ⟨k.1 ≫ t.act.act α, MonoidHom.mem_ker.2 (act_tors α (MonoidHom.mem_ker.1 k.2))⟩ a
      (w ≫ t.act.act α) (act_tors α hσ) ?_ ?_ ?_
    · show (k.1 ≫ t.act.act α).left = _
      rw [Over.comp_left, Over.comp_left, hk, Category.assoc]
    · rw [Over.comp_left, Over.comp_left, hw, Category.assoc]
    · rw [ha, hev, hχ α k _ rfl m]
  · have hp : ∀ m', ((χ m' k : Kˣ) : K) ^ q = 1 := fun m' => by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, GlobalTheory.HtChar.ker_pow, map_one, Units.val_one]
    have hr : ∀ m', ∃ b : Rˣ, algebraMap R K b = ((χ m' k : Kˣ) : K) := fun m' => by
      obtain ⟨b, hb⟩ := GlobalTheory.HtChar.root_mem (R := R) hq (hp m')
      have hb' : b ^ q = 1 := IsFractionRing.injective R K (by rw [map_pow, hb, hp, map_one])
      exact ⟨Units.ofPowEqOne b q hb' hq, hb⟩
    choose b hb using hr
    have h1 : Units.map (algebraMap R K : R →* K) (∏ m', b m' ^ ρ α m m') = ∏ m', χ m' k ^ ρ α m m' := by
      rw [map_prod]
      exact Finset.prod_congr rfl fun m' _ => by rw [map_zpow, show Units.map (algebraMap R K : R →* K) (b m') = χ m' k from Units.ext (hb m')]
    obtain rfl : a = ((∏ m', b m' ^ ρ α m m' : Rˣ) : R) := IsFractionRing.injective R K (by
      rw [ha, hev, ← h1]; rfl)
    have h2 : (∏ m', (ch m').χ _ w ^ ρ α m m' : (↥(intO ℂ_[p]))ˣ) =
        Units.map (ψ : R →* ↥(intO ℂ_[p])) (∏ m', b m' ^ ρ α m m') := by
      rw [map_prod]
      exact Finset.prod_congr rfl fun m' _ => by
        rw [map_zpow, show (ch m').χ _ w = Units.map (ψ : R →* ↥(intO ℂ_[p])) (b m') from
          Units.ext (hch m' σ k (b m') w hσ hk hw (hb m'))]
    exact congrArg Units.val h2

end GlobalTheory.EqHalf.InducedProof
