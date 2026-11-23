import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TowerRedToBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTowerAndHeightEqTwoDim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB mulN)
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.SerreTate
open GlobalTheory.DeRham (spOver)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbelianTower

open TensorProduct
open scoped CategoryTheory.Obj

theorem exists_isUnivTorsion {O : Type} [CommRing O] {A : Over (Sp O)} [GrpObj A] (hA : IsAbelianScheme A) {g : ℕ}
    (hg : SmoothOfRelativeDimension g A.hom) {N : ℕ} (hN : N ≠ 0) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (y : SpAlg O R ⟶ A), Module.Finite O R ∧
      Module.Projective O R ∧ AbelianPDiv.IsUnivTorsion N y ∧
      ∀ q : PrimeSpectrum O, Module.rankAtStalk R q = N ^ (2 * g) := by
  obtain ⟨R, _, _, y, h1, h2, h⟩ := AbelianPDiv.exists_isPullback (N := N) hA (Nat.one_le_iff_ne_zero.2 hN)
  refine ⟨R, inferInstance, inferInstance, y, h1, h2, AbelianPDiv.isUnivTorsion_of_isPullback y h, fun q => ?_⟩
  let K := q.asIdeal.ResidueField
  obtain ⟨y', h'⟩ := AbelianPDiv.exists_isPullback_baseChange y h K
  let B : AV.AbVar K :=
    { X := (Over.pullback (spMap (algebraMap O K))).obj A
      ab := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback _ A hA
      dim := g
      smooth := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback A.hom (spMap (algebraMap O K))) hg }
  have hr := AVTower.finrank_torsion B hN (S := K ⊗[O] R) y' h'
  have hq : PrimeSpectrum.comap (algebraMap O K) ⊥ = q :=
    PrimeSpectrum.ext ((RingHom.ker_eq_comap_bot _).symm.trans (Ideal.ker_algebraMap_residueField _))
  rw [← hq, ← Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_finrank_of_free, hr]
  rfl

theorem exists_pDivGroup (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A]
    (hA : IsAbelianScheme A) (g : ℕ) (hg : SmoothOfRelativeDimension g A.hom) :
    ∃ (G : PDivGroup p O) (_ : G.TorsionTower A), G.height = 2 * g := by
  have := hA.comm
  choose R _ _ y h1 h2 h hr using fun n : ℕ => exists_isUnivTorsion (N := p ^ n) hA hg
    (pow_ne_zero _ hp.out.ne_zero)
  choose r r1 r2 r3 using fun n : ℕ => (h n).exists_res (h (n + 1))
    (by rw [pow_succ, pow_mul, (h n).1, one_pow])
  let G : PDivGroup p O :=
    { height := 2 * g
      A := R
      hopf := fun n => (h n).hopfAlgebra
      cocomm := fun n => (h n).isCocomm
      finite := h1
      projective := h2
      rank_eq := fun n q => (hr n q).trans (pow_mul _ _ _).symm
      res := r
      res_surjective := r1
      ker_res := r2 }
  exact ⟨G, {
    y := y
    mul := fun n B _ _ => (h n).mul_y
    inj := fun n B _ _ _ _ => (h n).inj
    surj := fun n B _ _ z hz => ((h n).2 B z hz).exists
    res := r3 }, rfl⟩

theorem exists_pDivGroup_tower : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (G : PDivGroup p R) (_ : G.TorsionTower A), G.height = 2 * g :=
  fun p _ R _ _ A _ g hA hg => exists_pDivGroup p R A hA g hg

end GlobalTheory.AbelianTower
