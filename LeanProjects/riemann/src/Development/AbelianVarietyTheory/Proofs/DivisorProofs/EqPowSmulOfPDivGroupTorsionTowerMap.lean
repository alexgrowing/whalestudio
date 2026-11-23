import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FrobFieldExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfBijectiveAffinePts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughIsogenyOfKillsKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFiniteFreeFinrankLeFourMulDimStatement
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Semi
open CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.AV.AbVar

theorem eq_zero_of_forall_pow_dvd {M : Type} [AddCommGroup M] [Module.Free ℤ M] {p : ℕ}
    (hp : 1 < p) (x : M) (h : ∀ n : ℕ, ∃ y : M, x = p ^ n • y) : x = 0 := by
  let b := Module.Free.chooseBasis ℤ M
  refine b.repr.injective (Finsupp.ext fun i => ?_)
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have e : ∀ (m : ℕ) (y : M), x = p ^ m • y → b.repr x i = (p : ℤ) ^ m * b.repr y i := by
    intro m y hy
    subst hy
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
    push_cast
    rfl
  obtain ⟨y, hy⟩ := h (b.repr x i).natAbs
  have hd : ((p : ℤ) ^ (b.repr x i).natAbs) ∣ b.repr x i := ⟨b.repr y i, e _ y hy⟩
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd ?_
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self hp

theorem eq_pow_smul_of_torsionTower_map : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k)
    (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B),
    (∀ (n : ℕ) (g : G ⟶ H), t.map t' f.hom = (p : ℤ_[p]) ^ n • g → ∃ f' : A ⟶ B, f = p ^ n • f') ∧
    (t.map t' f.hom = 0 → f = 0) := by
  intro p _ k _ A B G H t t' f
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have key : ∀ (n : ℕ) (g : G ⟶ H), t.map t' f.hom = (p : ℤ_[p]) ^ n • g →
      ∃ f' : A ⟶ B, f = p ^ n • f' := by
    intro n g hg

    have happ : (t.map t' f.hom).app n = (0 : G ⟶ H).app n := by
      have h1 : Hom.conv (t.map t' f.hom) n = Hom.conv (0 : G ⟶ H) n := by
        rw [hg, pow_smul_conv, zero_conv]
      exact congrArg (fun c => c.ofConv) h1
    have hy : t.y n ≫ f.hom = 1 := by
      rw [← t.map_y t' f.hom n, happ]
      exact _root_.map_one (t'.pts n _)
    have hpn : ((p ^ n : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast (pow_pos (by omega : 0 < p) n).ne'
    have hiso : IsIsogeny ((p ^ n : ℕ) • 𝟙 A) := by
      have := (GlobalTheory.MulIsogeny.mul_isogeny k A ((p ^ n : ℕ) : ℤ) hpn).1
      rwa [natCast_zsmul] at this
    obtain ⟨f', hf'⟩ := exists_factor_of_isogeny k A A B ((p ^ n : ℕ) • 𝟙 A) f hiso
      (fun T x hx => by
        have hx' : x ≫ mulN A.X (p ^ n) = SemiCartesianMonoidalCategory.toUnit T ≫ MonObj.one := by
          rw [nsmul_hom, id_hom, MonObj.comp_pow, Category.comp_id] at hx
          rw [GrpTangent.comp_mulN, hx, CategoryTheory.Hom.one_def]
        have hP := TorsionTower.isPullback_y p k G A.X t n
        rw [← hP.lift_fst x (SemiCartesianMonoidalCategory.toUnit T) hx', Category.assoc, hy,
          MonObj.comp_one])
    exact ⟨f', by rw [← hf', Preadditive.nsmul_comp, Category.id_comp]⟩
  refine ⟨key, fun h0 => ?_⟩
  have hfree := (GlobalTheory.T.hom_finite_free_finrank_le_four_mul_dim k A B).2.1
  refine eq_zero_of_forall_pow_dvd hp f fun n => key n 0 ?_
  rw [h0, smul_zero]

end GlobalTheory.AV.AbVar

example : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), (∀ (n : ℕ) (g : G ⟶ H), t.map t' f.hom = (p : ℤ_[p]) ^ n • g → ∃ f' : A ⟶ B, f = p ^ n • f') ∧ (t.map t' f.hom = 0 → f = 0) :=
  GlobalTheory.AV.AbVar.eq_pow_smul_of_torsionTower_map
