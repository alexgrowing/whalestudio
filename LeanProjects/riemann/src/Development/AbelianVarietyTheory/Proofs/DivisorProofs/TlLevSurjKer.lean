import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleLevelSurjectiveOfDivisible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricPointsDivisible
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
private theorem tate_nsmul_lev {p : ℕ} {M : Type} [CommGroup M]
    (s : _root_.GlobalTheory.HTLat.Tate p M) (k m : ℕ) :
    (k • s).lev m = s.lev m ^ k := by
  induction k with
  | zero => simp [_root_.GlobalTheory.HTLat.Tate.lev_zero]
  | succ k ih => rw [succ_nsmul, _root_.GlobalTheory.HTLat.Tate.lev_add, ih, pow_succ]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.AV.AbVar.tl_lev_surj_ker : ∀ (K : Type) [Field K]
    (l : ℕ) [Fact l.Prime] (A : _root_.GlobalTheory.AV.AbVar K) (n : ℕ),
    (∀ x : A.Pt, x ^ l ^ n = 1 →
        ∃ t : _root_.GlobalTheory.AV.AbVar.Tl l A, t.lev n = x) ∧
      ∀ t : _root_.GlobalTheory.AV.AbVar.Tl l A, t.lev n = 1 ↔
        ∃ s : _root_.GlobalTheory.AV.AbVar.Tl l A, t = (l : ℤ_[l]) ^ n • s := by
  intro K _ l hl A n
  have hlpos : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  refine ⟨fun x hx => _root_.GlobalTheory.Published.tate_lev_surj l _
    (_root_.GlobalTheory.AV.AbVar.pt_divisible K A l hlpos) n x hx, fun t => ?_⟩
  have hcast : ∀ s : _root_.GlobalTheory.AV.AbVar.Tl l A,
      (l : ℤ_[l]) ^ n • s = (l ^ n : ℕ) • s := by
    intro s
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]
    push_cast
    rfl
  constructor
  · intro ht
    let u : ℕ → A.Pt := fun m => t.lev (m + n)
    have hu : ∀ m, u m ^ l ^ m = 1 ∧ u (m + 1) ^ l = u m := by
      intro m
      refine ⟨?_, ?_⟩
      · simp only [u]
        rw [Nat.add_comm, _root_.GlobalTheory.HTLat.Tate.lev_add_pow, ht]
      · simp only [u]
        rw [show m + 1 + n = m + n + 1 by omega, _root_.GlobalTheory.HTLat.Tate.lev_succ]
    refine ⟨_root_.GlobalTheory.HTLat.Tate.mk u hu, ?_⟩
    rw [hcast]
    refine _root_.GlobalTheory.HTLat.Tate.ext fun m => ?_
    rw [tate_nsmul_lev,
      _root_.GlobalTheory.HTLat.Tate.lev_mk]
    simp only [u]
    rw [_root_.GlobalTheory.HTLat.Tate.lev_add_pow]
  · rintro ⟨s, rfl⟩
    rw [hcast, tate_nsmul_lev, _root_.GlobalTheory.HTLat.Tate.lev_pow]

end GlobalTheory.AV.AbVar
