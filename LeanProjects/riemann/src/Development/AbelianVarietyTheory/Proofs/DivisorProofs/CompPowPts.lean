import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

theorem Obj.eta_zero {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) : o.eta 0 = 1 := by
  have h := o.eta_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h |>.symm ▸ rfl

theorem Obj.eta_nsmul {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (k : ℕ) (y : D.La) :
    o.eta (k • y) = o.eta y ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero, o.eta_zero]
  | succ k ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

theorem comp_pow_pts {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) (e : T ⟶ A) (k : ℕ) :
    f ≫ e ^ k = (f ≫ e) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, comp_one]
  | succ k ih => rw [pow_succ, pow_succ, comp_mul, ih]

def Obj.lower {b : Base D R} {N M₁ : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (hN : 0 < N) (hM : 0 < M₁)
    (hc : (N * M₁).Coprime p) (o : Obj b (N * M₁) s) : Obj b N s :=
  { o with
    eta := fun y => o.eta (M₁ • y)
    eta_add := fun x y => by rw [smul_add]; exact o.eta_add _ _
    eta_lin := fun c x => by rw [smul_comm]; exact o.eta_lin _ _
    eta_ker := fun x => by rw [smul_smul, Nat.mul_comm M₁ N]; exact o.eta_ker x
    geom := fun k _ _ x β hx => by
      obtain ⟨I, hI⟩ := o.geom k x β hx
      refine ⟨I, fun y => ?_⟩
      rw [o.eta_nsmul, comp_pow_pts, hI, I.tower N M₁ hN hM hc] }

def ObjMap.lower {b : Base D R} {N M₁ : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R}
    (hN : 0 < N) (hM : 0 < M₁) (hc : (N * M₁).Coprime p) {o' : Obj b (N * M₁) s'} {o : Obj b (N * M₁) s}
    {f : S' ⟶ S} (m : ObjMap o' o f) : ObjMap (o'.lower hN hM hc) (o.lower hN hM hc) f :=
  { m with eta := fun y => m.eta (M₁ • y) }

end GlobalTheory.UPel.HT
