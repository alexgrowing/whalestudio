import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem TateIsoO.ev_nsmul {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIsoO D k Q act e) (n m : ℕ) (x : D.La) :
    I.ev n (m • x) = I.ev n x ^ m := by
  let f : D.La →+ Additive Q := AddMonoidHom.mk' (fun x => Additive.ofMul (I.ev n x)) fun x y => by
    simp [I.add]
  exact congrArg Additive.toMul (map_nsmul f m x)

theorem levelPos_of_coprime {N' : ℕ} (hc : N'.Coprime p) : 0 < N' := by
  rcases Nat.eq_zero_or_pos N' with h | h
  · subst h
    exact absurd ((Nat.coprime_zero_left p).1 hc) (Fact.out : p.Prime).one_lt.ne'
  · exact h

def Obj.forget {b : Base D R} {N' : ℕ} {s : S ⟶ Sp R} (o : Obj b N' s) (N : ℕ) (hd : N ∣ N')
    (hc : N'.Coprime p) : Obj b N s where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  kerP := o.kerP
  rosati := o.rosati
  lie := o.lie
  lieRank := o.lieRank
  eta y := o.eta ((N' / N) • y)
  eta_add x y := by rw [smul_add, o.eta_add]
  eta_lin c x := by rw [smul_comm, o.eta_lin]
  eta_ker x := by rw [smul_smul, Nat.div_mul_cancel hd, o.eta_ker]
  geom k _ _ x β h := by
    obtain ⟨I, hI⟩ := o.geom k x β h
    have hN' := levelPos_of_coprime hc
    have hN : 0 < N := Nat.pos_of_dvd_of_pos hd hN'
    have hk : 0 < N' / N := Nat.div_pos (Nat.le_of_dvd hN' hd) hN
    refine ⟨I, fun y => ?_⟩
    rw [hI, I.ev_nsmul]
    have := I.tower N (N' / N) hN hk (by rw [Nat.mul_div_cancel' hd]; exact hc) y
    rwa [Nat.mul_div_cancel' hd] at this

@[simp] theorem Obj.forget_A {b : Base D R} {N' : ℕ} {s : S ⟶ Sp R} (o : Obj b N' s) (N : ℕ) (hd : N ∣ N')
    (hc : N'.Coprime p) : (o.forget N hd hc).A = o.A := rfl

@[simp] theorem Obj.forget_eta {b : Base D R} {N' : ℕ} {s : S ⟶ Sp R} (o : Obj b N' s) (N : ℕ) (hd : N ∣ N')
    (hc : N'.Coprime p) (y : D.La) : (o.forget N hd hc).eta y = o.eta ((N' / N) • y) := rfl

def IsLift {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (N' : ℕ) (T : Over S)
    (lv : D.La → (T ⟶ o.A)) : Prop :=
  (∀ x y, lv (x + y) = lv x * lv y) ∧
  (∀ x, lv (N' • x) = 1) ∧
  (∀ (c : D.O) x, lv (c • x) = lv x ≫ o.act.act c) ∧
  (∀ x, lv ((N' / N) • x) = toUnit T ≫ o.eta x) ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left),
    ∃ I : TateIsoO D k (Over.mk (x ≫ T.hom) ⟶ o.A) (fun c g => g ≫ o.act.act c)
        (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
      ∀ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv y = I.ev N' y

end GlobalTheory.UPel.HT
