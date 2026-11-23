import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.TwistLabels
section
variable {O : Type} [CommRing O] {N : NumD O} {k : ℕ} {β : N.Form k} {u r : Oˣ} {j : ℕ}

theorem wp_eq {p q : N.QT j} {p' q' : (N.twist β u).QT j} (hp : TwRel β u r p p') (hq : TwRel β u r q q') :
    (N.twist β u).wp p' q' = N.wp p q := by
  have a : p'.1.2.s q'.1.1.toAdd = p.1.2.s q.1.1.toAdd * r ^ β.be p.1.1.toAdd q.1.1.toAdd := by
    rw [hq.1]; exact hp.2.2 _
  have b : q'.1.2.s p'.1.1.toAdd = q.1.2.s p.1.1.toAdd * r ^ β.be p.1.1.toAdd q.1.1.toAdd := by
    rw [hp.1, β.symm]; exact hq.2.2 _
  unfold NumD.wp NumD.tk
  rw [a, b, hp.2.1, hq.2.1]
  change _ * _ * cubN N.θ j 1 q.1.2.b p.1.2.b / (_ * _ * cubN N.θ j 1 p.1.2.b q.1.2.b) = _
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]
  abel

theorem rel_mul {p q : N.QT j} {p' q' : (N.twist β u).QT j} (hp : TwRel β u r p p') (hq : TwRel β u r q q') :
    TwRel β u r (p * q) (p' * q') := by
  refine ⟨?_, ?_, fun z => ?_⟩
  · change p'.1.1 * q'.1.1 = p.1.1 * q.1.1
    rw [hp.1, hq.1]; rfl
  · change p'.1.2.b * q'.1.2.b = p.1.2.b * q.1.2.b
    rw [hp.2.1, hq.2.1]; rfl
  · change p'.1.2.s z * q'.1.2.s z / N.θ (N.c z) p'.1.2.b q'.1.2.b =
      p.1.2.s z * q.1.2.s z / N.θ (N.c z) p.1.2.b q.1.2.b * r ^ β.be (p.1.1.toAdd + q.1.1.toAdd) z
    rw [hp.2.2, hq.2.2, hp.2.1, hq.2.1, map_add, LinearMap.add_apply, zpow_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel

theorem rel_inj {p q : N.QT j} {p' : (N.twist β u).QT j} (hp : TwRel β u r p p') (hq : TwRel β u r q p') : p = q := by
  have e : p.1.1 = q.1.1 := hp.1.symm.trans hq.1
  refine Subtype.ext (Prod.ext e (NumD.Gt.ext (hp.2.1.symm.trans hq.2.1) (funext fun z => ?_)))
  have := (hp.2.2 z).symm.trans (hq.2.2 z)
  rw [e] at this
  exact mul_right_cancel this

theorem rel_fun {p : N.QT j} {p' q' : (N.twist β u).QT j} (hp : TwRel β u r p p') (hq : TwRel β u r p q') : p' = q' :=
  Subtype.ext (Prod.ext (hp.1.trans hq.1.symm) (NumD.Gt.ext (hp.2.1.trans hq.2.1.symm)
    (funext fun z => (hp.2.2 z).trans (hq.2.2 z).symm)))

theorem rel_triv (h : r ^ j = u) (z : N.X) : TwRel β u r (N.qTriv j z) ((N.twist β u).qTriv j z) := by
  refine ⟨rfl, rfl, fun χ => ?_⟩
  change (N.twist β u).τ z χ = N.τ z χ * r ^ β.be (j • z) χ
  rw [N.twist_τ, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, zpow_mul, zpow_natCast, h]

theorem qEq_iff (h : r ^ j = u) {p q : N.QT j} {p' q' : (N.twist β u).QT j} (hp : TwRel β u r p p')
    (hq : TwRel β u r q q') : (N.twist β u).QEq p' q' ↔ N.QEq p q := by
  rw [NumD.qEq_iff, NumD.qEq_iff]
  refine exists_congr fun (z : N.X) => ?_
  have t := rel_mul hp (rel_triv (β := β) h z)
  exact ⟨fun e => rel_inj hq (e ▸ t), fun e => rel_fun hq (e ▸ t)⟩

theorem pow_s_eq (g : N.Gt) (g' : (N.twist β u).Gt) (hb : g'.b = g.b) (z : N.X) (t : Oˣ) (hs : g'.s z = g.s z * t)
    (m : ℕ) : (g' ^ m).s z = (g ^ m).s z * t ^ m := by
  have a := g.pow_s m z
  have b := g'.pow_s m z
  rw [hs, hb, mul_pow, ← a, mul_right_comm] at b
  exact mul_right_cancel b

theorem zpow_pow_comm (x : Oˣ) (n : ℤ) (m : ℕ) : (x ^ n) ^ m = (x ^ m) ^ n := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem rel_surj (h : r ^ j = u) (p' : (N.twist β u).QT j) : ∃ p : N.QT j, TwRel β u r p p' := by
  let y : N.X := p'.1.1.toAdd
  let g : N.Gt := ⟨p'.1.2.b, fun z => p'.1.2.s z / r ^ β.be y z, fun χ χ' => by
    have a : p'.1.2.s (χ + χ') * N.θ (N.c χ) (N.c χ') p'.1.2.b = p'.1.2.s χ * p'.1.2.s χ' := p'.1.2.mult χ χ'
    rw [map_add, zpow_add, div_mul_eq_mul_div, a, div_mul_div_comm]⟩
  have hs : ∀ z : N.X, p'.1.2.s z = g.s z * r ^ β.be y z := fun z => (div_mul_cancel _ _).symm
  have hp : p'.1.2 ^ j = (N.twist β u).io y := p'.2
  refine ⟨⟨(Multiplicative.ofAdd y, g), ?_⟩, rfl, rfl, hs⟩
  refine NumD.Gt.ext ?_ (funext fun z => ?_)
  · exact (g.pow_b j).trans ((N.twist β u).QT_pow_b p')
  · have a := pow_s_eq g p'.1.2 rfl z _ (hs z) j
    rw [hp, zpow_pow_comm, h] at a
    exact mul_right_cancel (a.symm.trans (N.twist_τ β u y z))
end

theorem labels_twist : ∀ (C : Type) [Field C] (N : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (k₀ : ℕ) (β : N.Form k₀) (u : Cˣ) (r : ℕ → Cˣ), Roots u r → Labels N EF ζ lab → ∀ p : ∀ k : ℕ, La → (N.twist β u).QT k, (∀ k, 0 < k → ∀ x, TwRel β u (r k) (lab k x) (p k x)) → Labels (N.twist β u) EF ζ p := by
  intro C _ N La _ EF ζ lab k₀ β u r hr ⟨h1, h2, h3, h4, h5⟩ p hp
  refine ⟨fun k hk a b => ?_, fun k hk a b => ?_, fun k hk q' => ?_, fun k m hk hm a q' e1 e2 => ?_, fun k hk a b => ?_⟩
  · exact (qEq_iff (hr.pow hk) (rel_mul (hp k hk a) (hp k hk b)) (hp k hk (a + b))).2 (h1 k hk a b)
  · exact (qEq_iff (hr.pow hk) (hp k hk a) (hp k hk b)).trans (h2 k hk a b)
  · obtain ⟨q, hq⟩ := rel_surj (hr.pow hk) q'
    obtain ⟨a, ha⟩ := h3 k hk q
    exact ⟨a, (qEq_iff (hr.pow hk) (hp k hk a) hq).2 ha⟩
  · obtain ⟨q, hq⟩ := rel_surj (hr.pow hk) q'
    have t := hp (k * m) (Nat.mul_pos hk hm) a
    have e : q.1.1 = (lab (k * m) a).1.1 := hq.1.symm.trans (e1.trans t.1)
    refine (qEq_iff (hr.pow hk) hq (hp k hk a)).2 (h4 k m hk hm a q e (NumD.Gt.ext ?_ (funext fun z => ?_)))
    · rw [← hq.2.1, e2, NumD.Gt.pow_b, NumD.Gt.pow_b, t.2.1]; rfl
    · have s := pow_s_eq _ _ t.2.1 z _ (t.2.2 z) m
      rw [← e2, hq.2.2, e, zpow_pow_comm, hr.2 k m hk hm] at s
      exact mul_right_cancel s
  · exact (wp_eq (hp k hk a) (hp k hk b)).trans (h5 k hk a b)

end GlobalTheory.TwistLabels
