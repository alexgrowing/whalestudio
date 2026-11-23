import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
namespace GlobalTheory.Ex
namespace NumD
variable {O : Type} [CommRing O] (N : NumD O)

theorem Form.div_add_left {N : NumD O} {k : ℕ} (β : N.Form k) {j : ℕ} (hj : j ∣ k) (x y z : N.X) :
    β.be (x + y) z / j = β.be x z / j + β.be y z / j := by
  rw [β.symm, β.div_add hj, β.symm z, β.symm z]

theorem Form.div_add_nsmul {N : NumD O} {k : ℕ} (β : N.Form k) {j : ℕ} (hj : j ∣ k) (x y z : N.X) :
    β.be (x + j • y) z / j = β.be x z / j + β.be y z := by
  rcases eq_or_ne j 0 with rfl | h
  · obtain rfl : k = 0 := Nat.eq_zero_of_zero_dvd hj
    have h0 : β.be y z = 0 := by simpa using β.dvd y z
    simp [h0]
  · rw [β.div_add_left hj, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul,
      Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.2 h)]

theorem Form.div_nsmul {N : NumD O} {k : ℕ} (β : N.Form k) {j : ℕ} (hj : j ∣ k) (m : ℕ) (x y : N.X) :
    β.be x (m • y) / j = β.be x y / j * m := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_nsmul, β.div_add hj, ih]; push_cast; ring

theorem Form.exp_count {N : NumD O} {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ^ 2 ∣ k) (ho : Odd m) (y χ : N.X) :
    β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2) =
      β.be y y / 2 - β.be y y / (m ^ 2 : ℕ) * ((m ^ 2 - 1) / 2 : ℕ) + β.be χ χ / 2 + β.be y χ / (m ^ 2 : ℕ) * m := by
  have hd : ∀ x z, (2 * (m : ℤ) ^ 2) ∣ β.be x z := fun x z =>
    (mul_dvd_mul_left 2 (by exact_mod_cast hm)).trans (β.dvd x z)
  obtain ⟨a, ha⟩ := hd y y
  obtain ⟨b, hb⟩ := hd y χ
  obtain ⟨c, hc⟩ := hd χ χ
  obtain ⟨t, ht⟩ := ho.pow (n := 2)
  have hm0 : (m : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ (Int.natCast_ne_zero.2 ho.pos.ne')
  have h1 : (m ^ 2 - 1) / 2 = t := by omega
  have h2 : (m : ℤ) ^ 2 = 2 * t + 1 := by exact_mod_cast ht
  have e : β.be (y + m • χ) (y + m • χ) = 2 * m ^ 2 * (a + 2 * m * b + m ^ 2 * c) := by
    simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, β.symm χ y, ha, hb, hc]
    ring
  have d1 : ∀ x : ℤ, 2 * (m : ℤ) ^ 2 * x / 2 = m ^ 2 * x := fun x => by
    rw [mul_assoc, Int.mul_ediv_cancel_left _ two_ne_zero]
  have d2 : ∀ x : ℤ, 2 * (m : ℤ) ^ 2 * x / (m ^ 2 : ℕ) = 2 * x := fun x => by
    rw [Nat.cast_pow, mul_right_comm, Int.mul_ediv_cancel _ hm0]
  rw [e, h1, ha, hb, hc, d1, d1, d2, d2, Int.mul_ediv_cancel_left _ (mul_ne_zero two_ne_zero hm0)]
  linear_combination (-a) * h2

theorem twist_wQ {k : ℕ} (β : N.Form k) (u : Oˣ) {j : ℕ} (hj : j ∣ k) (p : N.QT j) :
    (N.twist β u).wQ (N.twQ β u hj p) =
      u ^ (β.be p.1.1.toAdd p.1.1.toAdd / 2 - β.be p.1.1.toAdd p.1.1.toAdd / j * ((j - 1) / 2 : ℕ)) * N.wQ p := by
  show N.ψ p.1.1.toAdd * u ^ (β.be p.1.1.toAdd p.1.1.toAdd / 2) * mulq N.θ N.σ j p.1.2.b /
      (p.1.2.s p.1.1.toAdd * u ^ (β.be p.1.1.toAdd p.1.1.toAdd / j) * cubN N.θ j 1 p.1.2.b p.1.2.b /
        dbl N.θ N.σ p.1.2.b ^ j) ^ ((j - 1) / 2) = _ * (N.ψ p.1.1.toAdd * mulq N.θ N.σ j p.1.2.b /
      (p.1.2.s p.1.1.toAdd * cubN N.θ j 1 p.1.2.b p.1.2.b / dbl N.θ N.σ p.1.2.b ^ j) ^ ((j - 1) / 2))
  rw [zpow_sub, zpow_mul, zpow_natCast, mul_right_comm (p.1.2.s _), mul_div_right_comm _ (u ^ _), mul_pow]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel

theorem twist_vt {k : ℕ} (β : N.Form k) (u : Oˣ) (g : N.Gt) (l : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b)
    (m : ℕ) (χ : N.X) :
    (N.twist β u).vt (N.twG β u g l hl ^ m) χ = (u ^ (β.be χ χ / 2 + l χ * m) : Oˣ) * N.vt (g ^ m) χ := by
  obtain ⟨h1, h2⟩ := N.twG_pow β u g l hl m
  show ((N.ψ χ * u ^ (β.be χ χ / 2) * (N.twG β u g l hl ^ m).s χ : Oˣ) : O) *
    N.th (N.c χ * (show N.A from (N.twG β u g l hl ^ m).b)) = _ * (((N.ψ χ * (g ^ m).s χ : Oˣ) : O) * N.th (N.c χ * (g ^ m).b))
  rw [h1, h2, ← mul_assoc (_ : O), ← Units.val_mul, zpow_add]
  congr 2
  apply Additive.ofMul.injective
  simp only [ofMul_mul]; abel

theorem twG_mul {k : ℕ} (β : N.Form k) (u : Oˣ) (g g' : N.Gt) (l l' : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b)
    (hl' : ∀ a b, l' (a + b) = l' a + l' b) :
    N.twG β u g l hl * N.twG β u g' l' hl' =
      N.twG β u (g * g') (fun z => l z + l' z) (fun a b => by rw [hl, hl']; ring) := by
  refine NumD.Gt.ext rfl (funext fun (z : N.X) => ?_)
  show g.s z * u ^ l z * (g'.s z * u ^ l' z) / N.θ (N.c z) g.b g'.b =
    g.s z * g'.s z / N.θ (N.c z) g.b g'.b * u ^ (l z + l' z)
  rw [zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem twG_congr {k : ℕ} (β : N.Form k) (u : Oˣ) (g : N.Gt) (l l' : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b)
    (hl' : ∀ a b, l' (a + b) = l' a + l' b) (h : ∀ z, l z = l' z) : N.twG β u g l hl = N.twG β u g l' hl' := by
  obtain rfl : l = l' := funext h
  rfl

theorem twG_inj {k : ℕ} (β : N.Form k) (u : Oˣ) (g g' : N.Gt) (l : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b)
    (h : N.twG β u g l hl = N.twG β u g' l hl) : g = g' :=
  NumD.Gt.ext (congrArg (fun x : (N.twist β u).Gt => x.b) h)
    (funext fun z => mul_right_cancel (congrArg (fun x : (N.twist β u).Gt => x.s z) h))

theorem twist_io {k : ℕ} (β : N.Form k) (u : Oˣ) (y : N.X) :
    (N.twist β u).io y = N.twG β u (N.io y) (fun z => β.be y z) (fun a b => map_add _ a b) :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => N.twist_τ β u y z)

theorem twist_txT {k : ℕ} (β : N.Form k) (u : Oˣ) (m : ℕ) (hm : m ^ 2 ∣ k) (ho : Odd m) (p : N.QT (m ^ 2)) (χ : N.X) :
    (N.twist β u).txT m (N.twQ β u hm p) χ =
      (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2)) : Oˣ) * N.txT m p χ := by
  show (((N.twist β u).wQ (N.twQ β u hm p) / mulq N.θ N.σ m p.1.2.b : Oˣ) : O) *
    (N.twist β u).vt (N.twG β u p.1.2 _ (β.div_add hm p.1.1.toAdd) ^ m) χ =
      _ * (((N.wQ p / mulq N.θ N.σ m p.1.2.b : Oˣ) : O) * N.vt (p.1.2 ^ m) χ)
  rw [twist_wQ, twist_vt, β.exp_count hm ho, ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul]
  congr 2
  simp only [zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem twist_evT {k : ℕ} (β : N.Form k) (u : Oˣ) (m : ℕ) (hm : m ^ 2 ∣ k) (ho : Odd m) (p : N.QT (m ^ 2)) (χ : N.X)
    {j : ℕ} (hj : j ∣ k) (q : N.QT j) :
    (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 χ =
      (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2) +
        β.be q.1.1.toAdd (p.1.1.toAdd + m • χ) / j) : Oˣ) * N.evT m p q.1.2 χ := by
  show ((q.1.2.s p.1.1.toAdd * u ^ (β.be q.1.1.toAdd p.1.1.toAdd / j) * cubN N.θ (m ^ 2) 1 p.1.2.b q.1.2.b *
    (N.twist β u).wQ (N.twQ β u hm p) / mulq N.θ N.σ m (q.1.2.b * p.1.2.b) : Oˣ) : O) *
    (N.twist β u).vt ((N.twG β u q.1.2 _ (β.div_add hj q.1.1.toAdd) *
      N.twG β u p.1.2 _ (β.div_add hm p.1.1.toAdd)) ^ m) χ =
      _ * (((q.1.2.s p.1.1.toAdd * cubN N.θ (m ^ 2) 1 p.1.2.b q.1.2.b *
        N.wQ p / mulq N.θ N.σ m (q.1.2.b * p.1.2.b) : Oˣ) : O) * N.vt ((q.1.2 * p.1.2) ^ m) χ)
  rw [twG_mul, twist_wQ, twist_vt, β.exp_count hm ho, β.div_add hj, β.div_nsmul hj, ← mul_assoc (_ : O), ← mul_assoc (_ : O),
    ← Units.val_mul, ← Units.val_mul]
  congr 2
  simp only [add_mul, zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem twist_wp {k : ℕ} (β : N.Form k) (u : Oˣ) {j : ℕ} (hj : j ∣ k) (q q' : N.QT j) :
    (N.twist β u).wp (N.twQ β u hj q) (N.twQ β u hj q') = N.wp q q' := by
  show q.1.2.s q'.1.1.toAdd * u ^ (β.be q.1.1.toAdd q'.1.1.toAdd / j) * cubN N.θ j 1 q'.1.2.b q.1.2.b /
    (q'.1.2.s q.1.1.toAdd * u ^ (β.be q'.1.1.toAdd q.1.1.toAdd / j) * cubN N.θ j 1 q.1.2.b q'.1.2.b) =
    q.1.2.s q'.1.1.toAdd * cubN N.θ j 1 q'.1.2.b q.1.2.b / (q'.1.2.s q.1.1.toAdd * cubN N.θ j 1 q.1.2.b q'.1.2.b)
  rw [β.symm q'.1.1.toAdd]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem twQ_mul {k : ℕ} (β : N.Form k) (u : Oˣ) {j : ℕ} (hj : j ∣ k) (q q' : N.QT j) :
    N.twQ β u hj (q * q') = N.twQ β u hj q * N.twQ β u hj q' := by
  refine Subtype.ext (Prod.ext rfl ?_)
  show N.twG β u (q.1.2 * q'.1.2) _ (β.div_add hj (q.1.1.toAdd + q'.1.1.toAdd)) =
    N.twG β u q.1.2 _ (β.div_add hj q.1.1.toAdd) * N.twG β u q'.1.2 _ (β.div_add hj q'.1.1.toAdd)
  rw [twG_mul]
  exact N.twG_congr β u _ _ _ _ _ fun z => β.div_add_left hj _ _ z

theorem twist_qEq {k : ℕ} (β : N.Form k) (u : Oˣ) {j : ℕ} (hj : j ∣ k) (q q' : N.QT j) :
    N.QEq q q' ↔ (N.twist β u).QEq (N.twQ β u hj q) (N.twQ β u hj q') := by
  refine exists_congr fun (z : N.X) => and_congr_right fun (h : q'.1.1.toAdd = q.1.1.toAdd + j • z) => ?_
  show _ ↔ N.twG β u q'.1.2 _ (β.div_add hj q'.1.1.toAdd) =
    N.twG β u q.1.2 _ (β.div_add hj q.1.1.toAdd) * (N.twist β u).io z
  rw [twist_io, twG_mul, ← N.twG_congr β u (q.1.2 * N.io z) (fun x => β.be q'.1.1.toAdd x / j)
    (fun x => β.be q.1.1.toAdd x / j + β.be z x) (β.div_add hj q'.1.1.toAdd) _
    fun x => by rw [h, β.div_add_nsmul hj]]
  exact ⟨fun e => by rw [e], N.twG_inj β u _ _ _ _⟩

end NumD

theorem twist_terms : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ) (β : N.Form k) (u : Oˣ) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (p : N.QT (m ^ 2)) (χ : N.X), (N.twist β u).txT m (N.twQ β u hm p) χ = (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2)) : Oˣ) * N.txT m p χ ∧ (∀ (j : ℕ) (hj : j ∣ k) (q : N.QT j), j ≠ 0 → (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 χ = (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2) + β.be q.1.1.toAdd (p.1.1.toAdd + m • χ) / j) : Oˣ) * N.evT m p q.1.2 χ) ∧ ∀ (j : ℕ) (hj : j ∣ k) (q q' : N.QT j), (N.twist β u).wp (N.twQ β u hj q) (N.twQ β u hj q') = N.wp q q' ∧ N.twQ β u hj (q * q') = N.twQ β u hj q * N.twQ β u hj q' ∧ (N.QEq q q' ↔ (N.twist β u).QEq (N.twQ β u hj q) (N.twQ β u hj q')) :=
  fun _ _ N _ β u m hm ho p χ => ⟨N.twist_txT β u m hm ho p χ, fun _ hj q _ => N.twist_evT β u m hm ho p χ hj q,
    fun _ hj q q' => ⟨N.twist_wp β u hj q q', N.twQ_mul β u hj q q', N.twist_qEq β u hj q q'⟩⟩
end GlobalTheory.Ex
