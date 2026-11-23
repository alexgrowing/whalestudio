import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsDerAt0
import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsDualOf

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Num.FamEx PositivityTheory.HtPt.Sgp
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

theorem bcLin_apply {Ω C : Type} [Field Ω] [Field C] [Algebra Ω C] {m n : ℕ} (f : (Fin m → Ω) →ₗ[Ω] (Fin n → Ω))
    (x : Fin m → C) (k : Fin n) : TestPt.bcLin C f x k = ∑ i, algebraMap Ω C (f (Pi.single i 1) k) * x i := by
  simp only [TestPt.bcLin, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, LinearMap.toMatrix'_apply]
  try (refine Finset.sum_congr rfl fun i _ => ?_; congr 4; funext j; simp [Pi.single_apply])

theorem bcLin_bc {Ω C : Type} [Field Ω] [Field C] [Algebra Ω C] {m n : ℕ} (f : (Fin m → Ω) →ₗ[Ω] (Fin n → Ω))
    (x : Fin m → Ω) (k : Fin n) : TestPt.bcLin C f (fun i => algebraMap Ω C (x i)) k = algebraMap Ω C (f x k) := by
  rw [bcLin_apply]
  have h := congrFun (LinearMap.toMatrix'_mulVec f x) k
  rw [← h]
  simp [Matrix.mulVec, dotProduct, LinearMap.toMatrix'_apply, map_sum, map_mul]

theorem isUnit_of_val {O C : Type} [CommRing O] [Field C] [Algebra O C] {RC : Subalgebra O C} {v : Valuation C NNReal}
    (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) (a : RC) (ha : v (a : C) = 1) : IsUnit a := by
  have h0 : (a : C) ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact zero_ne_one ha
  have hi : (a : C)⁻¹ ∈ RC := (hv _).2 (by rw [map_inv₀, ha, inv_one])
  refine ⟨⟨a, ⟨_, hi⟩, ?_, ?_⟩, rfl⟩
  · ext
    simp [h0]
  · ext
    simp [h0]

theorem chi_cong {E : Type} [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {C : Type} [Field C] [Algebra O C] (RC : Subalgebra O C) (v : Valuation C NNReal) (hv : ∀ c, c ∈ RC ↔ v c ≤ 1)
    {F : Type} [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F)
    (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (hsec : IsSec pq sc)
    (σF : F →+* IsLocalRing.ResidueField O) (χ : F →*₀ C)
    (hχ : ∀ a (o : O), IsLocalRing.residue O o = σF a →
      χ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ a - algebraMap O C o) ≠ 1)
    (σ : 𝓞 E →+* RC)
    (hσ : ∀ a, ∃ o : O, algebraMap O C o = σ a ∧ IsLocalRing.residue O o = σF (pq (Ideal.Quotient.mk _ a))) :
    ∃ χ' : F → RC, (∀ a, χ a = χ' a) ∧ ∀ a, χ' (pq (Ideal.Quotient.mk _ a)) - σ a ∈ Ideal.span {(p : RC)} := by
  have hmem : ∀ a, χ a ∈ RC := by
    intro a
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (σF a)
    have h1 := (hχ a o ho).1
    have h2 : algebraMap O C o ∈ RC := RC.algebraMap_mem o
    simpa using RC.add_mem h1 h2
  refine ⟨fun a => ⟨χ a, hmem a⟩, fun a => rfl, ?_⟩
  intro a
  have hq2 : 1 < Fintype.card F := Fintype.one_lt_card
  obtain ⟨f, -, hq⟩ := FiniteField.card F p
  set x := pq (Ideal.Quotient.mk _ a) with hx
  set c0 : RC := ⟨χ x, hmem x⟩ with hc0
  set d : RC := c0 - σ a with hd
  have hdn : ¬ IsUnit d := by
    obtain ⟨o, ho1, ho2⟩ := hσ a
    rintro ⟨u, hu⟩
    apply (hχ x o ho2).2 (((u⁻¹ : RCˣ) : RC) : C) ((u⁻¹ : RCˣ) : RC).2
    have h3 : ((u⁻¹ : RCˣ) : RC) * d = 1 := by rw [← hu]; simp
    have h4 := congrArg (fun r : RC => (r : C)) h3
    simp only [hd, hc0, Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one] at h4
    rw [ho1]
    exact h4
  have hvd : v (d : C) < 1 := by
    refine lt_of_le_of_ne ((hv _).1 d.2) ?_
    intro h
    exact hdn (isUnit_of_val hv d h)
  by_cases hpu : IsUnit (p : RC)
  · rw [Ideal.span_singleton_eq_top.mpr hpu]
    trivial
  haveI : CharP (RC ⧸ Ideal.span {(p : RC)}) p := CharP.quotient RC p hpu
  have hσq : σ a ^ Fintype.card F - σ a ∈ Ideal.span {(p : RC)} := by
    obtain ⟨e', he'⟩ := Ideal.Quotient.mk_surjective (sc 1)
    have hker : (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 E)}) (a ^ Fintype.card F - a)) * sc 1 = 0 := by
      apply hsec.2
      simp [map_sub, map_pow, FiniteField.pow_card]
    rw [← he', ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hker
    obtain ⟨c, hc⟩ := hker
    have hσe : IsUnit (σ e') := by
      obtain ⟨o, ho1, ho2⟩ := hσ e'
      have hres : IsLocalRing.residue O o ≠ 0 := by
        rw [ho2, he', hsec.1, map_one]
        exact one_ne_zero
      have hu := (IsLocalRing.residue_ne_zero_iff_isUnit o).1 hres
      have h5 : σ e' = algebraMap O RC o := Subtype.ext (by rw [← ho1]; rfl)
      rw [h5]
      exact hu.map _
    obtain ⟨w, hw⟩ := hσe
    have h2 := congrArg σ hc
    simp only [map_mul, map_sub, map_pow, map_natCast] at h2
    have h6 : σ a ^ Fintype.card F - σ a = (p : RC) * (σ c * ↑w⁻¹) := by
      calc σ a ^ Fintype.card F - σ a = (σ a ^ Fintype.card F - σ a) * σ e' * ↑w⁻¹ := by
            rw [← hw, mul_assoc, Units.mul_inv, mul_one]
        _ = _ := by rw [h2, mul_assoc]
    rw [h6]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hχq : c0 ^ Fintype.card F = c0 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hc0]
    show χ x ^ Fintype.card F = χ x
    rw [← map_pow, FiniteField.pow_card]
  have key : ∀ y z : RC ⧸ Ideal.span {(p : RC)}, (y - z) ^ Fintype.card F = y ^ Fintype.card F - z ^ Fintype.card F := by
    intro y z
    rw [hq]
    exact sub_pow_char_pow y z f
  have hdq : d ^ Fintype.card F - d ∈ Ideal.span {(p : RC)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hσq ⊢
    rw [map_sub, map_pow] at hσq
    rw [map_sub, map_pow, hd, map_sub, key, ← map_pow, hχq, sub_eq_zero.mp hσq]
    ring
  have hunit : IsUnit (d ^ (Fintype.card F - 1) - 1) := by
    apply isUnit_of_val hv
    have h7 : ((d ^ (Fintype.card F - 1) - 1 : RC) : C) = (d : C) ^ (Fintype.card F - 1) - 1 := by
      push_cast
      rfl
    rw [h7, Valuation.map_sub_eq_of_lt_right, map_one]
    rw [map_one, map_pow]
    exact pow_lt_one₀ zero_le' hvd (by omega)
  obtain ⟨w, hw⟩ := hunit
  have e1 : d ^ Fintype.card F - d = d * (d ^ (Fintype.card F - 1) - 1) := by
    conv_lhs => rw [show Fintype.card F = (Fintype.card F - 1) + 1 by omega]
    ring
  have h8 : d = (d ^ Fintype.card F - d) * ↑w⁻¹ := by
    rw [e1, ← hw, mul_assoc, Units.mul_inv, mul_one]
  rw [h8]
  exact Ideal.mul_mem_right _ _ hdq

theorem gram_cong {E : Type} [Field E] [NumberField E] {R : Type} [CommRing R] {p Rr n : ℕ} [Fact p.Prime] (hRr : 1 ≤ Rr)
    (e : (Fin n → 𝓞 E) →+ (Fin n → 𝓞 E) →+ ZMod (p ^ Rr)) (alt : ∀ x, e x x = 0) (bar : 𝓞 E ≃+* 𝓞 E)
    (hbar : ∀ a, bar (bar a) = a) (hadj : ∀ a x y, e (a • x) y = e x (bar a • y)) (Eg : Matrix (Ix E n) (Ix E n) R)
    (hE : ∀ m m', Eg m m' - ((e (dl m) (dl m')).val : R) ∈ Ideal.span {(p : R)}) {σ' : 𝓞 E →+* R}
    {s : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → R} (hd : IsDualOf σ' s) (x' : Fin n → R) (m : Ix E n) :
    ∑ m', Eg m m' * (s m'.2 * x' m'.1) + σ' (bar (RingOfIntegers.basis E m.2)) * ∑ l, x' l * ∑ k, s k *
      ((e (Pi.single l (RingOfIntegers.basis E k)) (Pi.single m.1 1)).val : R) ∈ Ideal.span {(p : R)} := by
  by_cases hpu : IsUnit (p : R)
  · rw [Ideal.span_singleton_eq_top.mpr hpu]
    trivial
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p hpu
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : NeZero (p ^ Rr) := ⟨pow_ne_zero _ hp0⟩
  let mk := Ideal.Quotient.mk (Ideal.span {(p : R)})
  let φ : ZMod (p ^ Rr) →+* (R ⧸ Ideal.span {(p : R)}) := ZMod.castHom (dvd_pow_self p (by omega)) _
  have hφ : ∀ z : ZMod (p ^ Rr), mk (z.val : R) = φ z := by
    intro z
    show _ = ZMod.cast z
    rw [map_natCast, ZMod.cast_eq_val]
  have hskew : ∀ x y, e x y = - e y x := by
    intro x y
    have h := alt (x + y)
    simp only [map_add, AddMonoidHom.add_apply, alt x, alt y, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h)
  set B := RingOfIntegers.basis E with hB
  let L : Fin n → 𝓞 E →+ (R ⧸ Ideal.span {(p : R)}) := fun l =>
    φ.toAddMonoidHom.comp ((e.flip (Pi.single m.1 1)).comp (AddMonoidHom.single (fun _ => 𝓞 E) l))
  have hL : ∀ l c, L l c = φ (e (Pi.single l c) (Pi.single m.1 1)) := fun l c => rfl
  have hswap : ∀ l k, φ (e (dl m) (Pi.single l (B k))) = - L l (bar (B m.2) * B k) := by
    intro l k
    rw [hL, hskew, map_neg]
    congr 2
    have h1 : dl m = B m.2 • (Pi.single m.1 1 : Fin n → 𝓞 E) := by
      funext t
      by_cases h : t = m.1 <;> simp [dl, Pi.single_apply, h, hB]
    have h2 : (Pi.single l (bar (B m.2) * B k) : Fin n → 𝓞 E) = bar (B m.2) • (Pi.single l (B k) : Fin n → 𝓞 E) := by
      funext t
      by_cases h : t = l <;> simp [Pi.single_apply, h]
    rw [h1, h2, hadj, hbar]
  have hexp : ∀ l c, L l c = ∑ t, ((B.repr c t : ℤ) : R ⧸ Ideal.span {(p : R)}) * L l (B t) := by
    intro l c
    conv_lhs => rw [← B.sum_repr c]
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_zsmul, zsmul_eq_mul]
  have hdual : ∀ l, ∑ k, mk (s k) * L l (bar (B m.2) * B k) = mk (σ' (bar (B m.2))) * ∑ t, mk (s t) * L l (B t) := by
    intro l
    have hx : ∀ k, L l (bar (B m.2) * B k) = ∑ t, ((B.repr (bar (B m.2) * B k) t : ℤ) : R ⧸ Ideal.span {(p : R)}) * L l (B t) :=
      fun k => hexp l _
    simp only [hx, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h3 := congrArg mk (hd.2 (bar (B m.2)) t)
    simp only [map_mul, map_sum, map_intCast] at h3
    rw [← mul_assoc, h3, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hE' : ∀ m', mk (Eg m m') = φ (e (dl m) (dl m')) := by
    intro m'
    rw [← hφ]
    exact Ideal.Quotient.eq.mpr (hE m m')
  have hfirst : ∀ l, ∑ k, φ (e (dl m) (Pi.single l (B k))) * (mk (s k) * mk (x' l)) =
      - (mk (σ' (bar (B m.2))) * (mk (x' l) * ∑ k, mk (s k) * L l (B k))) := by
    intro l
    simp_rw [hswap l]
    calc ∑ k, -L l (bar (B m.2) * B k) * (mk (s k) * mk (x' l))
        = -(mk (x' l) * ∑ k, mk (s k) * L l (bar (B m.2) * B k)) := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = _ := by
          rw [hdual l]
          ring
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change mk _ = 0
  simp only [map_add, map_sum, map_mul, hE', hφ]
  rw [Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro l _
  change ∑ k, φ (e (dl m) (Pi.single l (B k))) * (mk (s k) * mk (x' l)) +
    mk (σ' (bar (B m.2))) * (mk (x' l) * ∑ k, mk (s k) * L l (B k)) = 0
  rw [hfirst l]
  exact neg_add_cancel _

section Chart

variable {E : Type} [Field E] [NumberField E] {O Ω C Li : Type} [CommRing O] [Field Ω] [Field C] [Algebra O Ω]
  [Algebra O C] [Algebra Ω C] [AddCommGroup Li] [Module Ω Li] {R : Subalgebra O Ω} {RC : Subalgebra O C}
  {hR : ∀ a ∈ R, algebraMap Ω C a ∈ RC} {cc : E ≃+* E} {p Rr n g : ℕ}
  (Dh : HT.HTChart R Ω cc p Rr n (Module.Dual Ω Li)) (ρ : 𝓞 E →+* Module.End Ω Li) (bar : 𝓞 E ≃+* 𝓞 E)
  (io : Dh.om →ₛₗ[toRC R RC hR] (Fin g → RC)) (ev : Li → ((Fin g → C) →ₗ[C] C))
  (Hm : Matrix (Fin g) (Ix E n) RC)

theorem ev_col (hRr : 1 ≤ Rr) (hact : ∀ a u, Dh.ρΩ a u = u ∘ₗ ρ (bar a))
    (hev : ∀ v (u : Dh.om), ev v (fun k => (io u k : C)) = algebraMap Ω C (u.1 v))
    (hH : ∀ m k, Hm k m - io ⟨Dh.h (dl m), Dh.h_mem _⟩ k ∈ Ideal.span {(p : RC)}) (m : Ix E n) :
    ∃ u : Fin g → RC, ∀ (V : Li) (t : Ω), ρ (bar (RingOfIntegers.basis E m.2)) V = t • V →
      ev V (fun j => (Hm j m : C)) =
        algebraMap Ω C (t * Dh.h (Pi.single m.1 1) V) + (p : C) * ev V fun j => (u j : C) := by
  choose w hw using fun k => Ideal.mem_span_singleton.1 (hH m k)
  obtain ⟨y, hy, hyeq⟩ := Dh.h_lin (RingOfIntegers.basis E m.2) (Pi.single m.1 1)
  refine ⟨fun k => w k + (p : RC) ^ (Rr - 1) * io ⟨y, hy⟩ k, ?_⟩
  intro V t hV
  have hdl : dl m = RingOfIntegers.basis E m.2 • (Pi.single m.1 1 : Fin n → 𝓞 E) := by
    funext j
    by_cases h : j = m.1 <;> simp [dl, Pi.single_apply, h]
  have hvec : (fun j => (Hm j m : C)) =
      (fun j => (io ⟨Dh.h (dl m), Dh.h_mem _⟩ j : C)) + (p : C) • (fun j => (w j : C)) := by
    funext j
    have h1 := congrArg (fun r : RC => (r : C)) (hw j)
    push_cast at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination h1
  have hvec2 : (fun j => ((w j + (p : RC) ^ (Rr - 1) * io ⟨y, hy⟩ j : RC) : C)) =
      (fun j => (w j : C)) + ((p : C) ^ (Rr - 1)) • (fun j => (io ⟨y, hy⟩ j : C)) := by
    funext j
    simp
  have hhV : Dh.h (dl m) V = t * Dh.h (Pi.single m.1 1) V + (p : Ω) ^ Rr * y V := by
    rw [hdl, hyeq]
    simp [hact, hV, nsmul_eq_mul]
  rw [hvec, hvec2, map_add, map_smul, map_add, map_smul, hev, hev, smul_eq_mul, smul_eq_mul, hhV]
  have hRr' : (p : C) ^ Rr = p * p ^ (Rr - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  simp only [map_add, map_mul, map_pow, map_natCast]
  rw [hRr']
  ring

theorem hq_chart (hRr : 1 ≤ Rr) (hact : ∀ a u, Dh.ρΩ a u = u ∘ₗ ρ (bar a))
    (hev : ∀ v (u : Dh.om), ev v (fun k => (io u k : C)) = algebraMap Ω C (u.1 v))
    (hH : ∀ m k, Hm k m - io ⟨Dh.h (dl m), Dh.h_mem _⟩ k ∈ Ideal.span {(p : RC)})
    (σ : E →+* Ω) (σ' : 𝓞 E →+* RC) (hσ : ∀ a, (σ' a : C) = algebraMap Ω C (σ a)) {s : ℕ} (vs : Fin s → Li)
    (hvs : ∀ a k, ρ (bar a) (vs k) = σ a • vs k) (m : Ix E n) :
    ∃ u : Fin g → RC, ∀ k, ev (vs k) (fun j => (Hm j m : C)) -
      TestPt.bcLin C (Fintype.linearCombination Ω fun (i : Fin n) (k : Fin s) => Dh.h (Pi.single i 1) (vs k))
        (fun i => ((Pm n σ' i m : RC) : C)) k = (p : C) * ev (vs k) fun j => (u j : C) := by
  obtain ⟨u, hu⟩ := ev_col Dh ρ bar io ev Hm hRr hact hev hH m
  refine ⟨u, fun k => ?_⟩
  rw [hu _ _ (hvs _ k), bcLin_apply, Finset.sum_eq_single m.1 (fun i _ hi => by simp [Pm, hi.symm]) (by simp)]
  simp [Pm, hσ, mul_comm]

theorem hdual_chart [Fact p.Prime] (hRr : 1 ≤ Rr) (hact : ∀ a u, Dh.ρΩ a u = u ∘ₗ ρ (bar a))
    (hev : ∀ v (u : Dh.om), ev v (fun k => (io u k : C)) = algebraMap Ω C (u.1 v))
    (hH : ∀ m k, Hm k m - io ⟨Dh.h (dl m), Dh.h_mem _⟩ k ∈ Ideal.span {(p : RC)})
    (hbar : ∀ a, bar (bar a) = a) (hadj : ∀ a x y, Dh.e (a • x) y = Dh.e x (bar a • y))
    (Eg : Matrix (Ix E n) (Ix E n) RC)
    (hE : ∀ m m', Eg m m' - ((Dh.e (dl m) (dl m')).val : RC) ∈ Ideal.span {(p : RC)})
    (σ : E →+* Ω) (σ' : 𝓞 E →+* RC) (hσ : ∀ a, (σ' a : C) = algebraMap Ω C (σ a))
    (s : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → RC) (hs : ∀ k, (s k : C) = algebraMap Ω C (σ (HT.dualInt E k)))
    (hd : IsDualOf σ' s) {r : ℕ} (b : Fin r → Li) (hb : ∀ a k, ρ a (b k) = σ a • b k)
    (v : Valuation C NNReal) (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) (w : C) (hw0 : w ≠ 0) (hw1 : v w ≤ 1)
    (hpw : v (p : C) ≤ v w * v w) (a : Fin r → Ω) (x : Fin n → Ω) (hx : ∀ l, x l ∈ R) {M : ℕ} (hM : 1 ≤ M)
    (hseq : ∀ j, ∃ z ∈ R, ∑ l, x l * Dh.gram σ 1 l j = Dh.h (Pi.single j 1) (∑ k, a k • b k) + (p : Ω) ^ M * z)
    (ha : ∀ u : Fin g → RC, ∑ k, (w * algebraMap Ω C (a k)) * ev (b k) (fun j => (u j : C)) ∈ RC) (m : Ix E n) :
    v (∑ m', (Eg m m' : C) * ((Jm n s).map (algebraMap RC C) *ᵥ fun l => algebraMap Ω C (x l)) m' +
      ∑ k, algebraMap Ω C (a k) * ev (b k) fun j => (Hm j m : C)) ≤ v w := by
  set Bj := RingOfIntegers.basis E m.2 with hBj
  let x' : Fin n → RC := fun l => toRC R RC hR ⟨x l, hx l⟩
  have hx' : ∀ l, (x' l : C) = algebraMap Ω C (x l) := fun l => rfl
  have hP1 := gram_cong hRr Dh.e Dh.alt bar hbar hadj Eg hE hd x' m
  obtain ⟨c1, hc1⟩ := Ideal.mem_span_singleton.1 hP1
  obtain ⟨u, hu⟩ := ev_col (Dh := Dh) (ρ := ρ) (bar := bar) (io := io) (ev := ev) (Hm := Hm) hRr hact hev hH m
  obtain ⟨z, hz, hzeq⟩ := hseq m.1
  set t : Ω := σ ((bar Bj : 𝓞 E) : E) with ht
  have hσ' : (σ' (bar Bj) : C) = algebraMap Ω C t := hσ _
  set S : C := ∑ k, algebraMap Ω C (a k) * ev (b k) (fun j => (u j : C)) with hS
  set G : C := ∑ l, algebraMap Ω C (x l) * ∑ k, (s k : C) *
    (((Dh.e (Pi.single l (RingOfIntegers.basis E k))) (Pi.single m.1 1)).val : C) with hGdef
  have hF1 : ∀ m', ((Jm n s).map (algebraMap RC C) *ᵥ fun l => algebraMap Ω C (x l)) m' =
      (s m'.2 : C) * algebraMap Ω C (x m'.1) := by
    intro m'
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Jm]
    rw [Finset.sum_eq_single m'.1]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · simp
  have hc1C : ∑ m', (Eg m m' : C) * ((s m'.2 : C) * algebraMap Ω C (x m'.1)) + (σ' (bar Bj) : C) * G =
      (p : C) * (c1 : C) := by
    have h1 := congrArg (fun r : RC => (r : C)) hc1
    push_cast at h1
    simpa [hx', hGdef] using h1
  have hG : G = algebraMap Ω C (∑ l, x l * Dh.gram σ 1 l m.1) := by
    simp only [hGdef, HT.HTChart.gram, map_one, one_mul, map_sum, map_mul, map_natCast, hs]
  have hzC : algebraMap Ω C (∑ l, x l * Dh.gram σ 1 l m.1) =
      algebraMap Ω C (Dh.h (Pi.single m.1 1) (∑ k, a k • b k)) + (p : C) ^ M * algebraMap Ω C z := by
    rw [hzeq, map_add, map_mul, map_pow, map_natCast]
  have hsec : ∑ k, algebraMap Ω C (a k) * ev (b k) (fun j => (Hm j m : C)) =
      algebraMap Ω C t * algebraMap Ω C (Dh.h (Pi.single m.1 1) (∑ k, a k • b k)) + (p : C) * S := by
    rw [Finset.sum_congr rfl fun k _ => by rw [hu (b k) t (hb _ k)]]
    simp only [hS, map_sum, map_smul, smul_eq_mul, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hT : ∑ m', (Eg m m' : C) * ((Jm n s).map (algebraMap RC C) *ᵥ fun l => algebraMap Ω C (x l)) m' +
      ∑ k, algebraMap Ω C (a k) * ev (b k) (fun j => (Hm j m : C)) =
      (p : C) * (c1 : C) - algebraMap Ω C t * ((p : C) ^ M * algebraMap Ω C z) + (p : C) * S := by
    simp only [hF1]
    rw [hsec]
    linear_combination hc1C - G * hσ' - algebraMap Ω C t * hG - algebraMap Ω C t * hzC
  rw [hT]
  have hvp : v (p : C) ≤ 1 := (hv _).1 (by simpa using (p : RC).2)
  have hvpw : v (p : C) ≤ v w := le_trans hpw (by
    calc v w * v w ≤ v w * 1 := by gcongr
      _ = v w := mul_one _)
  have hvc : v (c1 : C) ≤ 1 := (hv _).1 c1.2
  have hvt : v (algebraMap Ω C t) ≤ 1 := by
    rw [← hσ']
    exact (hv _).1 (σ' (bar Bj)).2
  have hvz : v (algebraMap Ω C z) ≤ 1 := (hv _).1 (hR z hz)
  have hwS : v w * v S ≤ 1 := by
    rw [← map_mul]
    apply (hv _).1
    have h2 := ha u
    convert h2 using 1
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  apply Valuation.map_add_le
  · apply Valuation.map_sub_le
    · rw [map_mul]
      calc v (p : C) * v (c1 : C) ≤ v (p : C) * 1 := by gcongr
        _ ≤ v w := by rw [mul_one]; exact hvpw
    · rw [map_mul, map_mul, map_pow]
      calc v (algebraMap Ω C t) * (v (p : C) ^ M * v (algebraMap Ω C z)) ≤ 1 * (v (p : C) ^ M * 1) := by
            gcongr
        _ = v (p : C) ^ M := by ring
        _ ≤ v (p : C) := pow_le_of_le_one zero_le' hvp (by omega)
        _ ≤ v w := hvpw
  · rw [map_mul]
    calc v (p : C) * v S ≤ (v w * v w) * v S := by gcongr
      _ = v w * (v w * v S) := by ring
      _ ≤ v w * 1 := by gcongr
      _ = v w := mul_one _

end Chart

end PositivityTheory.Xgn.TestGroupPoint
