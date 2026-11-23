import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.HeckeVal

section Abstract

variable {E A : Type} [Field E] [NumberField E] [CommRing A] (ι : E →+* A) (S : Subring A)

theorem exists_pow_eq_mul (hint : ∀ e, IsIntegral ℤ e → ι e ∈ S)
    (hden : ∀ x : A, ∃ n : ℕ, 0 < n ∧ (n : A) * x ∈ S)
    (happ : ∀ n : ℕ, 0 < n → ∀ s ∈ S, ∃ r, IsIntegral ℤ r ∧ ∃ w ∈ S, s = ι r + (n : A) * w)
    (x : Aˣ) : ∃ (h : ℕ) (b : Eˣ) (u : Aˣ), 0 < h ∧ (u : A) ∈ S ∧ ((u⁻¹ : Aˣ) : A) ∈ S ∧
      x ^ h = Units.map ι.toMonoidHom b * u := by
  obtain ⟨n, hn, hnx⟩ := hden x
  obtain ⟨m, hm, hmx⟩ := hden ((x⁻¹ : Aˣ) : A)
  let φ : 𝓞 E →+* S := (ι.comp (algebraMap (𝓞 E) E)).codRestrict S
    (fun r => hint _ r.isIntegral_coe)
  let z : S := ⟨_, hnx⟩
  let I : Ideal (𝓞 E) := (Ideal.span {z}).comap φ
  have hMz : ((m * n : ℕ) : S) ∈ Ideal.span {z} := by
    refine Ideal.mem_span_singleton'.2 ⟨⟨_, hmx⟩, Subtype.ext ?_⟩
    show (m : A) * ((x⁻¹ : Aˣ) : A) * ((n : A) * x) = (((m * n : ℕ) : S) : A)
    have := x.inv_mul
    push_cast
    linear_combination (m : A) * n * this
  have hMI : ((m * n : ℕ) : 𝓞 E) ∈ I := by
    show φ _ ∈ Ideal.span {z}
    rwa [map_natCast]
  have hI : I ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hMI
    exact (Nat.cast_ne_zero.2 (Nat.mul_pos hm hn).ne') hMI
  have hmap : I.map φ = Ideal.span {z} := by
    refine le_antisymm Ideal.map_comap_le ?_
    rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨r, hr, w, hw, e⟩ := happ (m * n) (Nat.mul_pos hm hn) _ hnx
    have e' : z = φ ⟨r, hr⟩ + ((m * n : ℕ) : S) * ⟨w, hw⟩ := Subtype.ext (by
      show (n : A) * x = ι r + (((m * n : ℕ) : S) : A) * w
      rw [e]; simp)
    have hrI : (⟨r, hr⟩ : 𝓞 E) ∈ I := by
      show φ _ ∈ Ideal.span {z}
      rw [show φ ⟨r, hr⟩ = z - ((m * n : ℕ) : S) * ⟨w, hw⟩ by rw [e']; ring]
      exact sub_mem (Ideal.mem_span_singleton_self z) (Ideal.mul_mem_right _ _ hMz)
    rw [e']
    refine add_mem (Ideal.mem_map_of_mem _ hrI) (Ideal.mul_mem_right _ _ ?_)
    have := Ideal.mem_map_of_mem φ hMI
    rwa [map_natCast] at this
  have hI0 : I ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero hI
  set h := Fintype.card (ClassGroup (𝓞 E)) with hh
  have h1 : ClassGroup.mk0 ((⟨I, hI0⟩ : nonZeroDivisors (Ideal (𝓞 E))) ^ h) = 1 := by
    rw [map_pow, pow_card_eq_one]
  obtain ⟨s, hs⟩ : (I ^ h).IsPrincipal := (ClassGroup.mk0_eq_one_iff (pow_mem hI0 h)).1 h1
  have hs' : I ^ h = Ideal.span {s} := hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact pow_ne_zero h hI (by rw [hs']; simp)
  have hsp : Ideal.span {z ^ h} = Ideal.span {φ s} := by
    rw [← Ideal.span_singleton_pow, ← hmap, ← Ideal.map_pow, hs', Ideal.map_span,
      Set.image_singleton]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (hsp ▸ Ideal.mem_span_singleton_self (z ^ h))
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 (hsp.symm ▸ Ideal.mem_span_singleton_self (φ s))
  have ha1 : (a : A) * ι s = ((n : A) * x) ^ h := congrArg Subtype.val ha
  have ha2 : (a' : A) * ((n : A) * x) ^ h = ι s := congrArg Subtype.val ha'
  have hnE : (n : E) ^ h ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hn.ne')
  have hsE : (s : E) ≠ 0 := by simpa using hs0
  have hnu : IsUnit ((n : A) ^ h) := by
    have := (IsUnit.mk0 _ hnE).map ι
    simpa using this
  let b : Eˣ := Units.mk0 ((s : E) / (n : E) ^ h) (div_ne_zero hsE hnE)
  have hb : ι s = (n : A) ^ h * ι b := by
    have : (s : E) = (n : E) ^ h * (b : E) := by
      simp only [b, Units.val_mk0]; field_simp
    rw [this]; simp
  let B : Aˣ := Units.map ι.toMonoidHom b
  have hB : (B : A) = ι b := rfl
  have e1 : ((x ^ h : Aˣ) : A) = B * a := by
    apply hnu.mul_left_cancel
    rw [hB, Units.val_pow_eq_pow_val, ← mul_pow, ← ha1, hb]; ring
  have e2 : (B : A) = ((x ^ h : Aˣ) : A) * a' := by
    apply hnu.mul_left_cancel
    rw [hB, ← hb, Units.val_pow_eq_pow_val, ← ha2]; ring
  refine ⟨h, b, B⁻¹ * x ^ h, Fintype.card_pos, ?_, ?_, by simp [B]⟩
  · rw [Units.val_mul, e1, ← mul_assoc, Units.inv_mul, one_mul]; exact a.2
  · rw [mul_inv_rev, inv_inv, Units.val_mul, e2, ← mul_assoc, Units.inv_mul, one_mul]; exact a'.2

theorem exists_pow_sub_one (m : ℕ) (hfin : Finite (S ⧸ Ideal.span {(m : S)})) (u : Aˣ)
    (hu : (u : A) ∈ S) (hu' : ((u⁻¹ : Aˣ) : A) ∈ S) :
    ∃ k : ℕ, 0 < k ∧ ∃ s ∈ S, ((u ^ k : Aˣ) : A) - 1 = (m : A) * s := by
  let v : Sˣ := ⟨⟨_, hu⟩, ⟨_, hu'⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩
  let w := Units.map (Ideal.Quotient.mk (Ideal.span {(m : S)})).toMonoidHom v
  obtain ⟨k, hk, e⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite w)
  have e' : Ideal.Quotient.mk (Ideal.span {(m : S)}) ((v : S) ^ k) =
      Ideal.Quotient.mk (Ideal.span {(m : S)}) 1 := by
    have := congrArg Units.val e
    rw [map_pow, map_one]
    simpa [w] using this
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 e')
  refine ⟨k, hk, s, s.2, ?_⟩
  have := congrArg Subtype.val hs
  simp only [v] at this
  push_cast at this ⊢
  rw [← this, mul_comm]

theorem exists_coprime_denom (p : ℕ) (hp : p.Prime)
    (hden : ∀ x : A, ∃ n : ℕ, 0 < n ∧ (n : A) * x ∈ S) (w : Aˣ)
    (hw : ∀ k : ℕ, ∃ m : ℕ, 0 < m ∧ Nat.Coprime m p ∧ ∃ s ∈ S,
      (m : A) * ((w : A) - 1) = (p : A) ^ k * s) :
    (∃ M : ℕ, M.Coprime p ∧ (M : A) * w ∈ S) ∧
      ∃ M : ℕ, M.Coprime p ∧ (M : A) * ((w⁻¹ : Aˣ) : A) ∈ S := by
  constructor
  · obtain ⟨m, -, hm, s, hs, e⟩ := hw 0
    refine ⟨m, hm, ?_⟩
    rw [show (m : A) * w = m + s by linear_combination e]
    exact add_mem (natCast_mem S m) hs
  · obtain ⟨n, hn, hnw⟩ := hden ((w⁻¹ : Aˣ) : A)
    obtain ⟨k, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.ne_one
    obtain ⟨m, -, hm, s, hs, e⟩ := hw k
    refine ⟨m * n', Nat.Coprime.mul_left hm ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').symm, ?_⟩
    have h1 := w.mul_inv
    rw [show ((m * n' : ℕ) : A) * ((w⁻¹ : Aˣ) : A) =
      ((m * n' : ℕ) : A) - s * (((p ^ k * n' : ℕ) : A) * ((w⁻¹ : Aˣ) : A)) by
        push_cast
        linear_combination (-(n' : A) * ((w⁻¹ : Aˣ) : A)) * e + (m : A) * n' * h1]
    exact sub_mem (natCast_mem S _) (mul_mem hs hnw)

end Abstract

theorem root_value {E T : Type} [Field E] [NumberField E] [IsCMField E] [Fintype T]
    (emb : T → E →+* ℂ) (n : T → ℤ) (b : Eˣ) (z : ℂ) (K : ℕ) (hK : 0 < K)
    (h : z ^ K * ∏ τ, (emb τ (b : E) / (‖emb τ (b : E)‖ : ℂ)) ^ (n τ) = 1) :
    ∃ hz : z ∈ Qbar, ∀ (L : Type) [NormedField L] (ψ : Qbar →+* L),
      (∀ τ : E →+* Qbar, ‖ψ (τ b)‖ = ‖ψ (τ (IsCMField.complexConj E b))‖) → ‖ψ ⟨z, hz⟩‖ = 1 := by
  have hmem : ∀ (t : T) (e : E), emb t e ∈ Qbar := fun t e => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) e).algHom (emb t).toRatAlgHom
  let τ' : T → E →+* Qbar := fun t => (emb t).codRestrict Qbar (hmem t)
  let w : Qbar := ∏ t, (τ' t b / τ' t (IsCMField.complexConj E b)) ^ (n t)
  have hw : (w : ℂ) = (∏ τ, (emb τ (b : E) / (‖emb τ (b : E)‖ : ℂ)) ^ (n τ)) ^ 2 := by
    have : (w : ℂ) = algebraMap Qbar ℂ w := rfl
    rw [this, map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [map_zpow₀, map_div₀, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    congr 1
    show emb t b / emb t (IsCMField.complexConj E b) = _
    have h0 : emb t b ≠ 0 := (map_ne_zero _).2 b.ne_zero
    rw [IsCMField.complexEmbedding_complexConj, div_pow, ← Complex.mul_conj', pow_two,
      mul_div_mul_left _ _ h0]
  have h2 : z ^ (K * 2) * w = 1 := by
    rw [hw, pow_mul, ← mul_pow, h, one_pow]
  have hK2 : 0 < K * 2 := by omega
  have hz : z ∈ Qbar := by
    rw [mem_algebraicClosure_iff]
    refine IsAlgebraic.of_pow hK2 ?_
    rw [eq_inv_of_mul_eq_one_left h2]
    exact mem_algebraicClosure_iff.1 (inv_mem w.2)
  refine ⟨hz, fun L _ ψ hψ => ?_⟩
  have h3 : (⟨z, hz⟩ : Qbar) ^ (K * 2) * w = 1 := Subtype.ext h2
  have h4 : ‖ψ w‖ = 1 := by
    simp only [w, map_prod, norm_prod, map_zpow₀, norm_zpow, map_div₀, norm_div]
    refine Finset.prod_eq_one fun t _ => ?_
    have h0 : ‖ψ (τ' t b)‖ ≠ 0 :=
      norm_ne_zero_iff.2 ((map_ne_zero _).2 ((map_ne_zero _).2 b.ne_zero))
    rw [← hψ, div_self h0, one_zpow]
  have h5 := congrArg (fun t => ‖ψ t‖) h3
  simp only [map_mul, map_pow, norm_mul, norm_pow, h4, mul_one, map_one, norm_one] at h5
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hK2.ne').1 h5

theorem norm_natCast_eq_one {p : ℕ} [Fact p.Prime] {M : ℕ} (hM : M.Coprime p) :
    ‖(M : ℂ_[p])‖ = 1 := by
  have h := (Padic.norm_natCast_eq_one_iff (p := p)).2 hM.symm
  rw [← h, ← norm_algebraMap' ℂ_[p] (M : ℚ_[p]), map_natCast]

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_le_one_of_denom {E : Type} [Field E] {p : ℕ} [Fact p.Prime] (ψ : E →+* ℂ_[p]) {M : ℕ}
    (hM : M.Coprime p) {b : E} (hb : IsIntegral ℤ ((M : E) * b)) : ‖ψ b‖ ≤ 1 := by
  have h' := norm_le_one_of_isIntegral (map_isIntegral_int ψ hb)
  rwa [map_mul, map_natCast, norm_mul, norm_natCast_eq_one hM, one_mul] at h'

section Adelic

variable (D : D7)

theorem levelC_natCast (n : ℕ) : Formalism.UG.P.levelafC D.host.E (n : 𝓞 ℚ) = (n : AE D) := by
  rw [← Formalism.UG.P.adelstab_incl_C, map_natCast, map_natCast]

theorem inc_mem_iff (e : D.host.E) : inc D e ∈ OhE D ↔ IsIntegral ℤ e :=
  ⟨Formalism.UG.P.csGlob_int e, Formalism.UG.P.adelstabL_incl_int e⟩

theorem exists_denom (x : AE D) : ∃ n : ℕ, 0 < n ∧ (n : AE D) * x ∈ OhE D := by
  obtain ⟨d, hd, hx⟩ := Formalism.UG.P.levelaf_denom x
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨Ideal.absNorm (Ideal.span {d}), Nat.pos_of_ne_zero ?_, ?_⟩
  · simpa [Ideal.absNorm_eq_zero_iff] using hd
  · rw [← levelC_natCast, ← hc, Formalism.UG.P.levelafC_mul, mul_assoc]
    exact mul_mem (Formalism.UG.P.levelafC_mem c) hx

theorem exists_approx (n : ℕ) (hn : 0 < n) (s : AE D) (hs : s ∈ OhE D) :
    ∃ r, IsIntegral ℤ r ∧ ∃ w ∈ OhE D, s = inc D r + (n : AE D) * w := by
  rw [← levelC_natCast]
  exact Formalism.UG.P.csSpan_approx Formalism.UG.P.csGlob_intAdApprox (n : 𝓞 ℚ)
    (Nat.cast_ne_zero.2 hn.ne') hs

theorem finite_quot (m : ℕ) (hm : 0 < m) : Finite (OhE D ⧸ Ideal.span {(m : OhE D)}) :=
  Formalism.UG.P.levelaf_finite_quot (m : 𝓞 ℚ) (Nat.cast_ne_zero.2 hm.ne') (m : OhE D)
    (by rw [levelC_natCast]; simp)

variable {D} {N : ℕ} (χ : HeckeU D N)

theorem finite_order (u : (AE D)ˣ) (hu : IntU D u) : ∃ m : ℕ, 0 < m ∧ χ.f u ^ m = 1 := by
  obtain ⟨m, hm, hc⟩ := χ.cont
  obtain ⟨k, hk, hs⟩ := exists_pow_sub_one (OhE D) m (finite_quot D m hm) u hu.1 hu.2
  refine ⟨k, hk, ?_⟩
  rw [← map_pow]
  refine hc _ ⟨?_, ?_⟩ hs
  · rw [Units.val_pow_eq_pow_val]; exact pow_mem hu.1 _
  · rw [← inv_pow, Units.val_pow_eq_pow_val]; exact pow_mem hu.2 _

end Adelic

theorem hecke_values : ∀ (D : D7) (N : ℕ) (χ : HeckeU D N) (x : (AE D)ˣ), Mod1All ((χ.f x : ℂˣ) : ℂ) ∧ (IntU D x → ∃ m : ℕ, 0 < m ∧ χ.f x ^ m = 1) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), (∃ y : (AE D)ˣ, IntU D y ∧ ZeroAt D p (((x * y : (AE D)ˣ) : AE D) - 1)) → ‖lamC lam ((χ.f x : ℂˣ) : ℂ)‖ = 1 := by
  intro D N χ x
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨h, b, u, hh, hu, hu', e⟩ := exists_pow_eq_mul (inc D) (OhE D)
    (fun e he => (inc_mem_iff D e).2 he) (exists_denom D) (exists_approx D) x
  obtain ⟨k, hk, hk1⟩ := finite_order χ u ⟨hu, hu'⟩
  have e1 : χ.f x ^ (h * k) = χ.f (Units.map (inc D).toMonoidHom (b ^ k)) := by
    rw [pow_mul, ← map_pow, e, map_mul, mul_pow, hk1, mul_one, map_pow, map_pow]
  have e2 := χ.aut (b ^ k)
  rw [← e1, Units.val_pow_eq_pow_val] at e2
  obtain ⟨hz, H⟩ := root_value (embT D) χ.n (b ^ k) _ (h * k) (Nat.mul_pos hh hk) e2
  refine ⟨⟨hz, fun σ => H ℂ σ fun τ => ?_⟩, finite_order χ x, ?_⟩
  · have := IsCMField.complexEmbedding_complexConj D.host.E (σ.comp τ) (b ^ k : D.host.Eˣ)
    simp only [RingHom.comp_apply] at this
    rw [this, Complex.norm_conj]
  · rintro p hp lam ⟨y, hy, hxy⟩
    obtain ⟨⟨M, hM, hMw⟩, ⟨M', hM', hMw'⟩⟩ :=
      exists_coprime_denom (OhE D) p hp.out (exists_denom D) (x * y) hxy
    have hB : Units.map (inc D).toMonoidHom b = (x * y) ^ h * (y⁻¹ ^ h * u⁻¹) := by
      rw [eq_mul_inv_of_mul_eq e.symm, mul_pow, mul_assoc, ← mul_assoc (y ^ h), ← mul_pow,
        mul_inv_cancel, one_pow, one_mul]
    have hB' : Units.map (inc D).toMonoidHom b⁻¹ = (x * y)⁻¹ ^ h * (y ^ h * u) := by
      rw [map_inv, hB, mul_inv, mul_inv, inv_inv, ← inv_pow, ← inv_pow, inv_inv]
    have i1 : IsIntegral ℤ (((M ^ h : ℕ) : D.host.E) * b) := by
      rw [← inc_mem_iff, map_mul, map_natCast]
      have : inc D b = ((Units.map (inc D).toMonoidHom b : (AE D)ˣ) : AE D) := rfl
      rw [this, hB, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_pow_eq_pow_val, Nat.cast_pow, ← mul_assoc, ← mul_pow]
      exact mul_mem (pow_mem hMw _) (mul_mem (pow_mem hy.2 _) hu')
    have i2 : IsIntegral ℤ (((M' ^ h : ℕ) : D.host.E) * (b⁻¹ : D.host.Eˣ)) := by
      rw [← inc_mem_iff, map_mul, map_natCast]
      have : inc D (b⁻¹ : D.host.Eˣ) =
        ((Units.map (inc D).toMonoidHom b⁻¹ : (AE D)ˣ) : AE D) := rfl
      rw [this, hB', Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_pow_eq_pow_val, Nat.cast_pow, ← mul_assoc, ← mul_pow]
      exact mul_mem (pow_mem hMw' _) (mul_mem (pow_mem hy.1 _) hu)
    have key : ∀ ψ : D.host.E →+* ℂ_[p], ‖ψ (b ^ k : D.host.Eˣ)‖ = 1 := fun ψ => by
      have j1 := norm_le_one_of_denom ψ (hM.pow_left h) i1
      have j2 := norm_le_one_of_denom ψ (hM'.pow_left h) i2
      rw [Units.val_inv_eq_inv_val, map_inv₀, norm_inv] at j2
      have h0 : 0 < ‖ψ b‖ := norm_pos_iff.2 ((map_ne_zero _).2 b.ne_zero)
      have : ‖ψ b‖ = 1 := le_antisymm j1 ((inv_le_one₀ h0).1 j2)
      rw [Units.val_pow_eq_pow_val, map_pow, norm_pow, this, one_pow]
    rw [lamC, dif_pos hz]
    refine H _ lam fun τ => ?_
    exact (key (lam.comp τ)).trans
      (key ((lam.comp τ).comp (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E))).symm

end GlobalTheory.HeckeVal
