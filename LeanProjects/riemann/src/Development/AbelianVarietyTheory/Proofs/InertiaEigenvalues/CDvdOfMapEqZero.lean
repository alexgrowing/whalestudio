import Mathlib
import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesAlgHomActionLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfPowLeOfPowLe

noncomputable section

open PowerSeries GlobalTheory.Cyc

namespace GlobalTheory.PrismS

theorem series_hom_ext {A B : Type} [CommRing A] [CommRing B] {f g : A⟦X⟧ →+* B⟦X⟧}
    (hC : ∀ a, f (C a) = g (C a)) (hX : f X = g X) (hd : X ∣ f X) : f = g := by
  have hp : f.comp Polynomial.coeToPowerSeries.ringHom = g.comp Polynomial.coeToPowerSeries.ringHom :=
    Polynomial.ringHom_ext (fun a => by simpa using hC a) (by simpa using hX)
  ext x n
  have hx := eq_X_pow_mul_shift_add_trunc (n + 1) x
  have h1 : f (trunc (n + 1) x : A⟦X⟧) = g (trunc (n + 1) x : A⟦X⟧) := RingHom.congr_fun hp (trunc (n + 1) x)
  have h2 : X ^ (n + 1) ∣ f x - g x := by
    rw [hx, map_add, map_add, h1, add_sub_add_right_eq_sub, map_mul, map_mul, map_pow, map_pow, ← hX,
      ← mul_sub]
    exact (pow_dvd_pow_of_dvd hd _).mul_right _
  have h3 := X_pow_dvd_iff.1 h2 n (Nat.lt_succ_self n)
  rwa [map_sub, sub_eq_zero] at h3

theorem C_dvd_of_map_eq_zero {A : Type} [CommRing A] (p : A) (y : A⟦X⟧)
    (h : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {p})) y = 0) : ∃ b, y = C p * b := by
  have h1 : ∀ n, ∃ c, coeff n y = p * c := fun n => by
    have := congrArg (coeff n) h
    rw [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
    exact this
  choose c hc using h1
  exact ⟨PowerSeries.mk c, PowerSeries.ext fun n => by rw [coeff_C_mul, coeff_mk, hc]⟩

section Act

variable {l : ℕ} [hl : Fact l.Prime] {A B : Type} [CommRing A] [CommRing B] [Algebra ℤ_[l] A]
  [Algebra ℤ_[l] B]

theorem act_C (c : ℤ_[l]) (a : A) : act l A c (C a) = C a := (act l A c).commutes a

theorem act_X (c : ℤ_[l]) : act l A c X = cyc l A c := (act_laws l A).1 c

theorem phi_X : phi l A X = (1 + X) ^ l - 1 := (act_X _).trans ((act_laws l A).2.2.2.1 l)

theorem map_cyc (e : A →ₐ[ℤ_[l]] B) (c : ℤ_[l]) : PowerSeries.map e.toRingHom (cyc l A c) = cyc l B c := by
  rw [cyc, cyc, map_sub, map_one, ← RingHom.comp_apply, ← PowerSeries.map_comp]
  congr 3
  exact RingHom.ext fun z => e.commutes z

theorem map_act (e : A →ₐ[ℤ_[l]] B) (c : ℤ_[l]) (x : A⟦X⟧) :
    PowerSeries.map e.toRingHom (act l A c x) = act l B c (PowerSeries.map e.toRingHom x) := by
  have hX : PowerSeries.map e.toRingHom (act l A c X) = cyc l B c := by rw [act_X, map_cyc]
  refine RingHom.congr_fun (series_hom_ext (f := (PowerSeries.map e.toRingHom).comp (act l A c).toRingHom)
    (g := (act l B c).toRingHom.comp (PowerSeries.map e.toRingHom)) (fun a => ?_) ?_ ?_) x
  · change PowerSeries.map e.toRingHom (act l A c (C a)) = act l B c (PowerSeries.map e.toRingHom (C a))
    rw [act_C, map_C, act_C]
  · change PowerSeries.map e.toRingHom (act l A c X) = act l B c (PowerSeries.map e.toRingHom X)
    rw [hX, map_X, act_X]
  · change X ∣ PowerSeries.map e.toRingHom (act l A c X)
    rw [hX, X_dvd_iff, cyc_const]

theorem constantCoeff_act (c : ℤ_[l]) (x : A⟦X⟧) : constantCoeff (act l A c x) = constantCoeff x := by
  obtain ⟨y, hy⟩ : X ∣ x - C (constantCoeff x) := by rw [X_dvd_iff]; simp
  have h : x = C (constantCoeff x) + X * y := by rw [← hy]; ring
  conv_lhs => rw [h, map_add, map_mul, act_C, act_X, map_add, map_mul, cyc_const]
  simp

omit hl [Algebra ℤ_[l] A] [Algebra ℤ_[l] B] in

theorem map_QQ (e : A →+* B) (s : ℕ) : PowerSeries.map e (QQ l A s) = QQ l B s := by
  simp [QQ, XX]

def phiS (σ : A →ₐ[ℤ_[l]] A) : A⟦X⟧ →+* A⟦X⟧ := (PowerSeries.map σ.toRingHom).comp (phi l A).toRingHom

theorem phiS_apply (σ : A →ₐ[ℤ_[l]] A) (x : A⟦X⟧) : phiS σ x = PowerSeries.map σ.toRingHom (phi l A x) := rfl

theorem phiS_lift (σ : A →ₐ[ℤ_[l]] A) (hu : ¬ IsUnit (l : A)) (h : ∀ a, ∃ b, σ a = a ^ l + (l : A) * b)
    (x : A⟦X⟧) : ∃ b, phiS σ x = x ^ l + (l : A⟦X⟧) * b := by
  set q := Ideal.Quotient.mk (Ideal.span {(l : A)}) with hq
  have : CharP (A ⧸ Ideal.span {(l : A)}) l := CharP.quotient A l hu
  have : CharP (A ⧸ Ideal.span {(l : A)})⟦X⟧ l := charP_of_injective_ringHom (f := C) C_injective l
  have hX : PowerSeries.map q (phiS σ X) = X ^ l := by
    rw [phiS_apply, phi_X]
    simp [add_pow_char]
  have key : (PowerSeries.map q).comp (phiS σ) = (frobenius _ l).comp (PowerSeries.map q) := by
    refine series_hom_ext (fun a => ?_) ?_ ?_
    · obtain ⟨b, hb⟩ := h a
      have h1 : phi l A (C a) = C a := act_C _ a
      rw [RingHom.comp_apply, RingHom.comp_apply, phiS_apply, h1, map_C, map_C, map_C, frobenius_def,
        ← map_pow]
      change C (q (σ a)) = _
      rw [hb, map_add, map_mul, map_natCast, CharP.cast_eq_zero (A ⧸ Ideal.span {(l : A)}) l, zero_mul, add_zero,
        map_pow]
    · rw [RingHom.comp_apply, RingHom.comp_apply, hX, map_X, frobenius_def]
    · rw [RingHom.comp_apply, hX]; exact dvd_pow_self _ hl.out.ne_zero
  obtain ⟨b, hb⟩ := C_dvd_of_map_eq_zero (l : A) (phiS σ x - x ^ l) (by
    have h2 := RingHom.congr_fun key x
    rw [RingHom.comp_apply, RingHom.comp_apply, frobenius_def] at h2
    rw [map_sub, map_pow, ← hq, h2, sub_self])
  exact ⟨b, by rw [map_natCast] at hb; rw [← hb]; ring⟩

end Act

theorem ker_eq_span {A B : Type} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CommRing B] (f : A⟦X⟧ →+* B) (Q b : A⟦X⟧) (d : ℕ) (p : A) (hp : ¬ IsUnit p) (hQ : Q = X ^ d + C p * b)
    (h0 : f Q = 0) (h : ∀ r : Polynomial A, r.natDegree < d → f r = 0 → r = 0) :
    RingHom.ker f = Ideal.span {Q} := by
  refine le_antisymm (fun x hx => ?_) ((Ideal.span_singleton_le_iff_mem _).2 h0)
  have h1 : Q.map (IsLocalRing.residue A) = X ^ d := by
    rw [hQ, map_add, map_mul, map_C, (IsLocalRing.residue_eq_zero_iff p).2 hp]
    simp
  obtain ⟨q, r, hr⟩ := exists_isWeierstrassDivision x (g := Q) (by rw [h1]; exact pow_ne_zero _ X_ne_zero)
  have h2 : r.degree < d := by
    have := hr.degree_lt
    change r.degree < ((Q.map (IsLocalRing.residue A)).order.toNat : ℕ) at this
    rwa [h1, order_X_pow, ENat.toNat_natCast] at this
  have h3 : r = 0 := by
    by_contra hne
    refine hne (h r ((Polynomial.natDegree_lt_iff_degree_lt hne).2 h2) ?_)
    have := congrArg f hr.eq_mul_add
    rw [map_add, map_mul, h0, zero_mul, zero_add] at this
    exact this.symm.trans hx
  rw [hr.eq_mul_add, h3]
  simpa using Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self Q)

theorem isAdicComplete_span {A : Type} [CommRing A] (p : A) [IsAdicComplete (Ideal.span {p}) A] (Q b : A⟦X⟧)
    (d : ℕ) (hd : 0 < d) (hQ : Q = X ^ d + C p * b) :
    IsAdicComplete (Ideal.span {C p} ⊔ Ideal.span {Q}) A⟦X⟧ := by
  have hJ : (Ideal.span {p}).comap (constantCoeff (R := A)) = Ideal.span {C p} ⊔ Ideal.span {X} := by
    refine le_antisymm (fun x hx => ?_) (sup_le ?_ ?_)
    · rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hx
      obtain ⟨c, hc⟩ := hx
      obtain ⟨y, hy⟩ : X ∣ x - C (constantCoeff x) := by rw [X_dvd_iff]; simp
      have h : x = C p * C c + X * y := by rw [← hy, ← map_mul, ← hc]; ring
      rw [h]
      exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
        (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]; simp
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]; simp
  have hc := ReciprocityTheory.P1.isAdicComplete_comap_constantCoeff (Ideal.span {p})
  rw [hJ] at hc
  refine GlobalTheory.isAdicComplete_of_pow_le_of_pow_le _ _ _ d 1 ?_ ?_ hc
  · have h1 : ∀ (I J : Ideal A⟦X⟧) (n : ℕ), (I ⊔ J) ^ n ≤ I ⊔ J ^ n := fun I J n => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, pow_succ]
        refine (Ideal.mul_mono_left ih).trans ?_
        rw [Ideal.sup_mul, Ideal.mul_sup (J ^ n)]
        exact sup_le (le_sup_of_le_left Ideal.mul_le_left)
          (sup_le (le_sup_of_le_left Ideal.mul_le_right) le_sup_right)
    refine (h1 _ _ _).trans (sup_le le_sup_left ?_)
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem,
      show (X : A⟦X⟧) ^ d = -(C p * b) + Q by rw [hQ]; ring]
    exact Submodule.add_mem_sup (neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_span_singleton_self _)
  · rw [pow_one]
    refine sup_le le_sup_left ?_
    rw [Ideal.span_singleton_le_iff_mem, hQ, add_comm]
    exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ hd)

theorem existsUnique_series {A B κ : Type} [CommRing A] [CommRing B] {d : ℕ} (e : κ → (A →+* B)) (o : Fin d → B)
    (h : ∀ y : κ → B, ∃! c : Fin d → A, ∀ k, y k = ∑ i, o i * e k (c i)) (x : κ → B⟦X⟧) :
    ∃! c : Fin d → A⟦X⟧, ∀ k, x k = ∑ i, C (o i) * PowerSeries.map (e k) (c i) := by
  choose c hc hu using fun n => h fun k => coeff n (x k)
  refine ⟨fun i => PowerSeries.mk fun n => c n i, fun k => PowerSeries.ext fun n => ?_, fun c' hc' => ?_⟩
  · simpa [coeff_C_mul] using hc n k
  · funext i
    ext n
    rw [coeff_mk, ← hu n (fun i => coeff n (c' i)) fun k => by simp [hc' k, coeff_C_mul]]

end GlobalTheory.PrismS
