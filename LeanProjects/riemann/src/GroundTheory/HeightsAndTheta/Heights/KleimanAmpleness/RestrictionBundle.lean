import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionSystems
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem mul_mem_chartRing_of_mul_eq_one {S : Type u} [CommRing S] {Ω : Type w} [Field Ω]
    [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω} {I : Chart x} {P M : Submodule (chartRing S x I) Ω}
    (hPM : P * M = 1) {q m : Ω} (hq : q ∈ P) (hm : m ∈ M) : q * m ∈ chartRing S x I := by
  have := Submodule.mul_mem_mul hq hm
  rw [hPM, Submodule.mem_one] at this
  obtain ⟨c, hc⟩ := this
  rw [← hc]; exact c.2

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
  (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
  {Nb : LineBundle k x} {r : ℕ} {h : Fin (r + 1) → Ω}

theorem mem_sub_of_isVeryAmpleBy (hV : IsVeryAmpleBy Nb.toSubSystem h) (l : Fin (r + 1)) (I : Chart x) :
    h l ∈ Nb.sub I :=
  (Submodule.mem_iInf _).mp (hV.mem_secs l) I

include hsp

theorem exists_redGood (hV : IsVeryAmpleBy Nb.toSubSystem h) (I₀ : Chart y) :
    ∃ l₀ : Fin (r + 1), h l₀ ≠ 0 ∧ (∀ l, h l / h l₀ ∈ locAt k x y) ∧
      RedGood hxy Nb.toSubSystem (h l₀) := by
  obtain ⟨M, hM⟩ := Nb.invertible (liftChart hxy I₀)
  have hgen := hV.generates (liftChart hxy I₀)
  have hA : ∀ {q m : Ω}, q ∈ Nb.sub (liftChart hxy I₀) → m ∈ M → q * m ∈ locAt k x y :=
    fun hq hm => (chartRing_sub_locAt hsp hxy I₀ (mul_mem_chartRing_of_mul_eq_one hM hq hm)).1
  have h1 : (1 : Ω) ∈ Nb.sub (liftChart hxy I₀) * M := by
    rw [hM]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨l₀, m₀, hm₀, hne⟩ : ∃ l₀, ∃ m₀ ∈ M, redAt k x y (h l₀ * m₀) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero : ∀ q ∈ Nb.sub (liftChart hxy I₀), ∀ m ∈ M, redAt k x y (q * m) = 0 := by
      intro q hq m hm
      rw [← hgen] at hq
      refine Submodule.span_induction (p := fun q _ => redAt k x y (q * m) = 0) ?_ ?_ ?_ ?_ hq
      · rintro _ ⟨l, rfl⟩; exact hcon l m hm
      · rw [zero_mul]; exact (locAt_zero hsp).2
      · intro u v hu hv ihu ihv
        rw [add_mul, (locAt_add hsp (hA (hgen ▸ hu) hm) (hA (hgen ▸ hv) hm)).2, ihu, ihv, add_zero]
      · intro c u hu ihu
        rw [chartRing_smul_def, mul_assoc,
          (locAt_mul hsp (chartRing_sub_locAt hsp hxy I₀ c.2).1 (hA (hgen ▸ hu) hm)).2, ihu, mul_zero]
    have := Submodule.mul_induction_on (C := fun z => z ∈ locAt k x y ∧ redAt k x y z = 0) h1
      (fun q hq m hm => ⟨hA hq hm, hzero q hq m hm⟩)
      (fun u v hu hv => ⟨(locAt_add hsp hu.1 hv.1).1, by
        rw [(locAt_add hsp hu.1 hv.1).2, hu.2, hv.2, add_zero]⟩)
    rw [(locAt_one hsp).2] at this
    exact one_ne_zero this.2
  have hgm : h l₀ * m₀ ∈ locAt k x y := hA (mem_sub_of_isVeryAmpleBy hV l₀ _) hm₀
  have hgm0 := (locAt_inv hsp hgm hne).1
  have hg0 : h l₀ ≠ 0 := left_ne_zero_of_mul hgm0
  have hm0 : m₀ ≠ 0 := right_ne_zero_of_mul hgm0
  have hl : ∀ l, h l / h l₀ ∈ locAt k x y := by
    intro l
    rw [← mul_div_mul_right (h l) (h l₀) hm0]
    exact (locAt_div hsp (hA (mem_sub_of_isVeryAmpleBy hV l _) hm₀) hgm hne).1
  refine ⟨l₀, hg0, hl, ?_⟩
  intro I q hq
  have hgenI := hV.generates (liftChart hxy I)
  rw [← hgenI] at hq
  refine Submodule.span_induction (p := fun q _ => q / h l₀ ∈ locAt k x y) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨l, rfl⟩; exact hl l
  · rw [zero_div]; exact (locAt_zero hsp).1
  · intro u v _ _ hu hv; rw [add_div]; exact (locAt_add hsp hu hv).1
  · intro c u _ hu
    rw [chartRing_smul_def, mul_div_assoc]
    exact (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 hu).1

variable {g : Ω}

theorem redSys_sub_eq (hV : IsVeryAmpleBy Nb.toSubSystem h) (hg : RedGood hxy Nb.toSubSystem g)
    (I : Chart y) : (redSys hxy Nb.toSubSystem g).sub I =
      Submodule.span (chartRing k y I) (Set.range fun l => redAt k x y (h l / g)) := by
  have hgen := hV.generates (liftChart hxy I)
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    have hq' := hq
    rw [← hgen] at hq'
    refine Submodule.span_induction (p := fun q _ => redAt k x y (q / g) ∈
      Submodule.span (chartRing k y I) (Set.range fun l => redAt k x y (h l / g))) ?_ ?_ ?_ ?_ hq'
    · rintro _ ⟨l, rfl⟩; exact Submodule.subset_span ⟨l, rfl⟩
    · rw [zero_div, (locAt_zero hsp).2]; exact Submodule.zero_mem _
    · intro u v hu hv ihu ihv
      rw [add_div, (locAt_add hsp (hg I u (hgen ▸ hu)) (hg I v (hgen ▸ hv))).2]
      exact Submodule.add_mem _ ihu ihv
    · intro c u hu ihu
      rw [chartRing_smul_def, mul_div_assoc,
        (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 (hg I u (hgen ▸ hu))).2]
      have := Submodule.smul_mem _ (⟨_, (chartRing_sub_locAt hsp hxy I c.2).2⟩ : chartRing k y I) ihu
      rwa [chartRing_smul_def] at this
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, rfl⟩
    exact Submodule.subset_span ⟨h l, mem_sub_of_isVeryAmpleBy hV l _, rfl⟩

theorem exists_lineBundle_redSys (hV : IsVeryAmpleBy Nb.toSubSystem h) (hg0 : g ≠ 0)
    (hg : RedGood hxy Nb.toSubSystem g) (hgsec : ∀ I : Chart x, g ∈ Nb.sub I) :
    ∃ Q' : LineBundle k y, Q'.toSubSystem = redSys hxy Nb.toSubSystem g := by
  refine ⟨LineBundle.mk (SubFamily.mk (redSys hxy Nb.toSubSystem g) ?_) ?_ ?_, rfl⟩
  · intro I J hIJ z
    rw [redSys_sub_eq hsp hxy hV hg, redSys_sub_eq hsp hxy hV hg]
    exact res_mem_span_iff_exists_isUnit hIJ z
  · intro I
    rw [redSys_sub_eq hsp hxy hV hg]
    exact Submodule.fg_span (Set.finite_range _)
  · intro I
    obtain ⟨M, hM⟩ := Nb.invertible (liftChart hxy I)
    refine ⟨Submodule.span (chartRing k y I) ((fun m => redAt k x y (m * g)) '' M), ?_⟩
    have hA : ∀ {q m : Ω}, q ∈ Nb.sub (liftChart hxy I) → m ∈ M →
        q * m ∈ chartRing k x (liftChart hxy I) :=
      fun hq hm => mul_mem_chartRing_of_mul_eq_one hM hq hm
    have hmg : ∀ {m : Ω}, m ∈ M → m * g ∈ locAt k x y := fun hm =>
      (chartRing_sub_locAt hsp hxy I (by rw [mul_comm]; exact hA (hgsec _) hm)).1
    have hsplit : ∀ q m : Ω, q * m = q / g * (m * g) := fun q m => by field_simp
    apply le_antisymm
    · change Submodule.span _ _ * Submodule.span _ _ ≤ 1
      rw [Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨q, hq, rfl⟩, _, ⟨m, hm, rfl⟩, rfl⟩
      show redAt k x y (q / g) * redAt k x y (m * g) ∈ (1 : Submodule (chartRing k y I) K')
      rw [← (locAt_mul hsp (hg I q hq) (hmg hm)).2, ← hsplit]
      exact Submodule.mem_one.mpr ⟨⟨_, (chartRing_sub_locAt hsp hxy I (hA hq hm)).2⟩, rfl⟩
    · rw [Submodule.one_le]
      have h1 : (1 : Ω) ∈ Nb.sub (liftChart hxy I) * M := by
        rw [hM]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      have := Submodule.mul_induction_on (C := fun z => z ∈ locAt k x y ∧ redAt k x y z ∈
          (redSys hxy Nb.toSubSystem g).sub I *
            Submodule.span (chartRing k y I) ((fun m => redAt k x y (m * g)) '' M)) h1
        (fun q hq m hm => ⟨(chartRing_sub_locAt hsp hxy I (hA hq hm)).1, by
          rw [hsplit, (locAt_mul hsp (hg I q hq) (hmg hm)).2]
          exact Submodule.mul_mem_mul (Submodule.subset_span ⟨q, hq, rfl⟩)
            (Submodule.subset_span ⟨m, hm, rfl⟩)⟩)
        (fun u v hu hv => ⟨(locAt_add hsp hu.1 hv.1).1, by
          rw [(locAt_add hsp hu.1 hv.1).2]; exact Submodule.add_mem _ hu.2 hv.2⟩)
      rw [(locAt_one hsp).2] at this
      exact this.2

theorem restrictData_redSys (hg : RedGood hxy Nb.toSubSystem g) (Q' : LineBundle k y)
    (hQ : Q'.toSubSystem = redSys hxy Nb.toSubSystem g) :
    RestrictData Nb.toSubSystem hxy Q'.toSubSystem (fun q => redAt k x y (q / g)) := by
  rw [hQ]
  exact
    { mem := fun I q hq => Submodule.subset_span ⟨q, hq, rfl⟩
      add := fun I q hq q' hq' => by
        rw [add_div]; exact (locAt_add hsp (hg I q hq) (hg I q' hq')).2
      smul := fun I q hq f s e hs hf hse => by
        have hsy : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos I hs
        rw [mul_div_assoc, (locAt_mul hsp (mem_locAt hf hse hsy) (hg I q hq)).2,
          redAt_eq hsp hf hse hsy]
      span := fun I => rfl }

variable {σ : Ω}

theorem ne_zero_of_redAt_div (hσ : σ / g ∈ locAt k x y) (hσr : redAt k x y (σ / g) ≠ 0) : σ ≠ 0 :=
  fun h0 => (locAt_inv hsp hσ hσr).1 (by rw [h0, zero_div])

theorem redAt_mem_ampleChart (hg : RedGood hxy Nb.toSubSystem g) (Q' : LineBundle k y)
    (hQ : Q'.toSubSystem = redSys hxy Nb.toSubSystem g) (hσ : σ / g ∈ locAt k x y)
    (hσr : redAt k x y (σ / g) ≠ 0) (I : Chart y) {c : Ω}
    (hc : c ∈ ampleChart Nb.toSubSystem 1 σ (liftChart hxy I)) :
    c ∈ locAt k x y ∧ redAt k x y c ∈ ampleChart Q'.toSubSystem 1 (redAt k x y (σ / g)) I := by
  obtain ⟨n, hn⟩ := hc
  rw [one_mul] at hn
  have hpow := redSys_pow hsp hxy hg n
  have h1 : c * σ ^ n / g ^ n ∈ locAt k x y := hpow.1 I _ hn
  have hσ0 := ne_zero_of_redAt_div hsp hσ hσr
  have hg0 : g ≠ 0 := fun h0 => (locAt_inv hsp hσ hσr).1 (by rw [h0, div_zero])
  have hσn := locAt_pow hsp hσ n
  have hσnr : redAt k x y ((σ / g) ^ n) ≠ 0 := by rw [hσn.2]; exact pow_ne_zero _ hσr
  have hc_eq : c * σ ^ n / g ^ n / (σ / g) ^ n = c := by rw [div_pow]; field_simp
  obtain ⟨hcl, hcr⟩ := locAt_div hsp h1 hσn.1 hσnr
  rw [hc_eq] at hcl hcr
  refine ⟨hcl, n, ?_⟩
  rw [one_mul, hQ, ← hpow.2, hcr, hσn.2, div_mul_cancel₀ _ (pow_ne_zero _ hσr)]
  exact Submodule.subset_span ⟨_, hn, rfl⟩

theorem exists_lift_ampleChart (hg : RedGood hxy Nb.toSubSystem g) (Q' : LineBundle k y)
    (hQ : Q'.toSubSystem = redSys hxy Nb.toSubSystem g) (hσ : σ / g ∈ locAt k x y)
    (hσr : redAt k x y (σ / g) ≠ 0) (I : Chart y) {a : K'}
    (ha : a ∈ ampleChart Q'.toSubSystem 1 (redAt k x y (σ / g)) I) :
    ∃ e ∈ ampleChart Nb.toSubSystem 1 σ (liftChart hxy I), redAt k x y e = a := by
  obtain ⟨n, hn⟩ := ha
  have hpow := redSys_pow hsp hxy hg n
  rw [one_mul, hQ, ← hpow.2, mem_redSys_iff hsp hxy hpow.1] at hn
  obtain ⟨q, hq, hqa⟩ := hn
  have hσ0 := ne_zero_of_redAt_div hsp hσ hσr
  have hg0 : g ≠ 0 := fun h0 => (locAt_inv hsp hσ hσr).1 (by rw [h0, div_zero])
  refine ⟨q / σ ^ n, ⟨n, by rw [one_mul, div_mul_cancel₀ _ (pow_ne_zero _ hσ0)]; exact hq⟩, ?_⟩
  have hσn := locAt_pow hsp hσ n
  have hσnr : redAt k x y ((σ / g) ^ n) ≠ 0 := by rw [hσn.2]; exact pow_ne_zero _ hσr
  have heq : q / σ ^ n = q / g ^ n / (σ / g) ^ n := by rw [div_pow]; field_simp
  rw [heq, (locAt_div hsp (hpow.1 I q hq) hσn.1 hσnr).2, hqa, hσn.2,
    mul_div_cancel_right₀ _ (pow_ne_zero _ hσr)]

theorem redAt_mem_ampleBase (hg0 : g ≠ 0) (hgl : ∀ l, h l / g ∈ locAt k x y) {j : Fin (r + 1)}
    (hr : redAt k x y (h j / g) ≠ 0) {z : Ω} (hz : z ∈ ampleBase (S := k) h j) :
    z ∈ locAt k x y ∧
      redAt k x y z ∈ ampleBase (S := k) (fun l => redAt k x y (h l / g)) j := by
  refine Algebra.adjoin_induction (p := fun z _ => z ∈ locAt k x y ∧
    redAt k x y z ∈ ampleBase (S := k) (fun l => redAt k x y (h l / g)) j) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨l, rfl⟩
    dsimp only
    rw [← div_div_div_cancel_right₀ hg0 (h l) (h j)]
    obtain ⟨h1, h2⟩ := locAt_div hsp (hgl l) (hgl j) hr
    exact ⟨h1, by rw [h2]; exact Algebra.subset_adjoin ⟨l, rfl⟩⟩
  · intro c
    obtain ⟨h1, h2⟩ := locAt_algebraMap hsp c
    exact ⟨h1, by rw [h2]; exact Subalgebra.algebraMap_mem _ c⟩
  · intro u v _ _ hu hv
    obtain ⟨h1, h2⟩ := locAt_add hsp hu.1 hv.1
    exact ⟨h1, by rw [h2]; exact add_mem hu.2 hv.2⟩
  · intro u v _ _ hu hv
    obtain ⟨h1, h2⟩ := locAt_mul hsp hu.1 hv.1
    exact ⟨h1, by rw [h2]; exact mul_mem hu.2 hv.2⟩

theorem subset_support_of_redAt_ne_zero (hg : RedGood hxy Nb.toSubSystem g)
    (hσ : σ / g ∈ locAt k x y) (hσr : redAt k x y (σ / g) ≠ 0) (I₀ : Chart y) {b : Ω}
    (hb : b ∈ locAt k x y) (hbr : redAt k x y b ≠ 0) {J : Chart x}
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart Nb.toSubSystem 1 σ I) :
    J.1 ⊆ support y := by
  obtain ⟨e, he⟩ := hbJ (liftChart hxy I₀)
  have h1 : b ^ e * (xProd (liftChart hxy I₀) ^ J.1.card / xProd J ^ (liftChart hxy I₀).1.card) ∈
      locAt k x y := by
    obtain ⟨n, hn⟩ := he
    rw [one_mul] at hn
    have hpow := redSys_pow hsp hxy hg n
    have hc1 := hpow.1 I₀ _ hn
    have hσn := locAt_pow hsp hσ n
    have hσnr : redAt k x y ((σ / g) ^ n) ≠ 0 := by rw [hσn.2]; exact pow_ne_zero _ hσr
    have hσ0 := ne_zero_of_redAt_div hsp hσ hσr
    have hg0 : g ≠ 0 := fun h0 => (locAt_inv hsp hσ hσr).1 (by rw [h0, div_zero])
    have := (locAt_div hsp hc1 hσn.1 hσnr).1
    convert this using 1
    rw [div_pow]; field_simp
  have hbe := locAt_pow hsp hb e
  have hber : redAt k x y (b ^ e) ≠ 0 := by rw [hbe.2]; exact pow_ne_zero _ hbr
  have hb0 : b ≠ 0 := (locAt_inv hsp hb hbr).1
  have ht := (locAt_div hsp h1 hbe.1 hber).1
  rw [mul_div_cancel_left₀ _ (pow_ne_zero _ hb0)] at ht
  have hf := (res_isHomogeneous_prod_X (S := k) J.1).pow I₀.1.card
  have hs : ((∏ l ∈ I₀.1, (X l : Poly k N)) ^ J.1.card).IsHomogeneous (J.1.card * I₀.1.card) := by
    rw [mul_comm]; exact (res_isHomogeneous_prod_X (S := k) I₀.1).pow J.1.card
  have hsy : aeval y ((∏ l ∈ I₀.1, (X l : Poly k N)) ^ J.1.card) ≠ 0 := by
    rw [map_pow, res_aeval_prod_X]; exact pow_ne_zero _ (res_xProd_ne_zero I₀)
  have hti : (xProd (liftChart hxy I₀) ^ J.1.card / xProd J ^ (liftChart hxy I₀).1.card)⁻¹ =
      aeval x ((∏ l ∈ J.1, (X l : Poly k N)) ^ I₀.1.card) /
        aeval x ((∏ l ∈ I₀.1, (X l : Poly k N)) ^ J.1.card) := by
    rw [inv_div, map_pow, map_pow, res_aeval_prod_X, res_aeval_prod_X]; rfl
  have ht0 : xProd (liftChart hxy I₀) ^ J.1.card / xProd J ^ (liftChart hxy I₀).1.card ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (res_xProd_ne_zero _)) (pow_ne_zero _ (res_xProd_ne_zero _))
  have hmem := mem_locAt (x := x) hf hs hsy
  rw [← hti] at hmem
  have hmul := (locAt_mul hsp ht hmem).2
  rw [mul_inv_cancel₀ ht0, (locAt_one hsp).2, hti, redAt_eq hsp hf hs hsy] at hmul
  have hJy : aeval y ((∏ l ∈ J.1, (X l : Poly k N)) ^ I₀.1.card) ≠ 0 := by
    intro h0; rw [h0, zero_div, mul_zero] at hmul; exact one_ne_zero hmul
  rw [map_pow, res_aeval_prod_X] at hJy
  intro i hi
  exact (mem_support y).mpr (Finset.prod_ne_zero_iff.mp (pow_ne_zero_iff
    (Finset.card_pos.mpr I₀.2.1).ne' |>.mp hJy) i hi)

end

end GroundTheory.Heights₂.Heights.Kleiman
