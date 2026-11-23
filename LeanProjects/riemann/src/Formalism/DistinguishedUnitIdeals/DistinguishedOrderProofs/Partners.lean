import Mathlib
import Formalism.DistinguishedUnitIdeals.GammaCongruentArcFromStart
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.GoodOf
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Graded

noncomputable section

namespace Formalism.ExponentWindows.E

open PowerSeries

namespace XDivisibilityOfActions

open IdempotentNormalFormsRhoFacts GoodPlacesAlt

section ring
variable {O : Type} [CommRing O]

theorem X_dvd_alg_sub (f : PowerSeries O →ₐ[O] PowerSeries O) (hX : X ∣ f X) (a : PowerSeries O) :
    X ∣ f a - a := by
  obtain ⟨t, ht⟩ := hX
  have h := PowerSeries.eq_shift_mul_X_add_const a
  set a' := PowerSeries.mk fun p => coeff (p + 1) a with ha'
  refine ⟨f a' * t - a', ?_⟩
  have h2 : f a = f a' * f X + C (constantCoeff a) := by
    conv_lhs => rw [h]
    rw [map_add, map_mul, alg_C]
  generalize C (constantCoeff a) = c0 at h h2
  rw [h2, ht, h]
  ring

theorem X_dvd_φX (B : Base O) (h : B.E3) : X ∣ B.φ X := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u * B.q ^ (B.ℓ - 1), by rw [hu]; ring⟩

theorem X_dvd_γX (B : Base O) (h : B.E4) : X ∣ B.γ X := by
  obtain ⟨e, he⟩ := h
  exact ⟨_, he⟩

theorem X_dvd_itX (B : Base O) (h : B.E3) (k : ℕ) : X ∣ (⇑B.φ)^[k] X := by
  induction k with
  | zero => exact dvd_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (X_dvd_φX B h).trans (map_dvd B.φ ih)

theorem γp (B : Base O) (h3 : B.E3) (h4 : B.E4) (s : ℕ) :
    ∃ a : PowerSeries O, B.γ (B.p s) = B.p s * (1 + X * a) := by
  obtain ⟨e, he⟩ := h4
  have hq : B.γ B.q = B.q * (1 + (e : PowerSeries O) * X) := by
    have : B.γ B.q = B.γ X + C (B.ℓ : O) := by
      simp only [Base.q]
      rw [map_add, alg_C]
    rw [this, he]
    simp only [Base.q]
    ring
  obtain ⟨t, ht⟩ := X_dvd_itX B h3 s
  refine ⟨(⇑B.φ)^[s] (e : PowerSeries O) * t, ?_⟩
  simp only [Base.p]
  rw [γ_it, hq, it_mul, it_add, it_mul, ht, it_eq, map_one]
  ring

theorem γ_pow_one {B : Base O} {x : PowerSeries O}
    (h : ∃ a : PowerSeries O, B.γ x = x * (1 + X * a)) (k : ℕ) :
    ∃ a : PowerSeries O, B.γ (x ^ k) = x ^ k * (1 + X * a) := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := h
    obtain ⟨b, hb⟩ := ih
    exact ⟨a + b + X * a * b, by rw [pow_succ, map_mul, ha, hb]; ring⟩

theorem γLam (B : Base O) (h3 : B.E3) (h4 : B.E4) (H : ℕ → ℕ) (ell : ℕ) :
    ∃ a : PowerSeries O, B.γ (Formalism.ExponentWindows.abelian₂ B.p H ell) = Formalism.ExponentWindows.abelian₂ B.p H ell * (1 + X * a) := by
  simp only [Formalism.ExponentWindows.abelian₂]
  induction ell with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨b, hb⟩ := γ_pow_one (γp B h3 h4 k) (H k)
    exact ⟨a + b + X * a * b, by rw [Finset.prod_range_succ, map_mul, ha, hb]; ring⟩

theorem isUnit_one_add_X (a : PowerSeries O) : IsUnit (1 + X * a) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

end ring

section lat
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V] (L : Lat B n V)

theorem γ_sub_pull (h3 : B.E3) (h4 : B.E4) {i : ZMod n} (h9 : L.GamN i) (k : ℕ) {v : V}
    (hv : v ∈ L.pull i k) :
    L.γ (i + (k : ZMod n)) v - v ∈ sm X (L.pull i k) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    rw [γ_phiIt, ← phiIt_sub]
    obtain ⟨u', hu', he⟩ := mem_sm.1 (h9 u hu)
    obtain ⟨t, ht⟩ := X_dvd_itX B h3 k
    rw [← he, phiIt_smul, ht, mul_smul]
    exact smul_mem_sm _ (Submodule.smul_mem _ _ (phiIt_mem_pull L k hu'))
  | zero => simp
  | add x y _ _ hx hy =>
    have : L.γ (i + (k : ZMod n)) (x + y) - (x + y) =
        (L.γ (i + (k : ZMod n)) x - x) + (L.γ (i + (k : ZMod n)) y - y) := by
      rw [map_add]; abel
    rw [this]
    exact Submodule.add_mem _ hx hy
  | smul a x hx0 hx =>
    obtain ⟨t, ht⟩ := X_dvd_alg_sub B.γ (X_dvd_γX B h4) a
    have : L.γ (i + (k : ZMod n)) (a • x) - a • x =
        B.γ a • (L.γ (i + (k : ZMod n)) x - x) + (X : PowerSeries O) • (t • x) := by
      rw [L.γ_semi, smul_sub, smul_smul, ← ht, sub_smul]
      abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx)
      (smul_mem_sm _ (Submodule.smul_mem _ _ hx0))

end lat

end XDivisibilityOfActions

open IdempotentNormalFormsRhoFacts GoodPlacesAlt XDivisibilityOfActions

theorem partner_fourth_arc_form : GammaCongruentArcFromStart := by
  intro O _ B n _ V _ _ L c ell H h3 h4 h9 hX w hw
  set Λ := Formalism.ExponentWindows.abelian₂ B.p H ell with hΛ
  set P := L.pull (c - (ell : ZMod n)) ell with hP
  have hw' : Λ • w ∈ P := hw
  have hc : c - (ell : ZMod n) + (ell : ZMod n) = c := sub_add_cancel _ _
  have h1 := γ_sub_pull L h3 h4 h9 ell hw'
  rw [hc] at h1
  obtain ⟨p', hp', hpe⟩ := mem_sm.1 h1
  obtain ⟨a, ha⟩ := γLam B h3 h4 H ell
  obtain ⟨u, hu⟩ := isUnit_one_add_X a

  have h2 : (1 + X * a) • (Λ • L.γ c w) ∈ P := by
    have : (1 + X * a) • (Λ • L.γ c w) = L.γ c (Λ • w) := by
      rw [L.γ_semi, ha, smul_smul, mul_comm]
    rw [this]
    have := P.add_mem (sm_le _ _ h1) hw'
    simpa using this
  have h3' : Λ • L.γ c w ∈ P := by
    have := P.smul_mem ((u⁻¹ : (PowerSeries O)ˣ) : PowerSeries O) h2
    rwa [smul_smul, ← hu, Units.inv_mul, one_smul] at this
  obtain ⟨w', hw'e⟩ := hX.2 (L.γ c w - w)
  have hw'e : (X : PowerSeries O) • w' = L.γ c w - w := hw'e
  refine mem_sm.2 ⟨w', ?_, hw'e⟩
  change Λ • w' ∈ P
  have h5 : (X : PowerSeries O) • (Λ • w') = (X : PowerSeries O) • (p' - a • (Λ • L.γ c w)) := by
    rw [smul_comm, hw'e, smul_sub (X : PowerSeries O), hpe, L.γ_semi, ha, ← hΛ, smul_sub,
      smul_smul X a, mul_add, mul_one, add_smul, mul_smul Λ, smul_comm Λ (X * a)]
    abel
  rw [hX.1 h5]
  exact P.sub_mem hp' (P.smul_mem _ h3')

namespace XDivisibilityOfActions

section lev
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V] {L : Lat B n V} {c : ZMod n} {ell : ℕ} {Λ : PowerSeries O} {r : ℕ}
  (S : LevelData L c ell Λ r)

theorem unit_pow {s s' : ℕ} (h : ∀ e : S.Lv, B.p s' • e ∈ S.Nl s → e ∈ S.Nl s) (g : ℕ) {e : S.Lv}
    (he : B.p s' ^ g • e ∈ S.Nl s) : e ∈ S.Nl s := by
  induction g with
  | zero => simpa using he
  | succ g ih =>
    apply ih
    apply h
    rwa [smul_smul, ← pow_succ']

theorem unit_prod (hU : S.UnitsAt) {s : ℕ} (hs : s < ell) (g : ℕ) (T : Finset ℕ)
    (hT : ∀ s' ∈ T, s' < ell ∧ s' ≠ s) {e : S.Lv}
    (he : (∏ s' ∈ T, B.p s' ^ g) • e ∈ S.Nl s) : e ∈ S.Nl s := by
  classical
  induction T using Finset.induction_on generalizing e with
  | empty => simpa using he
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, mul_comm, mul_smul] at he
    have h1 := ih (fun s' hs' => hT s' (Finset.mem_insert_of_mem hs')) he
    obtain ⟨h2, h3⟩ := hT a (Finset.mem_insert_self _ _)
    exact unit_pow S ((hU s hs).2 a h2 h3) g h1

theorem Th_iff (hU : S.UnitsAt) {s : ℕ} (hs : s < ell) (g : ℕ) (e : S.Lv) :
    B.Th ell g • e ∈ S.Nl s ↔ B.p s ^ g • e ∈ S.Nl s := by
  classical
  have hsplit : B.Th ell g = (∏ s' ∈ (Finset.range ell).erase s, B.p s' ^ g) * B.p s ^ g := by
    simp only [Base.Th]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_range.2 hs)]
  rw [hsplit, mul_smul]
  constructor
  · intro h
    refine unit_prod S hU hs g _ (fun s' hs' => ?_) h
    exact ⟨Finset.mem_range.1 (Finset.mem_of_mem_erase hs'), Finset.ne_of_mem_erase hs'⟩
  · intro h
    exact Submodule.smul_mem _ _ h

end lev

end XDivisibilityOfActions

open XDivisibilityOfActions

theorem partner_fourth_first_form : DivisibleIffOf := by
  intro O _ B n _ V _ _ L c ell hh H r S g h5 hH hM hU
  constructor
  · intro x hx
    have hx' : B.Th ell g • x ∈ L.N c := hx
    have h1 := pullback_lemma_holds O B n V L c ell hh (fun s => H s - g) h5 (fun s hs => by
      have := hH s hs
      omega) hx'
    rw [mem_dv, smul_smul] at h1
    change Formalism.ExponentWindows.abelian₂ B.p H ell • x ∈ L.pull (c - (ell : ZMod n)) ell
    have : Formalism.ExponentWindows.abelian₂ B.p H ell = (∏ s ∈ Finset.range ell, B.p s ^ (H s - g)) * B.Th ell g := by
      simp only [Formalism.ExponentWindows.abelian₂, Base.Th]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun s hs => ?_
      have := hH s (Finset.mem_range.1 hs)
      rw [← pow_add]
      congr 1
      omega
    rw [this]
    exact h1
  · intro x
    have h1 := hM (B.Th ell g • x)
    have h2 : ((B.Th ell g • x : ↥(L.W c ell (Formalism.ExponentWindows.abelian₂ B.p H ell))) : V) =
        B.Th ell g • (x : V) := rfl
    rw [h2] at h1
    rw [mem_dv, h1]
    refine forall₂_congr fun s hs => ?_
    rw [map_smul, Th_iff S hU hs, mem_dv]

theorem partner_fourth_second_form : XMulIffOf := by
  intro O _ B n _ V _ _ L c ell hh H r S h5 hH hM hU x
  have hNW : L.N c ≤ L.W c ell (Formalism.ExponentWindows.abelian₂ B.p H ell) := pullback_lemma_holds O B n V L c ell hh H h5 hH
  constructor
  · intro hx
    obtain ⟨u, hu, hue⟩ := mem_sm.1 hx
    refine ⟨mem_sm.2 ⟨u, hNW hu, hue⟩, fun s hs => ?_⟩
    have : x = (X : PowerSeries O) • (⟨u, hNW hu⟩ : ↥(L.W c ell (Formalism.ExponentWindows.abelian₂ B.p H ell))) :=
      Subtype.ext hue.symm
    rw [this, map_smul]
    exact Submodule.smul_mem _ _ ((hM ⟨u, hNW hu⟩).1 hu s hs)
  · rintro ⟨hx, hl⟩
    obtain ⟨u, hu, hue⟩ := mem_sm.1 hx
    have : x = (X : PowerSeries O) • (⟨u, hu⟩ : ↥(L.W c ell (Formalism.ExponentWindows.abelian₂ B.p H ell))) :=
      Subtype.ext hue.symm
    refine mem_sm.2 ⟨u, (hM ⟨u, hu⟩).2 fun s hs => ?_, hue⟩
    have h1 := hl s hs
    rw [this, map_smul] at h1
    exact (hU s hs).1 _ h1

namespace XDivisibilityOfActions

section ring2
variable {O : Type} [CommRing O]

theorem it_span (f : PowerSeries O →ₐ[O] PowerSeries O) (k : ℕ) {a b : PowerSeries O}
    (h : a ∈ Ideal.span {b}) : (⇑f)^[k] a ∈ Ideal.span {(⇑f)^[k] b} := by
  rw [Ideal.mem_span_singleton] at h ⊢
  exact it_dvd f k h

theorem it_split (B : Base O) {ell j : ℕ} (h : j ≤ ell) (a : PowerSeries O) :
    (⇑B.φ)^[ell] a = (⇑B.φ)^[ell - j] ((⇑B.φ)^[j] a) := by
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel h]

theorem it_sub (f : PowerSeries O →ₐ[O] PowerSeries O) (k : ℕ) (a b : PowerSeries O) :
    (⇑f)^[k] (a - b) = (⇑f)^[k] a - (⇑f)^[k] b := by
  rw [it_eq, map_sub]

theorem it_sum (f : PowerSeries O →ₐ[O] PowerSeries O) (k : ℕ) {ι : Type} (s : Finset ι)
    (g : ι → PowerSeries O) : (⇑f)^[k] (∑ t ∈ s, g t) = ∑ t ∈ s, (⇑f)^[k] (g t) := by
  rw [it_eq, map_sum]

theorem it_lc (B : Base O) (k K : ℕ) : (⇑B.φ)^[k] (B.lc ^ K) = B.lc ^ K := by
  rw [lc_pow, it_C]

theorem trunc_pull (B : Base O) {ell j M g sig : ℕ} (hj : j ≤ ell) (hT : B.Trunc j M g sig)
    (t a : ℕ) (h : (B.ℓ - 1) * a ≤ B.ℓ * t) : ∃ x : PowerSeries O,
      B.lc ^ sig * ((⇑B.φ)^[ell] X) ^ t - B.lc ^ a * x ∈ Ideal.span {B.ff' ell j M g} := by
  obtain ⟨x, hx⟩ := hT t a h
  refine ⟨(⇑B.φ)^[ell - j] x, ?_⟩
  have := it_span B.φ (ell - j) hx
  rwa [it_sub, it_mul, it_mul, it_lc, it_lc, it_pow, ← it_split B hj] at this

theorem XM_pull (B : Base O) {ell j M g : ℕ} (hj : j ≤ ell) (hG : B.Good j M g) :
    ((⇑B.φ)^[ell] X) ^ M ∈ Ideal.span {B.ff' ell j M g} := by
  have := it_span B.φ (ell - j) hG.2.2
  rwa [it_pow, ← it_split B hj] at this

end ring2

section lat2
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V] (L : Lat B n V)

theorem bij_mul {a b : PowerSeries O} (ha : Function.Bijective fun v : V => a • v)
    (hb : Function.Bijective fun v : V => b • v) : Function.Bijective fun v : V => (a * b) • v := by
  have : (fun v : V => (a * b) • v) = (fun v : V => a • v) ∘ fun v : V => b • v := by
    funext v
    simp [mul_smul]
  rw [this]
  exact ha.comp hb

theorem bij_pow {a : PowerSeries O} (ha : Function.Bijective fun v : V => a • v) (k : ℕ) :
    Function.Bijective fun v : V => a ^ k • v := by
  induction k with
  | zero => simp only [pow_zero, one_smul]; exact Function.bijective_id
  | succ k ih => rw [pow_succ]; exact bij_mul ih ha

theorem bij_Lam (H : ℕ → ℕ) (ell : ℕ) (h : ∀ s < ell, L.Inv (B.p s)) :
    Function.Bijective fun v : V => Formalism.ExponentWindows.abelian₂ B.p H ell • v := by
  simp only [Formalism.ExponentWindows.abelian₂]
  induction ell with
  | zero => simp only [Finset.range_zero, Finset.prod_empty, one_smul]; exact Function.bijective_id
  | succ k ih =>
    rw [Finset.prod_range_succ]
    exact bij_mul (ih fun s hs => h s (by omega)) (bij_pow (h k (by omega)) _)

theorem frame_core {ell j M g sig : ℕ} (hj : j ≤ ell) (hT : B.Trunc j M g sig) {i : ZMod n}
    (h9 : L.GamN i) (hH : L.H i M) {e : V} (he : e ∈ L.N i) :
    ∃ (K : ℕ) (x Q R : V), x ∈ L.N i ∧ L.γ i x - x ∈ sm (X ^ M) (L.N i) ∧
      x - B.lc ^ K • e ∈ sm X (L.N i) ∧ Q ∈ L.pull i ell ∧ R ∈ L.pull i ell ∧
      B.lc ^ sig • L.phiIt i ell x = B.lc ^ K • Q + B.ff' ell j M g • R := by
  obtain ⟨K, a, b, d, habd, hres⟩ := hH (-(L.γ i e - e)) (Submodule.neg_mem _ (h9 e he))
  have hx : ∀ t, ∃ x y : PowerSeries O, 1 ≤ t → t < M →
      B.lc ^ sig * ((⇑B.φ)^[ell] X) ^ t - B.lc ^ a t * x = y * B.ff' ell j M g := by
    intro t
    by_cases ht : 1 ≤ t ∧ t < M
    · obtain ⟨x, hx⟩ := trunc_pull B hj hT t (a t) (habd t ht.1 ht.2).2.1
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
      exact ⟨x, y, fun _ _ => hy.symm⟩
    · exact ⟨0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ ht⟩
  choose x y hxy using hx
  set v := ∑ t ∈ Finset.Ico 1 M, (B.lc ^ b t * X ^ t) • d t with hv
  have hvX : v ∈ sm X (L.N i) := by
    refine Submodule.sum_mem _ fun t ht => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 ht
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have : (B.lc ^ b (t + 1) * X ^ (t + 1)) • d (t + 1) =
        (X : PowerSeries O) • ((B.lc ^ b (t + 1) * X ^ t) • d (t + 1)) := by
      rw [smul_smul]
      congr 1
      ring
    rw [this]
    exact smul_mem_sm _ (Submodule.smul_mem _ _ (habd _ h1 h2).2.2)
  refine ⟨K, B.lc ^ K • e + v, B.lc ^ sig • L.phiIt i ell e +
    ∑ t ∈ Finset.Ico 1 M, x t • L.phiIt i ell (d t),
    ∑ t ∈ Finset.Ico 1 M, (B.lc ^ b t * y t) • L.phiIt i ell (d t), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ he) (sm_le _ _ hvX)
  · convert hres using 1
    rw [map_add, γ_lc, smul_neg, smul_sub]
    abel
  · simpa using hvX
  · refine Submodule.add_mem _ (Submodule.smul_mem _ _ (phiIt_mem_pull L ell he))
      (Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _ ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 ht
    exact phiIt_mem_pull L ell (habd t h1 h2).2.2
  · refine Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _ ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 ht
    exact phiIt_mem_pull L ell (habd t h1 h2).2.2
  · rw [phiIt_add, phiIt_lc, hv, hh_phiIt_sum, smul_add, smul_add, Finset.smul_sum,
      Finset.smul_sum, Finset.smul_sum, add_assoc, ← Finset.sum_add_distrib, smul_comm]
    congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 ht
    obtain ⟨hK, -, -⟩ := habd t h1 h2
    have h := hxy t h1 h2
    rw [phiIt_smul, it_mul, it_lc, it_pow, smul_smul, smul_smul, smul_smul, ← add_smul, ← hK]
    congr 1
    linear_combination (B.lc ^ b t) * h

theorem inv_core {ell j M g sig : ℕ} (hj : j ≤ ell) (hG : B.Good j M g) (hT : B.Trunc j M g sig)
    {i : ZMod n} {r : ℕ} {e : Fin r → V} (hI : L.Hinv i M e) (m : Fin r) :
    ∃ (K K₀ : ℕ) (Z : Fin r → PowerSeries O) (D : Fin r → V) (R : V),
      (∀ k, D k ∈ L.N i ∧ D k - B.lc ^ K₀ • e k ∈ sm X (L.N i) ∧
        L.γ i (D k) - D k ∈ sm (X ^ M) (L.N i)) ∧ R ∈ L.pull i ell ∧
      B.lc ^ sig • B.lc ^ (K + K₀) • L.phiIt i ell (e m) =
        B.lc ^ K • ∑ k, Z k • L.phiIt i ell (D k) + B.ff' ell j M g • R := by
  obtain ⟨K, K₀, a, b, y, D, hab, hD, hres⟩ := hI m
  have hx : ∀ t, ∃ x z : PowerSeries O, t < M →
      B.lc ^ sig * ((⇑B.φ)^[ell] X) ^ t - B.lc ^ a t * x = z * B.ff' ell j M g := by
    intro t
    by_cases ht : t < M
    · obtain ⟨x, hx⟩ := trunc_pull B hj hT t (a t) (hab t ht).2
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hx
      exact ⟨x, z, fun _ => hz.symm⟩
    · exact ⟨0, 0, fun h1 => absurd h1 ht⟩
  choose x z hxz using hx
  obtain ⟨τ, hτ⟩ := Ideal.mem_span_singleton'.1 (XM_pull B hj hG)
  obtain ⟨n', hn', hne⟩ := mem_sm.1 hres
  refine ⟨K, K₀, fun k => ∑ t ∈ Finset.range M, x t * (⇑B.φ)^[ell] (y t k), D,
    ∑ k, (∑ t ∈ Finset.range M, B.lc ^ b t * z t * (⇑B.φ)^[ell] (y t k)) • L.phiIt i ell (D k) +
      (B.lc ^ sig * τ) • L.phiIt i ell n', hD, ?_, ?_⟩
  · refine Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (phiIt_mem_pull L ell (hD k).1)) (Submodule.smul_mem _ _ (phiIt_mem_pull L ell hn'))
  · have h1 : B.lc ^ (K + K₀) • e m =
        ∑ k, (∑ t ∈ Finset.range M, B.lc ^ b t * X ^ t * y t k) • D k +
          (X : PowerSeries O) ^ M • n' := by
      rw [hne]; abel
    rw [← phiIt_lc, h1, phiIt_add, hh_phiIt_sum, phiIt_smul, it_pow, ← hτ, smul_add, smul_add,
      Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← add_assoc, ← Finset.sum_add_distrib,
      smul_smul, smul_smul]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [phiIt_smul, smul_smul, smul_smul, smul_smul, ← add_smul]
      congr 1
      rw [it_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t ht => ?_
      have ht' := Finset.mem_range.1 ht
      have h := hxz t ht'
      rw [it_mul, it_mul, it_lc, it_pow, ← (hab t ht').1]
      linear_combination (B.lc ^ b t * (⇑B.φ)^[ell] (y t k)) * h
    · congr 1
      ring

end lat2

section lev2
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V] {L : Lat B n V} {c : ZMod n} {ell : ℕ} {Λ : PowerSeries O} {r : ℕ}
  (S : LevelData L c ell Λ r)

def bv (O : Type) [CommRing O] {r : ℕ} (k : Fin r) : Fin r → PowerSeries O :=
  fun j => if k = j then 1 else 0

theorem cst_single (B : Base O) (k : Fin r) (K : ℕ) :
    cst (fun m => if k = m then (B.ℓ : O) ^ K else 0) = B.lc ^ K • bv O k := by
  funext j
  simp only [cst, bv, Pi.smul_apply, smul_eq_mul, lc_pow]
  split_ifs <;> simp

theorem sum_single (B : Base O) (k : Fin r) (K : ℕ) (e : Fin r → V) :
    ∑ m, C (if k = m then (B.ℓ : O) ^ K else 0) • e m = B.lc ^ K • e k := by
  rw [lc_pow]
  simp only [apply_ite C, map_zero, ite_smul, zero_smul]
  simp

theorem flSat_pow (h : S.FlSat) {s : ℕ} (hs : s < ell) (K : ℕ) {x : S.Lv}
    (hx : B.lc ^ K • x ∈ S.Fl s) : x ∈ S.Fl s := by
  induction K with
  | zero => simpa using hx
  | succ K ih =>
    apply ih
    apply h s hs
    rwa [smul_smul, ← pow_succ']

theorem exists_div (hΛ : Function.Bijective fun v : V => Λ • v) :
    ∃ θ : ↥(L.pull (c - (ell : ZMod n)) ell) →ₗ[PowerSeries O] ↥(L.W c ell Λ),
      (∀ p, Λ • ((θ p : ↥(L.W c ell Λ)) : V) = (p : V)) ∧
      ∀ w : ↥(L.W c ell Λ), ∀ hw : Λ • (w : V) ∈ L.pull (c - (ell : ZMod n)) ell,
        θ ⟨Λ • (w : V), hw⟩ = w := by
  let f : ↥(L.W c ell Λ) →ₗ[PowerSeries O] ↥(L.pull (c - (ell : ZMod n)) ell) :=
    (LinearMap.lsmul (PowerSeries O) V Λ).restrict (fun x hx => hx)
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply hΛ.1
      exact congrArg Subtype.val hxy
    · intro p
      obtain ⟨w, hw⟩ := hΛ.2 (p : V)
      have hw : Λ • w = (p : V) := hw
      refine ⟨⟨w, ?_⟩, Subtype.ext hw⟩
      change Λ • w ∈ L.pull (c - (ell : ZMod n)) ell
      rw [hw]
      exact p.2
  let E := LinearEquiv.ofBijective f hf
  refine ⟨E.symm.toLinearMap, fun p => ?_, fun w hw => ?_⟩
  · have : f (E.symm p) = p := E.apply_symm_apply p
    exact congrArg Subtype.val this
  · have : E w = ⟨Λ • (w : V), hw⟩ := rfl
    change E.symm _ = w
    rw [← this, E.symm_apply_apply]

end lev2

end XDivisibilityOfActions

open XDivisibilityOfActions

theorem XDivisibilityOfActions.partner_gen {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type}
    [AddCommGroup V] [Module (PowerSeries O) V] {L : Lat B n V} {c : ZMod n} {ell : ℕ}
    {Λ : PowerSeries O} {r : ℕ} (S : LevelData L c ell Λ r) {j M g sig : ℕ} {e : Fin r → V}
    (hj : j ≤ ell) (hG : B.Good j M g) (hT : B.Trunc j M g sig)
    (he : Submodule.span (PowerSeries O) (Set.range e) = L.N (c - (ell : ZMod n)))
    (h9 : L.GamN (c - (ell : ZMod n))) (hH : L.H (c - (ell : ZMod n)) M)
    (hI : L.Hinv (c - (ell : ZMod n)) M e) (hP : Function.Bijective fun v : V => Λ • v)
    (hA : S.LocalizesConst M e) (hF : S.FlP (B.ff' ell j M g)) (hS : S.FlSat) : S.Partner sig := by
  set c' := c - (ell : ZMod n) with hc'
  set f' := B.ff' ell j M g with hf'
  obtain ⟨θ, hθ, hθ'⟩ := exists_div (L := L) (c := c) (ell := ell) hP
  have heN : ∀ k, e k ∈ L.N c' := fun k => by
    rw [← he]; exact Submodule.subset_span ⟨k, rfl⟩

  have hcon : ∀ (x : V) (K : ℕ) (k : Fin r) (hx : x ∈ L.N c'),
      L.γ c' x - x ∈ sm (X ^ M) (L.N c') → x - B.lc ^ K • e k ∈ sm X (L.N c') → ∀ s < ell,
      S.loc s (θ ⟨L.phiIt c' ell x, phiIt_mem_pull L ell hx⟩) - B.lc ^ K • S.locL s (bv O k) ∈
        S.Fl s := by
    intro x K k hx h1 h2 s hs
    have := hA x (fun m => if k = m then (B.ℓ : O) ^ K else 0)
      (θ ⟨L.phiIt c' ell x, phiIt_mem_pull L ell hx⟩) hx h1 (by rw [sum_single]; exact h2)
      (hθ _) s hs
    rwa [cst_single, map_smul] at this
  constructor
  ·
    have key : ∀ m : Fin r, ∃ z : Fin r → PowerSeries O, ∀ s < ell,
        S.locL s z - B.lc ^ sig • S.loc s (θ ⟨L.phiIt c' ell (e m), phiIt_mem_pull L ell (heN m)⟩) ∈
          S.Fl s := by
      intro m
      obtain ⟨K, K₀, Z, D, R, hD, hR, hid⟩ := inv_core L hj hG hT hI m
      refine ⟨Z, fun s hs => ?_⟩
      have hid' : B.lc ^ sig • B.lc ^ (K + K₀) •
          (⟨L.phiIt c' ell (e m), phiIt_mem_pull L ell (heN m)⟩ : ↥(L.pull c' ell)) =
          B.lc ^ K • ∑ k, Z k • (⟨L.phiIt c' ell (D k), phiIt_mem_pull L ell (hD k).1⟩ :
            ↥(L.pull c' ell)) + f' • (⟨R, hR⟩ : ↥(L.pull c' ell)) := by
        apply Subtype.ext
        simpa using hid
      have h1 := congrArg (fun p => S.loc s (θ p)) hid'
      simp only [map_add, map_smul, map_sum] at h1
      apply flSat_pow S hS hs (K + K₀)
      have hZ : S.locL s Z = ∑ k, Z k • S.locL s (bv O k) :=
        LinearMap.pi_apply_eq_sum_univ (S.locL s) Z
      have h2 : B.lc ^ (K + K₀) • (S.locL s Z - B.lc ^ sig • S.loc s
          (θ ⟨L.phiIt c' ell (e m), phiIt_mem_pull L ell (heN m)⟩)) =
          -(B.lc ^ K • ∑ k, Z k • (S.loc s (θ ⟨L.phiIt c' ell (D k), phiIt_mem_pull L ell (hD k).1⟩)
            - B.lc ^ K₀ • S.locL s (bv O k))) - f' • S.loc s (θ ⟨R, hR⟩) := by
        rw [smul_sub, smul_comm (B.lc ^ (K + K₀)) (B.lc ^ sig), h1, hZ]
        simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul, pow_add]
        have : ∀ k, B.lc ^ K * B.lc ^ K₀ * Z k = B.lc ^ K * (Z k * B.lc ^ K₀) := fun k => by ring
        simp only [this]
        abel
      rw [h2]
      refine Submodule.sub_mem _ (Submodule.neg_mem _ (Submodule.smul_mem _ _
        (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_))) (hF s hs _)
      exact hcon (D k) K₀ k (hD k).1 (hD k).2.2 (hD k).2.1 s hs
    choose z hz using key
    intro w
    have hw : Λ • (w : V) ∈ L.pull c' ell := w.2
    have hw2 := hw
    rw [sat_pull_eq L he] at hw2
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hw2
    have hwe : w = θ (∑ m, cf m • (⟨L.phiIt c' ell (e m), phiIt_mem_pull L ell (heN m)⟩ :
        ↥(L.pull c' ell))) := by
      rw [← hθ' w hw]
      congr 1
      apply Subtype.ext
      simpa using hcf.symm
    refine ⟨∑ m, cf m • z m, fun s hs => ?_⟩
    rw [hwe]
    simp only [map_sum, map_smul, Finset.smul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [smul_comm, ← smul_sub]
    exact Submodule.smul_mem _ _ (hz m s hs)
  ·
    have key : ∀ k : Fin r, ∃ Q : ↥(L.pull c' ell), ∀ s < ell,
        S.loc s (θ Q) - B.lc ^ sig • S.locL s (bv O k) ∈ S.Fl s := by
      intro k
      obtain ⟨K, x, Q, R, hx, h1, h2, hQ, hR, hid⟩ := frame_core L hj hT h9 hH (heN k)
      refine ⟨⟨Q, hQ⟩, fun s hs => ?_⟩
      have hid' : B.lc ^ sig • (⟨L.phiIt c' ell x, phiIt_mem_pull L ell hx⟩ : ↥(L.pull c' ell)) =
          B.lc ^ K • (⟨Q, hQ⟩ : ↥(L.pull c' ell)) + f' • (⟨R, hR⟩ : ↥(L.pull c' ell)) :=
        Subtype.ext hid
      have h3 := congrArg (fun p => S.loc s (θ p)) hid'
      simp only [map_add, map_smul] at h3
      apply flSat_pow S hS hs K
      have h4 : B.lc ^ K • (S.loc s (θ ⟨Q, hQ⟩) - B.lc ^ sig • S.locL s (bv O k)) =
          B.lc ^ sig • (S.loc s (θ ⟨L.phiIt c' ell x, phiIt_mem_pull L ell hx⟩) -
            B.lc ^ K • S.locL s (bv O k)) - f' • S.loc s (θ ⟨R, hR⟩) := by
        rw [smul_sub, smul_sub, h3, smul_comm (B.lc ^ K) (B.lc ^ sig)]
        abel
      rw [h4]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (hcon x K k hx h1 h2 s hs)) (hF s hs _)
    choose Q hQ using key
    intro y
    refine ⟨θ (∑ k, y k • Q k), fun s hs => ?_⟩
    have hy : S.locL s y = ∑ k, y k • S.locL s (bv O k) :=
      LinearMap.pi_apply_eq_sum_univ (S.locL s) y
    rw [hy]
    simp only [map_sum, map_smul, Finset.smul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [smul_comm, ← smul_sub]
    exact Submodule.smul_mem _ _ (hQ k s hs)

theorem partner_lattice_exists : PartnerOf := by
  intro O _ B n _ V _ _ L c ell H r S j M g sig e hj hG hT he h9 hH hI hP hA hF hS
  exact partner_gen S hj hG hT he h9 hH hI (bij_Lam L H ell hP) hA hF hS

namespace XDivisibilityOfActions

section hinv
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V] (L : Lat B n V)

def fr (B : Base O) (k : ℕ) (e : V) (d : ℕ → V) : V :=
  B.lc ^ hhA B.ℓ k • e +
    ∑ t ∈ Finset.Ico 1 (k + 1), (B.lc ^ (hhA B.ℓ k - hhA B.ℓ t) * X ^ t) • d t

theorem fr_exists {u₁ : O} (hE : B.GammaXUnitShape u₁) (h9 : L.P9) (c : ZMod n) {e : V} (he : e ∈ L.N c)
    (k : ℕ) : ∃ d : ℕ → V, (∀ t, d t ∈ L.N c) ∧
      L.γ c (fr B k e d) - fr B k e d ∈ sm (X ^ (k + 1)) (L.N c) := by
  obtain ⟨b, d, hbd, hres⟩ := hh_main L hE h9 c (z := -(L.γ c e - e))
    (Submodule.neg_mem _ (h9 c e he)) k
  refine ⟨fun t => if 1 ≤ t ∧ t ≤ k then d t else 0, fun t => ?_, ?_⟩
  · dsimp only
    split_ifs with h
    · exact (hbd t h.1 h.2).2
    · exact Submodule.zero_mem _
  · have hs : ∑ t ∈ Finset.Ico 1 (k + 1), (B.lc ^ (hhA B.ℓ k - hhA B.ℓ t) * X ^ t) •
        (if 1 ≤ t ∧ t ≤ k then d t else 0) =
        ∑ t ∈ Finset.Ico 1 (k + 1), (B.lc ^ b t * X ^ t) • d t := by
      refine Finset.sum_congr rfl fun t ht => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 ht
      rw [if_pos ⟨h1, by omega⟩]
      have := (hbd t h1 (by omega)).1
      have e1 : hhA B.ℓ k - hhA B.ℓ t = b t := by omega
      rw [e1]
    simp only [fr]
    rw [hs]
    convert hres using 1
    rw [map_add, γ_lc, smul_neg, smul_sub]
    abel

theorem fr_sub (k : ℕ) (e : V) {d : ℕ → V} {S : Submodule (PowerSeries O) V}
    (hd : ∀ t, d t ∈ S) : fr B k e d - B.lc ^ hhA B.ℓ k • e ∈ sm X S := by
  simp only [fr, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun t ht => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 ht
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have : (B.lc ^ (hhA B.ℓ k - hhA B.ℓ (t + 1)) * X ^ (t + 1)) • d (t + 1) =
      (X : PowerSeries O) • ((B.lc ^ (hhA B.ℓ k - hhA B.ℓ (t + 1)) * X ^ t) • d (t + 1)) := by
    rw [smul_smul]
    congr 1
    ring
  rw [this]
  exact smul_mem_sm _ (Submodule.smul_mem _ _ (hd _))

theorem uniq_tw {u₁ : O} (hE : B.GammaXUnitShape u₁) (h9 : L.P9) (c : ZMod n) {r : ℕ}
    (G₁ : Fin r → Fin r → PowerSeries O) (M : ℕ) (δ : Fin r → V)
    (h1 : ∀ m, δ m ∈ sm X (L.N c))
    (h2 : ∀ m, L.γ c (δ m) - (δ m + (X : PowerSeries O) • ∑ l, G₁ m l • δ l) ∈
      sm (X ^ M) (L.N c)) :
    ∃ K : ℕ, ∀ m, B.lc ^ K • δ m ∈ sm (X ^ M) (L.N c) := by
  obtain ⟨hu, hpow⟩ := hE
  have key : ∀ t, t ≤ M → ∃ K : ℕ, ∀ m, B.lc ^ K • δ m ∈ sm (X ^ t) (L.N c) := by
    intro t
    induction t with
    | zero => intro _; exact ⟨0, fun m => mem_sm.2 ⟨δ m, sm_le _ _ (h1 m), by simp⟩⟩
    | succ t ih =>
      intro ht
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · exact ⟨0, fun m => by simpa using h1 m⟩
      obtain ⟨K, hK⟩ := ih (by omega)
      have hK' : ∀ m, ∃ x ∈ L.N c, (X : PowerSeries O) ^ t • x = B.lc ^ K • δ m :=
        fun m => mem_sm.1 (hK m)
      choose x hx hxe using hK'
      obtain ⟨ε, hε⟩ := hpow t ht0
      refine ⟨1 + padicValNat B.ℓ t + K, fun m => ?_⟩
      have a1 := hh_gr L hu h9 c t (hx m)
      have a2 : L.γ c ((X : PowerSeries O) ^ t • x m) - ((X : PowerSeries O) ^ t • x m +
          (X : PowerSeries O) • ∑ l, G₁ m l • (X : PowerSeries O) ^ t • x l) ∈
          sm (X ^ (t + 1)) (L.N c) := by
        have : L.γ c ((X : PowerSeries O) ^ t • x m) - ((X : PowerSeries O) ^ t • x m +
            (X : PowerSeries O) • ∑ l, G₁ m l • (X : PowerSeries O) ^ t • x l) =
            B.lc ^ K • (L.γ c (δ m) - (δ m + (X : PowerSeries O) • ∑ l, G₁ m l • δ l)) := by
          simp only [hxe]
          have hc : ∀ l, G₁ m l • B.lc ^ K • δ l = B.lc ^ K • G₁ m l • δ l :=
            fun l => smul_comm _ _ _
          simp only [hc]
          rw [γ_lc, smul_sub, smul_add, smul_comm (B.lc ^ K) X, ← Finset.smul_sum]
        rw [this]
        exact Submodule.smul_mem _ _ (hh_sm_pow_mono ht (h2 m))
      have a3 : (X : PowerSeries O) • ∑ l, G₁ m l • (X : PowerSeries O) ^ t • x l ∈
          sm (X ^ (t + 1)) (L.N c) := by
        have : (X : PowerSeries O) • ∑ l, G₁ m l • (X : PowerSeries O) ^ t • x l =
            (X : PowerSeries O) ^ (t + 1) • ∑ l, G₁ m l • x l := by
          rw [Finset.smul_sum, Finset.smul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [smul_smul, smul_smul, smul_smul]
          congr 1
          ring
        rw [this]
        exact smul_mem_sm _ (Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hx l))
      have h3 : C (u₁ ^ t - 1) • (X : PowerSeries O) ^ t • x m ∈ sm (X ^ (t + 1)) (L.N c) := by
        have := Submodule.add_mem _ (Submodule.sub_mem _ a2 a1) a3
        convert this using 1
        rw [map_sub, map_one, sub_smul, one_smul]
        abel
      have h4 := Submodule.smul_mem _ (C ((ε⁻¹ : Oˣ) : O)) h3
      convert h4 using 1
      rw [hxe, hε, smul_smul, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul, pow_add, mul_smul,
        lc_pow]
  exact key M le_rfl

def semilinearMatrixLattice (B : Base O) (n : ℕ) {r : ℕ} (Gi : Matrix (Fin r) (Fin r) (PowerSeries O)) :
    Lat B n (Fin r → PowerSeries O) where
  φ _ := 0
  γ _ :=
    { toFun := fun y => Gi.mulVec fun m => B.γ (y m)
      map_zero' := by
        have : (fun m => B.γ ((0 : Fin r → PowerSeries O) m)) = 0 := by
          funext m
          simp
        rw [this, Matrix.mulVec_zero]
      map_add' := fun y z => by
        have : (fun m => B.γ ((y + z) m)) = (fun m => B.γ (y m)) + fun m => B.γ (z m) := by
          funext m
          simp
        rw [this, Matrix.mulVec_add] }
  φ_semi := fun _ _ _ => by simp
  γ_semi := fun _ a v => by
    change Gi.mulVec (fun m => B.γ ((a • v) m)) = B.γ a • Gi.mulVec (fun m => B.γ (v m))
    rw [← Matrix.mulVec_smul]
    congr 1
    funext m
    simp
  comm := fun _ _ => by rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, map_zero]
  N _ := ⊤

theorem semilinearMatrixLattice_gamma (n : ℕ) {r : ℕ} (Gi : Matrix (Fin r) (Fin r) (PowerSeries O)) (i : ZMod n)
    (y : Fin r → PowerSeries O) : (semilinearMatrixLattice B n Gi).γ i y = Gi.mulVec fun m => B.γ (y m) := rfl

theorem semilinearMatrixLattice_regular (hX : X ∣ B.γ X) (n : ℕ) {r : ℕ} {Gi Q : Matrix (Fin r) (Fin r) (PowerSeries O)}
    (hGi : Gi = 1 - (X : PowerSeries O) • Q) : (semilinearMatrixLattice B n Gi).P9 := by
  intro i y _
  have ht : ∀ m, ∃ t, B.γ (y m) - y m = X * t := fun m => X_dvd_alg_sub B.γ hX (y m)
  choose t ht using ht
  refine mem_sm.2 ⟨t - Q.mulVec (fun m => B.γ (y m)), Submodule.mem_top, ?_⟩
  rw [semilinearMatrixLattice_gamma, hGi, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, smul_sub]
  have : (X : PowerSeries O) • t = (fun m => B.γ (y m)) - y := by
    funext m
    simp [ht m]
  rw [this]
  abel

end hinv

end XDivisibilityOfActions

open XDivisibilityOfActions

theorem height_inverse_holds : HinvOf := by
  intro O _ B u₁ n _ M V _ _ L i r e hℓ hE h9 he m₀
  have heN : ∀ k, e k ∈ L.N i := fun k => by
    rw [← he]; exact Submodule.subset_span ⟨k, rfl⟩
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · refine ⟨0, 0, fun _ => 0, fun _ => 0, fun _ _ => 0, e, fun t ht => by omega, fun k => ?_, ?_⟩
    · refine ⟨heN k, by simp, ?_⟩
      exact mem_sm.2 ⟨_, sm_le _ _ (h9 i _ (heN k)), by simp⟩
    · exact mem_sm.2 ⟨e m₀, heN m₀, by simp⟩
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩

  have hG : ∀ m, ∃ g : Fin r → PowerSeries O,
      L.γ i (e m) = e m + (X : PowerSeries O) • ∑ l, g l • e l := by
    intro m
    obtain ⟨x, hx, hxe⟩ := mem_sm.1 (h9 i _ (heN m))
    rw [← he] at hx
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    exact ⟨g, by rw [hg, hxe]; abel⟩
  choose G₁ hG₁ using hG
  set Gm : Matrix (Fin r) (Fin r) (PowerSeries O) := 1 + (X : PowerSeries O) • Matrix.of G₁ with hGm
  have hdet : IsUnit Gm.det := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have h1 : (constantCoeff (R := O)).mapMatrix Gm = 1 := by
      rw [hGm, map_add, map_one]
      ext a b
      simp
    have h2 := RingHom.map_det (constantCoeff (R := O)) Gm
    rw [h1, Matrix.det_one] at h2
    rw [h2]
    exact isUnit_one
  set Gi := Gm⁻¹ with hGi
  have hm1 : Gm * Gi = 1 := Matrix.mul_nonsing_inv _ hdet
  have hm2 : Gi * Gm = 1 := Matrix.nonsing_inv_mul _ hdet
  have hGiQ : Gi = 1 - (X : PowerSeries O) • (Gi * Matrix.of G₁) := by
    have : Gi * Gm = Gi + (X : PowerSeries O) • (Gi * Matrix.of G₁) := by
      rw [hGm, mul_add, mul_one, Matrix.mul_smul]
    rw [hm2] at this
    rw [this]
    abel
  have hXγ : X ∣ B.γ X := by
    obtain ⟨a, ha⟩ := hE.1
    exact ⟨_, ha⟩
  have h9' := semilinearMatrixLattice_regular (B := B) hXγ n hGiQ
  set K := hhA B.ℓ k with hK

  have hY : ∀ k₀ : Fin r, ∃ dY : ℕ → Fin r → PowerSeries O, ∃ τ : Fin r → PowerSeries O,
      ∀ m, B.γ (fr B k (bv O k₀) dY m) = fr B k (bv O k₀) dY m +
        X * ∑ l, G₁ m l * fr B k (bv O k₀) dY l + X ^ (k + 1) * τ m := by
    intro k₀
    obtain ⟨dY, -, hd⟩ := fr_exists (semilinearMatrixLattice B n Gi) hE h9' i (e := bv O k₀) Submodule.mem_top k
    obtain ⟨τ, -, hτ⟩ := mem_sm.1 hd
    set Y := fr B k (bv O k₀) dY with hYdef
    rw [semilinearMatrixLattice_gamma] at hτ
    refine ⟨dY, Gm.mulVec τ, fun m => ?_⟩
    have h1 : Gm.mulVec ((X : PowerSeries O) ^ (k + 1) • τ) = (fun m => B.γ (Y m)) - Gm.mulVec Y := by
      rw [hτ, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hm1, Matrix.one_mulVec]
    rw [Matrix.mulVec_smul] at h1
    have h2 := congrFun h1 m
    have h3 : Gm.mulVec Y m = Y m + X * ∑ l, G₁ m l * Y l := by
      rw [hGm, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
      simp [Matrix.mulVec, dotProduct]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h2
    rw [h3] at h2
    linear_combination -h2
  choose dY τ hYτ using hY
  set Y : Fin r → Fin r → PowerSeries O := fun k₀ => fr B k (bv O k₀) (dY k₀) with hYdef

  have hD : ∀ k₀ : Fin r, ∃ dD : ℕ → V, (∀ t, dD t ∈ L.N i) ∧
      L.γ i (fr B k (e k₀) dD) - fr B k (e k₀) dD ∈ sm (X ^ (k + 1)) (L.N i) :=
    fun k₀ => fr_exists L hE h9 i (heN k₀) k
  choose dD hdD hγD using hD
  set D : Fin r → V := fun k₀ => fr B k (e k₀) (dD k₀) with hDdef
  have hDX : ∀ k₀, D k₀ - B.lc ^ K • e k₀ ∈ sm X (L.N i) := fun k₀ => fr_sub k (e k₀) (hdD k₀)
  have hDN : ∀ k₀, D k₀ ∈ L.N i := fun k₀ => by
    have := (L.N i).add_mem (sm_le _ _ (hDX k₀)) ((L.N i).smul_mem (B.lc ^ K) (heN k₀))
    simpa using this
  have hYX : ∀ k₀ m, ∃ t, Y k₀ m = B.lc ^ K * bv O k₀ m + X * t := by
    intro k₀ m
    obtain ⟨t, -, ht⟩ := mem_sm.1 (fr_sub (B := B) k (bv O k₀) (d := dY k₀)
      (S := ⊤) (fun _ => Submodule.mem_top))
    refine ⟨t m, ?_⟩
    have := congrFun ht m
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this
    change fr B k (bv O k₀) (dY k₀) m = _
    linear_combination -this
  set nn : Fin r → V := fun m => ∑ k₀, Y k₀ m • D k₀ with hnn
  set δ : Fin r → V := fun m => B.lc ^ (K + K) • e m - nn m with hδ
  have hδ1 : ∀ m, δ m ∈ sm X (L.N i) := by
    intro m
    choose t ht using fun k₀ => hYX k₀ m
    have : δ m = -(B.lc ^ K • (D m - B.lc ^ K • e m)) -
        (X : PowerSeries O) • ∑ k₀, t k₀ • D k₀ := by
      simp only [hδ, hnn, ht, add_smul, Finset.sum_add_distrib, bv, mul_ite, mul_one, mul_zero,
        ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.smul_sum,
        smul_smul, pow_add, smul_sub]
      abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ (hDX m)))
      (smul_mem_sm _ (Submodule.sum_mem _ fun k₀ _ => Submodule.smul_mem _ _ (hDN k₀)))
  have hδ2 : ∀ m, L.γ i (δ m) - (δ m + (X : PowerSeries O) • ∑ l, G₁ m l • δ l) ∈
      sm (X ^ (k + 1)) (L.N i) := by
    intro m
    have hρ : ∀ k₀, ∃ ρ ∈ L.N i, L.γ i (D k₀) = D k₀ + (X : PowerSeries O) ^ (k + 1) • ρ := by
      intro k₀
      obtain ⟨ρ, hρ, hρe⟩ := mem_sm.1 (hγD k₀)
      exact ⟨ρ, hρ, by rw [hρe]; abel⟩
    choose ρ hρN hρe using hρ
    have hn : L.γ i (nn m) = nn m + (X : PowerSeries O) • ∑ l, G₁ m l • nn l +
        (X : PowerSeries O) ^ (k + 1) • ∑ k₀, (τ k₀ m • D k₀ + B.γ (Y k₀ m) • ρ k₀) := by
      have hsw : ∑ l, G₁ m l • nn l = ∑ k₀, (∑ l, G₁ m l * Y k₀ l) • D k₀ := by
        simp only [hnn, Finset.smul_sum, Finset.sum_smul, smul_smul]
        exact Finset.sum_comm
      rw [hsw, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib, map_sum]
      refine Finset.sum_congr rfl fun k₀ _ => ?_
      have := hYτ k₀ m
      change B.γ (Y k₀ m) = Y k₀ m + X * ∑ l, G₁ m l * Y k₀ l + X ^ (k + 1) * τ k₀ m at this
      have h5 : B.γ (Y k₀ m) • D k₀ = Y k₀ m • D k₀ +
          (X : PowerSeries O) • (∑ l, G₁ m l * Y k₀ l) • D k₀ +
          (X : PowerSeries O) ^ (k + 1) • τ k₀ m • D k₀ := by
        rw [this, add_smul, add_smul, mul_smul, mul_smul]
      rw [L.γ_semi, hρe, smul_add, h5, smul_add, smul_comm (B.γ (Y k₀ m))]
      abel
    have he' : L.γ i (B.lc ^ (K + K) • e m) = B.lc ^ (K + K) • e m +
        (X : PowerSeries O) • ∑ l, G₁ m l • B.lc ^ (K + K) • e l := by
      rw [γ_lc, hG₁, smul_add, smul_comm _ X, Finset.smul_sum]
      have hc : ∀ l, G₁ m l • B.lc ^ (K + K) • e l = B.lc ^ (K + K) • G₁ m l • e l :=
        fun l => smul_comm _ _ _
      simp only [hc]
    have : L.γ i (δ m) - (δ m + (X : PowerSeries O) • ∑ l, G₁ m l • δ l) =
        (X : PowerSeries O) ^ (k + 1) • (-∑ k₀, (τ k₀ m • D k₀ + B.γ (Y k₀ m) • ρ k₀)) := by
      simp only [hδ]
      rw [map_sub, hn, he']
      simp only [smul_sub, Finset.sum_sub_distrib, smul_neg]
      abel
    rw [this]
    refine smul_mem_sm _ (Submodule.neg_mem _ (Submodule.sum_mem _ fun k₀ _ => ?_))
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hDN k₀)) (Submodule.smul_mem _ _ (hρN k₀))
  obtain ⟨K', hK'⟩ := uniq_tw L hE h9 i G₁ (k + 1) δ hδ1 hδ2
  refine ⟨K, K + K', hhA B.ℓ, fun t => K - hhA B.ℓ t,
    fun t k₀ => if t = 0 then bv O k₀ m₀ else dY k₀ t m₀, fun k₀ => B.lc ^ K' • D k₀, ?_, ?_, ?_⟩
  · intro t ht
    refine ⟨?_, hhA_le _ hℓ t⟩
    have : hhA B.ℓ t ≤ K := by
      have hmono : Monotone (hhA B.ℓ) := monotone_nat_of_le_succ fun a => by
        rw [hhA]; omega
      exact hmono (by omega)
    change hhA B.ℓ t + (K - hhA B.ℓ t) = K
    omega
  · intro k₀
    refine ⟨Submodule.smul_mem _ _ (hDN k₀), ?_, ?_⟩
    · have : B.lc ^ K' • D k₀ - B.lc ^ (K + K') • e k₀ = B.lc ^ K' • (D k₀ - B.lc ^ K • e k₀) := by
        rw [smul_sub, smul_smul, ← pow_add, add_comm K' K]
      rw [this]
      exact Submodule.smul_mem _ _ (hDX k₀)
    · rw [γ_lc, ← smul_sub]
      exact Submodule.smul_mem _ _ (hγD k₀)
  · have hYe : ∀ k₀, ∑ t ∈ Finset.range (k + 1), B.lc ^ (K - hhA B.ℓ t) * X ^ t *
        (if t = 0 then bv O k₀ m₀ else dY k₀ t m₀) = Y k₀ m₀ := by
      intro k₀
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      simp only [hYdef, fr, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      congr 1
      · simp [hhA, hK]
      · refine Finset.sum_congr rfl fun t ht => ?_
        have := (Finset.mem_Ico.1 ht).1
        rw [if_neg (by omega)]
    simp only [hYe]
    have : B.lc ^ (K + (K + K')) • e m₀ - ∑ k₀, Y k₀ m₀ • B.lc ^ K' • D k₀ = B.lc ^ K' • δ m₀ := by
      simp only [hδ, hnn, smul_sub, Finset.smul_sum, smul_smul, ← pow_add]
      congr 1
      · congr 2
        omega
      · refine Finset.sum_congr rfl fun k₀ _ => ?_
        rw [mul_comm]
    rw [this]
    exact hK' m₀

theorem partners_primitive_holds : PartnersPrim := by
  intro O _ _ _ ϖ B n _ V _ _ L c ell hh H r S j M g sig e hϖ hdvd hp h3 hE3 hE4 hj1 hj hM hsig hP
  obtain ⟨u₁, hu⟩ := one_add_unit_pow_formula O ϖ B hϖ hdvd hp h3 hE4
  refine ⟨partner_fourth_arc_form O B n V L c ell H hE3 hE4 (hP.p9 _) hP.invX,
    partner_fourth_first_form O B n V L c ell hh H r S g hP.p5h hP.hh_le hP.mem hP.unitsAt,
    partner_fourth_second_form O B n V L c ell hh H r S hP.p5h (fun s hs => by have := hP.hh_le s hs; omega)
      hP.mem hP.unitsAt,
    partner_lattice_exists O B n V L c ell H r S j M g sig e hj (base_ring_good_holds O B j M g hE3 hE4 hM)
      (truncation_holds O B j M g sig h3 hj1 hE3 hsig) hP.span (hP.p9 _)
      (height_bound_holds O B u₁ n M V L _ hp hu hP.p9) (height_inverse_holds O B u₁ n M V L _ r e hp hu hP.p9 hP.span)
      hP.invP hP.pa1b hP.flP hP.flSat⟩

end Formalism.ExponentWindows.E

namespace Formalism.ExponentWindows.G

open TensorProduct SlopeTestRemainingChoices

namespace PT

section lin
variable {LL Ks D : Type} [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]

lemma xi_mono {X Y : ℤ → Submodule LL D} (h : ∀ i, X i ≤ Y i) {f : Amb LL Ks D}
    (hf : f ∈ Xi Ks X) : f ∈ Xi Ks Y :=
  fun i => Submodule.baseChange_mono Ks (h i) (hf i)

lemma tw_mono (m : ℤ) : Monotone (Tw (LL := LL) (D := D) m) := by
  intro i j hij
  simp only [Tw]
  split_ifs <;> first | exact le_rfl | exact bot_le | exact le_top | omega

lemma fil_top (Fil : ℤ → Submodule LL D) (hF : IsFilt Fil) (a : ℤ)
    (h : ∀ u, u < a → Fil u = Fil (u + 1)) (u : ℤ) (hu : u ≤ a) : Fil u = ⊤ := by
  obtain ⟨lo, hlo⟩ := hF.2.1
  by_cases hul : u ≤ lo
  · exact top_le_iff.1 (hlo ▸ hF.1 hul)
  · have h1 := fil_const Fil (u - lo).toNat lo (fun v _ h2 => h v (by omega))
    have h2 : lo + ((u - lo).toNat : ℤ) = u := by omega
    rw [h2, hlo] at h1
    exact h1.symm

lemma cf_smul_cst (x : HahnSeries ℤ Ks) (d : D) (i : ℤ) :
    cf (x • cstD Ks d) i = x.coeff i • ((1 : Ks) ⊗ₜ[LL] d) := by
  unfold cf cstD
  rw [HahnModule.coeff_smul_right (s := {0}) (Set.isPWO_singleton 0)
    (by simpa using HahnSeries.support_single_subset)]
  by_cases hx : x.coeff i = 0
  · rw [hx, zero_smul]
    refine Finset.sum_eq_zero fun ij hij => ?_
    rw [Finset.mem_vaddAntidiagonal] at hij
    obtain ⟨h1, h2, h3⟩ := hij
    have h4 : ij.2 = 0 := h2
    have h5 : ij.1 = i := by
      have : ij.1 + ij.2 = i := h3
      omega
    exact absurd (h5 ▸ hx) h1
  · rw [Finset.sum_eq_single (i, 0)]
    · simp
    · intro ij hij hne
      rw [Finset.mem_vaddAntidiagonal] at hij
      obtain ⟨_, h2, h3⟩ := hij
      have h4 : ij.2 = 0 := h2
      have h5 : ij.1 = i := by
        have : ij.1 + ij.2 = i := h3
        omega
      exact absurd (Prod.ext h5 h4) hne
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_vaddAntidiagonal]
      exact ⟨hx, rfl, by simp⟩

lemma exists_dual {r : ℕ} (lam : Fin r → D) (h : LinearIndependent LL lam) (k : Fin r) :
    ∃ f : D →ₗ[LL] LL, ∀ j, f (lam j) = if j = k then 1 else 0 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination LL lam)
    (LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 h))
  refine ⟨LinearMap.proj k ∘ₗ g, fun j => ?_⟩
  have h1 : lam j = Fintype.linearCombination LL lam (Pi.single j 1) := by
    rw [Fintype.linearCombination_apply_single, one_smul]
  have h2 : g (Fintype.linearCombination LL lam (Pi.single j 1)) = Pi.single j 1 :=
    LinearMap.congr_fun hg _
  rw [LinearMap.comp_apply, h1, h2, LinearMap.proj_apply, Pi.single_apply]
  simp only [eq_comm]

lemma coeffs_zero {r : ℕ} (lam : Fin r → D) (h : LinearIndependent LL lam) (x : Fin r → Ks)
    (h0 : ∑ k, x k • ((1 : Ks) ⊗ₜ[LL] lam k) = 0) (k : Fin r) : x k = 0 := by
  obtain ⟨f, hf⟩ := exists_dual lam h k
  have h1 := congrArg ((TensorProduct.rid LL Ks).toLinearMap ∘ₗ LinearMap.lTensor Ks f) h0
  rw [map_sum, map_zero] at h1
  rw [Finset.sum_eq_single k] at h1
  · simpa [TensorProduct.smul_tmul', hf] using h1
  · intro j _ hj
    simp [TensorProduct.smul_tmul', hf, hj]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

lemma tp_smul_tw (k : ℕ) (w : PowerSeries Ks) (m : ℤ) {f : Amb LL Ks D}
    (hf : f ∈ Xi Ks (Tw (LL := LL) (D := D) m)) :
    HahnSeries.ofPowerSeries ℤ Ks (PowerSeries.X ^ k * w) • f ∈
      Xi Ks (Tw (LL := LL) (D := D) (m + k)) := by
  rw [map_mul, HahnSeries.ofPowerSeries_X_pow, mul_smul]
  have h1 := xi_module_structure LL Ks D _ (tw_mono m) w f hf
  change tp Ks (k : ℤ) • _ ∈ _
  rw [xi_shift_holds LL Ks D]
  refine xi_mono (fun i => ?_) h1
  simp only [Tw]
  split_ifs <;> first | exact le_rfl | exact bot_le | exact le_top | omega

lemma tw_shift (b a i : ℤ) : Tw (LL := LL) (D := D) b (i + a) = Tw (b - a) i := by
  simp only [Tw]
  split_ifs <;> first | rfl | omega

lemma tp_mem_tw (a m : ℤ) (f : Amb LL Ks D) :
    tp Ks a • f ∈ Xi Ks (Tw (LL := LL) (D := D) m) ↔ f ∈ Xi Ks (Tw (LL := LL) (D := D) (m - a)) := by
  rw [xi_shift_holds LL Ks D]
  constructor
  · exact xi_mono fun i => le_of_eq (tw_shift m a i)
  · exact xi_mono fun i => le_of_eq (tw_shift m a i).symm

lemma tp_mul (a b : ℤ) : tp Ks a * tp Ks b = tp Ks (a + b) := by
  unfold tp
  rw [HahnSeries.single_mul_single, one_mul]

lemma ofPS_unit_X (ε : (PowerSeries Ks)ˣ) (a : ℕ) :
    HahnSeries.ofPowerSeries ℤ Ks ((ε : PowerSeries Ks) * PowerSeries.X ^ a) =
      HahnSeries.ofPowerSeries ℤ Ks (ε : PowerSeries Ks) * tp Ks (a : ℤ) := by
  rw [map_mul, HahnSeries.ofPowerSeries_X_pow]
  rfl

lemma ofPS_inv_mul (ε : (PowerSeries Ks)ˣ) :
    HahnSeries.ofPowerSeries ℤ Ks ((ε⁻¹ : (PowerSeries Ks)ˣ) : PowerSeries Ks) *
      HahnSeries.ofPowerSeries ℤ Ks (ε : PowerSeries Ks) = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

lemma unit_smul_mem {X : ℤ → Submodule LL D} (hX : Monotone X) {a : PowerSeries Ks} (ha : IsUnit a)
    {f : Amb LL Ks D} (h : HahnSeries.ofPowerSeries ℤ Ks a • f ∈ Xi Ks X) : f ∈ Xi Ks X := by
  obtain ⟨u, rfl⟩ := ha
  have h1 := xi_module_structure LL Ks D X hX ((u⁻¹ : (PowerSeries Ks)ˣ) : PowerSeries Ks) _ h
  rwa [← mul_smul, ofPS_inv_mul, one_smul] at h1

lemma fl_iff (ε₁ ε₃ : (PowerSeries Ks)ˣ) (a b : ℕ) (f : Amb LL Ks D) :
    (∃ x ∈ Xi Ks (Tw (LL := LL) (D := D) 0),
      HahnSeries.ofPowerSeries ℤ Ks ((ε₁ : PowerSeries Ks) * PowerSeries.X ^ a) • f =
        HahnSeries.ofPowerSeries ℤ Ks ((ε₃ : PowerSeries Ks) * PowerSeries.X ^ b) • x) ↔
      f ∈ Xi Ks (Tw (LL := LL) (D := D) ((b : ℤ) - a)) := by
  rw [ofPS_unit_X, ofPS_unit_X]
  constructor
  · rintro ⟨x, hx, he⟩
    rw [← tp_mem_tw]
    have h1 : tp Ks (a : ℤ) • f =
        HahnSeries.ofPowerSeries ℤ Ks (((ε₁⁻¹ * ε₃ : (PowerSeries Ks)ˣ)) : PowerSeries Ks) •
          (tp Ks (b : ℤ) • x) := by
      have h2 := congrArg (fun z => HahnSeries.ofPowerSeries ℤ Ks
        ((ε₁⁻¹ : (PowerSeries Ks)ˣ) : PowerSeries Ks) • z) he
      simp only [← mul_smul, ← mul_assoc, ofPS_inv_mul, one_mul] at h2
      rw [h2, Units.val_mul, map_mul, mul_smul, mul_smul]
    rw [h1]
    refine xi_module_structure LL Ks D _ (tw_mono _) _ _ ?_
    rw [tp_mem_tw, sub_self]
    exact hx
  · intro hf
    refine ⟨HahnSeries.ofPowerSeries ℤ Ks (((ε₃⁻¹ * ε₁ : (PowerSeries Ks)ˣ)) : PowerSeries Ks) •
      (tp Ks ((a : ℤ) - b) • f), ?_, ?_⟩
    · refine xi_module_structure LL Ks D _ (tw_mono _) _ _ ?_
      rw [tp_mem_tw]
      have : (0 : ℤ) - ((a : ℤ) - b) = (b : ℤ) - a := by ring
      rw [this]
      exact hf
    · rw [← mul_smul, ← mul_smul]
      congr 1
      rw [Units.val_mul, map_mul]
      have h3 : tp Ks (a : ℤ) = tp Ks (b : ℤ) * tp Ks ((a : ℤ) - b) := by
        rw [tp_mul]
        congr 1
        ring
      have h4 := ofPS_inv_mul ε₃
      rw [h3]
      calc _ = (HahnSeries.ofPowerSeries ℤ Ks ((ε₃⁻¹ : (PowerSeries Ks)ˣ) : PowerSeries Ks) *
            HahnSeries.ofPowerSeries ℤ Ks (ε₃ : PowerSeries Ks)) *
            (HahnSeries.ofPowerSeries ℤ Ks (ε₁ : PowerSeries Ks) *
              (tp Ks (b : ℤ) * tp Ks ((a : ℤ) - b))) := by rw [h4, one_mul]
        _ = _ := by ring

end lin

section model
variable {O : Type} [CommRing O] {B : E.Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V] {L : E.Lat B n V} {c : ZMod n} {ell : ℕ} {Λ : PowerSeries O} {r : ℕ}
  {S : E.LevelData L c ell Λ r} {LL : Type} [Field LL] [Algebra O LL]
  {Ks : ℕ → Type} [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] {Δ D : Type}
  [AddCommGroup D] [Module LL D]

lemma rho_prod (R : LevelModel S LL Ks Δ D) (hb : R.K1b) (hu : R.UnitsAt) (s : ℕ) (hs : s < ell)
    (a : ℕ → ℕ) : ∃ ε : (PowerSeries (Ks s))ˣ,
      R.ρ s (∏ s' ∈ Finset.range ell, B.p s' ^ a s') =
        (ε : PowerSeries (Ks s)) * PowerSeries.X ^ a s := by
  obtain ⟨ε, hε⟩ := hb s hs
  have h1 : IsUnit (R.ρ s (∏ s' ∈ (Finset.range ell).erase s, B.p s' ^ a s')) := by
    rw [map_prod]
    refine IsUnit.prod_iff.2 fun s' hs' => ?_
    rw [map_pow]
    exact ((hu s hs).2 s' (Finset.mem_range.1 (Finset.mem_of_mem_erase hs'))
      (Finset.ne_of_mem_erase hs')).pow _
  refine ⟨ε ^ a s * h1.unit, ?_⟩
  rw [← Finset.mul_prod_erase (Finset.range ell) (fun s' => B.p s' ^ a s') (Finset.mem_range.2 hs),
    map_mul, map_pow, hε, Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  ring

end model

end PT

open PT

theorem third_partner_orders : HeightLeTruncOrder := by
  intro ell j ℓ M g G Sz η h kind b ⟨h1, h2, h3, h4, h5, h6⟩ s hs
  have h7 := h6 s hs
  cases hk : kind s with
  | thin =>
    simp only [HK, ordF]
    split_ifs <;> omega
  | up =>
    obtain ⟨h8, h9⟩ := h7 (by rw [hk]; intro h; cases h)
    simp only [HK, ordF, if_pos h9]
    omega
  | down =>
    obtain ⟨h8, h9⟩ := h7 (by rw [hk]; intro h; cases h)
    simp only [HK, ordF, if_pos h9]
    omega

theorem third_partner_estimate : FiltrationLeOf := by
  intro O _ B n V _ _ L c ell Λ r S LL _ _ Ks _ _ Δ D _ _ R j M g G Sz h H hN hH hF hFl s hs
  have hord := third_partner_orders ell j B.ℓ M g G Sz R.η h R.kind R.b hN s hs
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hN
  obtain ⟨hfil, hJ⟩ := hF s hs
  have hHs := hH s hs
  constructor
  · intro e he
    rw [R.mem_Nl s hs]
    refine xi_mono (fun i => ?_) ((hFl s hs e).1 he)
    simp only [Tw]
    split_ifs with hi
    · refine le_of_eq (Eq.symm ?_)
      cases hk : R.kind s with
      | thin =>
        rw [hk] at hJ hord hHs
        simp only [HK] at hord hHs
        refine fil_top _ hfil (-(G : ℤ)) (fun u hu => ?_) _ (by omega)
        by_contra hne
        have := hJ u hne
        omega
      | up =>
        rw [hk] at hJ hord hHs
        simp only [HK] at hord hHs
        refine fil_top _ hfil (-(R.η : ℤ)) (fun u hu => ?_) _ (by omega)
        by_contra hne
        have := hJ u hne
        omega
      | down =>
        rw [hk] at hJ hord hHs
        simp only [HK] at hord hHs
        obtain ⟨h8, h9⟩ := h6 s hs (by rw [hk]; intro h; cases h)
        have h10 : ordF ell j B.ℓ M g s = (B.ℓ - 1) * M := if_pos h9
        rw [h10] at hord hi
        by_cases hc : R.η ≤ R.b s + Sz
        · refine fil_top _ hfil (-(R.b s : ℤ) - Sz) (fun u hu => ?_) _ (by omega)
          by_contra hne
          have := hJ u hne
          omega
        · refine fil_top _ hfil (-(R.η : ℤ)) (fun u hu => ?_) _ (by push_cast at hi; omega)
          by_contra hne
          have := hJ u hne
          omega
    · exact bot_le
  · intro e he
    rw [R.mem_Nb s hs]
    refine xi_mono (fun i => ?_) ((hFl s hs e).1 he)
    simp only [Tw]
    split_ifs with hi
    · cases hk : R.kind s with
      | thin =>
        rw [hk] at hord hHs
        simp only [HK] at hord hHs
        simp only [NbK, NbThin]
        rw [if_neg (by omega)]
      | up =>
        rw [hk] at hord hHs
        simp only [HK] at hord hHs
        simp only [NbK, NbUp]
        rw [if_neg (by omega), if_neg (by omega)]
      | down =>
        rw [hk] at hord hHs
        simp only [HK] at hord hHs
        simp only [NbK, NbDown]
        rw [if_neg (by omega), if_neg (by omega)]
    · exact bot_le

theorem filtration_regular_holds : FlRegOf := by
  intro O _ B n V _ _ L c ell Λ r S LL _ _ Ks _ _ Δ D _ _ R ϖ H od lam hΛ hb hFl hod hloc hli hC
    s hs y hy
  obtain ⟨ε, hε⟩ := hb s hs

  have hL : Λ = B.p s ^ H s * ∏ s' ∈ (Finset.range ell).erase s, B.p s' ^ H s' := by
    rw [hΛ, Finset.mul_prod_erase (Finset.range ell) (fun s' => B.p s' ^ H s')
      (Finset.mem_range.2 hs)]
    rfl
  have hdiv : ∃ w : PowerSeries (Ks s), R.ρ s Λ = PowerSeries.X ^ H s * w := by
    refine ⟨(ε : PowerSeries (Ks s)) ^ H s *
      R.ρ s (∏ s' ∈ (Finset.range ell).erase s, B.p s' ^ H s'), ?_⟩
    rw [congrArg (R.ρ s) hL, map_mul, map_pow, hε]
    ring
  obtain ⟨w, hw⟩ := hdiv
  have h1 : R.pr s (S.locL s y) ∈ Xi (Ks s) (Tw (LL := LL) (D := D) 0) :=
    xi_mono (fun i => by
      have := hod s hs
      simp only [Tw]
      split_ifs <;> first | exact le_rfl | exact bot_le | exact le_top | omega)
      ((hFl s hs _).1 hy)
  have h2 := tp_smul_tw (H s) w 0 h1
  rw [← hw, ← R.pr_smul, hloc s hs y] at h2
  have h3 : ∀ k, PowerSeries.X ^ H s ∣ R.ρ s (y k) := by
    intro k
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    have h4 := h2 (m : ℤ)
    rw [cf_sum] at h4
    simp only [cf_smul_cst, Tw] at h4
    rw [if_neg (by omega), Submodule.baseChange_bot, Submodule.mem_bot] at h4
    have h5 := coeffs_zero lam hli _ h4 k
    rwa [HahnSeries.ofPowerSeries_apply_coeff] at h5
  choose N z hz using fun k => hC s hs (H s) (y k) (h3 k)
  refine ⟨Finset.univ.sup N, fun k => PowerSeries.C (ϖ ^ (Finset.univ.sup N - N k)) * z k, ?_⟩
  funext k
  have hle : N k ≤ Finset.univ.sup N := Finset.le_sup (Finset.mem_univ k)
  simp only [Pi.smul_apply, smul_eq_mul]
  have : ϖ ^ Finset.univ.sup N = ϖ ^ (Finset.univ.sup N - N k) * ϖ ^ N k := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [this, map_mul, mul_assoc, hz k]
  ring

theorem filtration_shape_holds : FShapeOf := by
  intro O _ B ell j M g hj h3
  obtain ⟨k, rfl⟩ : ∃ k, ell = k + j := ⟨ell - j, by omega⟩
  obtain ⟨u, hu⟩ := E.GoodPlacesAlt.e3it B h3 k
  refine ⟨u ^ M, ?_⟩
  have hA : (⇑B.φ)^[k] ((PowerSeries.X : PowerSeries O) ^ M) = ((⇑B.φ)^[k] PowerSeries.X) ^ M := by
    rw [E.GoodPlacesAlt.it_eq, map_pow]
  have hB : (⇑B.φ)^[k] (∏ s ∈ Finset.range j, B.p s ^ (3 * g)) =
      ∏ s ∈ Finset.range j, B.p (k + s) ^ (3 * g) := by
    rw [E.GoodPlacesAlt.it_eq, map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, ← E.GoodPlacesAlt.it_eq, E.GoodPlacesAlt.it_p, add_comm]
  have h1 : ∏ x ∈ Finset.range k, B.p x ^ ordF (k + j) j B.ℓ M g x =
      (∏ x ∈ Finset.range k, B.p x ^ (B.ℓ - 1)) ^ M := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [ordF, if_pos (by have := Finset.mem_range.1 hx; omega), pow_mul]
  have h2 : ∏ x ∈ Finset.range j, B.p (k + x) ^ ordF (k + j) j B.ℓ M g (k + x) =
      ∏ s ∈ Finset.range j, B.p (k + s) ^ (3 * g) := by
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [ordF, if_neg (by omega)]
  unfold E.Base.ff' E.Base.ff
  rw [Nat.add_sub_cancel, E.GoodPlacesAlt.it_mul, hA, hB, hu, Finset.prod_range_add, h1, h2, Units.val_pow_eq_pow_val]
  ring

theorem filtration_isomorphism_holds : FlIsOf := by
  intro O _ B n V _ _ L c ell Λ r S LL _ _ Ks _ _ Δ D _ _ R j M g H hΛ hf hb hu hFl s hs e
  obtain ⟨u, hfu⟩ := hf
  obtain ⟨ε₁, h1⟩ := rho_prod R hb hu s hs H
  obtain ⟨ε₂, h2⟩ := rho_prod R hb hu s hs (ordF ell j B.ℓ M g)
  have h1' : R.ρ s Λ = (ε₁ : PowerSeries (Ks s)) * PowerSeries.X ^ H s :=
    (congrArg (R.ρ s) hΛ).trans h1
  have hX := ((hu s hs).1).pow M
  have h3 : R.ρ s (B.ff' ell j M g) =
      ((Units.map (R.ρ s : PowerSeries O →* PowerSeries (Ks s)) u * hX.unit * ε₂ :
        (PowerSeries (Ks s))ˣ) : PowerSeries (Ks s)) * PowerSeries.X ^ ordF ell j B.ℓ M g s := by
    rw [hfu, map_mul, map_mul, map_pow, h2]
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, IsUnit.unit_spec]
    ring
  rw [hFl s hs e, R.pr_smul, h1', h3]
  exact fl_iff _ _ _ _ _

theorem units_at_level_holds : UnitsAtOf := by
  intro O _ B n V _ _ L c ell Λ r S LL _ _ Ks _ _ Δ D _ _ R hu hF s hs
  refine ⟨fun e he => ?_, fun s' hs' hne e he => ?_⟩
  · rw [R.mem_Nl s hs, R.pr_smul] at he
    rw [R.mem_Nl s hs]
    exact unit_smul_mem (fil_mono (hF s hs)) (hu s hs).1 he
  · rw [R.mem_Nl s hs, R.pr_smul] at he
    rw [R.mem_Nl s hs]
    exact unit_smul_mem (fil_mono (hF s hs)) ((hu s hs).2 s' hs' hne) he

theorem filtration_saturation_holds : FlSatOf := by
  intro O _ B n V _ _ L c ell Λ r S LL _ _ Ks _ _ Δ D _ _ R od hl hFl s hs e he
  rw [hFl s hs, R.pr_smul, E.Base.lc, R.ρ_C] at he
  rw [hFl s hs]
  exact unit_smul_mem (tw_mono _)
    (((IsUnit.mk0 _ hl).map (algebraMap LL (Ks s))).map PowerSeries.C) he

theorem filtration_partner_holds : FlPOf := by
  intro O _ B n V _ _ L c ell Λ r S LL _ _ Ks _ _ Δ D _ _ R f' hFl hreg s hs w
  rw [hFl s hs]
  refine ⟨_, hreg s hs w, ?_⟩
  rw [smul_comm, R.pr_smul]

theorem partners_model_holds : PartnersModel := by
  intro O _ _ _ ϖ B n _ V _ _ L c ell hh H r S LL _ _ Ks _ _ Δ D _ _ R j M g G Sz h sig e lam
    hϖ hdvd hp h3 hE3 hE4 hj1 hj hsig hP
  have hFl := filtration_isomorphism_holds O B n V L c ell _ r S LL Ks Δ D R j M g H rfl
    (filtration_shape_holds O B ell j M g hj hE3) hP.k1b hP.unitsAt hP.flDef
  have hM : 3 * g ≤ (B.ℓ - 1) * M := by
    obtain ⟨h1, -, -, -, h5, -⟩ := hP.num
    omega
  have hod : ∀ s < ell, (0 : ℤ) ≤ (ordF ell j B.ℓ M g s : ℤ) - (H s : ℤ) := by
    intro s hs
    have h1 := third_partner_orders ell j B.ℓ M g G Sz R.η h R.kind R.b hP.num s hs
    rw [hP.H_eq s hs]
    cases hk : R.kind s <;> simp only [hk] at h1 ⊢ <;> omega
  obtain ⟨a1, a2, a3, a4⟩ := E.partners_primitive_holds O ϖ B n V L c ell hh H r S j M g sig e hϖ hdvd hp
    h3 hE3 hE4 hj1 hj hM hsig
    { invX := hP.invX, invP := hP.invP, p9 := hP.p9, p5h := hP.p5h, hh_le := hP.hh_le,
      span := hP.span, mem := hP.mem, pa1b := hP.pa1b,
      unitsAt := units_at_level_holds O B n V L c ell _ r S LL Ks Δ D R hP.unitsAt
        (fun s hs => (hP.filt s hs).1.1),
      flP := filtration_partner_holds O B n V L c ell _ r S LL Ks Δ D R _ hP.flDef hP.locReg,
      flSat := filtration_saturation_holds O B n V L c ell _ r S LL Ks Δ D R _ hP.ell_ne hFl }
  exact ⟨a1, a2, a3, a4,
    third_partner_estimate O B n V L c ell _ r S LL Ks Δ D R j M g G Sz h H hP.num hP.H_eq hP.filt hFl,
    filtration_regular_holds O B n V L c ell _ r S LL Ks Δ D R ϖ H _ lam rfl hP.k1b hFl hod hP.locLIs
      hP.lamInd hP.compl⟩

end Formalism.ExponentWindows.G
