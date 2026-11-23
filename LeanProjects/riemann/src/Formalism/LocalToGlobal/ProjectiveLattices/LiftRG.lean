import Formalism.LocalToGlobal.ProjectiveLattices.LiftCurveSt

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain Finset

section Gen

variable {Λ : Type*} [CommRing Λ] {σ : Type*} [DecidableEq σ] (hd : (σ →₀ ℕ) → Λ →+ Λ)

def iterHd (l : List (σ →₀ ℕ)) (x : Λ) : Λ := l.foldr (fun β y => hd β y) x

theorem iterHd_nil (x : Λ) : iterHd hd [] x = x := rfl

theorem iterHd_cons (β : σ →₀ ℕ) (l : List (σ →₀ ℕ)) (x : Λ) :
    iterHd hd (β :: l) x = hd β (iterHd hd l x) := rfl

theorem iterHd_add (l : List (σ →₀ ℕ)) (x y : Λ) : iterHd hd l (x + y) = iterHd hd l x + iterHd hd l y := by
  induction l with
  | nil => rfl
  | cons β l ih => rw [iterHd_cons, iterHd_cons, iterHd_cons, ih, map_add]

theorem iterHd_neg (l : List (σ →₀ ℕ)) (x : Λ) : iterHd hd l (-x) = -iterHd hd l x := by
  induction l with
  | nil => rfl
  | cons β l ih => rw [iterHd_cons, iterHd_cons, ih, map_neg]

theorem iterHd_zero (l : List (σ →₀ ℕ)) : iterHd hd l 0 = 0 := by
  induction l with
  | nil => rfl
  | cons β l ih => rw [iterHd_cons, ih, map_zero]

variable {hd}

theorem hd_one' (hd0 : ∀ x, hd 0 x = x)
    (hdm : ∀ β x z, hd β (x * z) = ∑ q ∈ antidiagonal β, hd q.1 x * hd q.2 z) (β : σ →₀ ℕ) (hβ : β ≠ 0) :
    hd β 1 = 0 := by
  induction hn : Finsupp.degree β using Nat.strong_induction_on generalizing β with
  | _ n ih =>
  have h := hdm β 1 1
  rw [mul_one] at h
  have h0 : ((0 : σ →₀ ℕ), β) ∈ antidiagonal β := mem_antidiagonal.2 (zero_add β)
  have h1 : (β, (0 : σ →₀ ℕ)) ∈ (antidiagonal β).erase (0, β) :=
    mem_erase.2 ⟨fun h => hβ (congrArg Prod.fst h), mem_antidiagonal.2 (add_zero β)⟩
  rw [← add_sum_erase _ _ h0, ← add_sum_erase _ _ h1, hd0, one_mul, mul_one] at h
  have hr : ∑ q ∈ ((antidiagonal β).erase (0, β)).erase (β, 0), hd q.1 1 * hd q.2 1 = 0 := by
    refine sum_eq_zero fun q hq => ?_
    have hq2 := mem_erase.1 hq
    have hq1 := mem_erase.1 hq2.2
    have h12 : q.1 + q.2 = β := mem_antidiagonal.1 hq1.2
    have hne1 : q.1 ≠ 0 := fun h => hq1.1 (Prod.ext h (by rw [← h12, h, zero_add]))
    have hne2 : q.2 ≠ 0 := fun h => hq2.1 (Prod.ext (by rw [← h12, h, add_zero]) h)
    have hd2 : Finsupp.degree q.2 ≠ 0 := fun h => hne2 ((Finsupp.degree_eq_zero_iff _).1 h)
    have hlt : Finsupp.degree q.1 < n := by
      rw [← hn, ← h12, map_add]; omega
    rw [ih _ hlt q.1 hne1 rfl, zero_mul]
  rw [hr, add_zero] at h
  have : hd β 1 + hd β 1 = hd β 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

theorem iterHd_one (hd0 : ∀ x, hd 0 x = x)
    (hdm : ∀ β x z, hd β (x * z) = ∑ q ∈ antidiagonal β, hd q.1 x * hd q.2 z) (l : List (σ →₀ ℕ)) :
    iterHd hd l 1 = 0 ∨ iterHd hd l 1 = 1 := by
  induction l with
  | nil => exact Or.inr rfl
  | cons β l ih =>
    rw [iterHd_cons]
    rcases ih with h | h
    · left; rw [h, map_zero]
    · rw [h]
      by_cases hβ : β = 0
      · right; rw [hβ, hd0]
      · left; exact hd_one' hd0 hdm β hβ

theorem low_mul' (hdm : ∀ β x z, hd β (x * z) = ∑ q ∈ antidiagonal β, hd q.1 x * hd q.2 z) (I : Ideal Λ)
    {n m : ℕ} {z z' : Λ} (hz : ∀ β, hd β z ∈ I ^ (n - Finsupp.degree β))
    (hz' : ∀ β, hd β z' ∈ I ^ (m - Finsupp.degree β)) (β : σ →₀ ℕ) :
    hd β (z * z') ∈ I ^ (n + m - Finsupp.degree β) := by
  rw [hdm]
  refine Ideal.sum_mem _ fun q hq => ?_
  have h12 := mem_antidiagonal.1 hq
  have h := Ideal.mul_mem_mul (hz q.1) (hz' q.2)
  rw [← pow_add] at h
  refine Ideal.pow_le_pow_right ?_ h
  rw [← h12, map_add]
  omega

theorem hd_pow_mem' (hd0 : ∀ x, hd 0 x = x)
    (hdm : ∀ β x z, hd β (x * z) = ∑ q ∈ antidiagonal β, hd q.1 x * hd q.2 z) (I : Ideal Λ) (n : ℕ) {z : Λ}
    (hz : z ∈ I ^ n) (β : σ →₀ ℕ) : hd β z ∈ I ^ (n - Finsupp.degree β) := by
  induction n generalizing z β with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at hz
    refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun x y hx hy => ?_) β
    · intro β
      have hb1 : ∀ β', hd β' b ∈ I ^ (1 - Finsupp.degree β') := fun β' => by
        by_cases h : β' = 0
        · rw [h, hd0, map_zero, Nat.sub_zero, pow_one]; exact hb
        · have : Finsupp.degree β' ≠ 0 := fun h' => h ((Finsupp.degree_eq_zero_iff _).1 h')
          rw [show 1 - Finsupp.degree β' = 0 by omega, pow_zero, Ideal.one_eq_top]
          exact Submodule.mem_top
      exact low_mul' hdm I (fun β' => ih ha β') hb1 β
    · intro β
      rw [map_add]
      exact Ideal.add_mem _ (hx β) (hy β)

def stabSub (hd0 : ∀ x, hd 0 x = x)
    (hdm : ∀ β x z, hd β (x * z) = ∑ q ∈ antidiagonal β, hd q.1 x * hd q.2 z) (M : Subring Λ) : Subring Λ where
  carrier := {r | ∀ l, iterHd hd l r ∈ M}
  zero_mem' := fun l => by rw [iterHd_zero]; exact M.zero_mem
  one_mem' := fun l => by
    rcases iterHd_one hd0 hdm l with h | h <;> rw [h]
    · exact M.zero_mem
    · exact M.one_mem
  add_mem' := fun ha hb l => by rw [iterHd_add]; exact M.add_mem (ha l) (hb l)
  neg_mem' := fun ha l => by rw [iterHd_neg]; exact M.neg_mem (ha l)
  mul_mem' := by
    intro a b ha hb
    let A : AddSubgroup Λ := AddSubgroup.closure {z | ∃ l₁ l₂, z = iterHd hd l₁ a * iterHd hd l₂ b}
    have hA : ∀ β, ∀ z ∈ A, hd β z ∈ A := by
      intro β z hz
      refine AddSubgroup.closure_induction (fun x hx => ?_) ?_ (fun x y _ _ hx hy => ?_) (fun x _ hx => ?_) hz
      · obtain ⟨l₁, l₂, rfl⟩ := hx
        rw [hdm]
        exact AddSubgroup.sum_mem _ fun q _ => AddSubgroup.subset_closure ⟨q.1 :: l₁, q.2 :: l₂, rfl⟩
      · rw [map_zero]; exact A.zero_mem
      · rw [map_add]; exact A.add_mem hx hy
      · rw [map_neg]; exact A.neg_mem hx
    have hAl : ∀ l, iterHd hd l (a * b) ∈ A := by
      intro l
      induction l with
      | nil => exact AddSubgroup.subset_closure ⟨[], [], rfl⟩
      | cons β l ih => rw [iterHd_cons]; exact hA β _ ih
    have hAM : A ≤ M.toAddSubgroup := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨l₁, l₂, rfl⟩
      exact M.mul_mem (ha l₁) (hb l₂)
    exact fun l => hAM (hAl l)

theorem stabSub_le (hd0 : ∀ x, hd 0 x = x)
    (hdm : ∀ β x z, hd β (x * z) = ∑ q ∈ antidiagonal β, hd q.1 x * hd q.2 z) (M : Subring Λ) :
    stabSub hd0 hdm M ≤ M := fun _ h => h []

theorem stabSub_hd (hd0 : ∀ x, hd 0 x = x)
    (hdm : ∀ β x z, hd β (x * z) = ∑ q ∈ antidiagonal β, hd q.1 x * hd q.2 z) (M : Subring Λ) (β : σ →₀ ℕ)
    {r : Λ} (hr : r ∈ stabSub hd0 hdm M) : hd β r ∈ stabSub hd0 hdm M := fun l => by
  have := hr (l ++ [β])
  simpa [iterHd, List.foldr_append] using this

def appSub {L : Type*} [CommRing L] (ι : L →+* Λ) (F : Subring L) (I : Ideal Λ) : Subring Λ where
  carrier := {r | ∀ n : ℕ, ∃ f ∈ F, r - ι f ∈ I ^ n}
  zero_mem' := fun n => ⟨0, F.zero_mem, by rw [map_zero, sub_zero]; exact Ideal.zero_mem _⟩
  one_mem' := fun n => ⟨1, F.one_mem, by rw [map_one, sub_self]; exact Ideal.zero_mem _⟩
  add_mem' := by
    intro a b ha hb n
    obtain ⟨f, hf, hfa⟩ := ha n
    obtain ⟨g, hg, hgb⟩ := hb n
    refine ⟨f + g, F.add_mem hf hg, ?_⟩
    have : a + b - ι (f + g) = (a - ι f) + (b - ι g) := by rw [map_add]; ring
    rw [this]; exact Ideal.add_mem _ hfa hgb
  neg_mem' := by
    intro a ha n
    obtain ⟨f, hf, hfa⟩ := ha n
    refine ⟨-f, F.neg_mem hf, ?_⟩
    have : -a - ι (-f) = -(a - ι f) := by rw [map_neg]; ring
    rw [this]; exact Submodule.neg_mem _ hfa
  mul_mem' := by
    intro a b ha hb n
    obtain ⟨f, hf, hfa⟩ := ha n
    obtain ⟨g, hg, hgb⟩ := hb n
    refine ⟨f * g, F.mul_mem hf hg, ?_⟩
    have : a * b - ι (f * g) = a * (b - ι g) + (a - ι f) * ι g := by rw [map_mul]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hgb) (Ideal.mul_mem_right _ _ hfa)

theorem appSub_hd (hd0 : ∀ x, hd 0 x = x)
    (hdm : ∀ β x z, hd β (x * z) = ∑ q ∈ antidiagonal β, hd q.1 x * hd q.2 z)
    {L : Type*} [CommRing L] (ι : L →+* Λ) (F : Subring L) (I : Ideal Λ) (hL : (σ →₀ ℕ) → L → L)
    (hdι : ∀ β x, hd β (ι x) = ι (hL β x)) (hF : ∀ β, ∀ f ∈ F, hL β f ∈ F) (β : σ →₀ ℕ) {r : Λ}
    (hr : r ∈ appSub ι F I) : hd β r ∈ appSub ι F I := by
  intro n
  obtain ⟨f, hf, hfr⟩ := hr (n + Finsupp.degree β)
  refine ⟨hL β f, hF β f hf, ?_⟩
  have h := hd_pow_mem' hd0 hdm I _ hfr β
  rwa [map_sub, hdι, Nat.add_sub_cancel] at h

theorem hd_inv_const (hd0 : ∀ x, hd 0 x = x)
    (hdm : ∀ β x z, hd β (x * z) = ∑ q ∈ antidiagonal β, hd q.1 x * hd q.2 z) {u : Λ} (hu : IsUnit u)
    (hc : ∀ β, β ≠ 0 → hd β u = 0) (β : σ →₀ ℕ) (hβ : β ≠ 0) : hd β (↑hu.unit⁻¹ : Λ) = 0 := by
  have h := hdm β u ↑hu.unit⁻¹
  rw [hu.mul_val_inv, hd_one' hd0 hdm β hβ] at h
  have h0 : ((0 : σ →₀ ℕ), β) ∈ antidiagonal β := mem_antidiagonal.2 (zero_add β)
  rw [← add_sum_erase _ _ h0, hd0] at h
  have hr : ∑ q ∈ (antidiagonal β).erase (0, β), hd q.1 u * hd q.2 ↑hu.unit⁻¹ = 0 := by
    refine sum_eq_zero fun q hq => ?_
    have hq1 := mem_erase.1 hq
    have h12 : q.1 + q.2 = β := mem_antidiagonal.1 hq1.2
    have hne : q.1 ≠ 0 := fun h => hq1.1 (Prod.ext h (by rw [← h12, h, zero_add]))
    rw [hc _ hne, zero_mul]
  rw [hr, add_zero] at h
  calc hd β (↑hu.unit⁻¹ : Λ) = ↑hu.unit⁻¹ * (u * hd β ↑hu.unit⁻¹) := by
        rw [← mul_assoc, hu.val_inv_mul, one_mul]
    _ = 0 := by rw [← h, mul_zero]

theorem hd_mul_const (hdm : ∀ β x z, hd β (x * z) = ∑ q ∈ antidiagonal β, hd q.1 x * hd q.2 z) {a b : Λ}
    (ha : ∀ β, β ≠ 0 → hd β a = 0) (hb : ∀ β, β ≠ 0 → hd β b = 0) (β : σ →₀ ℕ) (hβ : β ≠ 0) :
    hd β (a * b) = 0 := by
  rw [hdm]
  refine sum_eq_zero fun q hq => ?_
  by_cases h1 : q.1 = 0
  · have h12 : q.1 + q.2 = β := mem_antidiagonal.1 hq
    have h2 : q.2 ≠ 0 := by rw [h1, zero_add] at h12; rw [h12]; exact hβ
    rw [hb _ h2, mul_zero]
  · rw [ha _ h1, zero_mul]

theorem stabSub_inv (hd0 : ∀ x, hd 0 x = x)
    (hdm : ∀ β x z, hd β (x * z) = ∑ q ∈ antidiagonal β, hd q.1 x * hd q.2 z) (M : Subring Λ) {u : Λ}
    (hu : IsUnit u) (hs : u ∈ stabSub hd0 hdm M) (hM : (↑hu.unit⁻¹ : Λ) ∈ M) :
    (↑hu.unit⁻¹ : Λ) ∈ stabSub hd0 hdm M := by
  set v : Λ := ↑hu.unit⁻¹ with hv
  let Bs : Subring Λ := Subring.closure ((stabSub hd0 hdm M : Set Λ) ∪ {v})
  have hsB : ∀ z ∈ stabSub hd0 hdm M, z ∈ Bs := fun z hz => Subring.subset_closure (Or.inl hz)
  have hvB : v ∈ Bs := Subring.subset_closure (Or.inr rfl)
  have hdv : ∀ β, hd β v ∈ Bs := by
    intro β
    induction hn : Finsupp.degree β using Nat.strong_induction_on generalizing β with
    | _ n ih =>
    by_cases hβ : β = 0
    · rw [hβ, hd0]; exact hvB
    have h := hdm β u v
    rw [hv, hu.mul_val_inv, hd_one' hd0 hdm β hβ, ← hv] at h
    have h0 : ((0 : σ →₀ ℕ), β) ∈ antidiagonal β := mem_antidiagonal.2 (zero_add β)
    rw [← add_sum_erase _ _ h0, hd0] at h
    have hS : ∑ q ∈ (antidiagonal β).erase (0, β), hd q.1 u * hd q.2 v ∈ Bs := by
      refine Bs.sum_mem fun q hq => Bs.mul_mem (hsB _ (stabSub_hd hd0 hdm M q.1 hs)) (ih _ ?_ q.2 rfl)
      have hq1 := mem_erase.1 hq
      have h12 : q.1 + q.2 = β := mem_antidiagonal.1 hq1.2
      have hne : q.1 ≠ 0 := fun h => hq1.1 (Prod.ext h (by rw [← h12, h, zero_add]))
      have : Finsupp.degree q.1 ≠ 0 := fun h => hne ((Finsupp.degree_eq_zero_iff _).1 h)
      rw [← hn, ← h12, map_add]; omega
    have e1 : v * u = 1 := hu.val_inv_mul
    have : hd β v = -(v * ∑ q ∈ (antidiagonal β).erase (0, β), hd q.1 u * hd q.2 v) := by
      linear_combination (-v) * h + (-(hd β v)) * e1
    rw [this]
    exact Bs.neg_mem (Bs.mul_mem hvB hS)
  have hBs : ∀ z ∈ Bs, ∀ β, hd β z ∈ Bs := by
    intro z hz
    induction hz using Subring.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact fun β => hsB _ (stabSub_hd hd0 hdm M β hx)
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hdv
    | zero => exact fun β => by rw [map_zero]; exact Bs.zero_mem
    | one =>
      intro β
      by_cases hβ : β = 0
      · rw [hβ, hd0]; exact Bs.one_mem
      · rw [hd_one' hd0 hdm β hβ]; exact Bs.zero_mem
    | add x y _ _ hx hy => exact fun β => by rw [map_add]; exact Bs.add_mem (hx β) (hy β)
    | neg x _ hx => exact fun β => by rw [map_neg]; exact Bs.neg_mem (hx β)
    | mul x y _ _ hx hy =>
      intro β
      rw [hdm]
      exact Bs.sum_mem fun q _ => Bs.mul_mem (hx q.1) (hy q.2)
  have hBM : Bs ≤ M := (Subring.closure_le).2
    (Set.union_subset (fun z hz => stabSub_le hd0 hdm M hz) (Set.singleton_subset_iff.2 hM))
  intro l
  have : iterHd hd l v ∈ Bs := by
    induction l with
    | nil => exact hvB
    | cons β l ih => rw [iterHd_cons]; exact hBs _ ih β
  exact hBM this

theorem appSub_inv {L : Type*} [CommRing L] (ι : L →+* Λ) (F : Subring L) (I : Ideal Λ) {d v : L} (hdF : d ∈ F)
    (hvF : v ∈ F) (hz : ι (1 - d * v) ∈ I) (hu : IsUnit (ι d)) : (↑hu.unit⁻¹ : Λ) ∈ appSub ι F I := by
  intro n
  refine ⟨v * ∑ i ∈ range n, (1 - d * v) ^ i, F.mul_mem hvF (F.sum_mem fun i _ =>
    F.pow_mem (F.sub_mem F.one_mem (F.mul_mem hdF hvF)) i), ?_⟩
  have hg : 1 - d * (v * ∑ i ∈ range n, (1 - d * v) ^ i) = (1 - d * v) ^ n := by
    linear_combination (-1 : L) * mul_neg_geom_sum (1 - d * v) n
  have e : (↑hu.unit⁻¹ : Λ) - ι (v * ∑ i ∈ range n, (1 - d * v) ^ i) =
      ↑hu.unit⁻¹ * ι (1 - d * (v * ∑ i ∈ range n, (1 - d * v) ^ i)) := by
    rw [map_sub, map_one, map_mul ι d, mul_sub, mul_one, ← mul_assoc, hu.val_inv_mul, one_mul]
  rw [e, hg, map_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hz n)

end Gen

section Int

lemma nval_neg_rg {T : CDVR} (e : ℕ) (x : T.Fr) : nval T.V e (-x) = nval T.V e x := by
  by_cases hx : x = 0
  · subst hx; rw [neg_zero]
  · rw [nval_of_ne (neg_ne_zero.2 hx), nval_of_ne hx]
    unfold vV; rw [Valuation.map_neg]

def intSub {Λ : Type*} [CommRing Λ] {Z : Type*} (T : Z → CDVR) (ev : ∀ ζ, Λ →+* (T ζ).Fr) : Subring Λ where
  carrier := {x | ∀ ζ, 0 ≤ nval (T ζ).V 1 (ev ζ x)}
  zero_mem' := fun ζ => by rw [map_zero, nval_zero]; exact le_top
  one_mem' := fun ζ => by rw [map_one, nval_of_ne one_ne_zero, vV_one']; simp
  add_mem' := fun ha hb ζ => by
    rw [map_add]; exact (le_min (ha ζ) (hb ζ)).trans (nval_add 1 _ _)
  neg_mem' := fun ha ζ => by rw [map_neg, nval_neg_rg]; exact ha ζ
  mul_mem' := fun ha hb ζ => by rw [map_mul, nval_mul]; exact add_nonneg (ha ζ) (hb ζ)

end Int

section Approx

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem approx_of {Λ : Type*} [CommRing Λ] (ι : Lw X la w →+* Λ) (I : Ideal Λ) (u : WeightFamilies.Wt D j) (e' : Λ) (n : ℕ)
    (xe : ↥(HK X la w u)) (he : ι (xe : Lw X la w) - e' ∈ I ^ n) {r : Λ}
    (hr : r ∈ appSub ι (Frac0 X la w).toSubring I) :
    ∃ x : ↥(HK X la w u), ι (x : Lw X la w) - r * e' ∈ I ^ n := by
  obtain ⟨f, hf, hfr⟩ := hr n
  refine ⟨(⟨f, hf⟩ : ↥(Frac0 X la w)) • xe, ?_⟩
  have hc : ((((⟨f, hf⟩ : ↥(Frac0 X la w)) • xe : ↥(HK X la w u)) : Lw X la w)) = f * (xe : Lw X la w) := rfl
  rw [hc, map_mul]
  have : ι f * ι (xe : Lw X la w) - r * e' = ι f * (ι (xe : Lw X la w) - e') - (r - ι f) * e' := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ he) (Ideal.mul_mem_right _ _ hfr)

end Approx

end Formalism.L2.Pj
