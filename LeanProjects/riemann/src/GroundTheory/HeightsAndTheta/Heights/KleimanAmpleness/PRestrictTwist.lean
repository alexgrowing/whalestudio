import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepTwo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace RestrictTwist

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']

def IsFrac (x : Fin (N + 1) → Ω) (c : ℤ) (I : Finset (Fin (N + 1))) (z : Ω)
    (t : Poly S N × Poly S N × ℕ × ℕ) : Prop :=
  t.2.1 ∈ monos I ∧ t.1.IsHomogeneous t.2.2.2 ∧ t.2.1.IsHomogeneous t.2.2.1 ∧
    (t.2.2.2 : ℤ) = t.2.2.1 + c ∧ z = aeval x t.1 / aeval x t.2.1

theorem isFrac_add {x : Fin (N + 1) → Ω} {c : ℤ} {I : Finset (Fin (N + 1))} {z z' : Ω}
    {t t' : Poly S N × Poly S N × ℕ × ℕ} (hI : ∀ s ∈ monos (S := S) I, aeval x s ≠ 0)
    (h : IsFrac x c I z t) (h' : IsFrac x c I z' t') :
    IsFrac x c I (z + z')
      (t.1 * t'.2.1 + t.2.1 * t'.1, t.2.1 * t'.2.1, t.2.2.1 + t'.2.2.1, t.2.2.2 + t'.2.2.1) := by
  obtain ⟨f, s, e, e'⟩ := t
  obtain ⟨f', s', d, d'⟩ := t'
  obtain ⟨hs, hf, hse, hc, rfl⟩ := h
  obtain ⟨hs', hf', hse', hc', rfl⟩ := h'
  dsimp only at hs hf hse hc hs' hf' hse' hc' ⊢
  refine ⟨mul_mem hs hs', (hf.mul hse').add ?_, hse.mul hse', by push_cast; omega, ?_⟩
  · have hdeg : e + d' = e' + d := by omega
    rw [← hdeg]; exact hse.mul hf'
  · simp only [map_add, map_mul]
    rw [div_add_div _ _ (hI s hs) (hI s' hs')]

theorem isFrac_mul {x : Fin (N + 1) → Ω} {c : ℤ} {I : Finset (Fin (N + 1))} {z : Ω}
    {t : Poly S N × Poly S N × ℕ × ℕ} {g u : Poly S N} {d : ℕ} (hu : u ∈ monos I)
    (hg : g.IsHomogeneous d) (hud : u.IsHomogeneous d) (h : IsFrac x c I z t) :
    IsFrac x c I (aeval x g / aeval x u * z) (g * t.1, u * t.2.1, d + t.2.2.1, d + t.2.2.2) := by
  obtain ⟨f, s, e, e'⟩ := t
  obtain ⟨hs, hf, hse, hc, rfl⟩ := h
  dsimp only at hs hf hse hc ⊢
  refine ⟨mul_mem hu hs, hg.mul hf, hud.mul hse, by push_cast; omega, ?_⟩
  simp only [map_mul, div_mul_div_comm]

theorem exists_isFrac {x : Fin (N + 1) → Ω} {c : ℤ} {I : Chart x} {z : Ω}
    (hz : z ∈ twistMod S x c I) : ∃ t, IsFrac (S := S) x c I.1 z t := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩ := hz
    exact ⟨(f, s, e, e'), hs, hf, hse, hc, rfl⟩
  | zero =>
    obtain ⟨i, hi⟩ := I.2.1
    have h0 : (0 : ℤ) ≤ ((-c).toNat : ℤ) + c := by
      have := Int.self_le_toNat (-c); omega
    refine ⟨(0, X i ^ (-c).toNat, (-c).toNat, (((-c).toNat : ℤ) + c).toNat),
      pow_mem (X_mem_monos hi) _, isHomogeneous_zero _ _ _, isHomogeneous_X_pow _ _, ?_, by simp⟩
    exact Int.toNat_of_nonneg h0
  | add a b _ _ ha hb =>
    obtain ⟨t, ht⟩ := ha
    obtain ⟨t', ht'⟩ := hb
    exact ⟨_, isFrac_add (fun s hs => eval_ne_zero_of_mem_monos I hs) ht ht'⟩
  | smul a z _ hz =>
    obtain ⟨t, ht⟩ := hz
    obtain ⟨g, u, d, hu, hg, hud, hga⟩ := a.2
    refine ⟨(g * t.1, u * t.2.1, d + t.2.2.1, d + t.2.2.2), ?_⟩
    rw [chartRing_smul_def, hga]
    exact isFrac_mul hu hg hud ht

theorem div_eq_of_isFrac {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) {c : ℤ} {I J : Finset (Fin (N + 1))} {z : Ω}
    {t t' : Poly S N × Poly S N × ℕ × ℕ} (h : IsFrac x c I z t) (h' : IsFrac x c J z t')
    (hx : aeval x t.2.1 ≠ 0) (hx' : aeval x t'.2.1 ≠ 0) (hy : aeval y t.2.1 ≠ 0)
    (hy' : aeval y t'.2.1 ≠ 0) :
    aeval y t.1 / aeval y t.2.1 = aeval y t'.1 / aeval y t'.2.1 := by
  obtain ⟨f, s, e, e'⟩ := t
  obtain ⟨f', s', d, d'⟩ := t'
  obtain ⟨-, hf, hs, hc, hz⟩ := h
  obtain ⟨-, hf', hs', hc', hz'⟩ := h'
  dsimp only at hf hs hc hz hf' hs' hc' hz' hx hx' hy hy' ⊢
  have hdeg : d' + e = e' + d := by omega
  have hg : (f * s' - f' * s).IsHomogeneous (e' + d) :=
    (hf.mul hs').sub (by rw [← hdeg]; exact hf'.mul hs)
  have hx0 : aeval x (f * s' - f' * s) = 0 := by
    have := hz.symm.trans hz'
    rw [div_eq_div_iff hx hx'] at this
    rw [map_sub, map_mul, map_mul, this, sub_self]
  have hy0 := (mem_primeOf_of_isHomogeneous y hg).mp (hle ((mem_primeOf_of_isHomogeneous x hg).mpr hx0))
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at hy0
  rw [div_eq_div_iff hy hy', hy0]

variable (S) in

def twistRes (x : Fin (N + 1) → Ω) (y : Fin (N + 1) → K') (c : ℤ) (z : Ω) : K' := by
  classical
  exact if h : ∃ (I : Chart y) (t : Poly S N × Poly S N × ℕ × ℕ), IsFrac x c I.1 z t then
    aeval y (Classical.choose (Classical.choose_spec h)).1 /
      aeval y (Classical.choose (Classical.choose_spec h)).2.1
  else 0

theorem twistRes_eq {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) {c : ℤ} (I : Chart y) {z : Ω}
    {t : Poly S N × Poly S N × ℕ × ℕ} (h : IsFrac x c I.1 z t) :
    twistRes S x y c z = aeval y t.1 / aeval y t.2.1 := by
  classical
  have hex : ∃ (I : Chart y) (t : Poly S N × Poly S N × ℕ × ℕ), IsFrac x c I.1 z t := ⟨I, t, h⟩
  rw [twistRes, dif_pos hex]
  have h₀ := Classical.choose_spec (Classical.choose_spec hex)
  exact div_eq_of_isFrac hle h₀ h
    (eval_ne_zero_of_mem_monos (liftChart hxy (Classical.choose hex)) h₀.1)
    (eval_ne_zero_of_mem_monos (liftChart hxy I) h.1)
    (eval_ne_zero_of_mem_monos (Classical.choose hex) h₀.1) (eval_ne_zero_of_mem_monos I h.1)

theorem twistRes_mem {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (c : ℤ) (I : Chart y) {q : Ω}
    (hq : q ∈ (twistSys S x c).sub (liftChart hxy I)) : twistRes S x y c q ∈ (twistSys S y c).sub I := by
  obtain ⟨t, ht⟩ := exists_isFrac hq
  rw [twistRes_eq hxy hle I ht]
  exact Submodule.subset_span ⟨t.1, t.2.1, t.2.2.1, t.2.2.2, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, rfl⟩

theorem restrictData_twistSys {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
    (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (c : ℤ) :
    RestrictData (twistSys S x c) hxy (twistSys S y c) (twistRes S x y c) where
  mem I q hq := twistRes_mem hxy hle c I hq
  add I q hq q' hq' := by
    obtain ⟨t, ht⟩ := exists_isFrac hq
    obtain ⟨t', ht'⟩ := exists_isFrac hq'
    have hsum := isFrac_add (fun s hs => eval_ne_zero_of_mem_monos (liftChart hxy I) hs) ht ht'
    rw [twistRes_eq hxy hle I hsum, twistRes_eq hxy hle I ht, twistRes_eq hxy hle I ht']
    simp only [map_add, map_mul]
    rw [div_add_div _ _ (eval_ne_zero_of_mem_monos I ht.1) (eval_ne_zero_of_mem_monos I ht'.1)]
  smul I q hq f s e hs hf hse := by
    obtain ⟨t, ht⟩ := exists_isFrac hq
    rw [twistRes_eq hxy hle I (isFrac_mul hs hf hse ht), twistRes_eq hxy hle I ht]
    simp only [map_mul, div_mul_div_comm]
  span I := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨q, hq, rfl⟩
      exact twistRes_mem hxy hle c I hq
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
      exact Submodule.subset_span ⟨aeval x f / aeval x s,
        Submodule.subset_span ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩,
        twistRes_eq (t := (f, s, e, e')) hxy hle I ⟨hs, hf, hse, hc, rfl⟩⟩

theorem twist_sub_eq {L : Type w} [Field L] [Algebra S L] {z : Fin (N + 1) → L}
    (F Q : SubSystem S z L) (I : Chart z) : (F.twist Q).sub I = Q.sub I * F.sub I := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, a, ha, rfl⟩
    exact Submodule.mul_mem_mul hq ha
  · exact Submodule.mul_le.mpr fun q hq a ha => Submodule.subset_span ⟨q, hq, a, ha, rfl⟩

theorem mul_mem' {x : Fin (N + 1) → Ω} {I : Chart x} {P : Submodule (chartRing S x I) Ω} {c q : Ω}
    (hc : c ∈ chartRing S x I) (hq : q ∈ P) : c * q ∈ P :=
  P.smul_mem (⟨c, hc⟩ : chartRing S x I) hq

theorem exists_list_of_mem_mul {A : Type*} [CommRing A] [Algebra A Ω] {P Q : Submodule A Ω} {z : Ω}
    (hz : z ∈ P * Q) :
    ∃ l : List (Ω × Ω), (∀ p ∈ l, p.1 ∈ P ∧ p.2 ∈ Q) ∧ (l.map fun p => p.1 * p.2).sum = z := by
  induction hz using Submodule.mul_induction_on' with
  | mem_mul_mem m hm n hn => exact ⟨[(m, n)], by simp [hm, hn], by simp⟩
  | add a _ b _ ha hb =>
    obtain ⟨l, hl, rfl⟩ := ha
    obtain ⟨l', hl', rfl⟩ := hb
    exact ⟨l ++ l', fun p hp => (List.mem_append.mp hp).elim (hl p) (hl' p), by simp⟩

theorem exists_dual {x : Fin (N + 1) → Ω} (Q : LineBundle S x) (I : Chart x) :
    ∃ l : List (Ω × Ω), (∀ p ∈ l, p.1 ∈ Q.sub I ∧ ∀ a ∈ Q.sub I, p.2 * a ∈ chartRing S x I) ∧
      (l.map fun p => p.1 * p.2).sum = 1 := by
  obtain ⟨Q', hQ'⟩ := Q.invertible I
  have h1 : (1 : Ω) ∈ Q.sub I * Q' := by
    rw [hQ']; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨l, hl, hsum⟩ := exists_list_of_mem_mul h1
  refine ⟨l, fun p hp => ⟨(hl p hp).1, fun a ha => ?_⟩, hsum⟩
  have h2 : p.2 * a ∈ Q.sub I * Q' := by
    rw [mul_comm p.2 a]; exact Submodule.mul_mem_mul ha (hl p hp).2
  rw [hQ'] at h2
  obtain ⟨b, hb⟩ := Submodule.mem_one.mp h2
  rw [← hb]; exact b.2

variable {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}

theorem map_zero_of {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (I : Chart y) : r 0 = 0 := by
  have := h.add I 0 (Q.sub _).zero_mem 0 (Q.sub _).zero_mem
  rw [add_zero] at this
  simpa using this

theorem map_list_sum_of {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (I : Chart y) :
    ∀ l : List Ω, (∀ q ∈ l, q ∈ Q.sub (liftChart hxy I)) → r l.sum = (l.map r).sum
  | [], _ => by simpa using map_zero_of h I
  | a :: l, hl => by
    rw [List.sum_cons, List.map_cons, List.sum_cons,
      h.add I a (hl a List.mem_cons_self) _ (list_sum_mem fun q hq => hl q (List.mem_cons_of_mem _ hq)),
      map_list_sum_of h I l fun q hq => hl q (List.mem_cons_of_mem _ hq)]

variable (S x y) in

def red (I : Finset (Fin (N + 1))) (a : Ω) : K' := by
  classical
  exact if h : ∃ t : Poly S N × Poly S N × ℕ, t.2.1 ∈ monos I ∧ t.1.IsHomogeneous t.2.2 ∧
      t.2.1.IsHomogeneous t.2.2 ∧ a = aeval x t.1 / aeval x t.2.1 then
    aeval y (Classical.choose h).1 / aeval y (Classical.choose h).2.1 else 0

theorem map_mul_of {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (I : Chart y) {a q : Ω}
    (ha : a ∈ chartRing S x (liftChart hxy I)) (hq : q ∈ Q.sub (liftChart hxy I)) :
    r (a * q) = red S x y I.1 a * r q := by
  classical
  have hex : ∃ t : Poly S N × Poly S N × ℕ, t.2.1 ∈ monos I.1 ∧ t.1.IsHomogeneous t.2.2 ∧
      t.2.1.IsHomogeneous t.2.2 ∧ a = aeval x t.1 / aeval x t.2.1 := by
    obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
    exact ⟨(f, s, e), hs, hf, hse, rfl⟩
  obtain ⟨hs, hf, hse, ha'⟩ := Classical.choose_spec hex
  rw [red, dif_pos hex]
  have := h.smul I q hq _ _ _ hs hf hse
  rw [← ha'] at this
  exact this

def prodRes (r₁ r₂ : Ω → K') (l : List (Ω × Ω)) (z : Ω) : K' :=
  (l.map fun p => r₁ p.1 * r₂ (p.2 * z)).sum

theorem mul_mem_of_mem_mul {Q₁ Q₂ : SubSystem S x Ω} {I : Chart x} {v z : Ω}
    (hv : ∀ a ∈ Q₁.sub I, v * a ∈ chartRing S x I) (hz : z ∈ Q₂.sub I * Q₁.sub I) :
    v * z ∈ Q₂.sub I := by
  induction hz using Submodule.mul_induction_on' with
  | mem_mul_mem b hb a ha =>
    rw [show v * (b * a) = (v * a) * b by ring]; exact mul_mem' (hv a ha) hb
  | add z _ z' _ h h' => rw [mul_add]; exact add_mem h h'

theorem prodRes_add {r₁ : Ω → K'} {Q₂ : SubSystem S x Ω} {Q₂' : SubSystem S y K'} {r₂ : Ω → K'}
    (h₂ : RestrictData Q₂ hxy Q₂' r₂) (I : Chart y) {l : List (Ω × Ω)} {z z' : Ω}
    (hz : ∀ p ∈ l, p.2 * z ∈ Q₂.sub (liftChart hxy I))
    (hz' : ∀ p ∈ l, p.2 * z' ∈ Q₂.sub (liftChart hxy I)) :
    prodRes r₁ r₂ l (z + z') = prodRes r₁ r₂ l z + prodRes r₁ r₂ l z' := by
  rw [prodRes, prodRes, prodRes, ← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
  rw [mul_add, h₂.add I _ (hz p hp) _ (hz' p hp), mul_add]

theorem prodRes_mul {Q₁ Q₂ : SubSystem S x Ω} {Q₁' Q₂' : SubSystem S y K'} {r₁ r₂ : Ω → K'}
    (h₁ : RestrictData Q₁ hxy Q₁' r₁) (h₂ : RestrictData Q₂ hxy Q₂' r₂) (I : Chart y)
    {l : List (Ω × Ω)} (hl : ∀ p ∈ l, p.1 ∈ Q₁.sub (liftChart hxy I) ∧
      ∀ a ∈ Q₁.sub (liftChart hxy I), p.2 * a ∈ chartRing S x (liftChart hxy I))
    (hl1 : (l.map fun p => p.1 * p.2).sum = 1) {a b : Ω} (ha : a ∈ Q₁.sub (liftChart hxy I))
    (hb : b ∈ Q₂.sub (liftChart hxy I)) :
    prodRes r₁ r₂ l (b * a) = r₁ a * r₂ b := by
  have ha' : a = (l.map fun p => (p.2 * a) * p.1).sum := by
    calc a = a * (l.map fun p => p.1 * p.2).sum := by rw [hl1, mul_one]
      _ = (l.map fun p => a * (p.1 * p.2)).sum := (List.sum_map_mul_left ..).symm
      _ = _ := congrArg List.sum (List.map_congr_left fun p _ => by ring)
  have key : r₁ a = (l.map fun p => red S x y I.1 (p.2 * a) * r₁ p.1).sum := by
    conv_lhs => rw [ha']
    rw [map_list_sum_of h₁ I _ ?_, List.map_map]
    · exact congrArg List.sum (List.map_congr_left fun p hp =>
        map_mul_of h₁ I ((hl p hp).2 a ha) (hl p hp).1)
    · intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      exact mul_mem' ((hl p hp).2 a ha) (hl p hp).1
  rw [key, prodRes, ← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
  rw [show p.2 * (b * a) = (p.2 * a) * b by ring, map_mul_of h₂ I ((hl p hp).2 a ha) hb]
  ring

theorem prodRes_eq_of_subset {Q₁ Q₂ : SubSystem S x Ω} {Q₁' Q₂' : SubSystem S y K'} {r₁ r₂ : Ω → K'}
    (h₁ : RestrictData Q₁ hxy Q₁' r₁) (h₂ : RestrictData Q₂ hxy Q₂' r₂) {I K : Chart y}
    (hIK : I.1 ⊆ K.1) {l l' : List (Ω × Ω)}
    (hl : ∀ p ∈ l, p.1 ∈ Q₁.sub (liftChart hxy I) ∧
      ∀ a ∈ Q₁.sub (liftChart hxy I), p.2 * a ∈ chartRing S x (liftChart hxy I))
    (hl1 : (l.map fun p => p.1 * p.2).sum = 1)
    (hl' : ∀ p ∈ l', p.1 ∈ Q₁.sub (liftChart hxy K) ∧
      ∀ a ∈ Q₁.sub (liftChart hxy K), p.2 * a ∈ chartRing S x (liftChart hxy K))
    (hl1' : (l'.map fun p => p.1 * p.2).sum = 1) {z : Ω}
    (hz : z ∈ Q₂.sub (liftChart hxy I) * Q₁.sub (liftChart hxy I)) :
    prodRes r₁ r₂ l z = prodRes r₁ r₂ l' z := by
  have H : prodRes r₁ r₂ l z = prodRes r₁ r₂ l' z ∧
      z ∈ Q₂.sub (liftChart hxy K) * Q₁.sub (liftChart hxy K) := by
    induction hz using Submodule.mul_induction_on' with
    | mem_mul_mem b hb a ha =>
      have ha' := Q₁.mono (liftChart hxy I) (liftChart hxy K) hIK a ha
      have hb' := Q₂.mono (liftChart hxy I) (liftChart hxy K) hIK b hb
      exact ⟨by rw [prodRes_mul h₁ h₂ I hl hl1 ha hb, prodRes_mul h₁ h₂ K hl' hl1' ha' hb'],
        Submodule.mul_mem_mul hb' ha'⟩
    | add z hz z' hz' h h' =>
      refine ⟨?_, add_mem h.2 h'.2⟩
      rw [prodRes_add h₂ I (fun p hp => mul_mem_of_mem_mul (hl p hp).2 hz)
          (fun p hp => mul_mem_of_mem_mul (hl p hp).2 hz'),
        prodRes_add h₂ K (fun p hp => mul_mem_of_mem_mul (hl' p hp).2 h.2)
          (fun p hp => mul_mem_of_mem_mul (hl' p hp).2 h'.2), h.1, h'.1]
  exact H.1

theorem restrictData_twist {Q₁ Q₂ : LineBundle S x} {Q₁' Q₂' : LineBundle S y} {r₁ r₂ : Ω → K'}
    (h₁ : RestrictData Q₁.toSubSystem hxy Q₁'.toSubSystem r₁)
    (h₂ : RestrictData Q₂.toSubSystem hxy Q₂'.toSubSystem r₂) :
    ∃ r : Ω → K', RestrictData (Q₁.toSubSystem.twist Q₂.toSubSystem) hxy
      (Q₁'.toSubSystem.twist Q₂'.toSubSystem) r := by
  classical
  choose L hL hL1 using fun I : Chart y => exists_dual Q₁ (liftChart hxy I)
  let r : Ω → K' := fun z =>
    if h : ∃ I : Chart y, z ∈ Q₂.sub (liftChart hxy I) * Q₁.sub (liftChart hxy I) then
      prodRes r₁ r₂ (L (Classical.choose h)) z else 0
  have hr : ∀ (I : Chart y) (z : Ω), z ∈ Q₂.sub (liftChart hxy I) * Q₁.sub (liftChart hxy I) →
      r z = prodRes r₁ r₂ (L I) z := by
    intro I z hz
    have hex : ∃ I : Chart y, z ∈ Q₂.sub (liftChart hxy I) * Q₁.sub (liftChart hxy I) := ⟨I, hz⟩
    simp only [r, dif_pos hex]
    have hJ := Classical.choose_spec hex
    let K : Chart y := ⟨(Classical.choose hex).1 ∪ I.1,
      (Classical.choose hex).2.1.mono Finset.subset_union_left,
      Finset.union_subset (Classical.choose hex).2.2 I.2.2⟩
    rw [prodRes_eq_of_subset h₁ h₂ (K := K) Finset.subset_union_left (hL _) (hL1 _) (hL K) (hL1 K) hJ,
      prodRes_eq_of_subset h₁ h₂ (K := K) Finset.subset_union_right (hL I) (hL1 I) (hL K) (hL1 K) hz]
  have hmem : ∀ (I : Chart y) (z : Ω), z ∈ (Q₁.toSubSystem.twist Q₂.toSubSystem).sub (liftChart hxy I) →
      z ∈ Q₂.sub (liftChart hxy I) * Q₁.sub (liftChart hxy I) := fun I z hz => by
    rwa [twist_sub_eq] at hz
  have hv : ∀ (I : Chart y) (z : Ω), z ∈ Q₂.sub (liftChart hxy I) * Q₁.sub (liftChart hxy I) →
      ∀ p ∈ L I, p.2 * z ∈ Q₂.sub (liftChart hxy I) := fun I z hz p hp =>
    mul_mem_of_mem_mul (hL I p hp).2 hz
  have hrmem : ∀ (I : Chart y), ∀ q ∈ (Q₁.toSubSystem.twist Q₂.toSubSystem).sub (liftChart hxy I),
      r q ∈ (Q₁'.toSubSystem.twist Q₂'.toSubSystem).sub I := by
    intro I q hq
    rw [twist_sub_eq, hr I q (hmem I q hq), prodRes]
    refine list_sum_mem fun w hw => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    rw [mul_comm (r₁ p.1)]
    exact Submodule.mul_mem_mul (h₂.mem I _ (hv I q (hmem I q hq) p hp)) (h₁.mem I _ (hL I p hp).1)
  refine ⟨r, hrmem, ?_, ?_, ?_⟩
  · intro I q hq q' hq'
    have hq₁ := hmem I q hq
    have hq₁' := hmem I q' hq'
    rw [hr I _ (add_mem hq₁ hq₁'), hr I _ hq₁, hr I _ hq₁']
    exact prodRes_add h₂ I (hv I q hq₁) (hv I q' hq₁')
  · intro I q hq f s e hs hf hse
    have hq₁ := hmem I q hq
    have hc : aeval x f / aeval x s ∈ chartRing S x (liftChart hxy I) := ⟨f, s, e, hs, hf, hse, rfl⟩
    rw [hr I _ (mul_mem' hc hq₁), hr I _ hq₁, prodRes, prodRes, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
    rw [show p.2 * (aeval x f / aeval x s * q) = aeval x f / aeval x s * (p.2 * q) by ring,
      h₂.smul I _ (hv I q hq₁ p hp) f s e hs hf hse]
    ring
  · intro I
    apply le_antisymm
    · exact Submodule.span_le.mpr fun _ ⟨q, hq, hrq⟩ => hrq ▸ hrmem I q hq
    · rw [twist_sub_eq Q₁'.toSubSystem Q₂'.toSubSystem I, ← h₁.span I, ← h₂.span I,
        Submodule.span_mul_span]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨_, ⟨b, hb, rfl⟩, _, ⟨a, ha, rfl⟩, rfl⟩
      have hba : b * a ∈ Q₂.sub (liftChart hxy I) * Q₁.sub (liftChart hxy I) :=
        Submodule.mul_mem_mul hb ha
      refine Submodule.subset_span ⟨b * a, ?_, ?_⟩
      · rw [twist_sub_eq]; exact hba
      · rw [hr I _ hba, prodRes_mul h₁ h₂ I (hL I) (hL1 I) ha hb, mul_comm]

theorem proof : Statement.{u, w} := by
  refine ⟨?_, ?_⟩
  · intro S _ Ω _ _ N x K' _ _ y hxy hle c
    exact ⟨_, restrictData_twistSys hxy hle c⟩
  · intro S _ Ω _ _ N x K' _ _ y hxy Q₁ Q₂ Q₁' Q₂' r₁ r₂ h₁ h₂
    exact restrictData_twist h₁ h₂

end RestrictTwist

end

end GroundTheory.Heights₂.Heights.Kleiman
