import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.SelfConjugateRowData
import Formalism.LocalToGlobal.CharacterGerms.RowTieLab
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.RestNonneg
import Formalism.LocalToGlobal.Divisibility.Numbers
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsMulInvolutionAddOneMemPow

open scoped BigOperators
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace UpperTheory.G2.RowLab.Hyp

section Val

variable {C : Type} [Field C] {V : VF C}

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  V.v.map_lt_add ha hb

theorem mm_neg {a : C} (ha : V.MM a) : V.MM (-a) := by
  unfold VF.MM; rw [V.v.map_neg]; exact ha

theorem mm_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM at *; rw [V.v.map_mul]
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left ha)

theorem not_mm_one : ¬ V.MM (1 : C) := by simp [VF.MM]

theorem mm_or {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) (h : V.MM (a * b)) : V.MM a ∨ V.MM b := by
  by_contra hc
  rw [not_or] at hc
  have h1 : V.v a = 0 := le_antisymm (not_lt.mp hc.1) ha
  have h2 : V.v b = 0 := le_antisymm (not_lt.mp hc.2) hb
  unfold VF.MM at h
  rw [V.v.map_mul, h1, h2] at h
  simp at h

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM; rw [V.v_l]; exact zero_lt_one

theorem mm_pow_iff {a : C} (ha : V.Ge 0 a) {n : ℕ} (hn : n ≠ 0) : V.MM (a ^ n) ↔ V.MM a := by
  induction n with
  | zero => exact absurd rfl hn
  | succ n ih =>
    rw [pow_succ]
    refine ⟨fun h => ?_, fun h => mm_mul (ha.pow n) h⟩
    rcases mm_or (ha.pow n) ha h with h | h
    · by_cases h0 : n = 0
      · subst h0; exact absurd (by simpa using h) not_mm_one
      · exact (ih h0).mp h
    · exact h

theorem ge_pow_mul {w : ℝ} {a : C} (ha : V.Ge w a) (n : ℕ) : V.Ge (n * w) (a ^ n) := by
  induction n with
  | zero => simpa using VF.Ge.one
  | succ n ih =>
    rw [pow_succ]
    exact (ih.mul ha).mono (by push_cast; linarith)

theorem exists_pow_ge {a : C} (ha : V.MM a) : ∃ n : ℕ, V.Ge 1 (a ^ n) := by
  obtain ⟨w, hw, hwa⟩ : ∃ w : ℝ, 0 < w ∧ V.Ge w a := by
    unfold VF.MM at ha
    unfold VF.Ge
    induction hv : V.v a using WithTop.recTopCoe with
    | top => exact ⟨1, one_pos, le_top⟩
    | coe t =>
      rw [hv] at ha
      exact ⟨t, by exact_mod_cast ha, le_rfl⟩
  obtain ⟨n, hn⟩ := exists_nat_ge (1 / w)
  exact ⟨n, (ge_pow_mul hwa n).mono ((div_le_iff₀ hw).mp hn)⟩

theorem eq_zero_of_ge {a : C} (h : ∀ n : ℕ, V.Ge n a) : a = 0 := by
  by_contra h0
  have h1 : V.v a ≠ ⊤ := by rwa [Ne, AddValuation.top_iff]
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp h1
  obtain ⟨n, hn⟩ := exists_nat_gt t
  have h2 := h n
  unfold VF.Ge at h2
  rw [← ht] at h2
  exact absurd (by exact_mod_cast h2 : (n : ℝ) ≤ t) (not_le.mpr hn)

theorem not_mm_two (h2 : V.l ≠ 2) : ¬ V.MM (2 : C) := by
  intro h
  obtain ⟨k, hk⟩ := V.l_prime.odd_of_ne_two h2
  have e : (1 : C) = V.l + -((k : C) * 2) := by rw [hk]; push_cast; ring
  exact not_mm_one (V := V) (e ▸ mm_add mm_l (mm_neg (mm_mul (VF.ge_natCast k) h)))

theorem ge_half [CharZero C] (h2 : V.l ≠ 2) : V.Ge 0 (2 : C)⁻¹ := by
  have h1 : V.v (2 : C) = 0 := le_antisymm (not_lt.mp (not_mm_two h2)) (by exact_mod_cast VF.ge_natCast (V := V) 2)
  have h3 := V.v.map_mul (2 : C) 2⁻¹
  rw [mul_inv_cancel₀ two_ne_zero, V.v.map_one, h1, zero_add] at h3
  unfold VF.Ge
  rw [← h3]; rfl

theorem exists_half [CharZero C] (h2 : V.l ≠ 2) (N : ℕ) : ∃ k : ℕ, V.Ge N ((2 : C)⁻¹ - k) := by
  obtain ⟨k, hk⟩ := (V.l_prime.odd_of_ne_two h2).pow (n := N)
  refine ⟨k + 1, ?_⟩
  have e : (2 : C)⁻¹ - (k + 1 : ℕ) = -(2⁻¹ * (V.l : C) ^ N) := by
    rw [← Nat.cast_pow, hk]; push_cast; ring
  rw [e]
  exact ((ge_half h2).mul_int (by simpa using ge_pow_mul (VF.ge_l (V := V)) N)).neg

end Val

section Ring

variable {C : Type} [Field C] (V : VF C) {O : Type} [CommRing O] {A : Type}

def depthIdeal (em : A → O →+* C) (hi : ∀ a x, V.Ge 0 (em a x)) (w : ℝ) : Ideal O where
  carrier := {x | ∀ a, V.Ge w (em a x)}
  zero_mem' := fun a => by simpa using VF.Ge.zero w
  add_mem' := fun hx hy a => by rw [map_add]; exact (hx a).add (hy a)
  smul_mem' := fun c x hx a => by rw [smul_eq_mul, map_mul]; exact (hi a c).mul_int (hx a)

def resIdeal (em : O →+* C) (hi : ∀ x, V.Ge 0 (em x)) : Ideal O where
  carrier := {x | V.MM (em x)}
  zero_mem' := by simp [VF.MM]
  add_mem' := fun hx hy => by simpa using mm_add hx hy
  smul_mem' := fun c x hx => by simpa using mm_mul (hi c) hx

theorem resIdeal_prime (em : O →+* C) (hi : ∀ x, V.Ge 0 (em x)) : (resIdeal V em hi).IsPrime where
  ne_top' := by
    rw [Ideal.ne_top_iff_one]
    intro h
    have h' : V.MM (em 1) := h
    exact not_mm_one (V := V) (by simpa using h')
  mem_or_mem' := fun {x y} h => mm_or (hi x) (hi y) (by have h' : V.MM (em (x * y)) := h; simpa using h')

theorem depthIdeal_pow (em : A → O →+* C) (hi : ∀ a x, V.Ge 0 (em a x)) (n : ℕ) :
    depthIdeal V em hi 1 ^ n ≤ depthIdeal V em hi n := by
  induction n with
  | zero => intro x _ a; simpa using hi a x
  | succ n ih =>
    rw [pow_succ, Ideal.mul_le]
    intro r hr s hs a
    rw [map_mul]
    exact ((ih hr a).mul (hs a)).mono (by push_cast; rfl)

theorem exists_pow_le [IsNoetherianRing O] [Finite A] (em : A → O →+* C) (hi : ∀ a x, V.Ge 0 (em a x)) (P : Ideal O)
    (hP : ∀ x ∈ P, ∀ a, V.MM (em a x)) : ∃ e : ℕ, ∀ n : ℕ, P ^ (e * n) ≤ depthIdeal V em hi n := by
  have h : P ≤ (depthIdeal V em hi 1).radical := by
    intro x hx
    choose m hm using fun a => exists_pow_ge (hP x hx a)
    obtain ⟨M, hM⟩ := (Set.finite_range m).bddAbove
    refine ⟨M, fun a => ?_⟩
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hM ⟨a, rfl⟩)
    rw [map_pow, hk, add_comm, pow_add]
    exact ((hi a x).pow k).mul_int (hm a)
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h (IsNoetherian.noetherian P)
  refine ⟨e, fun n => ?_⟩
  rw [pow_mul]
  exact le_trans (Ideal.pow_right_mono he n) (depthIdeal_pow V em hi n)

theorem exists_seq (s : O →+* O) (hs : ∀ x, s (s x) = x) (P : Ideal O) [P.IsMaximal] [Finite (O ⧸ P)]
    (h1 : ∀ x ∈ P, s x ∈ P) (h2 : ∃ x, s x - x ∉ P) (h3 : (2 : O) ∉ P) :
    ∃ z : ℕ → O, (∀ n, z n * s (z n) + 1 ∈ P ^ n) ∧ ∀ n m, z (n + m) - z n ∈ P ^ n := by
  have H := GlobalTheory.NormResidue.exists_mul_involution_add_one_mem_pow O s hs P h1 h2 h3
  obtain ⟨z0, hz0, -⟩ := H 0 0 (Or.inl rfl)
  choose f hf1 hf2 using fun (N : ℕ) (x : O) (hx : x * s x + 1 ∈ P ^ (N + 1)) => H (N + 1) x (Or.inr hx)
  let y : (N : ℕ) → {x : O // x * s x + 1 ∈ P ^ (N + 1)} := fun N =>
    Nat.rec ⟨z0, hz0⟩ (fun N p => ⟨f N p.1 p.2, hf1 N p.1 p.2⟩) N
  refine ⟨fun n => (y n).1, fun n => Ideal.pow_le_pow_right (Nat.le_succ n) (y n).2, fun n m => ?_⟩
  induction m with
  | zero => simp
  | succ m ih =>
    have h4 : (y (n + m + 1)).1 - (y (n + m)).1 ∈ P ^ (n + m + 1) := hf2 _ _ (y (n + m)).2 (Nat.succ_ne_zero _)
    have h5 := (P ^ n).add_mem (Ideal.pow_le_pow_right (by omega : n ≤ n + m + 1) h4) ih
    rw [sub_add_sub_cancel] at h5
    exact h5

end Ring

theorem exists_root {E : Type} [Field E] [NumberField E] {C : Type} [Field C] [CharZero C] (V : VF C)
    (hc : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) (h2 : V.l ≠ 2)
    {d : ℕ} [NeZero d] (em : ZMod d → 𝓞 E →+* C) (hi : ∀ a x, V.Ge 0 (em a x)) (hd : ZMod d)
    (s : 𝓞 E →+* 𝓞 E) (hs : ∀ x, s (s x) = x) (hconj : ∀ a x, em (a + hd) x = em a (s x))
    (hfrob : ∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) (hsep : ∃ x, V.v (em 0 x - em hd x) = 0) :
    ∃ ζ : ZMod d → C, (∀ a, ζ (a + hd) * ζ a = -1) ∧ ∀ N : ℕ, ∃ z : 𝓞 E, ∀ a, V.Ge N (ζ a - em a z) := by
  have hstep : ∀ a x, V.MM (em (a + 1) x) ↔ V.MM (em a x) := by
    intro a x
    rw [← mm_pow_iff (hi a x) V.l_prime.ne_zero]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simpa using mm_add h (mm_neg (hfrob a x))
    · simpa using mm_add (hfrob a x) h
  have hall : ∀ a x, V.MM (em a x) ↔ V.MM (em 0 x) := by
    intro a x
    rw [← ZMod.natCast_zmod_val a]
    induction a.val with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, hstep, ih]
  set P := resIdeal V (em 0) (hi 0) with hP
  have hmem : ∀ x, x ∈ P ↔ V.MM (em 0 x) := fun x => Iff.rfl
  have hne : P ≠ ⊥ := by
    intro h
    have h1 : ((V.l : ℕ) : 𝓞 E) ∈ P := by rw [hmem, map_natCast]; exact mm_l
    rw [h, Ideal.mem_bot] at h1
    exact V.l_prime.ne_zero (by exact_mod_cast h1)
  have : P.IsMaximal := (resIdeal_prime V (em 0) (hi 0)).isMaximal hne
  have : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne
  obtain ⟨z, hz1, hz2⟩ := exists_seq s hs P
    (fun x hx => by rw [hmem, ← hconj, hall]; exact hx)
    (by
      obtain ⟨x, hx⟩ := hsep
      refine ⟨x, fun h => ?_⟩
      rw [hmem, map_sub, ← hconj, zero_add] at h
      have h' := mm_neg h
      rw [neg_sub] at h'
      exact absurd hx (ne_of_gt h'))
    (by rw [hmem, map_ofNat]; exact not_mm_two h2)
  obtain ⟨e, he⟩ := exists_pow_le V em hi P (fun x hx a => (hall a x).mpr hx)
  have hlim : ∀ a, ∃ x, ∀ n : ℕ, V.Ge n (x - em a (z (e * n))) := fun a =>
    hc _ fun n => by
      rw [← map_sub, mul_add]
      exact he n (hz2 _ _) a
  choose ζ hζ using hlim
  refine ⟨ζ, fun a => ?_, fun N => ⟨z (e * N), fun a => hζ a N⟩⟩
  rw [← add_eq_zero_iff_eq_neg]
  refine eq_zero_of_ge (V := V) fun n => ?_
  have hint : V.Ge 0 (ζ a) := by
    have := ((hζ a 0).mono (by simp)).add (hi a (z (e * 0)))
    simpa using this
  have h3 : V.Ge n (em a (z (e * n) * s (z (e * n)) + 1)) := he n (hz1 _) a
  rw [map_add, map_mul, map_one, ← hconj] at h3
  have h4 := (h3.add (hint.mul_int (hζ (a + hd) n))).add ((hi (a + hd) (z (e * n))).mul_int (hζ a n))
  convert h4 using 1
  ring

theorem gmEx : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H)
    (c : Coeff l), GmExSt c := by
  intro E _ _ _ H l c T io C _ _ V ι _ hc h2 Orb d _ tau hd hd0 _ hconj hfrob hsep
  have hint : ∀ τ x, V.Ge 0 (emA3 io ι τ x) := fun τ x =>
    ge_of_isIntegral V (map_isIntegral_int (emA3 io ι τ) (Algebra.IsIntegral.isIntegral x))
  have hbar : ∀ (τ : E →+* ℂ) (x : 𝓞 E),
      emA3 io ι (ComplexEmbedding.conjugate τ) x = emA3 io ι τ (H.bar x) := by
    intro τ x
    have : embK c (ComplexEmbedding.conjugate τ) x = embK c τ (H.bar x) := by
      apply Subtype.ext
      rw [embK_coe, embK_coe, H.bar_eq, IsCMField.complexEmbedding_complexConj]
      rfl
    unfold emA3
    simp only [RingHom.comp_apply]
    rw [this]
  have hbb : ∀ x, H.bar (H.bar x) = x := by
    intro x
    apply RingOfIntegers.ext
    simp [H.bar_eq]
  have key := fun o => exists_root V hc h2 (fun a => emA3 io ι (tau o a)) (fun a x => hint _ x) hd
    (H.bar : 𝓞 E →+* 𝓞 E) hbb (fun a x => by rw [← hconj]; exact hbar _ x) (hfrob o)
    (hsep (o, 0) (o, hd) (fun h => hd0 (Prod.mk.inj h).2.symm))
  choose ζ hζ1 hζ2 using key
  refine ⟨fun o a => !![1, 2⁻¹; ζ o a, -(ζ o a * 2⁻¹)], fun o N => ?_, fun o a s s' => ?_⟩
  · obtain ⟨z, hz⟩ := hζ2 o N
    obtain ⟨k, hk⟩ := exists_half h2 N
    refine ⟨!![1, (k : 𝓞 E); z, -(z * k)], fun a r s => ?_⟩
    have h4 := (((ge_half h2).mul_int (hz a)).add ((hint (tau o a) z).mul_int hk)).neg
    fin_cases r <;> fin_cases s
    · simpa using VF.Ge.zero _
    · simpa using hk
    · simpa using hz a
    · convert h4 using 1
      simp
      ring
  · have h := hζ1 o a
    fin_cases s <;> fin_cases s' <;> simp [Fin.sum_univ_two]
    · rw [h]; simp
    · linear_combination (-2⁻¹ : C) * h
    · linear_combination (-2⁻¹ : C) * h
    · linear_combination (4⁻¹ : C) * h

end UpperTheory.G2.RowLab.Hyp

namespace UpperTheory.G2.RowLab.Sep

theorem v_intCast_eq_zero {C : Type} [Field C] (V : VF C) {n : ℤ} (hn : ¬ (V.l : ℤ) ∣ n) : V.v (n : C) = 0 := by
  have hint : ∀ m : ℤ, V.Ge 0 (m : C) := fun m => by
    rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
    · simpa using VF.ge_natCast (V := V) k
    · simpa using (VF.ge_natCast (V := V) k).neg
  have hp : Prime (V.l : ℤ) := Nat.prime_iff_prime_int.1 V.l_prime
  obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).2 hn
  have h1 : (a : C) * (V.l : C) + (b : C) * (n : C) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → C) hab
  refine le_antisymm ?_ (hint n)
  by_contra hc
  have hc' : 0 < V.v (n : C) := lt_of_not_ge hc
  have h2 : 0 < V.v ((a : C) * (V.l : C)) := by
    rw [V.v.map_mul, V.v_l]
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left (hint a))
  have h3 : 0 < V.v ((b : C) * (n : C)) := by
    rw [V.v.map_mul]
    exact lt_of_lt_of_le hc' (le_add_of_nonneg_left (hint b))
  have h4 := V.v.map_lt_add h2 h3
  rw [h1, V.v.map_one] at h4
  exact lt_irrefl _ h4

theorem exists_v_sub_eq_zero {C : Type} [Field C] (V : VF C) {I : Type} [Fintype I] (M : Matrix I I C)
    (h : ∀ i j, V.Ge 0 (M i j)) (hd : V.v M.det = 0) {j j' : I} (hj : j ≠ j') :
    ∃ i, V.v (M i j - M i j') = 0 := by
  by_contra hc
  push Not at hc
  have hpos : ∀ i, 0 < V.v (M i j - M i j') := fun i =>
    lt_of_le_of_ne ((h i j).sub (h i j')) (hc i).symm
  have hd0 : M.det ≠ 0 := by
    intro h0
    rw [h0, V.v.map_zero] at hd
    exact WithTop.top_ne_zero hd
  have hM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (Ne.isUnit hd0)
  have h1 := congrFun (congrFun hM j) j
  have h2 := congrFun (congrFun hM j) j'
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  rw [Matrix.mul_apply, Matrix.one_apply_ne hj] at h2
  have h3 : ∑ i, M⁻¹ j i * (M i j - M i j') = 1 := by
    simp only [mul_sub, Finset.sum_sub_distrib, h1, h2, sub_zero]
  have h4 : 0 < V.v (∑ i, M⁻¹ j i * (M i j - M i j')) := by
    refine V.v.map_lt_sum WithTop.zero_ne_top fun i _ => ?_
    rw [V.v.map_mul]
    exact lt_of_lt_of_le (hpos i) (le_add_of_nonneg_left (inv_int M h hd j i))
  rw [h3, V.v.map_one] at h4
  exact lt_irrefl _ h4

theorem cmEmbeddings_integral_and_distinct_mod_maximal' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ¬ (V.l : ℤ) ∣ NumberField.discr E → (∀ τ x, V.Ge 0 (emA3 io ι τ x)) ∧ ∀ τ τ' : E →+* ℂ, τ ≠ τ' → ∃ a : 𝓞 E, V.v (emA3 io ι τ a - emA3 io ι τ' a) = 0 := by
  intro E _ _ _ H lv c T io C _ _ V ι _ hd
  have hint : ∀ τ x, V.Ge 0 (emA3 io ι τ x) := fun τ x =>
    ge_of_isIntegral V (map_isIntegral_int (emA3 io ι τ) (Algebra.IsIntegral.isIntegral x))
  refine ⟨hint, fun τ τ' hne => ?_⟩
  let b : (E →+* ℂ) → 𝓞 E := fun i => RingOfIntegers.basis E (equivReindex E i)
  let M : Matrix (E →+* ℂ) (E →+* ℂ) c.F := Matrix.of fun i σ => embK c σ (b i)
  have hM : (algebraMap c.F ℂ).mapMatrix M = basisMatrix E := by
    ext i σ
    simp only [basisMatrix, Matrix.of_apply, canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
    rfl
  have hdet : M.det ^ 2 = (discr E : c.F) := by
    apply (algebraMap c.F ℂ).injective
    rw [map_pow, RingHom.map_det, hM, map_intCast, discr_eq_basisMatrix_det_sq]
  let N : Matrix (E →+* ℂ) (E →+* ℂ) C := (ι.comp io).mapMatrix M
  have hN : N.det ^ 2 = (discr E : C) := by
    rw [← RingHom.map_det, ← map_pow, hdet, map_intCast]
  have hNi : ∀ i j, V.Ge 0 (N i j) := fun i j => hint j (b i)
  have hv : V.v N.det = 0 := by
    have h1 := v_intCast_eq_zero V hd
    rw [← hN, pow_two, V.v.map_mul] at h1
    have h0 : 0 ≤ V.v N.det := det_int N hNi
    refine le_antisymm ?_ h0
    rw [← h1]
    exact le_add_of_nonneg_right h0
  obtain ⟨i, hi⟩ := exists_v_sub_eq_zero V N hNi hv hne
  exact ⟨b i, hi⟩

end UpperTheory.G2.RowLab.Sep

namespace UpperTheory.G2.RowLab.Idem

theorem exists_idem (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime)
    (hd : ¬ (l : ℤ) ∣ NumberField.discr E) (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hlP : (l : 𝓞 E) ∈ P) :
    ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (l : 𝓞 E) * y) ∧ ε - 1 ∈ P ∧ ∀ x ∈ P, ∃ y, ε * x = (l : 𝓞 E) * y := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hun : Algebra.IsUnramifiedAt ℤ P :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hp).mp hd P hP (by simpa using hlP)
  have hov : P.LiesOver (Ideal.span {(l : ℤ)}) :=
    (Ideal.liesOver_span_iff hP.ne_top hp).mpr (by simpa using hlP)
  have hmap : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 E)) = Ideal.span {(l : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hl0 : (l : 𝓞 E) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hne : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := by
    rw [hmap]; simpa using hl.ne_zero
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hl0 (by simpa using hlP)
  have := hP.isMaximal hP0
  obtain ⟨Q, h₁, h₂⟩ := Ideal.eq_prime_pow_mul_coprime hne P
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ hne,
    Ideal.ramificationIdx_eq_one P ℤ, pow_one, hmap] at h₂
  obtain ⟨p, hpP, q, hqQ, hpq⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp h₁)
  have key : ∀ x ∈ P, ∃ y, q * x = (l : 𝓞 E) * y := by
    intro x hx
    have : x * q ∈ Ideal.span {(l : 𝓞 E)} := h₂ ▸ Ideal.mul_mem_mul hx hqQ
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp this
    exact ⟨y, by rw [mul_comm, hy]⟩
  have hq1 : q - 1 ∈ P := by
    have : q - 1 = -p := by rw [← hpq]; ring
    rw [this]; exact P.neg_mem hpP
  refine ⟨q, ?_, hq1, key⟩
  obtain ⟨y, hy⟩ := key _ hq1
  exact ⟨y, by rw [← hy]; ring⟩

variable {C : Type} [Field C] {V : VF C}

theorem ge_int {x : C} (hx : IsIntegral ℤ x) : V.Ge 0 x := by
  have h1 : IsIntegral (Valuation.integer (V.v : Valuation C (Multiplicative (WithTop ℝ)ᵒᵈ))) x := hx.tower_top
  exact (Valuation.integer.integers (V.v : Valuation C (Multiplicative (WithTop ℝ)ᵒᵈ))).mem_of_integral h1

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := V.v.map_lt_add ha hb

theorem mm_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at ha
  rw [V.v.map_mul]
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left (by simpa using ha))

def ker (V : VF C) {R : Type} [CommRing R] (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) : Ideal R where
  carrier := {x | V.MM (f x)}
  add_mem' := fun {a b} ha hb => by
    show V.MM (f (a + b))
    rw [map_add]; exact mm_add ha hb
  zero_mem' := by
    show V.MM (f 0)
    simp [VF.MM]
  smul_mem' := fun c x hx => by
    show V.MM (f (c * x))
    rw [map_mul]; exact mm_mul (hf c) hx

theorem ker_isPrime {R : Type} [CommRing R] (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) : (ker V f hf).IsPrime := by
  refine ⟨(Ideal.ne_top_iff_one _).mpr ?_, fun {a b} hab => ?_⟩
  · show ¬ V.MM (f 1)
    simp [VF.MM]
  · change V.MM (f (a * b)) at hab
    show V.MM (f a) ∨ V.MM (f b)
    have ha := hf a
    have hb := hf b
    unfold VF.MM VF.Ge at *
    rw [map_mul, V.v.map_mul] at hab
    by_contra hc
    push Not at hc
    exact absurd hab (not_lt.mpr (add_nonpos hc.1 hc.2))

end UpperTheory.G2.RowLab.Idem

open UpperTheory.G2.RowLab.Idem in
theorem UpperTheory.G2.RowLab.exists_idempotent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (d : ℕ) [NeZero d] (tau : ZMod d → (E →+* ℂ)), (∀ s x, V.MM (emA3 io ι (tau (s + 1)) x - emA3 io ι (tau s) x ^ V.l)) → ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (V.l : 𝓞 E) * y) ∧ (∀ a, V.MM (emA3 io ι (tau a) ε - 1)) ∧ ∀ x : 𝓞 E, (∀ a, V.MM (emA3 io ι (tau a) x)) → ∃ y, ε * x = (V.l : 𝓞 E) * y := by
  intro E _ _ _ H lv c T io C _ _ V ι _ hd d _ tau hF
  have hint : ∀ τ x, V.Ge 0 (emA3 io ι τ x) := fun τ x =>
    ge_int ((RingOfIntegers.isIntegral x).map (emA3 io ι τ).toIntAlgHom)
  have hstep : ∀ x s, V.MM (emA3 io ι (tau s) x) → V.MM (emA3 io ι (tau (s + 1)) x) := by
    intro x s hs
    have h1 := hF s x
    have h2 : V.MM (emA3 io ι (tau s) x ^ V.l) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero V.l_prime.ne_zero
      rw [hk, pow_succ]
      exact mm_mul ((hint _ _).pow k) hs
    simpa using mm_add h1 h2
  have hall : ∀ x, V.MM (emA3 io ι (tau 0) x) → ∀ a, V.MM (emA3 io ι (tau a) x) := by
    intro x h0 a
    have : ∀ n : ℕ, V.MM (emA3 io ι (tau (n : ZMod d)) x) := by
      intro n
      induction n with
      | zero => simpa using h0
      | succ n ih => push_cast; exact hstep x _ ih
    simpa using this a.val
  have hP := ker_isPrime (V := V) (emA3 io ι (tau 0)) (hint _)
  obtain ⟨ε, h1, h2, h3⟩ := exists_idem E V.l V.l_prime hd (ker V (emA3 io ι (tau 0)) (hint _)) (by
    show V.MM (emA3 io ι (tau 0) (V.l : 𝓞 E))
    rw [map_natCast]
    unfold VF.MM
    rw [V.v_l]
    exact zero_lt_one)
  refine ⟨ε, h1, fun a => ?_, fun x hx => h3 x (hx 0)⟩
  have := hall _ h2 a
  rwa [map_sub, map_one] at this

namespace UpperTheory.G2.RowLab

lemma pos_add (N : NumDatum) (l : ℕ) (z : RPl N.R) (s t : ℕ) :
    N.pos l (N.pos l z s) t = N.pos l z (s + t) := by
  unfold NumDatum.pos
  refine Prod.ext ?_ ?_
  · dsimp only
    by_cases h : N.cls l = PrimeClass.signal <;> by_cases hs : Odd s <;> by_cases ht : Odd t <;>
      simp [h, hs, ht, Nat.odd_add, ← Nat.not_odd_iff_even]
  · dsimp only
    rw [add_smul, add_assoc]

lemma pos_mul_period (N : NumDatum) (l : ℕ) (z : RPl N.R) (c : ℕ) :
    N.pos l z (N.ordP l * c) = z := by
  unfold NumDatum.pos NumDatum.ordP
  by_cases h : N.cls l = PrimeClass.signal
  · rw [if_pos h]
    refine Prod.ext ?_ ?_
    · have : ¬ Odd (2 * addOrderOf (2 • N.hP l) * c) := by
        rw [Nat.not_odd_iff_even, mul_assoc]; exact even_two_mul _
      dsimp only
      rw [decide_eq_false (fun hh => this hh.2), Bool.xor_false]
    · dsimp only
      rw [show 2 * addOrderOf (2 • N.hP l) * c = c * addOrderOf (2 • N.hP l) * 2 by ring,
        mul_smul, mul_smul, addOrderOf_nsmul_eq_zero, smul_zero, add_zero]
  · rw [if_neg h]
    refine Prod.ext ?_ ?_
    · simp [h]
    · dsimp only
      rw [mul_comm, mul_smul, addOrderOf_nsmul_eq_zero, smul_zero, add_zero]

lemma pos_mod (N : NumDatum) (l : ℕ) (z : RPl N.R) (e : ℕ) :
    N.pos l z (e % N.ordP l) = N.pos l z e := by
  conv_rhs => rw [← Nat.div_add_mod e (N.ordP l), ← pos_add, pos_mul_period]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

lemma inPsi_conj_iff (τ : E →+* ℂ) : InPsi H (ComplexEmbedding.conjugate τ) ↔ ¬ InPsi H τ := by
  have hd : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have h0 : H.rt0 ≠ 0 := fun h => by
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    exact hd (by linear_combination this)
  have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    rw [← map_pow, this, map_neg, map_natCast]
  have h2 : ∀ w : ℂ, w ^ 2 = -(H.d : ℂ) → starRingEnd ℂ w = -w := by
    intro w hw
    have hre := congrArg Complex.re hw
    have him := congrArg Complex.im hw
    simp [pow_two] at hre him
    have hdp : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have : w.re = 0 := by
      by_contra hne
      have : w.im = 0 := by
        have : w.re * w.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [mul_self_nonneg w.re]
    apply Complex.ext <;> simp [this]
  unfold InPsi
  rw [ComplexEmbedding.conjugate_coe_eq, h2 _ h1]
  have h3 : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm)
  constructor
  · intro a b
    exact h0 (by linear_combination (-1/2 : ℂ) * a - (1/2 : ℂ) * b)
  · intro a
    rw [h3.resolve_left a, neg_neg]

lemma embK_conj_bar {lv : Level H} (c : Coeff lv) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c τ (H.bar x) = embK c (ComplexEmbedding.conjugate τ) x := by
  apply Subtype.ext
  rw [embK_coe, embK_coe, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  rfl

lemma conj_conj (τ : E →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
  ComplexEmbedding.involutive_conjugate E τ

noncomputable def tauN (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)) (l : ℕ) (z : RPl N.R) (n : ℕ) : E →+* ℂ :=
  if Even n then pl (N.pos l z n) else ComplexEmbedding.conjugate (pl (N.pos l z n))

omit [NumberField E] [IsCMField E] in
lemma tauN_mod (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)) (l : ℕ) (z : RPl N.R) (n : ℕ) :
    tauN N pl l z (n % (2 * N.ordP l)) = tauN N pl l z n := by
  have h1 : N.pos l z (n % (2 * N.ordP l)) = N.pos l z n := by
    rw [← pos_mod, Nat.mod_mod_of_dvd _ (Dvd.intro_left 2 rfl), pos_mod]
  have h2 : Even (n % (2 * N.ordP l)) ↔ Even n := by
    rw [Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ (Dvd.intro _ rfl)]
  unfold tauN
  rw [h1]
  simp only [h2]

omit [NumberField E] [IsCMField E] in
lemma tauN_add (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)) (l : ℕ) (z : RPl N.R) (s : ZMod (2 * N.ordP l)) (k : ℕ) :
    tauN N pl l z (s + (k : ZMod (2 * N.ordP l))).val = tauN N pl l z (s.val + k) := by
  have e : s + (k : ZMod (2 * N.ordP l)) = ((s.val + k : ℕ) : ZMod (2 * N.ordP l)) := by simp
  rw [e, ZMod.val_natCast, tauN_mod]

lemma pos_add_ord (N : NumDatum) (l : ℕ) (z : RPl N.R) (n : ℕ) : N.pos l z (n + N.ordP l) = N.pos l z n := by
  rw [← pos_mod, Nat.add_mod_right, pos_mod]

lemma tauN_ord (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)) (l : ℕ) (ho : Odd (N.ordP l)) (z : RPl N.R) (n : ℕ) :
    tauN N pl l z (n + N.ordP l) = ComplexEmbedding.conjugate (tauN N pl l z n) := by
  unfold tauN
  rw [pos_add_ord]
  by_cases h : Even n
  · rw [if_pos h, if_neg (Nat.not_even_iff_odd.2 (h.add_odd ho))]
  · rw [if_neg h, if_pos ((Nat.not_even_iff_odd.1 h).add_odd ho), conj_conj]

theorem exists_lab {lv : Level H} (c : Coeff lv) (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)) (hinj : Function.Injective pl)
    (hpsi : ∀ τ, InPsi H τ ↔ ∃ z, pl z = τ) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C)
    (ι : T.Fr →+* C) (hι : EmbOK T V ι)
    (hc : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) (h2 : V.l ≠ 2)
    (hunr : ¬ (V.l : ℤ) ∣ NumberField.discr E)
    (hf : ∀ (w : RPl N.R) (x : 𝓞 E), V.MM (emA3 io ι (ComplexEmbedding.conjugate (pl (N.pos V.l w 1))) x -
        emA3 io ι (pl w) x ^ V.l))
    (ho : Odd (N.ordP V.l)) (Z : Finset (RPl N.R))
    (hZ : ∀ z' : RPl N.R, ∃! p : RPl N.R × ZMod (N.ordP V.l), p.1 ∈ Z ∧ N.pos V.l p.1 p.2.val = z') (n j₁ j₂ : ℕ) :
    ∃ lab : Formalism.L2.FormalSeriesBounds.LabS E C {z // z ∈ Z} (2 * N.ordP V.l), LabSArith V io ι lab ∧
      lab.hd = (N.ordP V.l : ZMod (2 * N.ordP V.l)) ∧ lab.n = n ∧ lab.j = j₁ ∧ lab.j' = j₂ ∧
      (∀ o g s, lab.big o g s ↔ (Even s.val ↔ g = 0)) ∧
      (∀ o s, lab.tau o s = if Even s.val then pl (N.pos V.l o.1 s.val) else ComplexEmbedding.conjugate (pl (N.pos V.l o.1 s.val))) ∧
      Function.Surjective (fun x : {z // z ∈ Z} × ZMod (2 * N.ordP V.l) => lab.tau x.1 x.2) := by
  have hpos : 0 < N.ordP V.l := Nat.pos_of_ne_zero (NeZero.ne _)
  have hin : ∀ z, InPsi H (pl z) := fun z => (hpsi _).2 ⟨z, rfl⟩
  have hne : ∀ z z', pl z ≠ ComplexEmbedding.conjugate (pl z') := fun z z' h =>
    (inPsi_conj_iff (pl z')).1 (h ▸ hin z) (hin z')
  have hcinj : Function.Injective (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) :=
    (ComplexEmbedding.involutive_conjugate E).injective
  let tau : {z // z ∈ Z} → ZMod (2 * N.ordP V.l) → (E →+* ℂ) := fun o s => tauN N pl V.l o.1 s.val
  have htinj : Function.Injective fun x : {z // z ∈ Z} × ZMod (2 * N.ordP V.l) => tau x.1 x.2 := by
    rintro ⟨z, s⟩ ⟨z', s'⟩ h
    have main : N.pos V.l z.1 s.val = N.pos V.l z'.1 s'.val → (Even s.val ↔ Even s'.val) → (z, s) = (z', s') := by
      intro h1 h2
      have := (hZ (N.pos V.l z'.1 s'.val)).unique (y₁ := (z.1, (s.val : ZMod (N.ordP V.l))))
        (y₂ := (z'.1, (s'.val : ZMod (N.ordP V.l))))
        ⟨z.2, by dsimp only; rw [ZMod.val_natCast, pos_mod, h1]⟩ ⟨z'.2, by dsimp only; rw [ZMod.val_natCast, pos_mod]⟩
      obtain ⟨a, b⟩ := Prod.mk.inj this
      obtain rfl := Subtype.ext a
      have b1 : s.val ≡ s'.val [MOD N.ordP V.l] := (ZMod.natCast_eq_natCast_iff _ _ _).1 b
      have b2 : s.val ≡ s'.val [MOD 2] := by
        rw [Nat.even_iff, Nat.even_iff] at h2
        unfold Nat.ModEq
        omega
      have b3 : s.val ≡ s'.val [MOD 2 * N.ordP V.l] :=
        (Nat.modEq_and_modEq_iff_modEq_mul (Nat.coprime_two_left.2 ho)).1 ⟨b2, b1⟩
      have b4 := (ZMod.natCast_eq_natCast_iff _ _ _).2 b3
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at b4
      rw [b4]
    dsimp only [tau, tauN] at h
    by_cases a : Even s.val <;> by_cases b : Even s'.val
    · rw [if_pos a, if_pos b] at h
      exact main (hinj h) (by tauto)
    · rw [if_pos a, if_neg b] at h
      exact absurd h (hne _ _)
    · rw [if_neg a, if_pos b] at h
      exact absurd h.symm (hne _ _)
    · rw [if_neg a, if_neg b] at h
      exact main (hinj (hcinj h)) (by tauto)
  have hd0 : (N.ordP V.l : ZMod (2 * N.ordP V.l)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd hpos h
    omega
  have hd2 : (N.ordP V.l : ZMod (2 * N.ordP V.l)) + (N.ordP V.l : ZMod (2 * N.ordP V.l)) = 0 := by
    rw [← Nat.cast_add, ← two_mul, ZMod.natCast_self]
  have hconj : ∀ o a, ComplexEmbedding.conjugate (tau o a) = tau o (a + (N.ordP V.l : ZMod (2 * N.ordP V.l))) := by
    intro o a
    dsimp only [tau]
    rw [tauN_add, tauN_ord N pl V.l ho]
  have hfrob : ∀ o a x, V.MM (emA3 io ι (tau o (a + 1)) x - emA3 io ι (tau o a) x ^ V.l) := by
    intro o a x
    have e := tauN_add N pl V.l o.1 a 1
    rw [Nat.cast_one] at e
    dsimp only [tau]
    rw [e]
    unfold tauN
    rw [← pos_add]
    by_cases h : Even a.val
    · rw [if_pos h, if_neg (fun hh => Nat.even_add_one.1 hh h)]
      exact hf _ _
    · rw [if_neg h, if_pos (Nat.even_add_one.2 h)]
      have := hf (N.pos V.l o.1 a.val) (H.bar x)
      simp only [emA3, RingHom.comp_apply, embK_conj_bar, conj_conj] at this ⊢
      exact this
  have hsep : ∀ x x' : {z // z ∈ Z} × ZMod (2 * N.ordP V.l), x ≠ x' →
      ∃ a : 𝓞 E, V.v (emA3 io ι (tau x.1 x.2) a - emA3 io ι (tau x'.1 x'.2) a) = 0 := fun x x' hx =>
    (Sep.cmEmbeddings_integral_and_distinct_mod_maximal' E H lv c T io C V ι hι hunr).2 _ _ fun h => hx (htinj h)
  obtain ⟨gm, g1, g2⟩ := Hyp.gmEx E H lv c T io C V ι hι hc h2 _ _ tau _ hd0 hd2 hconj hfrob hsep
  refine ⟨⟨tau, (N.ordP V.l : ZMod (2 * N.ordP V.l)), gm, n, j₁, j₂, fun _ g s => (Even s.val ↔ g = 0)⟩,
    ⟨htinj, hd0, hd2, hconj, hfrob, hsep,
      fun o => exists_idempotent E H lv c T io C V ι hι hunr _ (tau o) (hfrob o), g1, g2⟩,
    rfl, rfl, rfl, rfl, fun _ _ _ => Iff.rfl, fun _ _ => rfl, fun τ => ?_⟩
  have key : ∀ z', ∃ x : {z // z ∈ Z} × ZMod (2 * N.ordP V.l), tau x.1 x.2 = pl z' ∨
      ComplexEmbedding.conjugate (tau x.1 x.2) = pl z' := by
    intro z'
    obtain ⟨p, hp, -⟩ := hZ z'
    refine ⟨(⟨p.1, hp.1⟩, (p.2.val : ZMod (2 * N.ordP V.l))), ?_⟩
    dsimp only [tau]
    rw [ZMod.val_natCast, tauN_mod]
    unfold tauN
    rw [hp.2]
    by_cases h : Even p.2.val
    · rw [if_pos h]; exact Or.inl rfl
    · rw [if_neg h]; exact Or.inr (conj_conj _)
  have key2 : ∀ σ : E →+* ℂ, (∃ x : {z // z ∈ Z} × ZMod (2 * N.ordP V.l), tau x.1 x.2 = σ) →
      ∃ x : {z // z ∈ Z} × ZMod (2 * N.ordP V.l), tau x.1 x.2 = ComplexEmbedding.conjugate σ := by
    rintro σ ⟨x, rfl⟩
    exact ⟨(x.1, _), (hconj x.1 x.2).symm⟩
  have key3 : ∀ z', ∃ x : {z // z ∈ Z} × ZMod (2 * N.ordP V.l), tau x.1 x.2 = pl z' := by
    intro z'
    obtain ⟨x, h | h⟩ := key z'
    · exact ⟨x, h⟩
    · rw [← h]; exact key2 _ ⟨x, rfl⟩
  by_cases h : InPsi H τ
  · obtain ⟨z', rfl⟩ := (hpsi _).1 h
    exact key3 z'
  · obtain ⟨z', hz'⟩ := (hpsi _).1 ((inPsi_conj_iff τ).2 h)
    have := key2 _ (key3 z')
    rwa [hz', conj_conj] at this

end UpperTheory.G2.RowLab
