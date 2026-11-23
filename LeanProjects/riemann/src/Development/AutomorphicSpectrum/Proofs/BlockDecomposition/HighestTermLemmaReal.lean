import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ExpansionTerms
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealCompression
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignAntisymmetric

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.SpinBound

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open Formalism.REAL (dot)
open GlobalTheory.CompanionTheory.RealMult.Short

variable {n : ℕ}

theorem nsq_dot (x : Fin n → ℝ) : nsq x = dot x x := by
  unfold nsq dot
  exact sum_congr rfl fun a _ => sq _

def supp (g : Fin n → ℝ) : ℝ := (∑ a, ∑ b, |g a - g b|) / 4

theorem supp_perm (g : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : supp (g ∘ σ) = supp g := by
  unfold supp
  congr 1
  simp only [Function.comp]
  rw [Equiv.sum_comp σ (fun a => ∑ b, |g a - g (σ b)|)]
  exact sum_congr rfl fun a _ => Equiv.sum_comp σ (fun b => |g a - g b|)

theorem dot_table (g : Fin n → ℝ) (s : Fin n → Fin n → ℝ) (hs : ∀ a b, s b a = -s a b) :
    ∑ a, g a * ∑ b, s a b = (∑ a, ∑ b, (g a - g b) * s a b) / 2 := by
  have h1 : ∑ a, ∑ b, g b * s a b = -∑ a, g a * ∑ b, s a b := by
    rw [sum_comm, ← sum_neg_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [hs a b]
    ring
  have h2 : ∑ a, ∑ b, (g a - g b) * s a b = ∑ a, g a * ∑ b, s a b - ∑ a, ∑ b, g b * s a b := by
    simp only [sub_mul, sum_sub_distrib, mul_sum]
  rw [h2, h1]
  ring

theorem dot_rho_sub_le (B : Finset (Fin n × Fin n)) (hB : ∀ p ∈ B, p.1 < p.2) (g : Fin n → ℝ) :
    dot (rhoV n - wtB B) g ≤ supp g := by
  have e : dot (rhoV n - wtB B) g = (∑ a, g a * ∑ b, sg B a b) / 2 := by
    simp only [dot, sum_sg, Pi.sub_apply, sum_div]
    refine sum_congr rfl fun a _ => ?_
    ring
  rw [e, dot_table g (sg B) (sg_anti B)]
  have h : ∑ a, ∑ b, (g a - g b) * sg B a b ≤ ∑ a, ∑ b, |g a - g b| := by
    refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
    by_cases hab : a = b
    · subst hab
      simp
    · rcases sg_val B hB hab with h | h <;> rw [h]
      · simpa using le_abs_self (g a - g b)
      · simpa using neg_le_abs (g a - g b)
  unfold supp
  linarith

theorem dot_antitone (g : Fin n → ℝ) (hg : Antitone g) : dot g (rhoV n) = supp g := by
  have e : dot g (rhoV n) = (∑ a, g a * ∑ b, s0 a b) / 2 := by
    simp only [dot, sum_sign_eq_two_rho, sum_div]
    refine sum_congr rfl fun a _ => ?_
    ring
  rw [e, dot_table g s0 sign_antisymmetric_alt]
  have h : ∑ a, ∑ b, (g a - g b) * s0 a b = ∑ a, ∑ b, |g a - g b| := by
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rcases lt_trichotomy a b with h | h | h
    · have h1 : g b ≤ g a := hg h.le
      rw [abs_of_nonneg (by linarith)]
      simp [s0, h]
    · subst h
      simp
    · have h1 : g a ≤ g b := hg h.le
      rw [abs_of_nonpos (by linarith)]
      simp [s0, h, asymm h]
  rw [h]
  unfold supp
  ring

theorem dot_swap (x g : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    dot (x ∘ Equiv.swap i j) g = dot x g + (x j - x i) * (g i - g j) := by
  have h : ∀ a, x (Equiv.swap i j a) * g a - x a * g a =
      (if a = i then (x j - x i) * g i else 0) + (if a = j then (x i - x j) * g j else 0) := by
    intro a
    by_cases h1 : a = i
    · subst h1
      simp [hij]
      ring
    · by_cases h2 : a = j
      · subst h2
        simp [h1]
        ring
      · simp [h1, h2, Equiv.swap_apply_of_ne_of_ne]
  have h3 : dot (x ∘ Equiv.swap i j) g - dot x g = (x j - x i) * g i + (x i - x j) * g j := by
    simp only [dot, Function.comp, ← sum_sub_distrib, h, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
  linarith

theorem domC_anti (x : Fin n → ℝ) : Antitone (domC x) := by
  intro a b h
  have := Tuple.monotone_sort (fun a => -x a) h
  simpa [domC] using this

theorem maj_sort (c x : Fin n → ℝ) (hc : Antitone c) (hx : ∀ g, dot x g ≤ supp g) :
    ∀ g, dot (domC (c + x) - c) g ≤ supp g := by
  have key := Tuple.bubble_sort_induction (f := fun a => -(c + x) a)
    (P := fun h => ∀ g, dot (-h - c) g ≤ supp g) ?_ ?_
  · intro g
    convert key g using 2
    funext a
    simp [domC]
  · intro g
    convert hx g using 2
    funext a
    simp
  · intro h i j hij hji hP g
    have hne : i ≠ j := hij.ne
    have h1 := hP g
    have h2 := hP (g ∘ Equiv.swap i j)
    rw [supp_perm, d_comm, dot_swap g _ hne, d_comm g] at h2
    have e : dot (-(h ∘ Equiv.swap i j) - c) g = dot (-h - c) g + (h i - h j) * (g i - g j) := by
      have e1 : -(h ∘ Equiv.swap i j) = (-h) ∘ Equiv.swap i j := rfl
      rw [e1, dL_sub, dL_sub, dot_swap _ _ hne]
      simp only [Pi.neg_apply]
      ring
    rw [e]
    have hd : 0 < h i - h j := by linarith
    have hcij : c j ≤ c i := hc hij.le
    simp only [Pi.sub_apply, Pi.neg_apply] at h2
    rcases le_total 0 (g i - g j) with hE | hE
    · nlinarith
    · nlinarith

theorem dot_sq_le (u v : Fin n → ℝ) : dot u v ^ 2 ≤ dot u u * dot v v := by
  have := Finset.sum_mul_sq_le_sq_mul_sq univ u v
  simpa [dot, sq] using this

theorem dot_self_le (x : Fin n → ℝ) (hx : ∀ g, dot x g ≤ supp g) :
    dot x x ≤ dot (rhoV n) (rhoV n) := by
  have h1 := hx x
  have e1 : domC x = x ∘ Tuple.sort (fun a => -x a) := rfl
  have h2 : supp x = dot (domC x) (rhoV n) := by
    rw [dot_antitone _ (domC_anti x), e1, supp_perm]
  have h3 : dot (domC x) (domC x) = dot x x := by
    rw [e1, d_perm]
  have h4 := dot_sq_le (domC x) (rhoV n)
  rw [h3, ← h2] at h4
  have h5 := d_self_nonneg x
  have h6 := d_self_nonneg (rhoV n)
  by_contra hlt
  have hlt' := not_le.1 hlt
  nlinarith

theorem exists_spin (ν : Fin n → ℝ) :
    ∃ π : Equiv.Perm (Fin n), spinSq ν = dot (ν - rhoV n + rhoV n ∘ π) (ν - rhoV n + rhoV n ∘ π) := by
  refine ⟨(Tuple.sort (fun a => -(ν - rhoV n) a))⁻¹, ?_⟩
  set τ := Tuple.sort (fun a => -(ν - rhoV n) a) with hτ
  have e : domC (ν - rhoV n) + rhoV n = (ν - rhoV n + rhoV n ∘ (τ⁻¹ : Equiv.Perm (Fin n))) ∘ τ := by
    funext a
    show (ν - rhoV n) (τ a) + rhoV n a = (ν - rhoV n) (τ a) + rhoV n (τ⁻¹ (τ a))
    rw [show τ⁻¹ (τ a) = a from τ.symm_apply_apply a]
  unfold spinSq
  rw [e, nsq_dot]
  exact d_perm _ _ τ

theorem step_mono (p : Fin n → ℕ) (hs : ∀ a b : Fin n, (b : ℕ) = a + 1 → p a ≤ p b + 1) :
    ∀ (d : ℕ) (a c : Fin n), (c : ℕ) = a + d → (a : ℕ) + p a ≤ c + p c := by
  intro d
  induction d with
  | zero =>
    intro a c h
    have : a = c := Fin.ext (by omega)
    simp [this]
  | succ d ih =>
    intro a c h
    have hm : (a : ℕ) + d < n := by have := c.2; omega
    have h1 := ih a ⟨a + d, hm⟩ rfl
    have h2 := hs ⟨a + d, hm⟩ c (by simp; omega)
    simp only at h1 h2
    omega

theorem key_lev (p : Fin n → ℕ) (hinj : Function.Injective p)
    (hs : ∀ a b : Fin n, (b : ℕ) = a + 1 → p a ≤ p b + 1) :
    ∀ (d : ℕ) (a c : Fin n), (c : ℕ) = a + d + 1 → p c < p a → (a : ℕ) + p a = c + p c := by
  intro d
  induction d with
  | zero =>
    intro a c h hlt
    have := hs a c (by omega)
    omega
  | succ d ih =>
    intro a c h hlt
    have hc := c.2
    have ha1 : (a : ℕ) + 1 < n := by omega
    have hc1 : (a : ℕ) + d + 1 < n := by omega
    set a' : Fin n := ⟨a + 1, ha1⟩ with ha'
    set c' : Fin n := ⟨a + d + 1, hc1⟩ with hc'
    have v1 : (a' : ℕ) = a + 1 := rfl
    have v2 : (c' : ℕ) = a + d + 1 := rfl
    have n1 : p a' ≠ p c := fun e => by
      have := congrArg Fin.val (hinj e)
      omega
    have n2 : p c' ≠ p a := fun e => by
      have := congrArg Fin.val (hinj e)
      omega
    have s1 := hs a a' v1
    have s2 := hs c' c (by omega)
    have i1 := ih a' c (by omega) (by omega)
    have i2 := ih a c' v2 (by omega)
    have m1 := step_mono p hs d a' c' (by omega)
    have m2 := step_mono p hs (d + 2) a c (by omega)
    omega

theorem two_rhoU (lev : Fin n → ℕ) (a : Fin n) :
    2 * rhoU lev a = ∑ b, ((if lev a < lev b then (1 : ℝ) else 0) - (if lev b < lev a then (1 : ℝ) else 0)) := by
  rw [sum_sub_distrib, sum_boole, sum_boole]
  unfold rhoU
  ring

theorem harm_of_eq (lam : Fin n → ℤ) (hlam : Antitone lam) (π : Equiv.Perm (Fin n))
    (hs : StrictAnti fun a => 2 * (lam a : ℝ) + 2 * rhoV n a + rhoV n (π a))
    (he : ∑ a, (lam a : ℝ) * rhoV n (π a) = ∑ a, (lam a : ℝ) * rhoV n a) :
    (fun a => 2 * (lam a : ℝ) + rhoV n a + rhoV n (π a)) ∈ harmSet lam := by
  have hX : Antitone fun a => (lam a : ℝ) := fun a b h => by
    show (lam b : ℝ) ≤ lam a
    exact_mod_cast hlam h
  have hmono : Monovary (fun a => (lam a : ℝ)) (rhoV n ∘ π) :=
    (Monovary.sum_mul_comp_perm_eq_sum_mul_iff (hX.monovary rho_anti.antitone)).1 he
  have hlt : ∀ a c : Fin n, lam c < lam a → π a < π c := by
    intro a c h
    by_contra hn
    have hne : π a ≠ π c := fun e => by
      have : a = c := π.injective e
      subst this
      exact lt_irrefl _ h
    have h1 : π c < π a := lt_of_le_of_ne (not_lt.1 hn) hne.symm
    have h2 : (lam a : ℝ) ≤ lam c := hmono (rho_anti h1)
    have h3 : lam a ≤ lam c := by exact_mod_cast h2
    omega
  set p : Fin n → ℕ := fun a => (π a : ℕ) with hp
  have hinj : Function.Injective p := fun a b h => π.injective (Fin.ext h)
  have hstep : ∀ a b : Fin n, (b : ℕ) = a + 1 → p a ≤ p b + 1 := by
    intro a b h
    have hab : a < b := by rw [Fin.lt_def]; omega
    rcases (hlam hab.le).lt_or_eq with h1 | h1
    · have := hlt a b h1
      rw [Fin.lt_def] at this
      simp only [hp]
      omega
    · have h2 := hs hab
      simp only [h1] at h2
      have h3 := rho_sub a b
      have h4 := rho_sub (π a) (π b)
      have h5 : ((b : ℕ) : ℝ) = (a : ℕ) + 1 := by exact_mod_cast h
      have h6 : ((π a : ℕ) : ℝ) < (π b : ℕ) + 2 := by linarith
      have h7 : (π a : ℕ) < (π b : ℕ) + 2 := by exact_mod_cast h6
      simp only [hp]
      omega
  set lev : Fin n → ℕ := fun a => (a : ℕ) + p a with hlev
  have hmon : Monotone lev := by
    intro a c hac
    have hac' : (a : ℕ) ≤ c := hac
    exact step_mono p hstep ((c : ℕ) - a) a c (by omega)
  have hL : ∀ a b : Fin n, a < b → lev a = lev b → lam a = lam b := by
    intro a b hab h
    rcases (hlam hab.le).lt_or_eq with h1 | h1
    · have h2 := hlt a b h1
      rw [Fin.lt_def] at h2 hab
      simp only [hlev, hp] at h
      omega
    · exact h1.symm
  have hIs : IsLev lam lev := by
    refine ⟨hmon, fun a b h => ?_⟩
    rcases lt_trichotomy a b with h1 | h1 | h1
    · exact hL a b h1 h
    · rw [h1]
    · exact (hL b a h1 h.symm).symm

  set F : Fin n → Fin n → ℝ := fun a b =>
    2 * ((if lev a < lev b then (1 : ℝ) else 0) - (if lev b < lev a then (1 : ℝ) else 0)) with hF
  have hFa : ∀ a b, F b a = -F a b := fun a b => by
    simp only [hF]
    ring
  have hpos : ∀ a b : Fin n, a < b → F a b = s0 a b + s0 (π a) (π b) := by
    intro a b hab
    have hne : π a ≠ π b := fun e => hab.ne (π.injective e)
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have hlv : lev a < lev b := by
        have h2 : (π a : ℕ) < π b := h1
        have h3 : (a : ℕ) < b := hab
        simp only [hlev, hp]
        omega
      simp [hF, hlv, hlv.not_gt, s0, hab, h1]
      norm_num
    · have hab' : (a : ℕ) < b := hab
      have hlv : lev a = lev b :=
        key_lev p hinj hstep ((b : ℕ) - a - 1) a b (by omega) h1
      simp [hF, hlv, s0, hab, h1, asymm h1]
  have hall : ∀ a b : Fin n, F a b = s0 a b + s0 (π a) (π b) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · exact hpos a b h
    · subst h
      simp [hF, sign_self_eq_zero]
    · have := hpos b a h
      rw [hFa a b, sign_antisymmetric_alt a b, sign_antisymmetric_alt (π a) (π b)] at this
      linarith
  have hr : ∀ a, 2 * rhoU lev a = rhoV n a + rhoV n (π a) := by
    intro a
    have h1 : ∑ b, F a b = 2 * (2 * rhoU lev a) := by
      rw [two_rhoU, mul_sum]
    have h2 : ∑ b, F a b = 2 * rhoV n a + 2 * rhoV n (π a) := by
      simp only [hall, sum_add_distrib, sum_sign_eq_two_rho]
      rw [Equiv.sum_comp π (fun b => s0 (π a) b), sum_sign_eq_two_rho]
    linarith
  have e : (fun a => 2 * (lam a : ℝ) + rhoV n a + rhoV n (π a)) = muQ lam lev := by
    funext a
    simp only [muQ]
    rw [hr]
    ring
  rw [e]
  exact GlobalTheory.CompanionTheory.LevelCompress.muQ_mem_harmSet hIs

theorem domC_of_anti (x : Fin n → ℝ) (hx : Antitone x) : domC x = x := by
  have h : Tuple.sort (fun a => -x a) = Equiv.refl (Fin n) :=
    Tuple.sort_eq_refl_iff_monotone.2 fun a b hab => neg_le_neg (hx hab)
  unfold domC
  rw [h]
  rfl

theorem rhoU_anti (lev : Fin n → ℕ) {a b : Fin n} (h : lev a ≤ lev b) : rhoU lev b ≤ rhoU lev a := by
  have h1 : (univ.filter fun c => lev b < lev c).card ≤ (univ.filter fun c => lev a < lev c).card :=
    card_le_card fun c hc => by
      simp only [mem_filter, mem_univ, true_and] at hc ⊢
      omega
  have h2 : (univ.filter fun c => lev c < lev a).card ≤ (univ.filter fun c => lev c < lev b).card :=
    card_le_card fun c hc => by
      simp only [mem_filter, mem_univ, true_and] at hc ⊢
      omega
  have h1' : ((univ.filter fun c => lev b < lev c).card : ℝ) ≤ ((univ.filter fun c => lev a < lev c).card : ℝ) := by
    exact_mod_cast h1
  have h2' : ((univ.filter fun c => lev c < lev a).card : ℝ) ≤ ((univ.filter fun c => lev c < lev b).card : ℝ) := by
    exact_mod_cast h2
  unfold rhoU
  linarith

def levi (lev : Fin n → ℕ) : Finset (Fin n × Fin n) := univ.filter fun p => p.1 < p.2 ∧ lev p.1 = lev p.2

theorem wtB_levi (lev : Fin n → ℕ) (hm : Monotone lev) (a : Fin n) :
    wtB (levi lev) a = 2 * rhoV n a - 2 * rhoU lev a := by
  have h : ∀ b, s0 a b - mB (levi lev) a b + mB (levi lev) b a =
      (if lev a < lev b then (1 : ℝ) else 0) - (if lev b < lev a then (1 : ℝ) else 0) := by
    intro b
    rcases lt_trichotomy a b with h | h | h
    · have h1 := hm h.le
      by_cases he : lev a = lev b
      · simp [s0, mB, levi, h, asymm h, he]
      · have h2 : lev a < lev b := lt_of_le_of_ne h1 he
        simp [s0, mB, levi, h, asymm h, he, h2, h2.not_gt]
    · subst h
      simp [s0, mB]
    · have h1 := hm h.le
      by_cases he : lev a = lev b
      · simp [s0, mB, levi, h, asymm h, he]
      · have h2 : lev b < lev a := lt_of_le_of_ne h1 (Ne.symm he)
        simp [s0, mB, levi, h, asymm h, he, h2, h2.not_gt, Ne.symm he]
  have h2 := two_rhoU lev a
  simp only [← h, sum_add_distrib, sum_sub_distrib, sum_sign_eq_two_rho, sum_row_count, sum_column_count] at h2
  unfold wtB
  linarith

theorem harm_sub (lam : Fin n → ℤ) (hlam : Antitone lam) : harmSet lam ⊆ topTypes lam := by
  intro μ hμ
  unfold harmSet at hμ
  obtain ⟨l, hl, rfl⟩ := mem_image.1 hμ
  have hl' : IsLev lam fun a => (l a : ℕ) := by simpa using hl
  set lev : Fin n → ℕ := fun a => (l a : ℕ) with hlev
  have hX : ∀ {a b : Fin n}, a ≤ b → (lam b : ℝ) ≤ lam a := fun h => by exact_mod_cast hlam h
  have hanti : StrictAnti (muQ lam lev + rhoV n) := by
    intro a b hab
    have h1 := hX hab.le
    have h2 := rhoU_anti lev (hl'.1 hab.le)
    have h3 := rho_anti (n := n) hab
    simp only [Pi.add_apply, muQ]
    linarith
  have hx : (fun a => 2 * (lam a : ℝ) + 2 * rhoV n a) + rhoV n - wtB (levi lev) = muQ lam lev + rhoV n := by
    funext a
    simp only [Pi.add_apply, Pi.sub_apply, muQ, wtB_levi lev hl'.1 a]
    ring
  unfold topTypes
  refine mem_filter.2 ⟨mem_image.2 ⟨levi lev, ?_, ?_⟩, ?_⟩
  · refine mem_filter.2 ⟨mem_univ _, fun p hp => ?_⟩
    exact (mem_filter.1 hp).2.1
  · rw [hx, domC_of_anti _ hanti.antitone]
    simp
  · exact hanti

theorem top_form (lam : Fin n → ℤ) (hlam : Antitone lam) {ν : Fin n → ℝ} (h : ν ∈ topTypes lam) :
    ∃ η : Fin n → ℝ, (∀ g, dot η g ≤ supp g) ∧ ν = (fun a => 2 * (lam a : ℝ) + rhoV n a) + η ∧
      StrictAnti (ν + rhoV n) := by
  unfold topTypes at h
  obtain ⟨h1, h2⟩ := mem_filter.1 h
  obtain ⟨B, hB, rfl⟩ := mem_image.1 h1
  have hB' := (mem_filter.1 hB).2
  set c : Fin n → ℝ := fun a => 2 * (lam a : ℝ) + 2 * rhoV n a with hc
  have hcA : Antitone c := by
    intro a b hab
    have h3 : (lam b : ℝ) ≤ lam a := by exact_mod_cast hlam hab
    have h4 := (rho_anti (n := n)).antitone hab
    simp only [hc]
    linarith
  have e : c + rhoV n - wtB B = c + (rhoV n - wtB B) := by
    funext a
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [e] at h2 ⊢
  refine ⟨domC (c + (rhoV n - wtB B)) - c, maj_sort c _ hcA (dot_rho_sub_le B hB'), ?_, h2⟩
  funext a
  simp only [Pi.add_apply, Pi.sub_apply, hc]
  ring

theorem spin_le (lam : Fin n → ℤ) (hlam : Antitone lam) {ν : Fin n → ℝ} (h : ν ∈ topTypes lam) :
    spinSq ν ≤ LSq lam ∧ (spinSq ν = LSq lam → ν ∈ harmSet lam) := by
  obtain ⟨η, hη, rfl, hst⟩ := top_form lam hlam h
  obtain ⟨π, hπ⟩ := exists_spin ((fun a => 2 * (lam a : ℝ) + rhoV n a) + η)
  set X : Fin n → ℝ := fun a => (lam a : ℝ) with hXd
  set r : Fin n → ℝ := rhoV n ∘ π with hr
  have hXA : Antitone X := fun a b hab => by
    show (lam b : ℝ) ≤ lam a
    exact_mod_cast hlam hab
  have e1 : (fun a => 2 * (lam a : ℝ) + rhoV n a) + η - rhoV n + r = (2 : ℝ) • X + η + r := by
    funext a
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hXd]
    ring
  have e2 : LSq lam = dot ((2 : ℝ) • X + (2 : ℝ) • rhoV n) ((2 : ℝ) • X + (2 : ℝ) • rhoV n) := by
    unfold LSq
    rw [nsq_dot]
    congr 1 <;>
    · funext a
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hXd]
      ring
  have f1 := dot_self_le η hη
  have f2 : dot r r = dot (rhoV n) (rhoV n) := d_perm _ _ π
  have f3 : dot η X ≤ dot X (rhoV n) := by
    rw [dot_antitone X hXA]
    exact hη X
  have f4 : dot X r ≤ dot X (rhoV n) := rearr X hXA π
  have f5 : dot η r ≤ dot (rhoV n) (rhoV n) := by
    rw [dot_antitone _ rho_anti.antitone, ← supp_perm (rhoV n) π]
    exact hη r
  rw [hπ, e1, e2]
  simp only [dL_add, dR_add, dL_smul, dR_smul]
  rw [d_comm r X, d_comm r η, d_comm η X, d_comm (rhoV n) X] at *
  constructor
  · linarith
  · intro heq
    have t1 : dot η η = dot (rhoV n) (rhoV n) := by linarith
    have t4 : dot X r = dot X (rhoV n) := by linarith
    have t5 : dot η r = dot (rhoV n) (rhoV n) := by linarith
    have hz : dot (η - r) (η - r) = 0 := by
      simp only [dL_sub, dR_sub]
      rw [d_comm r η]
      linarith
    have hηr : η = r := by
      funext a
      have h0 := (sum_eq_zero_iff_of_nonneg fun a _ => mul_self_nonneg ((η - r) a)).1 hz a (mem_univ a)
      have := mul_self_eq_zero.1 h0
      simpa [sub_eq_zero] using this
    have hs : StrictAnti fun a => 2 * (lam a : ℝ) + 2 * rhoV n a + rhoV n (π a) := by
      intro a b hab
      have := hst hab
      simp only [Pi.add_apply, hηr, hr, Function.comp] at this
      linarith
    have := harm_of_eq lam hlam π hs t4
    convert this using 1
    funext a
    simp only [Pi.add_apply, hηr, hr, Function.comp]

theorem lemmaHT : LemmaHT := fun _ lam hlam =>
  ⟨harm_sub lam hlam, fun _ h => spin_le lam hlam h⟩

end GlobalTheory.CompanionTheory.SpinBound
