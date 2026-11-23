import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.AltBranchStatement

open Finset

noncomputable section

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

def sq_Intl {k : ℕ} (f : Fin k → Fin k → ℕ) : Prop :=
  ∀ l j : Fin k, j.val = l.val + 1 → ∀ a : Fin k,
    (∑ b : Fin k with b ≤ a, f b j) ≤ ∑ b : Fin k with b < a, f b l

def sq_SSZ (k : ℕ) (κ : Fin k → ℤ) : Type :=
  {g : Fin k → Fin k → ℕ // sq_Intl g ∧ ∀ s, ((∑ a, g a s : ℕ) : ℤ) = κ s}

def sq_rowSum {k : ℕ} (g : Fin k → Fin k → ℕ) (a : Fin k) : ℕ := ∑ s, g a s

def sq_mono {K : Type*} [Field K] {k : ℕ} (t : Fin k → K) (g : Fin k → Fin k → ℕ) : K :=
  ∏ a, t a ^ sq_rowSum g a

theorem sq_sum_le_castSucc {k : ℕ} (F : Fin (k + 1) → ℕ) (a : Fin k) :
    (∑ b : Fin (k + 1) with b ≤ a.castSucc, F b) = ∑ b : Fin k with b ≤ a, F b.castSucc := by
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc]
  simp

theorem sq_sum_lt_castSucc {k : ℕ} (F : Fin (k + 1) → ℕ) (a : Fin k) :
    (∑ b : Fin (k + 1) with b < a.castSucc, F b) = ∑ b : Fin k with b < a, F b.castSucc := by
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc]
  have : ¬ (Fin.last k < a.castSucc) := not_lt.2 (Fin.le_last _)
  simp [this]

theorem sq_sum_le_last {k : ℕ} (F : Fin (k + 1) → ℕ) :
    (∑ b : Fin (k + 1) with b ≤ Fin.last k, F b) = ∑ b, F b := by
  rw [Finset.sum_filter]
  simp [Fin.le_last]

theorem sq_sum_lt_last {k : ℕ} (F : Fin (k + 1) → ℕ) :
    (∑ b : Fin (k + 1) with b < Fin.last k, F b) = ∑ b : Fin k, F b.castSucc := by
  rw [Finset.sum_filter, Fin.sum_univ_castSucc]
  simp [Fin.castSucc_lt_last]

theorem sq_intl_zero {k : ℕ} (f : Fin k → Fin k → ℕ) (hf : sq_Intl f) :
    ∀ (tv : ℕ) (t : Fin k), t.val = tv → ∀ a : Fin k, a.val < tv → f a t = 0 := by
  intro tv
  induction tv with
  | zero => intro t _ a ha; omega
  | succ tv ih =>
    intro t ht a ha
    have hl : tv < k := by have := t.isLt; omega
    have h1 := hf ⟨tv, hl⟩ t (by simp [ht]) a
    have h2 : (∑ b : Fin k with b < a, f b ⟨tv, hl⟩) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [Finset.mem_filter] at hb
      exact ih ⟨tv, hl⟩ rfl b (by have : b.val < a.val := hb.2; omega)
    rw [h2] at h1
    have h3 : f a t ≤ ∑ b : Fin k with b ≤ a, f b t :=
      Finset.single_le_sum (f := fun b => f b t) (fun _ _ => Nat.zero_le _) (by simp)
    omega

theorem sq_mem_interl {n : ℕ} (μ : Fin (n + 1) → ℤ) (κ : Fin n → ℤ) :
    κ ∈ interl μ ↔ ∀ i, μ i.succ ≤ κ i ∧ κ i ≤ μ i.castSucc := by
  simp [interl, Fintype.mem_piFinset, Finset.mem_Icc]

def sq_restr {k : ℕ} (f : Fin (k + 1) → Fin (k + 1) → ℕ) : Fin k → Fin k → ℕ :=
  fun a t => f a.castSucc t.castSucc

def sq_UU (k : ℕ) (μ : Fin (k + 1) → ℤ) : Type :=
  {g : Fin k → Fin k → ℕ // sq_Intl g ∧ (fun t => ((∑ a, g a t : ℕ) : ℤ)) ∈ interl μ}

theorem sq_restr_mem {k : ℕ} (μ : Fin (k + 1) → ℤ) (f : sq_SSZ (k + 1) μ) :
    sq_Intl (sq_restr f.1) ∧ (fun t => ((∑ a, sq_restr f.1 a t : ℕ) : ℤ)) ∈ interl μ := by
  obtain ⟨f, hI, hs⟩ := f
  refine ⟨?_, ?_⟩
  · intro l j hlj a
    have h := hI l.castSucc j.castSucc (by simpa using hlj) a.castSucc
    rw [sq_sum_le_castSucc, sq_sum_lt_castSucc] at h
    exact h
  · rw [sq_mem_interl]
    intro i
    constructor
    · have h := hI i.castSucc i.succ (by simp) (Fin.last k)
      rw [sq_sum_le_last, sq_sum_lt_last] at h
      rw [← hs i.succ]
      exact_mod_cast h
    · rw [← hs i.castSucc, Fin.sum_univ_castSucc]
      simp only [sq_restr]
      push_cast
      have : (0 : ℤ) ≤ (f (Fin.last k) i.castSucc : ℤ) := Int.natCast_nonneg _
      linarith

def sq_rho {k : ℕ} (μ : Fin (k + 1) → ℤ) (f : sq_SSZ (k + 1) μ) : sq_UU k μ :=
  ⟨sq_restr f.1, sq_restr_mem μ f⟩

theorem sq_rho_inj {k : ℕ} (μ : Fin (k + 1) → ℤ) : Function.Injective (sq_rho μ) := by
  intro f f' h
  have h0 : sq_restr f.1 = sq_restr f'.1 := congrArg Subtype.val h
  obtain ⟨f, hI, hs⟩ := f
  obtain ⟨f', hI', hs'⟩ := f'
  simp only at h0
  have hc : ∀ a t : Fin k, f a.castSucc t.castSucc = f' a.castSucc t.castSucc :=
    fun a t => congrFun (congrFun h0 a) t
  have hz : ∀ a : Fin k, f a.castSucc (Fin.last k) = f' a.castSucc (Fin.last k) := by
    intro a
    rw [sq_intl_zero f hI k (Fin.last k) rfl a.castSucc (by simp),
      sq_intl_zero f' hI' k (Fin.last k) rfl a.castSucc (by simp)]
  have hup : ∀ (a : Fin k) (t : Fin (k + 1)), f a.castSucc t = f' a.castSucc t := by
    intro a t
    induction t using Fin.lastCases with
    | last => exact hz a
    | cast t => exact hc a t
  apply Subtype.ext
  funext a t
  induction a using Fin.lastCases with
  | cast a => exact hup a t
  | last =>
    have h1 := hs t
    have h2 := hs' t
    rw [Fin.sum_univ_castSucc] at h1 h2
    have h3 : ∑ a : Fin k, f a.castSucc t = ∑ a : Fin k, f' a.castSucc t :=
      Finset.sum_congr rfl fun a _ => hup a t
    rw [h3] at h1
    have h4 := h1.trans h2.symm
    have h5 : (∑ a : Fin k, f' a.castSucc t) + f (Fin.last k) t =
        (∑ a : Fin k, f' a.castSucc t) + f' (Fin.last k) t := by
      exact_mod_cast h4
    exact Nat.add_left_cancel h5

def sq_ext {k : ℕ} (μ : Fin (k + 1) → ℤ) (g : Fin k → Fin k → ℕ) : Fin (k + 1) → Fin (k + 1) → ℕ :=
  fun a t => Fin.lastCases (motive := fun _ => ℕ)
    (Fin.lastCases (motive := fun _ => ℕ) (μ (Fin.last k)).toNat
      (fun t' => (μ t'.castSucc - ((∑ b, g b t' : ℕ) : ℤ)).toNat) t)
    (fun a' => Fin.lastCases (motive := fun _ => ℕ) 0 (fun t' => g a' t') t) a

theorem sq_ext_cc {k : ℕ} (μ : Fin (k + 1) → ℤ) (g : Fin k → Fin k → ℕ) (a t : Fin k) :
    sq_ext μ g a.castSucc t.castSucc = g a t := by simp [sq_ext]

theorem sq_ext_cl {k : ℕ} (μ : Fin (k + 1) → ℤ) (g : Fin k → Fin k → ℕ) (a : Fin k) :
    sq_ext μ g a.castSucc (Fin.last k) = 0 := by simp [sq_ext]

theorem sq_ext_lc {k : ℕ} (μ : Fin (k + 1) → ℤ) (g : Fin k → Fin k → ℕ) (t : Fin k) :
    sq_ext μ g (Fin.last k) t.castSucc = (μ t.castSucc - ((∑ b, g b t : ℕ) : ℤ)).toNat := by
  simp [sq_ext]

theorem sq_ext_ll {k : ℕ} (μ : Fin (k + 1) → ℤ) (g : Fin k → Fin k → ℕ) :
    sq_ext μ g (Fin.last k) (Fin.last k) = (μ (Fin.last k)).toNat := by simp [sq_ext]

theorem sq_ext_sum {k : ℕ} (μ : Fin (k + 1) → ℤ) (hμ : 0 ≤ μ (Fin.last k)) (g : sq_UU k μ)
    (t : Fin (k + 1)) : ((∑ a, sq_ext μ g.1 a t : ℕ) : ℤ) = μ t := by
  obtain ⟨g, hI, hb⟩ := g
  rw [sq_mem_interl] at hb
  rw [Fin.sum_univ_castSucc]
  induction t using Fin.lastCases with
  | last =>
    simp only [sq_ext_cl, sq_ext_ll, Finset.sum_const_zero, zero_add]
    exact Int.toNat_of_nonneg hμ
  | cast t =>
    simp only [sq_ext_cc, sq_ext_lc]
    have h := (hb t).2
    omega

theorem sq_ext_intl {k : ℕ} (μ : Fin (k + 1) → ℤ) (hμ : 0 ≤ μ (Fin.last k)) (g : sq_UU k μ) :
    sq_Intl (sq_ext μ g.1) := by
  have hsum := sq_ext_sum μ hμ g
  obtain ⟨g, hI, hb⟩ := g
  rw [sq_mem_interl] at hb
  simp only at hsum
  intro l j hlj a
  induction l using Fin.lastCases with
  | last => exfalso; have := j.isLt; simp at hlj; omega
  | cast l =>
    induction a using Fin.lastCases with
    | last =>
      rw [sq_sum_le_last, sq_sum_lt_last]
      simp only [sq_ext_cc]
      have hj : j = l.succ := Fin.ext (by simpa using hlj)
      have h1 := hsum j
      have h2 := (hb l).1
      rw [← hj, ← h1] at h2
      exact_mod_cast h2
    | cast a =>
      rw [sq_sum_le_castSucc, sq_sum_lt_castSucc]
      simp only [sq_ext_cc]
      induction j using Fin.lastCases with
      | last => simp [sq_ext_cl]
      | cast j =>
        simp only [sq_ext_cc]
        exact hI l j (by simpa using hlj) a

theorem sq_rho_surj {k : ℕ} (μ : Fin (k + 1) → ℤ) (hμ : 0 ≤ μ (Fin.last k)) :
    Function.Surjective (sq_rho μ) := by
  intro g
  refine ⟨⟨sq_ext μ g.1, sq_ext_intl μ hμ g, sq_ext_sum μ hμ g⟩, ?_⟩
  apply Subtype.ext
  funext a t
  exact sq_ext_cc μ g.1 a t

theorem sq_SSZ_finite (k : ℕ) (κ : Fin k → ℤ) : Finite (sq_SSZ k κ) := by
  classical
  let B : ℕ := ∑ t, (κ t).toNat
  have hinj : Function.Injective (fun g : sq_SSZ k κ => fun a t => (⟨g.1 a t, by
      have h1 : g.1 a t ≤ ∑ a, g.1 a t :=
        Finset.single_le_sum (f := fun a => g.1 a t) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      have h2 := g.2.2 t
      have h3 : (κ t).toNat ≤ B :=
        Finset.single_le_sum (f := fun t => (κ t).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      omega⟩ : Fin (B + 1))) := by
    intro g g' h
    apply Subtype.ext
    funext a t
    exact congrArg Fin.val (congrFun (congrFun h a) t)
  exact Finite.of_injective _ hinj

def sq_fibEquiv {k : ℕ} (μ : Fin (k + 1) → ℤ) : sq_UU k μ ≃ Σ κ : ↥(interl μ), sq_SSZ k κ.1 where
  toFun g := ⟨⟨_, g.2.2⟩, ⟨g.1, g.2.1, fun _ => rfl⟩⟩
  invFun x := ⟨x.2.1, x.2.2.1, by
    have : (fun t => ((∑ a, x.2.1 a t : ℕ) : ℤ)) = x.1.1 := funext x.2.2.2
    rw [this]; exact x.1.2⟩
  left_inv g := rfl
  right_inv x := by
    obtain ⟨⟨κ, hκ⟩, ⟨g, hI, hs⟩⟩ := x
    have : (fun t => ((∑ a, g a t : ℕ) : ℤ)) = κ := funext hs
    subst this
    rfl

theorem sq_mono_split {K : Type*} [Field K] {k : ℕ} (μ : Fin (k + 1) → ℤ) (t : Fin (k + 1) → K)
    (g : sq_SSZ (k + 1) μ) :
    sq_mono t g.1 = sq_mono (fun i => t i.castSucc) (sq_restr g.1) *
      t (Fin.last k) ^ (wsum μ - wsum (fun s => ((∑ a, sq_restr g.1 a s : ℕ) : ℤ))) := by
  obtain ⟨g, hI, hs⟩ := g
  have hrow : ∀ a : Fin k, sq_rowSum g a.castSucc = sq_rowSum (sq_restr g) a := by
    intro a
    rw [sq_rowSum, Fin.sum_univ_castSucc,
      sq_intl_zero g hI k (Fin.last k) rfl a.castSucc (by simp), add_zero]
    rfl
  have hlast : ((sq_rowSum g (Fin.last k) : ℕ) : ℤ) =
      wsum μ - wsum (fun s => ((∑ a, sq_restr g a s : ℕ) : ℤ)) := by
    have h1 : wsum μ = ∑ a, (sq_rowSum g a : ℤ) := by
      simp only [wsum, ← hs, sq_rowSum]
      push_cast
      exact Finset.sum_comm
    have h2 : wsum (fun s => ((∑ a, sq_restr g a s : ℕ) : ℤ)) =
        ∑ a : Fin k, (sq_rowSum (sq_restr g) a : ℤ) := by
      simp only [wsum, sq_rowSum]
      push_cast
      exact Finset.sum_comm
    rw [h1, h2, Fin.sum_univ_castSucc]
    simp only [hrow]
    ring
  simp only [sq_mono]
  rw [Fin.prod_univ_castSucc, ← hlast, zpow_natCast]
  simp only [hrow]

theorem sq_gt_sum {K : Type*} [Field K] : ∀ (k : ℕ) (κ : Fin k → ℤ), (∀ s, 0 ≤ κ s) →
    ∀ [Fintype (sq_SSZ k κ)] (t : Fin k → K), ∑ g : sq_SSZ k κ, sq_mono t g.1 = gtChar k κ t := by
  intro k
  induction k with
  | zero =>
    intro κ _ _ t
    have : Unique (sq_SSZ 0 κ) :=
      { default := ⟨fun a => a.elim0, fun l => l.elim0, fun s => s.elim0⟩
        uniq := fun g => Subtype.ext (funext fun a => a.elim0) }
    rw [Fintype.sum_unique]
    simp [sq_mono, gtChar]
  | succ k ih =>
    intro μ hμ _ t
    have : ∀ κ : Fin k → ℤ, Fintype (sq_SSZ k κ) := fun κ => @Fintype.ofFinite _ (sq_SSZ_finite k κ)
    have : Fintype (sq_UU k μ) := Fintype.ofEquiv _ (sq_fibEquiv μ).symm
    rw [Fintype.sum_bijective (sq_rho μ) ⟨sq_rho_inj μ, sq_rho_surj μ (hμ _)⟩ _
      (fun u : sq_UU k μ => sq_mono (fun i => t i.castSucc) u.1 *
        t (Fin.last k) ^ (wsum μ - wsum (fun s => ((∑ a, u.1 a s : ℕ) : ℤ)))) (sq_mono_split μ t)]
    refine (Fintype.sum_equiv (sq_fibEquiv μ) _
      (fun x : (Σ κ : ↥(interl μ), sq_SSZ k κ.1) => sq_mono (fun i => t i.castSucc) x.2.1 *
        t (Fin.last k) ^ (wsum μ - wsum x.1.1)) (fun u => rfl)).trans ?_
    rw [Fintype.sum_sigma]
    simp only [← Finset.sum_mul]
    rw [gtChar, ← Finset.sum_coe_sort (interl μ)]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [ih κ.1 (fun s => le_trans (hμ _) ((sq_mem_interl μ κ.1).1 κ.2 s).1)]

end ReciprocityTheory.ChartRestriction.TR.Weyl
