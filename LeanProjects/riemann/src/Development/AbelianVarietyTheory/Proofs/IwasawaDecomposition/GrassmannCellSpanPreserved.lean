import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GrCl

variable {S : Type} [CommRing S] {m a k b : ℕ}

def gcellOff (x : GVar m a k b → S) (i l : Fin m) : S :=
  if h : a ≤ (l : ℕ) ∧ (l : ℕ) < k ∧ k ≤ (i : ℕ) ∧ (i : ℕ) < b then x ⟨(i, l), h⟩ else 0

theorem gcellOff_ne (x : GVar m a k b → S) {i l : Fin m} (h : gcellOff x i l ≠ 0) :
    a ≤ (l : ℕ) ∧ (l : ℕ) < k ∧ k ≤ (i : ℕ) ∧ (i : ℕ) < b := by
  by_contra h'
  exact h (by simp [gcellOff, h'])

theorem gcellOff_of_ge (x : GVar m a k b → S) (i : Fin m) {l : Fin m} (h : k ≤ (l : ℕ)) : gcellOff x i l = 0 := by
  by_contra h'
  have := gcellOff_ne x h'
  omega

theorem gcellOff_of_lt (x : GVar m a k b → S) {i : Fin m} (l : Fin m) (h : (i : ℕ) < k) : gcellOff x i l = 0 := by
  by_contra h'
  have := gcellOff_ne x h'
  omega

theorem gcell_eq_add (x : GVar m a k b → S) (i l : Fin m) :
    gcell x i l = gcellOff x i l + if i = l then 1 else 0 := by
  by_cases h : a ≤ (l : ℕ) ∧ (l : ℕ) < k ∧ k ≤ (i : ℕ) ∧ (i : ℕ) < b
  · have hne : i ≠ l := fun e => by subst e; omega
    simp [gcell, gcellOff, h, hne]
  · simp [gcell, gcellOff, h]

variable {Q : Type} [AddCommGroup Q] [Module S Q]

theorem gvec_eq_add (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) (l : Fin m) :
    gvec c w x l = c (w.1 l) + ∑ i, gcellOff x i l • c (w.1 i) := by
  simp only [gvec, gcell_eq_add, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [add_comm]

theorem gvec_of_ge (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) {l : Fin m} (h : k ≤ (l : ℕ)) :
    gvec c w x l = c (w.1 l) := by
  rw [gvec_eq_add]
  simp [gcellOff_of_ge x _ h]

theorem gvec_inv (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) (l : Fin m) :
    c (w.1 l) = gvec c w x l - ∑ i, gcellOff x i l • gvec c w x i := by
  have hs : ∑ i, gcellOff x i l • gvec c w x i = ∑ i, gcellOff x i l • c (w.1 i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : gcellOff x i l = 0
    · simp [h]
    · rw [gvec_of_ge c w x (gcellOff_ne x h).2.2.1]
  rw [hs, gvec_eq_add]
  abel

theorem gvec_combo (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) (g : Fin m → S) :
    ∑ l, g l • gvec c w x l = ∑ i, (g i + ∑ l, gcellOff x i l * g l) • c (w.1 i) := by
  simp only [gvec_eq_add, smul_add, Finset.sum_add_distrib, add_smul, Finset.smul_sum, smul_smul, Finset.sum_smul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]

theorem gpm_lt_iff (w : GPm m a b) {e : ℕ} (he : e ≤ a ∨ b ≤ e) (i : Fin m) :
    (w.1 i : ℕ) < e ↔ (i : ℕ) < e := by
  by_cases hi : (i : ℕ) < a ∨ b ≤ (i : ℕ)
  · rw [w.2 i hi]
  · have hwi : ¬ ((w.1 i : ℕ) < a ∨ b ≤ (w.1 i : ℕ)) := fun h => by
      have := w.1.injective (w.2 _ h)
      rw [this] at h
      exact hi h
    omega

theorem gvec_linearIndependent (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) (hc : LinearIndependent S c) :
    LinearIndependent S (gvec c w x) := by
  have hd : LinearIndependent S (c ∘ w.1) := hc.comp _ w.1.injective
  rw [Fintype.linearIndependent_iff] at hd ⊢
  intro g hg
  rw [gvec_combo] at hg
  have h1 := hd _ hg
  have hlow : ∀ l : Fin m, (l : ℕ) < k → g l = 0 := fun l hl => by
    have hs : ∑ l', gcellOff x l l' * g l' = 0 :=
      Finset.sum_eq_zero fun l' _ => by rw [gcellOff_of_lt x l' hl, zero_mul]
    have := h1 l
    rwa [hs, add_zero] at this
  intro l
  by_cases hl : (l : ℕ) < k
  · exact hlow l hl
  · have hs : ∑ l', gcellOff x l l' * g l' = 0 := Finset.sum_eq_zero fun l' _ => by
      by_cases h : gcellOff x l l' = 0
      · rw [h, zero_mul]
      · rw [hlow l' (gcellOff_ne x h).2.1, mul_zero]
    have := h1 l
    rwa [hs, add_zero] at this

theorem gvec_span (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) :
    Submodule.span S (Set.range (gvec c w x)) = Submodule.span S (Set.range c) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    rw [SetLike.mem_coe, gvec_eq_add]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨_, rfl⟩)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨l, rfl⟩ := w.1.surjective j
    rw [SetLike.mem_coe, gvec_inv c w x l]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

theorem gvec_initSpan (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) {e : ℕ} (he : e ≤ a ∨ b ≤ e) :
    initSpan S (gvec c w x) e = initSpan S c e := by
  unfold GlobalTheory.FlagMod.initSpan
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, hj, rfl⟩
    have hj : (j : ℕ) < e := hj
    rw [SetLike.mem_coe, gvec_eq_add]
    refine Submodule.add_mem _ (Submodule.subset_span ⟨w.1 j, (gpm_lt_iff w he j).2 hj, rfl⟩)
      (Submodule.sum_mem _ fun i _ => ?_)
    by_cases h : gcellOff x i j = 0
    · rw [h, zero_smul]
      exact Submodule.zero_mem _
    · have := gcellOff_ne x h
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w.1 i, (gpm_lt_iff w he i).2 (by omega), rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, hj, rfl⟩
    have hj : (j : ℕ) < e := hj
    obtain ⟨l, rfl⟩ := w.1.surjective j
    have hl : (l : ℕ) < e := (gpm_lt_iff w he l).1 hj
    rw [SetLike.mem_coe, gvec_inv c w x l]
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨l, hl, rfl⟩) (Submodule.sum_mem _ fun i _ => ?_)
    by_cases h : gcellOff x i l = 0
    · rw [h, zero_smul]
      exact Submodule.zero_mem _
    · have := gcellOff_ne x h
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, (show (i : ℕ) < e by omega), rfl⟩)

theorem gvec_frame : ∀ (S : Type) [CommRing S] (m a k b : ℕ) (Q : Type) [AddCommGroup Q] [Module S Q] (c : Fin m → Q)
    (w : GPm m a b) (x : GVar m a k b → S), a ≤ k → k ≤ b →
    (LinearIndependent S c → LinearIndependent S (gvec c w x)) ∧
      Submodule.span S (Set.range (gvec c w x)) = Submodule.span S (Set.range c) ∧
      ∀ e : ℕ, e ≤ a ∨ b ≤ e → initSpan S (gvec c w x) e = initSpan S c e :=
  fun _ _ _ _ _ _ _ _ _ c w x _ _ =>
    ⟨gvec_linearIndependent c w x, gvec_span c w x, fun _ he => gvec_initSpan c w x he⟩

end GlobalTheory.GrCl
