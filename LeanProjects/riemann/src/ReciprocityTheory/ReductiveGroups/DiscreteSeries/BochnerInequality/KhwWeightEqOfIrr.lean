import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.CasimirKKhwVec

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section KIrr

variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X} {Λ : Fin n → ℝ} {V : Submodule ℂ X}

def kirrWord (A : Fin n → Fin n → Module.End ℂ X) (u : X) : List (Fin n × Fin n) → X
  | [] => u
  | p :: l => A p.1 p.2 (kirrWord A u l)

def kirrWt (ν : Fin n → ℝ) : List (Fin n × Fin n) → Fin n → ℝ
  | [] => ν
  | p :: l => kirrWt ν l + root p.1 p.2

def KirrLow (ε : Fin n → Bool) (l : List (Fin n × Fin n)) : Prop :=
  ∀ p ∈ l, p.2 < p.1 ∧ ε p.1 = ε p.2

def kirrSpan (ε : Fin n → Bool) (A : Fin n → Fin n → Module.End ℂ X) (u : X) : Submodule ℂ X :=
  Submodule.span ℂ {x | ∃ l, KirrLow ε l ∧ x = kirrWord A u l}

def kirrPs (k : ℕ) (μ : Fin n → ℝ) : ℝ := ∑ a ∈ univ.filter (fun a : Fin n => a.val < k), μ a

def kirrH (A : Fin n → Fin n → Module.End ℂ X) (k : ℕ) : Module.End ℂ X :=
  ∑ a ∈ univ.filter (fun a : Fin n => a.val < k), A a a

private theorem glRep_apply_commutator (hA : IsGlRep A) (a b c d : Fin n) (v : X) :
    A a b (A c d v) = A c d (A a b v) + ((if b = c then A a d else 0) - if d = a then A c b else 0) v :=
  eq_add_of_sub_eq' (by
    have h := LinearMap.congr_fun (hA a b c d) v
    rw [LinearMap.sub_apply] at h
    exact h)

theorem kirrWord_wt (hA : IsGlRep A) {ν : Fin n → ℝ} {u : X} (hu : ∀ a, A a a u = (ν a : ℂ) • u) :
    ∀ l a, A a a (kirrWord A u l) = (kirrWt ν l a : ℂ) • kirrWord A u l
  | [], a => by simpa [kirrWord, kirrWt] using hu a
  | p :: l, a => by
    obtain ⟨b, c⟩ := p
    have ih := kirrWord_wt hA hu l a
    have key := LinearMap.congr_fun (hA a a b c) (kirrWord A u l)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at key
    simp only [kirrWord, kirrWt]
    rw [sub_eq_iff_eq_add, ih, map_smul] at key
    rw [key]
    by_cases h1 : a = b <;> by_cases h2 : c = a
    · subst h1; subst h2; simp [root]
    · subst h1; (simp [root, h2, Ne.symm h2, add_smul]; abel)
    · subst h2; (simp [root, h1, add_smul]; abel)
    · simp [root, h1, h2, Ne.symm h2]

theorem kirrWord_mem (u : X) {l : List (Fin n × Fin n)} (hl : KirrLow ε l) :
    kirrWord A u l ∈ kirrSpan ε A u := Submodule.subset_span ⟨l, hl, rfl⟩

theorem kirr_low_mem {u : X} {a b : Fin n} (hba : b < a) (hab : ε a = ε b) {x : X}
    (hx : x ∈ kirrSpan ε A u) : A a b x ∈ kirrSpan ε A u := by
  have h : kirrSpan ε A u ≤ (kirrSpan ε A u).comap (A a b) := Submodule.span_le.2 (by
    rintro _ ⟨l, hl, rfl⟩
    exact Submodule.subset_span ⟨(a, b) :: l, fun p hp => by
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hba, hab⟩
      · exact hl p hp, rfl⟩)
  exact h hx

theorem kirr_compact_word (hA : IsGlRep A) {ν : Fin n → ℝ} {u : X} (hu : IsKHWVec ε A ν u) :
    ∀ l, KirrLow ε l → ∀ a b, ε a = ε b → A a b (kirrWord A u l) ∈ kirrSpan ε A u := by
  intro l
  induction l with
  | nil =>
    intro _ a b hab
    rcases lt_trichotomy a b with h | rfl | h
    · show A a b u ∈ _
      rw [hu.2 a b h hab]; exact Submodule.zero_mem _
    · show A a a u ∈ _
      rw [hu.1 a]
      exact Submodule.smul_mem _ _ (kirrWord_mem (l := []) u (fun p hp => by simp at hp))
    · exact kirrWord_mem (l := [(a, b)]) u (fun p hp => by
        rw [List.mem_singleton] at hp; subst hp; exact ⟨h, hab⟩)
  | cons p l ih =>
    intro hl a b hab
    obtain ⟨x, y⟩ := p
    have hl' : KirrLow ε l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hxy : y < x ∧ ε x = ε y := hl (x, y) (by simp)
    have hw := ih hl'
    show A a b (A x y (kirrWord A u l)) ∈ _
    rw [glRep_apply_commutator hA]
    refine Submodule.add_mem _ (kirr_low_mem hxy.1 hxy.2 (hw a b hab)) ?_
    rw [LinearMap.sub_apply]
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs with h
      · subst h; exact hw _ _ (hab.trans hxy.2)
      · rw [LinearMap.zero_apply]; exact Submodule.zero_mem _
    · split_ifs with h
      · subst h; exact hw _ _ (hxy.2.trans hab)
      · rw [LinearMap.zero_apply]; exact Submodule.zero_mem _

theorem kirrSpan_kStable (hA : IsGlRep A) {ν : Fin n → ℝ} {u : X} (hu : IsKHWVec ε A ν u) :
    IsKStableSub ε A (kirrSpan ε A u) := by
  intro a b hab v hv
  have h : kirrSpan ε A u ≤ (kirrSpan ε A u).comap (A a b) := Submodule.span_le.2 (by
    rintro _ ⟨l, hl, rfl⟩
    exact kirr_compact_word hA hu l hl a b hab)
  exact h hv

theorem kirrSpan_le (hV : IsKStableSub ε A V) {u : X} (hu : u ∈ V) : kirrSpan ε A u ≤ V := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨l, hl, rfl⟩
  induction l with
  | nil => exact hu
  | cons p l ih =>
    exact hV p.1 p.2 (hl p (by simp)).2 _ (ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)))

theorem kirrPs_wt (k : ℕ) (ν : Fin n → ℝ) :
    ∀ l, KirrLow ε l → kirrPs k (kirrWt ν l) ≤ kirrPs k ν
  | [], _ => le_rfl
  | p :: l, hl => by
    have ih := kirrPs_wt k ν l fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p List.mem_cons_self
    have hr : kirrPs k (root p.1 p.2) ≤ 0 := by
      unfold kirrPs root
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.mem_filter,
        Finset.mem_univ, true_and]
      have h3 : (p.2 : ℕ) < p.1 := hp.1
      split_ifs with h1 h2 <;> first | (exfalso; omega) | norm_num
    have hadd : kirrPs k (kirrWt ν (p :: l)) = kirrPs k (kirrWt ν l) + kirrPs k (root p.1 p.2) := by
      simp [kirrPs, kirrWt, Finset.sum_add_distrib]
    linarith

theorem kirrH_apply (k : ℕ) {μ : Fin n → ℝ} {x : X} (hx : ∀ a, A a a x = (μ a : ℂ) • x) :
    kirrH A k x = (kirrPs k μ : ℂ) • x := by
  rw [kirrH, LinearMap.sum_apply]
  simp only [hx, kirrPs, Complex.ofReal_sum, Finset.sum_smul]

theorem kirrPs_le (hA : IsGlRep A) (hV : IsKIrrHW ε A Λ V) {u : X} (hu : u ∈ V) (hu0 : u ≠ 0)
    {ν : Fin n → ℝ} (hν : IsKHWVec ε A ν u) {w : X} (hw : w ∈ V) (hw0 : w ≠ 0) {μ : Fin n → ℝ}
    (hμ : ∀ a, A a a w = (μ a : ℂ) • w) (k : ℕ) : kirrPs k μ ≤ kirrPs k ν := by
  classical
  obtain ⟨-, hVs, hirr, -⟩ := id hV
  have hspan : kirrSpan ε A u = V := by
    rcases hirr _ (kirrSpan_le hVs hu) (kirrSpan_kStable hA hν) with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ kirrWord_mem (l := []) u (fun p hp => by simp at hp))) hu0
    · exact h
  have hle : kirrSpan ε A u ≤
      ⨆ z ∈ {z : ℂ | ∃ r : ℝ, r ≤ kirrPs k ν ∧ z = r}, Module.End.eigenspace (kirrH A k) z :=
    Submodule.span_le.2 (by
      rintro _ ⟨l, hl, rfl⟩
      refine Submodule.mem_iSup_of_mem ((kirrPs k (kirrWt ν l) : ℝ) : ℂ)
        (Submodule.mem_iSup_of_mem (Set.mem_setOf.2 ⟨_, kirrPs_wt k ν l hl, rfl⟩) ?_)
      rw [Module.End.mem_eigenspace_iff]
      exact kirrH_apply k (kirrWord_wt hA hν.1 l))
  have hwS := hle (by rw [hspan]; exact hw)
  by_contra hlt
  push_neg at hlt
  have hwE : w ∈ Module.End.eigenspace (kirrH A k) ((kirrPs k μ : ℝ) : ℂ) := by
    rw [Module.End.mem_eigenspace_iff]; exact kirrH_apply k hμ
  have hx : ((kirrPs k μ : ℝ) : ℂ) ∉ {z : ℂ | ∃ r : ℝ, r ≤ kirrPs k ν ∧ z = r} := by
    rintro ⟨r, hr, he⟩
    have := Complex.ofReal_injective he
    linarith
  have hd : Disjoint (Module.End.eigenspace (kirrH A k) ((kirrPs k μ : ℝ) : ℂ))
      (⨆ z ∈ {z : ℂ | ∃ r : ℝ, r ≤ kirrPs k ν ∧ z = r}, Module.End.eigenspace (kirrH A k) z) := by
    first
      | exact (Module.End.eigenspaces_iSupIndep (kirrH A k)).disjoint_biSup hx
      | exact (Module.End.eigenspaces_independent (kirrH A k)).disjoint_biSup hx
  exact hw0 (Submodule.disjoint_def.1 hd w hwE hwS)

private theorem kirrPs_succ (μ : Fin n → ℝ) (a : Fin n) : kirrPs (a.val + 1) μ = kirrPs a.val μ + μ a := by
  simp only [kirrPs]
  rw [show univ.filter (fun b : Fin n => b.val < a.val + 1) = insert a (univ.filter (fun b : Fin n => b.val < a.val)) by
    ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]; omega]
  rw [Finset.sum_insert (by simp), add_comm]

theorem kirr_eq_of_ps {μ ν : Fin n → ℝ} (h : ∀ k, kirrPs k μ = kirrPs k ν) : μ = ν := by
  funext a
  have h1 := h (a.val + 1)
  rw [kirrPs_succ, kirrPs_succ, h a.val] at h1
  linarith

theorem khw_weight_eq_of_irr (hA : IsGlRep A) (hV : IsKIrrHW ε A Λ V) {u : X} (hu : u ∈ V)
    (hu0 : u ≠ 0) {ν : Fin n → ℝ} (hν : IsKHWVec ε A ν u) : ν = Λ := by
  obtain ⟨-, -, -, w, hw, hw0, hwΛ⟩ := id hV
  exact kirr_eq_of_ps fun k =>
    le_antisymm (kirrPs_le hA hV hw hw0 hwΛ hu hu0 hν.1 k) (kirrPs_le hA hV hu hu0 hν hw hw0 hwΛ.1 k)

theorem casimirK_irr (hA : IsGlRep A) (hV : IsKIrrHW ε A Λ V) :
    ∀ v ∈ V, casimirK ε A v = (casValK ε Λ : ℂ) • v := by
  obtain ⟨-, hst, hirr, w, hwV, hw0, hwK⟩ := hV
  let S : Submodule ℂ X := V ⊓ (casimirK ε A).eigenspace (casValK ε Λ : ℂ)
  have hS : IsKStableSub ε A S := by
    intro a b hab v hv
    have hv2 := Module.End.mem_eigenspace_iff.1 hv.2
    refine ⟨hst a b hab v hv.1, Module.End.mem_eigenspace_iff.2 ?_⟩
    have := LinearMap.congr_fun (casimirK_comm ε hA a b hab) v
    simp only [Module.End.mul_apply] at this
    rw [this, hv2, map_smul]
  rcases hirr S inf_le_left hS with h | h
  · exfalso
    have hwS : w ∈ S := ⟨hwV, Module.End.mem_eigenspace_iff.2 (casimirK_khwVec ε hA hwK)⟩
    rw [h] at hwS
    exact hw0 ((Submodule.mem_bot ℂ).1 hwS)
  · intro v hv
    rw [← h] at hv
    exact Module.End.mem_eigenspace_iff.1 hv.2

end KIrr

end ReciprocityTheory.ChartRestriction.DS
