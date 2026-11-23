import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import Lemmata.SmulListSum.SmulListSum

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Core

variable {n : ℕ} {U : Type*} [AddCommGroup U] [Module ℂ U]

theorem vc_le_genSub (T : Fin n → Fin n → Module.End ℂ U) (S : Submodule ℂ U) : S ≤ genSub T S := by
  unfold genSub
  exact le_sInf fun X hX => hX.1

theorem vc_genSub_stable (T : Fin n → Fin n → Module.End ℂ U) (S : Submodule ℂ U) (a b : Fin n) {v : U}
    (hv : v ∈ genSub T S) : T a b v ∈ genSub T S := by
  unfold genSub at hv ⊢
  rw [Submodule.mem_sInf] at hv ⊢
  intro X hX
  exact hX.2 a b v (hv X hX)

theorem vc_genSub_le (T : Fin n → Fin n → Module.End ℂ U) (S X : Submodule ℂ U) (hSX : S ≤ X)
    (hX : ∀ a b, ∀ v ∈ X, T a b v ∈ X) : genSub T S ≤ X := by
  unfold genSub
  exact sInf_le ⟨hSX, hX⟩

def vcGood (T : Fin n → Fin n → Module.End ℂ U) (P : (Fin n → ℝ) → Prop) : Set U :=
  {w | ∃ ν, P ν ∧ ∀ a, T a a w = ((ν a : ℝ) : ℂ) • w}

theorem vcGood_smul (T : Fin n → Fin n → Module.End ℂ U) (P : (Fin n → ℝ) → Prop) {w : U}
    (hw : w ∈ vcGood T P) (c : ℂ) : c • w ∈ vcGood T P := by
  simp only [vcGood, Set.mem_setOf_eq] at hw ⊢
  obtain ⟨ν, hP, hν⟩ := hw
  refine ⟨ν, hP, fun a => ?_⟩
  rw [map_smul, hν a, smul_comm]

theorem vc_exists_list {G : Set U} (hs : ∀ w ∈ G, ∀ c : ℂ, c • w ∈ G) {y : U}
    (hy : y ∈ Submodule.span ℂ G) : ∃ l : List U, (∀ w ∈ l, w ∈ G) ∧ y = l.sum := by
  first | exact Bl.SmulListSum.goal1 .. | (apply Bl.SmulListSum.goal1 <;> assumption) | (intros; apply Bl.SmulListSum.goal1 <;> assumption)

theorem vc_eq_zero_of_list (T : Fin n → Fin n → Module.End ℂ U) (P : (Fin n → ℝ) → Prop)
    {μ : Fin n → ℝ} (hμ : ¬ P μ) :
    ∀ (N : ℕ) (l : List U), l.length = N → (∀ w ∈ l, w ∈ vcGood T P) → ∀ x : U,
      (∀ a, T a a x = ((μ a : ℝ) : ℂ) • x) → x = l.sum → x = 0 := by
  intro N
  induction N with
  | zero =>
    intro l hl _ x _ hxl
    cases l with
    | nil => simpa using hxl
    | cons w l' => simp at hl
  | succ N ih =>
    intro l hl hg x hx hxl
    cases l with
    | nil => simp at hl
    | cons w l' =>
      have hl' : l'.length = N := by simpa using hl
      have hw0 := hg w (by simp)
      simp only [vcGood, Set.mem_setOf_eq] at hw0
      obtain ⟨ν, hPν, hν⟩ := hw0
      have hne : ν ≠ μ := fun h => hμ (h ▸ hPν)
      obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
      have hc0 : ((μ a : ℝ) : ℂ) - ((ν a : ℝ) : ℂ) ≠ 0 :=
        sub_ne_zero.mpr (by exact_mod_cast ha.symm)
      obtain ⟨D, hD⟩ : ∃ D : Module.End ℂ U, ∀ u, D u = T a a u - ((ν a : ℝ) : ℂ) • u :=
        ⟨T a a - ((ν a : ℝ) : ℂ) • 1, fun u => by simp⟩
      have h1 : D x = (((μ a : ℝ) : ℂ) - ((ν a : ℝ) : ℂ)) • x := by
        rw [hD, hx a, sub_smul]
      have h2 : D w = 0 := by rw [hD, hν a, sub_self]
      have h3 : D x = (l'.map D).sum := by
        rw [hxl, List.sum_cons, map_add, h2, zero_add, map_list_sum]
      have hgood : ∀ u ∈ l'.map D, u ∈ vcGood T P := by
        intro u hu
        obtain ⟨u0, hu0, rfl⟩ := List.mem_map.mp hu
        have hg0 := hg u0 (by simp [hu0])
        simp only [vcGood, Set.mem_setOf_eq] at hg0 ⊢
        obtain ⟨ν', hP', hν'⟩ := hg0
        refine ⟨ν', hP', fun b => ?_⟩
        rw [hD, hν' a, ← sub_smul, map_smul, hν' b, smul_comm]
      have hwt : ∀ b, T b b ((((μ a : ℝ) : ℂ) - ((ν a : ℝ) : ℂ)) • x)
          = ((μ b : ℝ) : ℂ) • ((((μ a : ℝ) : ℂ) - ((ν a : ℝ) : ℂ)) • x) := by
        intro b
        rw [map_smul, hx b, smul_comm]
      have hz := ih (l'.map D) (by simpa using hl') hgood _ hwt (by rw [← h1, h3])
      exact (smul_eq_zero.mp hz).resolve_left hc0

theorem vc_eq_zero_of_mem_span (T : Fin n → Fin n → Module.End ℂ U) (P : (Fin n → ℝ) → Prop)
    {μ : Fin n → ℝ} (hμ : ¬ P μ) {x : U} (hx : ∀ a, T a a x = ((μ a : ℝ) : ℂ) • x)
    (hxs : x ∈ Submodule.span ℂ (vcGood T P)) : x = 0 := by
  obtain ⟨l, hl, e⟩ := vc_exists_list (fun w hw c => vcGood_smul T P hw c) hxs
  exact vc_eq_zero_of_list T P hμ l.length l rfl hl x hx e

def vcMon (T : Fin n → Fin n → Module.End ℂ U) (v : U) : ℕ → Set U
  | 0 => {v}
  | k + 1 => {y | ∃ a b, a < b ∧ ∃ x ∈ vcMon T v k, y = T a b x}

def vcMonAll (T : Fin n → Fin n → Module.End ℂ U) (v : U) : Set U := ⋃ k, vcMon T v k

def vcHt (β : Fin n → ℝ) : ℝ := ∑ a : Fin n, -((a : ℕ) : ℝ) * β a

theorem vcHt_add (β γ : Fin n → ℝ) : vcHt (β + γ) = vcHt β + vcHt γ := by
  simp only [vcHt, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem vcHt_zero : vcHt (0 : Fin n → ℝ) = 0 := by
  simp [vcHt]

theorem vcHt_root {c d : Fin n} (h : c < d) : 1 ≤ vcHt (root c d) := by
  have h1 : ∀ e : Fin n, ∑ a : Fin n, -((a : ℕ) : ℝ) * (Pi.single e (1 : ℝ) : Fin n → ℝ) a
      = -((e : ℕ) : ℝ) := by
    intro e
    rw [Fintype.sum_eq_single e (fun a ha => by simp [Pi.single_apply, ha])]
    simp
  have key : vcHt (root c d) = ((d : ℕ) : ℝ) - ((c : ℕ) : ℝ) := by
    simp only [vcHt, root, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, h1]
    ring
  rw [key]
  have h' : (c : ℕ) + 1 ≤ (d : ℕ) := h
  have h'' : ((c : ℕ) : ℝ) + 1 ≤ ((d : ℕ) : ℝ) := by exact_mod_cast h'
  linarith

theorem vc_inRootCone_zero' : InRootCone (0 : Fin n → ℝ) := by
  unfold InRootCone
  exact ⟨fun _ _ => 0, by simp⟩

theorem vc_inRootCone_add_root {β : Fin n → ℝ} (hβ : InRootCone β) {c d : Fin n} (h : c < d) :
    InRootCone (β + root c d) := by
  unfold InRootCone at hβ ⊢
  obtain ⟨m, hm⟩ := hβ
  refine ⟨fun a b => m a b + if a = c ∧ b = d then 1 else 0, ?_⟩
  have hsplit : ∀ a b : Fin n,
      (if a < b then (((m a b + if a = c ∧ b = d then 1 else 0 : ℕ)) : ℝ) • root a b else 0)
        = (if a < b then (m a b : ℝ) • root a b else 0)
          + (if a = c ∧ b = d then root c d else 0) := by
    intro a b
    by_cases hab : a = c ∧ b = d
    · obtain ⟨rfl, rfl⟩ := hab
      simp [h, add_smul]
    · rw [if_neg hab, if_neg hab]
      simp
  have hind : (∑ a : Fin n, ∑ b : Fin n, (if a = c ∧ b = d then root c d else 0)) = root c d := by
    rw [Finset.sum_eq_single c (fun a _ ha => by simp [ha]) (by simp)]
    rw [Finset.sum_eq_single d (fun b _ hb => by simp [hb]) (by simp)]
    simp
  rw [hm]
  simp only [hsplit, Finset.sum_add_distrib, hind]

theorem vcMon_weight (T : Fin n → Fin n → Module.End ℂ U) (hT : IsGlRep T) {v : U}
    {base : Fin n → ℝ} (hv : ∀ a, T a a v = ((base a : ℝ) : ℂ) • v) :
    ∀ k, ∀ w ∈ vcMon T v k, ∃ ν : Fin n → ℝ, (∀ a, T a a w = ((ν a : ℝ) : ℂ) • w) ∧
      InRootCone (ν - base) ∧ (k : ℝ) ≤ vcHt (ν - base) := by
  have hz : ∀ w, w ∈ vcMon T v 0 → w = v := fun w hw => hw
  have hs : ∀ k w, w ∈ vcMon T v (k + 1) → ∃ a b, a < b ∧ ∃ x ∈ vcMon T v k, w = T a b x :=
    fun k w hw => hw
  intro k
  induction k with
  | zero =>
    intro w hw
    rw [hz w hw]
    refine ⟨base, hv, ?_, ?_⟩
    · rw [sub_self]
      exact vc_inRootCone_zero'
    · rw [sub_self, vcHt_zero]
      simp
  | succ k ih =>
    intro w hw
    obtain ⟨a, b, hab', x, hx, rfl⟩ := hs k w hw
    obtain ⟨ν, hxν, hcone, hht⟩ := ih x hx
    have hab : a ≠ b := ne_of_lt hab'
    have hw : ∀ c, T c c (T a b x) = (((ν + root a b) c : ℝ) : ℂ) • T a b x := by
      intro c
      have hc := LinearMap.congr_fun (hT c c a b) x
      have e : (T c c * T a b - T a b * T c c) x = T c c (T a b x) - T a b (T c c x) := by
        first
          | rfl
          | simp [LinearMap.sub_apply, Module.End.mul_apply]
          | simp [LinearMap.sub_apply, LinearMap.mul_apply]
      rw [e, hxν c, map_smul] at hc
      simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
      by_cases h1 : c = a
      · have h2 : ¬ b = c := by
          rw [h1]
          exact fun h => hab h.symm
        rw [if_pos h1, if_neg h2, sub_zero] at hc
        rw [h1] at hc ⊢
        rw [if_pos rfl, if_neg hab, sub_zero, Complex.ofReal_add, Complex.ofReal_one, add_smul,
          one_smul]
        rw [sub_eq_iff_eq_add] at hc
        rw [hc, add_comm]
      · by_cases h3 : c = b
        · have h2 : b = c := h3.symm
          rw [if_neg h1, if_pos h2, zero_sub] at hc
          rw [h3] at hc ⊢
          rw [if_neg (Ne.symm hab), if_pos rfl, zero_sub, ← sub_eq_add_neg, Complex.ofReal_sub,
            Complex.ofReal_one, sub_smul, one_smul]
          rw [LinearMap.neg_apply, sub_eq_iff_eq_add] at hc
          rw [hc, neg_add_eq_sub]
        · have h2 : ¬ b = c := fun h => h3 h.symm
          rw [if_neg h1, if_neg h2, sub_zero, LinearMap.zero_apply, sub_eq_zero] at hc
          rw [if_neg h1, if_neg h3, sub_zero, add_zero, hc]
    have e : ν + root a b - base = (ν - base) + root a b := by abel
    refine ⟨ν + root a b, hw, ?_, ?_⟩
    · rw [e]
      exact vc_inRootCone_add_root hcone hab'
    · rw [e, vcHt_add]
      have := vcHt_root hab'
      push_cast
      linarith

theorem vc_sup_stable {G : Set U} {F : Submodule ℂ U} (X : Module.End ℂ U)
    (hG : ∀ w ∈ G, X w ∈ Submodule.span ℂ G ⊔ F) (hF : ∀ x ∈ F, X x ∈ F) :
    ∀ x ∈ Submodule.span ℂ G ⊔ F, X x ∈ Submodule.span ℂ G ⊔ F := by
  intro x hx
  have h : Submodule.span ℂ G ⊔ F ≤ (Submodule.span ℂ G ⊔ F).comap X := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      intro w hw
      exact hG w hw
    · intro y hy
      exact Submodule.mem_sup_right (hF y hy)
  exact h hx

theorem vc_genSub_le_mon (T : Fin n → Fin n → Module.End ℂ U) (hT : IsGlRep T) (v : U)
    (F : Submodule ℂ U) (hF : ∀ a b, ∀ x ∈ F, T a b x ∈ F) (hlow : ∀ a b, b < a → T a b v ∈ F)
    (hdiag : ∀ a, ∃ c : ℂ, T a a v = c • v) :
    genSub T (Submodule.span ℂ {v}) ≤ Submodule.span ℂ (vcMonAll T v) ⊔ F := by
  have hz : ∀ w, w ∈ vcMon T v 0 → w = v := fun w hw => hw
  have hv0 : v ∈ vcMon T v 0 := by
    show v ∈ ({v} : Set U)
    exact Set.mem_singleton v
  have hs : ∀ k w, w ∈ vcMon T v (k + 1) → ∃ a b, a < b ∧ ∃ x ∈ vcMon T v k, w = T a b x :=
    fun k w hw => hw
  have hn : ∀ k a b, a < b → ∀ x ∈ vcMon T v k, T a b x ∈ vcMon T v (k + 1) := by
    intro k a b hab x hx
    show ∃ a' b', a' < b' ∧ ∃ y ∈ vcMon T v k, T a b x = T a' b' y
    exact ⟨a, b, hab, x, hx, rfl⟩
  have hmon : ∀ k, ∀ w ∈ vcMon T v k, w ∈ Submodule.span ℂ (vcMonAll T v) ⊔ F := by
    intro k w hw
    refine Submodule.mem_sup_left (Submodule.subset_span ?_)
    show w ∈ ⋃ k, vcMon T v k
    exact Set.mem_iUnion.mpr ⟨k, hw⟩
  have hup : ∀ c d, c < d → ∀ y ∈ Submodule.span ℂ (vcMonAll T v) ⊔ F,
      T c d y ∈ Submodule.span ℂ (vcMonAll T v) ⊔ F := by
    intro c d hcd
    refine vc_sup_stable (T c d) ?_ (hF c d)
    intro w hw
    obtain ⟨k, hk⟩ : ∃ k, w ∈ vcMon T v k := by simpa [vcMonAll] using hw
    exact hmon (k + 1) _ (hn k c d hcd w hk)
  have hstab : ∀ k, ∀ a b, ∀ w ∈ vcMon T v k,
      T a b w ∈ Submodule.span ℂ (vcMonAll T v) ⊔ F := by
    intro k
    induction k with
    | zero =>
      intro a b w hw
      rw [hz w hw]
      rcases lt_trichotomy a b with h | h | h
      · exact hmon 1 _ (hn 0 a b h v hv0)
      · rw [h]
        obtain ⟨c, hc⟩ := hdiag b
        rw [hc]
        exact Submodule.smul_mem _ c (hmon 0 v hv0)
      · exact Submodule.mem_sup_right (hlow a b h)
    | succ k ih =>
      intro a b w hw
      obtain ⟨c, d, hcd, x, hx, rfl⟩ := hs k w hw
      have hc := LinearMap.congr_fun (hT a b c d) x
      have e : (T a b * T c d - T c d * T a b) x = T a b (T c d x) - T c d (T a b x) := by
        first
          | rfl
          | simp [LinearMap.sub_apply, Module.End.mul_apply]
          | simp [LinearMap.sub_apply, LinearMap.mul_apply]
      rw [e, sub_eq_iff_eq_add] at hc
      rw [hc]
      refine Submodule.add_mem _ ?_ (hup c d hcd _ (ih a b x hx))
      rw [LinearMap.sub_apply]
      refine Submodule.sub_mem _ ?_ ?_
      · split_ifs
        · exact ih a d x hx
        · rw [LinearMap.zero_apply]
          exact Submodule.zero_mem _
      · split_ifs
        · exact ih c b x hx
        · rw [LinearMap.zero_apply]
          exact Submodule.zero_mem _
  refine vc_genSub_le T (Submodule.span ℂ {v}) _ ?_ ?_
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hmon 0 v hv0
  · intro a b y hy
    refine vc_sup_stable (T a b) ?_ (hF a b) y hy
    intro w hw
    obtain ⟨k, hk⟩ : ∃ k, w ∈ vcMon T v k := by simpa [vcMonAll] using hw
    exact hstab k a b w hk

def vcIter (A : Module.End ℂ U) (θ : ℕ → ℂ) (k0 : ℕ) : ℕ → Module.End ℂ U
  | 0 => 1
  | i + 1 => (A - θ (k0 + i) • 1) * vcIter A θ k0 i

theorem vcIter_maps (A : Module.End ℂ U) (θ : ℕ → ℂ) (F : ℕ → Submodule ℂ U)
    (hstep : ∀ k, ∀ x ∈ F k, A x - θ k • x ∈ F (k + 1)) (k0 : ℕ) :
    ∀ i, ∀ x ∈ F k0, vcIter A θ k0 i x ∈ F (k0 + i)
  | 0, x, hx => by simpa [vcIter] using hx
  | i + 1, x, hx => by
    have h := hstep (k0 + i) _ (vcIter_maps A θ F hstep k0 i x hx)
    simpa [vcIter, Module.End.mul_apply, LinearMap.sub_apply, add_assoc] using h

theorem vcIter_eig (A : Module.End ℂ U) (θ : ℕ → ℂ) (k0 : ℕ) {x : U} {t : ℂ} (hx : A x = t • x) :
    ∀ i, vcIter A θ k0 i x = (∏ i' ∈ range i, (t - θ (k0 + i'))) • x
  | 0 => by simp [vcIter]
  | i + 1 => by
    rw [vcIter, Module.End.mul_apply, vcIter_eig A θ k0 hx i, Finset.prod_range_succ]
    simp only [map_smul, LinearMap.sub_apply, hx, LinearMap.smul_apply, Module.End.one_apply]
    rw [← sub_smul, smul_smul, mul_comm]

theorem vcIter_comm (A : Module.End ℂ U) (θ : ℕ → ℂ) (k0 : ℕ) {X : Module.End ℂ U} (hX : Commute A X) :
    ∀ i, Commute (vcIter A θ k0 i) X
  | 0 => Commute.one_left X
  | i + 1 => ((hX.sub_left ((Commute.one_left X).smul_left _)).mul_left (vcIter_comm A θ k0 hX i))

end Core

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
