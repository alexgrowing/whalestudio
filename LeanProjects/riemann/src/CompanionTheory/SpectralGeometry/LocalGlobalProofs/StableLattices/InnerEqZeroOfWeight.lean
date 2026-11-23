import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.EqSmulOfWeight

open scoped InnerProductSpace
open Formalism.REAL (KHighest IsWeight)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open CompanionTheory.D.gk.HwAlg (word word_nil word_cons)

noncomputable section

namespace GlobalTheory.CompanionTheory.KLowSpan

variable {n : ℕ} {ε : Fin n → Bool}

def KLower (ε : Fin n → Bool) (l : List (Fin n × Fin n)) : Prop := ∀ p ∈ l, p.2 < p.1 ∧ ε p.1 = ε p.2

section Alg

variable {U : Type} [AddCommGroup U] [Module ℂ U]

def kLowSpan (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ U) (w : U) : Submodule ℂ U :=
  Submodule.span ℂ {x | ∃ l, KLower ε l ∧ x = word F l w}

variable {F : Fin n → Fin n → Module.End ℂ U} {μ : Fin n → ℝ} {w : U}

lemma kword_mem {l : List (Fin n × Fin n)} (hl : KLower ε l) : word F l w ∈ kLowSpan ε F w := by
  exact Submodule.subset_span ⟨l, hl, rfl⟩

lemma kself_mem : w ∈ kLowSpan ε F w := by
  have h := kword_mem (ε := ε) (F := F) (w := w) (l := []) (fun p hp => by simp at hp)
  simpa using h

lemma klower_mem {a b : Fin n} (hab : b < a) (he : ε a = ε b) {x : U}
    (hx : x ∈ kLowSpan ε F w) : F a b x ∈ kLowSpan ε F w := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    have hl' : KLower ε ((a, b) :: l) := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hab, he⟩
      · exact hl p hp
    have h := kword_mem (F := F) (w := w) hl'
    simpa [word_cons] using h
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

lemma kcomm_apply (hF : KRel ε F) {i j a b : Fin n} (hij : ε i = ε j) (hab : ε a = ε b) (u : U) :
    F i j (F a b u) = F a b (F i j u) +
      ((if j = a then F i b u else 0) - (if b = i then F a j u else 0)) := by
  have h := congrArg (fun T : Module.End ℂ U => T u) (hF i j a b hij hab)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  split_ifs at h ⊢ <;> simp_all [sub_eq_iff_eq_add, add_comm]

lemma kgen_mem (hF : KRel ε F) (hw : KHighest ε F μ w) :
    ∀ (l : List (Fin n × Fin n)), KLower ε l → ∀ i j, ε i = ε j → F i j (word F l w) ∈ kLowSpan ε F w := by
  intro l
  induction l with
  | nil =>
    intro _ i j he
    simp only [word_nil, Module.End.one_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [hw.2 i j h he]; exact Submodule.zero_mem _
    · rw [hw.1 i]; exact Submodule.smul_mem _ _ kself_mem
    · exact klower_mem h he kself_mem
  | cons p l ih =>
    intro hl i j he
    have hl' : KLower ε l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p (by simp)
    rw [word_cons, Module.End.mul_apply, kcomm_apply hF he hp.2]
    refine Submodule.add_mem _ (klower_mem hp.1 hp.2 (ih hl' i j he)) (Submodule.sub_mem _ ?_ ?_)
    · split_ifs with h
      · exact ih hl' _ _ (by rw [he, h, hp.2])
      · exact Submodule.zero_mem _
    · split_ifs with h
      · exact ih hl' _ _ (by rw [hp.2, h, he])
      · exact Submodule.zero_mem _

theorem kstab_kLowSpan (hF : KRel ε F) (hw : KHighest ε F μ w) : KStab ε F (kLowSpan ε F w) := by
  intro i j he x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact kgen_mem hF hw l hl i j he
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem kLowSpan_le {S : Submodule ℂ U} (hS : KStab ε F S) (hw : w ∈ S) : kLowSpan ε F w ≤ S := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨l, hl, rfl⟩
  induction l with
  | nil => simpa using hw
  | cons p l ih =>
    rw [word_cons, Module.End.mul_apply]
    exact hS _ _ (hl p (by simp)).2 _ (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))

def kwt (μ : Fin n → ℝ) (l : List (Fin n × Fin n)) : Fin n → ℝ :=
  μ + (l.map fun p => (Pi.single p.1 1 - Pi.single p.2 1 : Fin n → ℝ)).sum

lemma kwt_nil (μ : Fin n → ℝ) : kwt μ [] = μ := by simp [kwt]

lemma kwt_cons (μ : Fin n → ℝ) (p : Fin n × Fin n) (l : List (Fin n × Fin n)) :
    kwt μ (p :: l) = kwt μ l + (Pi.single p.1 1 - Pi.single p.2 1) := by
  simp only [kwt, List.map_cons, List.sum_cons]
  abel

lemma isWeight_word (hF : KRel ε F) (hw : IsWeight F μ w) :
    ∀ (l : List (Fin n × Fin n)), KLower ε l → IsWeight F (kwt μ l) (word F l w) := by
  intro l
  induction l with
  | nil => intro _ c; simpa [kwt_nil] using hw c
  | cons p l ih =>
    intro hl c
    have hl' : KLower ε l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p (by simp)
    rw [word_cons, Module.End.mul_apply, kcomm_apply hF rfl hp.2, ih hl' c, map_smul]
    simp only [kwt_cons, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    by_cases h1 : c = p.1 <;> by_cases h2 : p.2 = c
    · subst h1; rw [h2] at *; simp
    · subst h1; simp [h2, Ne.symm h2, add_smul]
    · subst h2; simp [h1, add_smul, sub_eq_add_neg]
    · simp [h1, h2, Ne.symm h2]

lemma hgt_kwt (μ : Fin n → ℝ) :
    ∀ l : List (Fin n × Fin n), KLower ε l →
      ∑ c : Fin n, ((c : ℕ) : ℝ) * μ c + l.length ≤ ∑ c : Fin n, ((c : ℕ) : ℝ) * kwt μ l c := by
  intro l
  induction l with
  | nil => intro _; simp [kwt_nil]
  | cons p l ih =>
    intro hl
    have hp := (hl p (List.mem_cons_self ..)).1
    have ih' := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    have key : ∑ c : Fin n, ((c : ℕ) : ℝ) * kwt μ (p :: l) c =
        ∑ c : Fin n, ((c : ℕ) : ℝ) * kwt μ l c + (((p.1 : ℕ) : ℝ) - ((p.2 : ℕ) : ℝ)) := by
      rw [kwt_cons]
      simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp [Pi.single_apply]
    have h1 : (1 : ℝ) ≤ ((p.1 : ℕ) : ℝ) - ((p.2 : ℕ) : ℝ) := by
      have h2 : (p.2 : ℕ) + 1 ≤ (p.1 : ℕ) := Fin.lt_def.mp hp
      have h3 : ((p.2 : ℕ) : ℝ) + 1 ≤ ((p.1 : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    rw [key, List.length_cons]
    push_cast
    linarith

lemma cdom_kwt (μ : Fin n → ℝ) :
    ∀ l : List (Fin n × Fin n), KLower ε l → PI.UpqRep.CDom ε (kwt μ l) μ := by
  intro l
  induction l with
  | nil => intro; exact ⟨0, by simp, by simp [kwt_nil]⟩
  | cons p l ih =>
    intro hl
    have hl' : KLower ε l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p (by simp)
    obtain ⟨c, hc, hs⟩ := ih hl'
    refine ⟨fun a b => c a b + if b = p.1 then (if a = p.2 then 1 else 0) else 0, ?_, ?_⟩
    · intro a b h
      by_cases h0 : c a b = 0
      · simp only [h0, zero_add] at h
        split_ifs at h with h1 h2
        · subst h1 h2; exact ⟨hp.1, hp.2.symm⟩
        · exact absurd rfl h
        · exact absurd rfl h
      · exact hc a b h0
    · simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib, ← hs, Nat.cast_ite, ite_smul,
        Nat.cast_zero, Nat.cast_one, zero_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, kwt_cons]
      simp only [PI.UpqRep.root]
      abel

end Alg

section Unit

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V} {μ : Fin n → ℝ} {v : V}

lemma inner_eq_zero_of_weight (hU : KUnit ε E) {ν ν' : Fin n → ℝ} {x y : V} (hx : IsWeight E ν x)
    (hy : IsWeight E ν' y) (hne : ν ≠ ν') : ⟪x, y⟫_ℂ = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
  have h := hU a a rfl x y
  rw [hx a, hy a, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have h2 : ((ν a : ℂ) - ν' a) * ⟪x, y⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (by exact_mod_cast sub_eq_zero.1 h3) ha
  · exact h3

lemma eq_zero_of_orth {x : V} (hx : x ∈ kLowSpan ε E v)
    (h : ∀ l, KLower ε l → ⟪word E l v, x⟫_ℂ = 0) : x = 0 := by
  have key : ∀ y ∈ kLowSpan ε E v, ⟪y, x⟫_ℂ = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      exact h l hl
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
    | smul c y _ hy => rw [inner_smul_left, hy, mul_zero]
  exact inner_self_eq_zero.1 (key x hx)

lemma cdom_of_weight (hF : KRel ε E) (hU : KUnit ε E) (hv : IsWeight E μ v) {ν : Fin n → ℝ} {x : V}
    (hx : x ∈ kLowSpan ε E v) (hx0 : x ≠ 0) (hν : IsWeight E ν x) : PI.UpqRep.CDom ε ν μ := by
  by_contra hc
  refine hx0 (eq_zero_of_orth hx fun l hl => ?_)
  refine inner_eq_zero_of_weight hU (isWeight_word hF hv l hl) hν ?_
  rintro rfl
  exact hc (cdom_kwt μ l hl)

lemma eq_smul_of_top (hF : KRel ε E) (hU : KUnit ε E) (hv0 : v ≠ 0) (hv : IsWeight E μ v) {x : V}
    (hx : x ∈ kLowSpan ε E v) (hμ : IsWeight E μ x) : ∃ c : ℂ, x = c • v := by
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := fun h => hv0 (inner_self_eq_zero.1 h)
  refine ⟨⟪v, x⟫_ℂ / ⟪v, v⟫_ℂ, sub_eq_zero.1 ?_⟩
  refine eq_zero_of_orth (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ kself_mem)) fun l hl => ?_
  rcases l with _ | ⟨p, l⟩
  · simp only [word_nil, Module.End.one_apply]
    rw [inner_sub_right, inner_smul_right, div_mul_cancel₀ _ hvv, sub_self]
  · refine inner_eq_zero_of_weight (ν' := μ) hU (isWeight_word hF hv _ hl) ?_ ?_
    · intro a
      rw [map_sub, map_smul, hμ a, hv a, smul_sub, smul_comm]
    · intro h
      have := hgt_kwt μ _ hl
      rw [h] at this
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at this
      have h0 : (0 : ℝ) ≤ l.length := Nat.cast_nonneg _
      linarith

lemma kstab_orthogonal (hU : KUnit ε E) {L : Submodule ℂ V} (hL : KStab ε E L) : KStab ε E Lᗮ := by
  intro a b he z hz
  rw [Submodule.mem_orthogonal] at hz ⊢
  intro u hu
  rw [← hU b a he.symm]
  exact hz _ (hL b a he.symm u hu)

end Unit

theorem lowSpan_holds : CompanionTheory.D.DSIC.LowSpan := by
  intro n ε V _ _ E μ v S hF hU hv0 hv hfd hS hvS
  have hle : kLowSpan ε E v ≤ S := kLowSpan_le hS hvS
  refine ⟨kLowSpan ε E v, hle, kself_mem, kstab_kLowSpan hF hv, ?_,
    fun ν x hx hx0 hν => cdom_of_weight hF hU hv.1 hx hx0 hν,
    fun x hx hμ => eq_smul_of_top hF hU hv0 hv.1 hx hμ⟩
  intro L hL hst
  have : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le (hL.trans hle)
  have hst' := kstab_orthogonal hU hst
  have hdis : ∀ u ∈ L, u ∈ Lᗮ → u = 0 := fun u h1 h2 =>
    inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 h2 u h1)
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.exists_add_mem_mem_orthogonal (K := L) v
  have hyw : IsWeight E μ y := by
    intro a
    refine sub_eq_zero.1 (hdis _ (L.sub_mem (hst a a rfl y hy) (L.smul_mem _ hy)) ?_)
    have h := hv.1 a
    rw [hyz, map_add, smul_add] at h
    have : E a a y - (μ a : ℂ) • y = (μ a : ℂ) • z - E a a z := by
      rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    rw [this]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hz) (hst' a a rfl z hz)
  obtain ⟨c, hc⟩ := eq_smul_of_top hF hU hv0 hv.1 (hL hy) hyw
  by_cases h0 : c = 0
  · left
    rw [h0, zero_smul] at hc
    rw [hc, zero_add] at hyz
    have h1 : kLowSpan ε E v ≤ Lᗮ := kLowSpan_le hst' (hyz ▸ hz)
    exact (Submodule.eq_bot_iff _).2 fun u hu => hdis u hu (h1 (hL hu))
  · right
    refine le_antisymm hL (kLowSpan_le hst ?_)
    have : v = c⁻¹ • y := by rw [hc, smul_smul, inv_mul_cancel₀ h0, one_smul]
    rw [this]
    exact L.smul_mem _ hy

end GlobalTheory.CompanionTheory.KLowSpan
