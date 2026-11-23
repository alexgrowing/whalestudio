import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero

noncomputable section

open GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.LocGL.IwahoriFactor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [Fintype n] in

theorem one_same (e : (Σ a, m a) ≃ n) (a : α) (i j : m a) :
    (1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) k) i j := by
  simp [Matrix.one_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] in

theorem one_ne (e : (Σ a, m a) ≃ n) {a b : α} (h : a ≠ b) (i : m a) (j : m b) :
    (1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 :=
  Matrix.one_apply_ne fun e' => h (congrArg Sigma.fst (e.injective e'))

theorem exists_jPlus_mul_KOne (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ u ∈ jPlus k e, ∃ x ∈ KOne k n, g = u * x := by
  obtain ⟨h1, h3⟩ := mem_proRad.1 hg
  obtain ⟨h1, h2⟩ := mem_parahoric.1 h1
  let U : Matrix n n k := Matrix.of fun i j => if blk e i < blk e j then g.val i j else (1 : Matrix n n k) i j
  have hU : StepData.MaxM (U - g.val) := by
    intro i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    simp only [U, Matrix.sub_apply, Matrix.of_apply, blk_apply]
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h]
    · rw [if_neg (lt_irrefl a), one_same, Valuation.map_sub_swap]
      exact h3 a i j
    · rw [if_neg h.not_gt, one_ne e h.ne', zero_sub, Valuation.map_neg]
      exact h2 a b i j h
  obtain ⟨x, hx, hgx⟩ := StepData.exists_mul_KOne h1 hU
  refine ⟨g * x, ⟨mem_unipRad.2 ⟨mem_parab_iff.2 fun a b i j h => ?_, fun a i j => ?_⟩,
    mul_mem h1 (StepData.KOne_le_KO hx)⟩, x⁻¹, inv_mem hx, by simp⟩
  · rw [hgx]
    simp only [U, Matrix.of_apply, blk_apply]
    rw [if_neg h.not_gt, one_ne e h.ne']
  · rw [hgx]
    simp only [U, Matrix.of_apply, blk_apply]
    rw [if_neg (lt_irrefl a), one_same]

theorem exists_KOne_mul_jPlus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ x ∈ KOne k n, ∃ u ∈ jPlus k e, g = x * u := by
  obtain ⟨u, hu, x, hx, rfl⟩ := exists_jPlus_mul_KOne e hg
  exact ⟨u * x * u⁻¹, (Subgroup.mem_normalizer_iff.1 (KO_le_normalizer hu.2) x).1 hx, u, hu, by simp⟩

theorem proRad_eq_sup (e : (Σ a, m a) ≃ n) : proRad k e = KOne k n ⊔ jPlus k e := by
  refine le_antisymm (fun g hg => ?_) (sup_le (KOne_le_proRad e) (jPlus_le_proRad e))
  obtain ⟨x, hx, u, hu, rfl⟩ := exists_KOne_mul_jPlus e hg
  exact Subgroup.mul_mem_sup hx hu

theorem exists_mul_mem_parab (e : (Σ a, m a) ≃ n) {x : GL n k} (hx : x ∈ KOne k n) :
    ∃ c ∈ jMinus k e, x * c ∈ parab k e := by
  have hx' := StepData.mem_KOne.1 hx
  have hA : ∀ a : α, ∃ y ∈ KOne k n, y.val =
      Matrix.of fun i l => if a < blk e i then x.val i l else (1 : Matrix n n k) i l := fun a =>
    StepData.exists_mem_KOne fun i l => by
      simp only [Matrix.sub_apply, Matrix.of_apply]
      split_ifs
      · exact hx' i l
      · simp
  choose y hy hyv using hA
  obtain ⟨c, hc, hcv⟩ := StepData.exists_mem_KOne (M := Matrix.of fun i j => (y (blk e j))⁻¹.val i j)
    fun i j => StepData.mem_KOne.1 (inv_mem (hy (blk e j))) i j
  have key : ∀ i j, ∑ l, (if blk e j < blk e i then x.val i l else (1 : Matrix n n k) i l) * c.val l j =
      (1 : Matrix n n k) i j := fun i j => by
    have := congrFun (congrFun (y (blk e j)).mul_inv i) j
    rw [Matrix.mul_apply, hyv] at this
    rw [hcv]
    exact this
  have h1 : ∀ i j, blk e i ≤ blk e j → c.val i j = (1 : Matrix n n k) i j := fun i j h => by
    have := key i j
    simp only [if_neg h.not_gt] at this
    rwa [← Matrix.mul_apply, Matrix.one_mul] at this
  refine ⟨c, ⟨(mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i j h => ?_, fun a i j => ?_⟩, hc⟩,
    mem_parab_iff.2 fun a b i j h => ?_⟩
  · rw [h1 _ _ (by simpa using h.le), one_ne e h.ne]
  · rw [h1 _ _ (by simp), one_same]
  · have := key (e ⟨a, i⟩) (e ⟨b, j⟩)
    simp only [blk_apply, if_pos h] at this
    rw [Units.val_mul, Matrix.mul_apply, this, one_ne e h.ne']

theorem exists_jLevi_mul_jPlus (e : (Σ a, m a) ≃ n) {p : GL n k} (hp : p ∈ parab k e) (h : p ∈ KOne k n) :
    ∃ d ∈ jLevi k e, ∃ u ∈ jPlus k e, p = d * u := by
  obtain ⟨u, hu, hpu⟩ := exists_levi_mul_unip k e ⟨p, hp⟩
  have hd : leviEmb k e (leviProj k e ⟨p, hp⟩) ∈ jLevi k e :=
    ⟨_, fun a _ => StepData.mem_KOne.2 fun i j => by
      have := StepData.mem_KOne.1 h (e ⟨a, i⟩) (e ⟨a, j⟩)
      rw [Matrix.sub_apply, one_same] at this
      exact this, rfl⟩
  refine ⟨_, hd, u, ⟨hu, ?_⟩, hpu⟩
  rw [(inv_mul_eq_iff_eq_mul.2 hpu).symm]
  exact StepData.KOne_le_KO (mul_mem (inv_mem (jLevi_le_KOne e hd)) h)

theorem conj_mem_jPlus (e : (Σ a, m a) ≃ n) {d u : GL n k} (hd : d ∈ jLevi k e) (hu : u ∈ jPlus k e) :
    d * u * d⁻¹ ∈ jPlus k e := by
  have h := StepData.KOne_le_KO (jLevi_le_KOne e hd)
  obtain ⟨g, -, rfl⟩ := hd
  exact ⟨(Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k e g) u).1 hu.1,
    (KO k n).mul_mem ((KO k n).mul_mem h hu.2) ((KO k n).inv_mem h)⟩

theorem conj_mem_jMinus (e : (Σ a, m a) ≃ n) {d c : GL n k} (hd : d ∈ jLevi k e) (hc : c ∈ jMinus k e) :
    d * c * d⁻¹ ∈ jMinus k e := by
  have h := jLevi_le_KOne e hd
  obtain ⟨g, -, rfl⟩ := hd
  exact ⟨(Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer_lower k e g) c).1 hc.1,
    (KOne k n).mul_mem ((KOne k n).mul_mem h hc.2) ((KOne k n).inv_mem h)⟩

theorem plus_levi_minus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ u ∈ jPlus k e, ∃ d ∈ jLevi k e, ∃ c ∈ jMinus k e, g = u * d * c := by
  obtain ⟨u, hu, x, hx, rfl⟩ := exists_jPlus_mul_KOne e hg
  obtain ⟨c, hc, hp⟩ := exists_mul_mem_parab e hx
  obtain ⟨d, hd, v, hv, h⟩ := exists_jLevi_mul_jPlus e hp (mul_mem hx hc.2)
  refine ⟨_, mul_mem hu (conj_mem_jPlus e hd hv), d, hd, c⁻¹, inv_mem hc, ?_⟩
  rw [eq_mul_inv_of_mul_eq h]
  group

theorem levi_plus_minus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ d ∈ jLevi k e, ∃ u ∈ jPlus k e, ∃ c ∈ jMinus k e, g = d * u * c := by
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := plus_levi_minus e hg
  exact ⟨d, hd, _, conj_mem_jPlus e (inv_mem hd) hu, c, hc, by group⟩

theorem plus_minus_levi (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ u ∈ jPlus k e, ∃ c ∈ jMinus k e, ∃ d ∈ jLevi k e, g = u * c * d := by
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := plus_levi_minus e hg
  exact ⟨u, hu, _, conj_mem_jMinus e hd hc, d, hd, by group⟩

theorem minus_levi_plus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ c ∈ jMinus k e, ∃ d ∈ jLevi k e, ∃ u ∈ jPlus k e, g = c * d * u := by
  obtain ⟨u, hu, d, hd, c, hc, h⟩ := plus_levi_minus e (inv_mem hg)
  exact ⟨_, inv_mem hc, _, inv_mem hd, _, inv_mem hu, by rw [← inv_inv g, h]; group⟩

theorem levi_minus_plus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ d ∈ jLevi k e, ∃ c ∈ jMinus k e, ∃ u ∈ jPlus k e, g = d * c * u := by
  obtain ⟨c, hc, d, hd, u, hu, rfl⟩ := minus_levi_plus e hg
  exact ⟨d, hd, _, conj_mem_jMinus e (inv_mem hd) hc, u, hu, by group⟩

theorem minus_plus_levi (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ c ∈ jMinus k e, ∃ u ∈ jPlus k e, ∃ d ∈ jLevi k e, g = c * u * d := by
  obtain ⟨c, hc, d, hd, u, hu, rfl⟩ := minus_levi_plus e hg
  exact ⟨c, hc, _, conj_mem_jPlus e hd hu, d, hd, by group⟩

theorem proRad_factorisation (e : (Σ a, m a) ≃ n) :
    proRad k e = KOne k n ⊔ jPlus k e ∧ jMinus k e ⊔ jLevi k e ⊔ jPlus k e = proRad k e ∧
    ∀ g ∈ proRad k e,
      ((∃ x ∈ KOne k n, ∃ u ∈ jPlus k e, g = x * u) ∧ ∃ u ∈ jPlus k e, ∃ x ∈ KOne k n, g = u * x) ∧
      (∃ c ∈ jMinus k e, ∃ d ∈ jLevi k e, ∃ u ∈ jPlus k e, g = c * d * u) ∧
      (∃ c ∈ jMinus k e, ∃ u ∈ jPlus k e, ∃ d ∈ jLevi k e, g = c * u * d) ∧
      (∃ d ∈ jLevi k e, ∃ c ∈ jMinus k e, ∃ u ∈ jPlus k e, g = d * c * u) ∧
      (∃ d ∈ jLevi k e, ∃ u ∈ jPlus k e, ∃ c ∈ jMinus k e, g = d * u * c) ∧
      (∃ u ∈ jPlus k e, ∃ c ∈ jMinus k e, ∃ d ∈ jLevi k e, g = u * c * d) ∧
      (∃ u ∈ jPlus k e, ∃ d ∈ jLevi k e, ∃ c ∈ jMinus k e, g = u * d * c) := by
  refine ⟨proRad_eq_sup e, le_antisymm
    (sup_le (sup_le (jMinus_le_proRad e) (jLevi_le_proRad e)) (jPlus_le_proRad e)) fun g hg => ?_, fun g hg =>
    ⟨⟨exists_KOne_mul_jPlus e hg, exists_jPlus_mul_KOne e hg⟩, minus_levi_plus e hg, minus_plus_levi e hg,
      levi_minus_plus e hg, levi_plus_minus e hg, plus_minus_levi e hg, plus_levi_minus e hg⟩⟩
  obtain ⟨c, hc, d, hd, u, hu, rfl⟩ := minus_levi_plus e hg
  exact Subgroup.mul_mem_sup (Subgroup.mul_mem_sup hc hd) hu

end GlobalTheory.LocGL.IwahoriFactor
