import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.RealPar.HwGen

theorem weight_of_mem_span {V ι κ : Type*} [AddCommGroup V] [Module ℂ V] (H : ι → Module.End ℂ V)
    (m : κ → V) (χ : κ → ι → ℂ) (hm : ∀ k a, H a (m k) = χ k a • m k) (ν : ι → ℂ) (w : V)
    (hw : w ∈ Submodule.span ℂ (Set.range m)) (h0 : w ≠ 0) (hν : ∀ a, H a w = ν a • w) :
    ∃ k, χ k = ν := by
  by_contra hne
  push Not at hne
  let M : Submonoid (Module.End ℂ V) :=
    Submonoid.closure {P | ∃ a c, c ≠ ν a ∧ P = H a - c • (1 : Module.End ℂ V)}
  have hM : ∀ P ∈ M, ∀ (s : V) (η : ι → ℂ), (∀ a, H a s = η a • s) →
      ∃ c : ℂ, P s = c • s ∧ (η = ν → c ≠ 0) := by
    intro P hP s η hs
    induction hP using Submonoid.closure_induction with
    | mem P hP =>
      obtain ⟨a, c, hc, rfl⟩ := hP
      refine ⟨η a - c, by simp [hs, sub_smul], ?_⟩
      rintro rfl
      exact sub_ne_zero.2 hc.symm
    | one => exact ⟨1, by simp, fun _ => one_ne_zero⟩
    | mul P Q _ _ hP hQ =>
      obtain ⟨c, hc, hc'⟩ := hP
      obtain ⟨d, hd, hd'⟩ := hQ
      exact ⟨d * c, by simp [hc, hd, mul_smul], fun h => mul_ne_zero (hd' h) (hc' h)⟩
  have key : ∀ x ∈ Submodule.span ℂ (Set.range m), ∀ Q ∈ M, ∃ P ∈ M, P (Q x) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      intro Q hQ
      obtain ⟨c, hc, -⟩ := hM Q hQ (m k) (χ k) (hm k)
      obtain ⟨a, ha⟩ := Function.ne_iff.1 (hne k)
      refine ⟨H a - χ k a • 1, Submonoid.subset_closure ⟨a, _, ha, rfl⟩, ?_⟩
      rw [hc, map_smul]
      simp [hm]
    | zero => exact fun Q _ => ⟨1, one_mem _, by simp⟩
    | add x y _ _ hx hy =>
      intro Q hQ
      obtain ⟨P, hP, h1⟩ := hx Q hQ
      obtain ⟨R, hR, h2⟩ := hy (P * Q) (mul_mem hP hQ)
      refine ⟨R * P, mul_mem hR hP, ?_⟩
      simp only [Module.End.mul_apply] at h2 ⊢
      simp [h1, h2]
    | smul c x _ hx =>
      intro Q hQ
      obtain ⟨P, hP, h1⟩ := hx Q hQ
      exact ⟨P, hP, by simp [h1]⟩
  obtain ⟨P, hP, h1⟩ := key w hw 1 (one_mem _)
  obtain ⟨c, hc, hc'⟩ := hM P hP w ν hν
  rw [Module.End.one_apply, hc] at h1
  exact h0 ((smul_eq_zero.1 h1).resolve_left (hc' rfl))

variable {p q : ℕ}

theorem isKC_Eab {a b : Ix p q} (h : posC a b) : IsKC (Eab b a) := by
  intro x y hxy
  by_contra hne
  have : b = x ∧ a = y := by
    by_contra hh
    exact hne (by simp [Eab, hh])
  obtain ⟨rfl, rfl⟩ := this
  cases a <;> cases b <;> simp_all [posC, sameBlock]

theorem isKC_mul {X Y : Mat p q} (hX : IsKC X) (hY : IsKC Y) : IsKC (X * Y) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h : sameBlock a c
  · rw [hY c b (by cases a <;> cases b <;> cases c <;> simp_all [sameBlock]), mul_zero]
  · rw [hX a c h, zero_mul]

theorem isKC_sub {X Y : Mat p q} (hX : IsKC X) (hY : IsKC Y) : IsKC (X - Y) := by
  intro a b hab
  simp [hX a b hab, hY a b hab]

theorem sameBlock_cases {a b : Ix p q} (h : sameBlock a b) : a = b ∨ posC a b ∨ posC b a := by
  rcases a with a | a <;> rcases b with b | b
  · rcases lt_trichotomy a b with x | x | x
    · exact .inr (.inl x)
    · exact .inl (by rw [x])
    · exact .inr (.inr x)
  · exact h.elim
  · exact h.elim
  · rcases lt_trichotomy a b with x | x | x
    · exact .inr (.inl x)
    · exact .inl (by rw [x])
    · exact .inr (.inr x)

theorem bracket_diag (x a b : Ix p q) :
    Eab x x * Eab b a - Eab b a * Eab x x =
      (((if x = b then 1 else 0) - (if x = a then 1 else 0) : ℂ)) • Eab b a := by
  have h1 : Eab x x * Eab b a = ((if x = b then 1 else 0) : ℂ) • Eab b a := by
    by_cases h : x = b
    · subst h; simp [Eab]
    · simp [Eab, h]
  have h2 : Eab b a * Eab x x = ((if x = a then 1 else 0) : ℂ) • Eab b a := by
    by_cases h : x = a
    · subst h; simp [Eab]
    · simp [Eab, h, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm h)]
  rw [h1, h2, sub_smul]

abbrev PosRoot (p q : ℕ) := {r : Ix p q × Ix p q // posC r.1 r.2}

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

noncomputable def mono (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (v : V) : List (PosRoot p q) → V
  | [] => v
  | r :: l => act (Eab r.1.2 r.1.1) (mono act v l)

noncomputable def cnt : List (PosRoot p q) → Ix p q → Ix p q → ℕ
  | [], _, _ => 0
  | r :: l, a, b => cnt l a b + if a = r.1.1 ∧ b = r.1.2 then 1 else 0

theorem posC_of_cnt (l : List (PosRoot p q)) (a b : Ix p q) (h : cnt l a b ≠ 0) : posC a b := by
  induction l with
  | nil => exact (h rfl).elim
  | cons r l ih =>
    by_cases hh : a = r.1.1 ∧ b = r.1.2
    · rw [hh.1, hh.2]; exact r.2
    · exact ih (by simpa [cnt, hh] using h)

noncomputable def drop (l : List (PosRoot p q)) (x : Ix p q) : ℝ :=
  ∑ a, ∑ b, (cnt l a b : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0))

theorem drop_cons (r : PosRoot p q) (l : List (PosRoot p q)) (x : Ix p q) :
    drop (r :: l) x = drop l x + ((if x = r.1.1 then 1 else 0) - (if x = r.1.2 then 1 else 0)) := by
  simp only [drop, cnt, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single r.1.1, Finset.sum_eq_single r.1.2]
  · simp
  · intro b _ hb; simp [hb]
  · simp
  · intro a _ ha; simp [ha]
  · simp

theorem act_comm {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) (X Y : Mat p q) (u : V) :
    act X (act Y u) = act Y (act X u) + act (X * Y - Y * X) u := by
  rw [h X Y]; simp

theorem mono_weight {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) {μ : Ix p q → ℚ} {v : V}
    (hv : ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) (l : List (PosRoot p q)) (x : Ix p q) :
    act (Eab x x) (mono act v l) = ((((μ x : ℚ) : ℝ) - drop l x : ℝ) : ℂ) • mono act v l := by
  induction l with
  | nil => simp [mono, drop, cnt, hv]
  | cons r l ih =>
    rw [mono, act_comm h, ih, bracket_diag, map_smul, map_smul, LinearMap.smul_apply, ← add_smul, drop_cons]
    congr 1
    push_cast
    split_ifs <;> simp <;> ring

theorem mono_stable {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) {μ : Ix p q → ℚ} {v : V}
    (hv : ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) (hr : ∀ a b, posC a b → act (Eab a b) v = 0) :
    KStable act (Submodule.span ℂ (Set.range (mono act v))) := by
  set W := Submodule.span ℂ (Set.range (mono act v)) with hW
  have hm : ∀ l, mono act v l ∈ W := fun l => Submodule.subset_span ⟨l, rfl⟩
  have ext : ∀ T : Module.End ℂ V, (∀ l, T (mono act v l) ∈ W) → ∀ w ∈ W, T w ∈ W := by
    intro T hT w hw
    have : W ≤ W.comap T := Submodule.span_le.2 (by rintro _ ⟨l, rfl⟩; exact hT l)
    exact this hw
  have low : ∀ r : PosRoot p q, ∀ w ∈ W, act (Eab r.1.2 r.1.1) w ∈ W :=
    fun r => ext _ fun l => hm (r :: l)
  have key : ∀ l, ∀ Z, IsKC Z → act Z (mono act v l) ∈ W := by
    intro l
    induction l with
    | nil =>
      intro Z hZ
      have hZ' : Z = ∑ a, ∑ b, Z a b • Eab a b := by
        conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
        simp [Eab]
      rw [hZ']
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      refine W.sum_mem fun a _ => W.sum_mem fun b _ => ?_
      by_cases hab : sameBlock a b
      · refine W.smul_mem _ ?_
        rcases sameBlock_cases hab with x | x | x
        · subst x
          rw [mono, hv]; exact W.smul_mem _ (hm [])
        · rw [mono, hr a b x]; exact W.zero_mem
        · exact hm [⟨(b, a), x⟩]
      · rw [hZ a b hab, zero_smul]; exact W.zero_mem
    | cons r l ih =>
      intro Z hZ
      rw [mono, act_comm h]
      have hF := isKC_Eab r.2
      exact W.add_mem (low r _ (ih Z hZ)) (ih _ (isKC_sub (isKC_mul hZ hF) (isKC_mul hF hZ)))
  exact fun Z hZ => ext _ fun l => key l Z hZ

theorem hw_generated : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (μ : Ix p q → ℚ) (v : V), Formalism.BasicNotions.TH.IsHW act μ v → ∃ W : Submodule ℂ V, v ∈ W ∧ KStable act W ∧ (∀ W' : Submodule ℂ V, v ∈ W' → KStable act W' → W ≤ W') ∧ ∀ (ν : Ix p q → ℝ) (w : V), w ∈ W → w ≠ 0 → (∀ a, act (Eab a a) w = ((ν a : ℝ) : ℂ) • w) → ∃ c : Ix p q → Ix p q → ℕ, (∀ a b, c a b ≠ 0 → posC a b) ∧ ∀ x, ((μ x : ℚ) : ℝ) - ν x = ∑ a, ∑ b, (c a b : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0)) := by
  intro p q V _ _ act h μ v hv
  obtain ⟨-, hw, hr⟩ := hv
  have hv : ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
    intro a
    have := (Submodule.mem_iInf _).1 hw a
    simpa [sub_eq_zero] using this
  have hr : ∀ a b, posC a b → act (Eab a b) v = 0 := by
    intro a b hab
    have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hr a) b) hab
    simpa using this
  refine ⟨Submodule.span ℂ (Set.range (mono act v)), Submodule.subset_span ⟨[], rfl⟩, mono_stable h hv hr, ?_, ?_⟩
  · intro W' hvW hW
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, rfl⟩
    induction l with
    | nil => exact hvW
    | cons r l ih => exact hW _ (isKC_Eab r.2) _ ih
  · intro ν w hw h0 hν
    obtain ⟨l, hl⟩ := weight_of_mem_span (fun a => act (Eab a a)) (mono act v) _
      (fun l x => mono_weight h hv l x) (fun a => ((ν a : ℝ) : ℂ)) w hw h0 hν
    refine ⟨cnt l, posC_of_cnt l, fun x => ?_⟩
    have := Complex.ofReal_injective (congrFun hl x)
    change _ = drop l x
    linarith

end GlobalTheory.RealPar.HwGen
