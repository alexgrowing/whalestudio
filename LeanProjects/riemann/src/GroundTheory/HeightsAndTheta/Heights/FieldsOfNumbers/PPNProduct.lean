import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsAddBlock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

noncomputable section

universe u

section Product

variable {K : Type}

def prodFn (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) : (Option K → ℤ) → ℤ :=
  fun m => A (fun k => m (some k)) * B (m none)

def diff1 (g : ℤ → ℤ) : ℤ → ℤ := fun t => g t - g (t - 1)

theorem backwardDifference_apply (g : ℤ → ℤ) (t : ℤ) : diff1 g t = g t - g (t - 1) := rfl

theorem pullDeg_some (c : K → ℤ) (k : K) :
    pullDeg Function.Embedding.some c (some k) = c k :=
  (Function.Embedding.some (α := K)).injective.extend_apply c 0 k

theorem pullDeg_none (c : K → ℤ) : pullDeg Function.Embedding.some c none = 0 := by
  unfold pullDeg
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨a, h⟩
    exact Option.some_ne_none a h

theorem diffStep_pull (c : K → ℤ) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    diffStep (pullDeg Function.Embedding.some c) (prodFn A B) = prodFn (diffStep c A) B := by
  funext m
  have h1 : (fun k => (m - pullDeg Function.Embedding.some c) (some k)) =
      (fun k => m (some k)) - c := by
    funext k
    simp [pullDeg_some]
  have h2 : (m - pullDeg Function.Embedding.some c) none = m none := by
    simp [pullDeg_none]
  unfold diffStep prodFn
  rw [h1, h2]
  ring

theorem diffStep_newBlock (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    diffStep (newBlockDeg : Option K → ℤ) (prodFn A B) = prodFn A (diff1 B) := by
  funext m
  have h1 : (fun k => (m - (newBlockDeg : Option K → ℤ)) (some k)) = fun k => m (some k) := by
    funext k
    simp [newBlockDeg]
  have h2 : (m - (newBlockDeg : Option K → ℤ)) none = m none - 1 := by
    simp [newBlockDeg]
  unfold diffStep prodFn diff1
  rw [h1, h2]
  ring

theorem foldr_pull (L : List (K → ℤ)) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    (L.map (pullDeg Function.Embedding.some)).foldr diffStep (prodFn A B) =
      prodFn (L.foldr diffStep A) B := by
  induction L with
  | nil => rfl
  | cons c L ih => simp only [List.map_cons, List.foldr_cons, ih, diffStep_pull]

theorem foldr_newBlock (j : ℕ) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    (List.replicate j (newBlockDeg : Option K → ℤ)).foldr diffStep (prodFn A B) =
      prodFn A (diff1^[j] B) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ, List.foldr_cons, ih, diffStep_newBlock,
      Function.iterate_succ_apply']

theorem mixedDiff_prodFn {m r : ℕ} (cs : Fin r → K → ℤ) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    mixedDiff (Fin.append (fun _ : Fin m => (newBlockDeg : Option K → ℤ))
        (fun i => pullDeg Function.Embedding.some (cs i))) (prodFn A B) =
      prodFn (mixedDiff cs A) (diff1^[m] B) := by
  have h : List.ofFn (fun i => pullDeg Function.Embedding.some (cs i)) =
      (List.ofFn cs).map (pullDeg Function.Embedding.some) := by
    rw [List.map_ofFn]
    rfl
  unfold mixedDiff
  rw [List.ofFn_fin_append, List.foldr_append, List.ofFn_const, h, foldr_pull, foldr_newBlock]

theorem tendsto_restrict :
    Tendsto (fun m : Option K → ℤ => fun k => m (some k)) atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨fun o => Option.elim o 0 b, fun _ ha k => ha (some k)⟩

theorem eventually_none_ge (a : ℤ) : ∀ᶠ m : Option K → ℤ in atTop, a ≤ m none :=
  (eventually_ge_atTop (fun _ : Option K => a)).mono fun _ hm => hm none

theorem eventualValue_eq {f : (Option K → ℤ) → ℤ} {c : ℤ} (hf : ∀ᶠ m in atTop, f m = c) :
    eventualValue f = c := by
  have h : ∃ c, ∀ᶠ m in atTop, f m = c := ⟨c, hf⟩
  unfold eventualValue
  rw [dif_pos h]
  obtain ⟨m, h1, h2⟩ := (h.choose_spec.and hf).exists
  exact h1.symm.trans h2

end Product

section Binomial

theorem iter_projSpaceHilb (N : ℕ) : ∀ j : ℕ, j ≤ N → ∀ s : ℕ,
    diff1^[j] (projSpaceHilb N) ((s : ℤ) + j) = (((s + N).choose (N - j) : ℕ) : ℤ) := by
  intro j
  induction j with
  | zero =>
    intro _ s
    simp [projSpaceHilb]
  | succ j ih =>
    intro hj s
    have e1 : (s : ℤ) + ((j + 1 : ℕ) : ℤ) = ((s + 1 : ℕ) : ℤ) + j := by push_cast; ring
    have e2 : (s : ℤ) + ((j + 1 : ℕ) : ℤ) - 1 = (s : ℤ) + j := by push_cast; ring
    rw [Function.iterate_succ_apply', backwardDifference_apply, e2, e1, ih (by omega), ih (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, N - j = k + 1 := ⟨N - (j + 1), by omega⟩
    have hk' : N - (j + 1) = k := by omega
    rw [hk, hk', show s + 1 + N = (s + N) + 1 by omega, Nat.choose_succ_succ']
    push_cast
    ring

theorem backwardDifference_eq_zero_of_eventually_const {g : ℤ → ℤ} {a c : ℤ} (h : ∀ s : ℕ, g (s + a) = c) (s : ℕ) :
    diff1 g (s + (a + 1)) = 0 := by
  rw [backwardDifference_apply, show (s : ℤ) + (a + 1) = ((s + 1 : ℕ) : ℤ) + a by push_cast; ring,
    show ((s + 1 : ℕ) : ℤ) + a - 1 = (s : ℤ) + a by push_cast; ring, h, h, sub_self]

theorem iter_projSpaceHilb_top (N : ℕ) (t : ℤ) (ht : (N : ℤ) ≤ t) :
    diff1^[N] (projSpaceHilb N) t = 1 := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, t = s + N := ⟨(t - N).toNat, by omega⟩
  rw [iter_projSpaceHilb N N le_rfl s, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]

theorem iter_projSpaceHilb_high (N : ℕ) : ∀ i s : ℕ,
    diff1^[N + 1 + i] (projSpaceHilb N) ((s : ℤ) + ((N + 1 + i : ℕ) : ℤ)) = 0 := by
  intro i
  induction i with
  | zero =>
    intro s
    have hN : ∀ s : ℕ, diff1^[N] (projSpaceHilb N) ((s : ℤ) + (N : ℤ)) = 1 := fun s =>
      iter_projSpaceHilb_top N _ (by omega)
    have e : (s : ℤ) + ((N + 1 + 0 : ℕ) : ℤ) = s + ((N : ℤ) + 1) := by push_cast; ring
    rw [e, show N + 1 + 0 = N + 1 from rfl, Function.iterate_succ_apply']
    exact backwardDifference_eq_zero_of_eventually_const hN s
  | succ i ih =>
    intro s
    rw [show N + 1 + (i + 1) = (N + 1 + i) + 1 by omega, Function.iterate_succ_apply',
      Nat.cast_add_one]
    exact backwardDifference_eq_zero_of_eventually_const ih s

theorem iter_projSpaceHilb_above (N j : ℕ) (hj : N < j) (t : ℤ) (ht : (j : ℤ) ≤ t) :
    diff1^[j] (projSpaceHilb N) t = 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = N + 1 + i := ⟨j - (N + 1), by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, t = s + ((N + 1 + i : ℕ) : ℤ) :=
    ⟨(t - ((N + 1 + i : ℕ) : ℤ)).toNat, by omega⟩
  exact iter_projSpaceHilb_high N i s

end Binomial

theorem ProductWithProjectiveSpace.proof (h1 : MixedDiffConst.Statement.{u})
    (h2 : HilbAddBlock.Statement.{u}) : ProductWithProjectiveSpace.Statement.{u} := by
  intro F _ K _ _ ι _ P hP e N r m he hrm cs
  have hH : hilbFn (addBlockPrime N P) = prodFn (hilbFn P) (projSpaceHilb N) := by
    funext x
    exact h2 F K ι P N x
  unfold intNum
  rw [hH, mixedDiff_prodFn]
  have hlim := tendsto_restrict (K := K)
  rcases lt_trichotomy m N with hmN | hmN | hmN
  · rw [if_neg hmN.ne]
    apply eventualValue_eq
    have hz := (h1 F K ι P hP.multiHomog hP.relevant e he).2 r (by omega) cs
    filter_upwards [hlim.eventually hz] with x hx
    simp only [prodFn]
    rw [hx, zero_mul]
  · subst hmN
    rw [if_pos rfl]
    obtain rfl : r = e := by omega
    apply eventualValue_eq
    have hc := (h1 F K ι P hP.multiHomog hP.relevant r he).1 cs
    filter_upwards [hlim.eventually hc, eventually_none_ge (m : ℤ)] with x hx hn
    simp only [prodFn]
    rw [hx, iter_projSpaceHilb_top m _ hn, mul_one]
    rfl
  · rw [if_neg hmN.ne']
    apply eventualValue_eq
    filter_upwards [eventually_none_ge (m : ℤ)] with x hn
    simp only [prodFn]
    rw [iter_projSpaceHilb_above N m hmN _ hn, mul_zero]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
