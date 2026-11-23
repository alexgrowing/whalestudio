import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.GaussDegenerate
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

namespace CharacterSumTripleLemmas

open Formalism.L2.Th1.H.Inv

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem sum_shift {M Λ : AddSubgroup V} {S : Finset V} (hS : IsReps M Λ S) (T : V → ℂ)
    (hT : ∀ x ∈ Λ, ∀ t ∈ Λ, t ∈ M → T (x + t) = T x) {a : V} (ha : a ∈ Λ) :
    ∑ x ∈ S, T (x + a) = ∑ x ∈ S, T x := by
  classical
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have hf : ∀ x ∈ S, ∃ x' ∈ S, (x + a) - x' ∈ M := fun x hx => hS3 _ (Λ.add_mem (hS1 x hx) ha)
  choose! f hfS hf2 using hf
  have hTf : ∀ x ∈ S, T (x + a) = T (f x) := by
    intro x hx
    have e : x + a = f x + (x + a - f x) := by abel
    rw [e]
    exact hT _ (hS1 _ (hfS x hx)) _
      (Λ.sub_mem (Λ.add_mem (hS1 x hx) ha) (hS1 _ (hfS x hx))) (hf2 x hx)
  have hinj : Set.InjOn f (S : Set V) := by
    intro p hp q hq hpq
    refine hS2 p hp q hq ?_
    have e : p - q = (p + a - f p) - (q + a - f q) := by rw [hpq]; abel
    rw [e]
    exact M.sub_mem (hf2 p hp) (hf2 q hq)
  have himg : S.image f = S := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro w hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
      exact hfS p hp
    · rw [Finset.card_image_of_injOn hinj]
  conv_rhs => rw [← himg]
  rw [Finset.sum_image hinj]
  exact Finset.sum_congr rfl hTf

theorem card_mul_sum {M' M Λ : AddSubgroup V} {R S : Finset V} (hR : IsReps M' Λ R)
    (hS : IsReps M Λ S) (hM : M' ≤ M) (T : V → ℂ)
    (hT : ∀ x ∈ Λ, ∀ t ∈ Λ, t ∈ M → T (x + t) = T x) :
    (S.card : ℂ) * ∑ x ∈ R, T x = (R.card : ℂ) * ∑ x ∈ S, T x := by
  have h1 : ∑ s ∈ S, ∑ x ∈ R, T (x + s) = (S.card : ℂ) * ∑ x ∈ R, T x := by
    rw [Finset.sum_congr rfl fun s hs =>
      sum_shift hR T (fun x hx t ht htM => hT x hx t ht (hM htM)) (hS.1 s hs)]
    simp
  have h2 : ∑ x ∈ R, ∑ s ∈ S, T (x + s) = (R.card : ℂ) * ∑ s ∈ S, T s := by
    have : ∀ x ∈ R, ∑ s ∈ S, T (x + s) = ∑ s ∈ S, T s := by
      intro x hx
      rw [← sum_shift hS T hT (hR.1 x hx)]
      exact Finset.sum_congr rfl fun s _ => by rw [add_comm]
    rw [Finset.sum_congr rfl this]
    simp
  rw [← h1, ← h2, Finset.sum_comm]

theorem char_sum {H : Sesq V} (hH : IsHerm H) {M Λ : AddSubgroup V} (hΛ : IsSelfDual H Λ)
    {R : Finset V} (hR : IsReps M Λ R) {v : V}
    (hv : ∀ t ∈ Λ, t ∈ M → ∃ m : ℤ, altE H t v = (m : ℝ)) [Decidable (v ∈ Λ)] :
    ∑ x ∈ R, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x v : ℂ))
      = if v ∈ Λ then (R.card : ℂ) else 0 := by
  have hΛ' : dualLat H Λ = Λ := hΛ
  by_cases hv1 : v ∈ Λ
  · rw [if_pos hv1, Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' : x ∈ dualLat H Λ := by rw [hΛ']; exact hR.1 x hx
    obtain ⟨m, hm⟩ := hx' v hv1
    rw [hm, exp_two_pi_int]; simp
  · rw [if_neg hv1]
    have hv' : v ∉ dualLat H Λ := by rw [hΛ']; exact hv1
    have hex : ∃ x₀ ∈ Λ, ¬ ∃ m : ℤ, altE H v x₀ = (m : ℝ) := by
      by_contra hcon
      refine hv' fun x hx => ?_
      by_contra hm
      exact hcon ⟨x, hx, hm⟩
    obtain ⟨x₀, hx₀, hx₀n⟩ := hex
    set χ : V → ℂ := fun x => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x v : ℂ)) with hχ
    have hadd : ∀ a b, χ (a + b) = χ a * χ b := by
      intro a b
      simp only [hχ, altE_add_left]
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hone : ∀ t ∈ Λ, t ∈ M → χ t = 1 := by
      intro t ht htM
      obtain ⟨m, hm⟩ := hv t ht htM
      simp only [hχ]
      rw [hm, exp_two_pi_int]
    have hne : χ x₀ ≠ 1 := by
      intro hc
      obtain ⟨m, hm⟩ := int_of_exp_two_pi hc
      refine hx₀n ⟨-m, ?_⟩
      rw [Formalism.L2.Th1.H.Inv.altE_swap hH x₀ v, hm]; push_cast; ring
    have hsum : ∑ x ∈ R, χ (x + x₀) = ∑ x ∈ R, χ x :=
      sum_shift hR χ (fun x _ t ht htM => by rw [hadd, hone t ht htM, mul_one]) hx₀
    have hsum' : (∑ x ∈ R, χ x) * χ x₀ = ∑ x ∈ R, χ x := by
      rw [Finset.sum_mul, ← hsum]
      exact Finset.sum_congr rfl fun x _ => (hadd x x₀).symm
    have hz : (∑ x ∈ R, χ x) * (χ x₀ - 1) = 0 := by linear_combination hsum'
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne

theorem int_of_selfDual {H : Sesq V} {Λ : AddSubgroup V} (hΛ : IsSelfDual H Λ) {x y : V} (hx : x ∈ Λ)
    (hy : y ∈ Λ) : ∃ m : ℤ, altE H x y = (m : ℝ) := by
  have hx' : x ∈ dualLat H Λ := by
    have h : dualLat H Λ = Λ := hΛ
    rw [h]; exact hx
  exact hx' y hy

theorem altE_add_right (H : Sesq V) (x y y' : V) : altE H x (y + y') = altE H x y + altE H x y' := by
  simp [altE]

theorem move_left {H : Sesq V} (hH : IsHerm H) (α : V → ℂ) (F : V → ℂ) (x z y : V)
    (hx : ∀ w, α x * opU H x F w = F w) (v : V) :
    α x * opU H x (opU H z (opU H y F)) v
      = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x (z + y) : ℂ)) * opU H z (opU H y F) v := by
  rw [(opUComm V H hH (opU H y F) v).2 x z]
  have e1 : opU H x (opU H y F)
      = fun w => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x y : ℂ)) * opU H y (opU H x F) w :=
    funext fun w => (opUComm V H hH F w).2 x y
  rw [e1, opU_const_mul]
  have e2 : α x * opU H z (opU H y (opU H x F)) v = opU H z (opU H y F) v := by
    rw [← opU_const_mul]
    congr 1
    funext w
    rw [← opU_const_mul]
    congr 1
    funext u
    exact hx u
  rw [altE_add_right, Complex.ofReal_add, mul_add, Complex.exp_add]
  linear_combination (Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x z : ℂ)) *
    Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x y : ℂ))) * e2

theorem psi_term {H : Sesq V} (hH : IsHerm H) {α : V → ℂ} {Λ : AddSubgroup V} (hα : IsSemiChar H Λ α)
    {F : V → ℂ} (hF : F ∈ fixedBy H α Λ) {z y : V} (hzy : z + y ∈ Λ) (v : V) :
    α z * α y * opU H z (opU H y F) v = psiT H α z y * F v := by
  rw [opUMul V H hH z y F v]
  have h1 := hF (z + y) hzy v
  have h2 : α (z + y) * α (z + y) = 1 := by
    rcases hα.1 (z + y) hzy with h | h <;> rw [h] <;> norm_num
  have h3 : opU H (z + y) F v = α (z + y) * F v := by
    linear_combination (-opU H (z + y) F v) * h2 + α (z + y) * h1
  rw [h3]
  simp only [psiT]
  ring

end CharacterSumTripleLemmas

open Formalism.L2.Th1.H.Inv Formalism.L2.Th1.H.CharacterSumTripleLemmas in
theorem TripleFormula_proof : TripleFormula := by
  classical
  intro V _ _ H α Λ₁ Λ₂ Λ₃ hd S₂ S₃ hS₂ hS₃ F hF v
  have hH := hd.herm
  have hF2 : inter H α Λ₁ Λ₂ F ∈ fixedBy H α Λ₂ := interFixed V H hH Λ₁ Λ₂ α hd.sc₂ hd.i₁₂ F hF
  have hG3 : inter H α Λ₂ Λ₃ (inter H α Λ₁ Λ₂ F) ∈ fixedBy H α Λ₃ :=
    interFixed V H hH Λ₂ Λ₃ α hd.sc₃ hd.i₂₃ _ hF2
  set G := inter H α Λ₂ Λ₃ (inter H α Λ₁ Λ₂ F) with hGdef
  set c₁₂ : ℂ := ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ with hc₁₂
  set c₂₃ : ℂ := ((Real.sqrt (relIdx Λ₂ Λ₃) : ℝ) : ℂ)⁻¹ with hc₂₃
  have hG : ∀ w, G w = c₂₃ * c₁₂ * ∑ z ∈ S₃, ∑ y ∈ S₂, α z * α y * opU H z (opU H y F) w := by
    intro w
    rw [hGdef, interReps V H hH Λ₂ Λ₃ α hd.sc₃ _ hF2 S₃ hS₃ w]
    have e : inter H α Λ₁ Λ₂ F = fun u => c₁₂ * sumU H α S₂ F u :=
      funext (interReps V H hH Λ₁ Λ₂ α hd.sc₂ F hF S₂ hS₂)
    rw [e]
    simp only [sumU, opU_const_mul, opU_finset_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  have hGf : G = fun w => c₂₃ * c₁₂ * ∑ z ∈ S₃, ∑ y ∈ S₂, α z * α y * opU H z (opU H y F) w :=
    funext hG

  have hn : relIdx (Λ₂ ⊓ Λ₃) Λ₁ ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hd.i₂₁ hd.i₃₁
  obtain ⟨⟨R, hR⟩, hcardR⟩ := repsExist V (Λ₂ ⊓ Λ₃) Λ₁ hn
  obtain ⟨⟨S₁, hS₁⟩, hcard₁⟩ := repsExist V Λ₃ Λ₁ hd.i₃₁
  have key : ∀ w, inter H α Λ₃ Λ₁ G w = tripleMu H α Λ₁ Λ₂ Λ₃ S₂ S₃ * F w := by
    intro w
    have step : ∀ x ∈ R, α x * opU H x G w = c₂₃ * c₁₂ * ∑ z ∈ S₃, ∑ y ∈ S₂,
        α z * α y * opU H z (opU H y F) w
          * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x (z + y) : ℂ)) := by
      intro x hx
      have hxF : ∀ u, α x * opU H x F u = F u := hF x (hR.1 x hx)
      rw [hGf, opU_const_mul]
      simp only [opU_finset_sum, opU_const_mul]
      rw [← mul_assoc, mul_comm (α x) (c₂₃ * c₁₂), mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      linear_combination (α z * α y) * move_left hH α F x z y hxF w
    have hA : ∑ x ∈ R, α x * opU H x G w
        = (R.card : ℂ) * (c₂₃ * c₁₂ * tripleSum H α Λ₁ S₂ S₃ * F w) := by
      rw [Finset.sum_congr rfl step]
      calc ∑ x ∈ R, c₂₃ * c₁₂ * ∑ z ∈ S₃, ∑ y ∈ S₂, α z * α y * opU H z (opU H y F) w
              * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x (z + y) : ℂ))
          = c₂₃ * c₁₂ * ∑ z ∈ S₃, ∑ y ∈ S₂, α z * α y * opU H z (opU H y F) w
              * ∑ x ∈ R, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x (z + y) : ℂ)) := by
            rw [← Finset.mul_sum]
            congr 1
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [Finset.mul_sum]
        _ = c₂₃ * c₁₂ * ∑ z ∈ S₃, ∑ y ∈ S₂,
              (if z + y ∈ Λ₁ then (R.card : ℂ) * (psiT H α z y * F w) else 0) := by
            congr 1
            refine Finset.sum_congr rfl fun z hz => Finset.sum_congr rfl fun y hy => ?_
            have hz3 : z ∈ Λ₃ := hS₃.1 z hz
            have hy2 : y ∈ Λ₂ := hS₂.1 y hy
            have hv : ∀ t ∈ Λ₁, t ∈ Λ₂ ⊓ Λ₃ → ∃ m : ℤ, altE H t (z + y) = (m : ℝ) := by
              intro t _ ht
              obtain ⟨m₁, hm₁⟩ := int_of_selfDual hd.sd₃ (AddSubgroup.mem_inf.1 ht).2 hz3
              obtain ⟨m₂, hm₂⟩ := int_of_selfDual hd.sd₂ (AddSubgroup.mem_inf.1 ht).1 hy2
              exact ⟨m₁ + m₂, by rw [altE_add_right, hm₁, hm₂]; push_cast; ring⟩
            rw [char_sum hH hd.sd₁ hR hv]
            split_ifs with h
            · rw [← psi_term hH hd.sc₁ hF h w]; ring
            · ring
        _ = (R.card : ℂ) * (c₂₃ * c₁₂ * tripleSum H α Λ₁ S₂ S₃ * F w) := by
            simp only [tripleSum, Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
            split_ifs <;> ring
    have hB := card_mul_sum hR hS₁ (inf_le_right : Λ₂ ⊓ Λ₃ ≤ Λ₃) (fun x => α x * opU H x G w)
      (fun x hx t ht htM => interClass V H hH Λ₃ Λ₁ α hd.sc₁ G hG3 x hx t ht htM w)
    rw [hA] at hB
    have hR0 : (R.card : ℂ) ≠ 0 := by rw [hcardR R hR]; exact_mod_cast hn
    have hS1sum : ∑ x ∈ S₁, α x * opU H x G w
        = (S₁.card : ℂ) * (c₂₃ * c₁₂ * tripleSum H α Λ₁ S₂ S₃ * F w) := by
      apply mul_left_cancel₀ hR0
      linear_combination -hB
    rw [interReps V H hH Λ₃ Λ₁ α hd.sc₁ G hG3 S₁ hS₁ w]
    simp only [sumU]
    rw [hS1sum, hcard₁ S₁ hS₁, ← indexEq V H hH Λ₁ Λ₃ hd.sd₁ hd.sd₃ hd.i₁₃ hd.i₃₁]
    simp only [tripleMu, hc₁₂, hc₂₃]
    have ha : ((Real.sqrt (relIdx Λ₁ Λ₃) : ℝ) : ℂ) * ((Real.sqrt (relIdx Λ₁ Λ₃) : ℝ) : ℂ)
        = ((relIdx Λ₁ Λ₃ : ℕ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
    have ha0 : ((Real.sqrt (relIdx Λ₁ Λ₃) : ℝ) : ℂ) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at ha
      exact hd.i₁₃ (by exact_mod_cast ha.symm)
    rw [← ha]
    push_cast
    field_simp
  have hinv := interInv V H hH Λ₃ Λ₁ α hd.sd₃ hd.sd₁ hd.sc₃ hd.sc₁ hd.i₃₁ hd.i₁₃ G hG3 v
  have hI : inter H α Λ₃ Λ₁ G = tripleMu H α Λ₁ Λ₂ Λ₃ S₂ S₃ • F := funext fun w => by
    rw [key w]; rfl
  rw [← hinv, hI, inter_smul]
  rfl

end Formalism.L2.Th1.H
