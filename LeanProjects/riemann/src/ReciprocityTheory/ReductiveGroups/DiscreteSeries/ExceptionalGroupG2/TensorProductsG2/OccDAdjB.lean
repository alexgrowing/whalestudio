import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccDAdjA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccDTensKStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

def adjSg (ε : Fin n → Bool) (c : Fin n) : ℂ := if ε c then 1 else -1

theorem adjSg_mul_self (ε : Fin n → Bool) (c : Fin n) : adjSg ε c * adjSg ε c = 1 := by
  unfold adjSg; split_ifs <;> norm_num

theorem adjSg_conj (ε : Fin n → Bool) (c : Fin n) : (starRingEnd ℂ) (adjSg ε c) = adjSg ε c := by
  unfold adjSg; split_ifs <;> simp

theorem adjSign_eq_adjSg (ε : Fin n → Bool) (a b : Fin n) : adjSign ε a b = adjSg ε a * adjSg ε b := by
  unfold adjSign adjSg
  cases ε a <;> cases ε b <;> norm_num

section R

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

def adjR (ε : Fin n → Bool) (M : Submodule ℂ X) (ps : (Fin n → X) →ₗ[ℂ] X) (x : X) (u : Fin n → X) : Prop :=
  u ∈ tensSub M ∧ ∀ c, ∀ y ∈ M, inner ℂ (u c) y = adjSg ε c * inner ℂ x (ps (Pi.single c y))

variable {ε : Fin n → Bool} {M : Submodule ℂ X} {ps : (Fin n → X) →ₗ[ℂ] X}

theorem adjR_inv {x : X} {u : Fin n → X} (h : adjR ε M ps x u) (c : Fin n) {y : X} (hy : y ∈ M) :
    inner ℂ x (ps (Pi.single c y)) = adjSg ε c * inner ℂ (u c) y := by
  rw [h.2 c y hy, ← mul_assoc, adjSg_mul_self, one_mul]

theorem adjR_unique {x : X} {u u' : Fin n → X} (h : adjR ε M ps x u) (h' : adjR ε M ps x u') : u = u' := by
  funext c
  have hm : u c - u' c ∈ M := M.sub_mem (tset_mem.1 h.1 c) (tset_mem.1 h'.1 c)
  have h0 : inner ℂ (u c - u' c) (u c - u' c) = (0 : ℂ) := by
    rw [inner_sub_left, h.2 c _ hm, h'.2 c _ hm, sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

theorem adjR_add {x x' : X} {u u' : Fin n → X} (h : adjR ε M ps x u) (h' : adjR ε M ps x' u') :
    adjR ε M ps (x + x') (u + u') := by
  refine ⟨(tensSub M).add_mem h.1 h'.1, fun c y hy => ?_⟩
  rw [Pi.add_apply, inner_add_left, inner_add_left, h.2 c y hy, h'.2 c y hy, mul_add]

theorem adjR_smul {x : X} {u : Fin n → X} (h : adjR ε M ps x u) (r : ℂ) : adjR ε M ps (r • x) (r • u) := by
  refine ⟨(tensSub M).smul_mem r h.1, fun c y hy => ?_⟩
  rw [Pi.smul_apply, inner_smul_left, inner_smul_left, h.2 c y hy]
  ring

theorem adjR_linear {M' : Submodule ℂ X} (hex : ∀ x ∈ M', ∃ u, adjR ε M ps x u) :
    ∃ ι : X →ₗ[ℂ] (Fin n → X), ∀ x ∈ M', adjR ε M ps x (ι x) := by
  classical
  choose g hg using hex
  let φ : M' →ₗ[ℂ] (Fin n → X) :=
    { toFun := fun x => g x.1 x.2
      map_add' := fun x y => (adjR_unique (hg _ (x + y).2) (adjR_add (hg _ x.2) (hg _ y.2))).trans rfl
      map_smul' := fun r x => (adjR_unique (hg _ (r • x).2) (adjR_smul (hg _ x.2) r)).trans rfl }
  obtain ⟨ι, hι⟩ := LinearMap.exists_extend φ
  refine ⟨ι, fun x hx => ?_⟩
  have : ι x = g x hx := LinearMap.congr_fun hι ⟨x, hx⟩
  rw [this]
  exact hg x hx

end R

section Amb

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem adjB_tensF_mem (dual : Bool) {M : Submodule ℂ D} (hME : ∀ a b, ∀ v ∈ M, E a b v ∈ M)
    {u : Fin n → D} (hu : u ∈ tensSub M) (a b : Fin n) : tensF dual E a b u ∈ tensSub M := by
  refine tset_mem.2 fun c => ?_
  have hu' := tset_mem.1 hu
  cases dual
  · simp only [tensF, cond_false, tensV_coord]
    refine M.add_mem (hME a b _ (hu' c)) ?_
    split_ifs
    · exact hu' b
    · exact M.zero_mem
  · simp only [tensF, cond_true, tensVd_coord]
    refine M.sub_mem (hME a b _ (hu' c)) ?_
    split_ifs
    · exact hu' a
    · exact M.zero_mem

theorem adjB_E (dual : Bool) (hU : IsInfUnitary ε E) {M : Submodule ℂ D} (hME : ∀ a b, ∀ v ∈ M, E a b v ∈ M)
    {ps : (Fin n → D) →ₗ[ℂ] D} (hps2 : ∀ a b, ∀ f ∈ tensSub M, ps (tensF dual E a b f) = E a b (ps f))
    {x : D} {u : Fin n → D} (h : adjR ε M ps x u) (a b : Fin n) :
    adjR ε M ps (E a b x) (tensF dual E a b u) := by
  classical
  refine ⟨adjB_tensF_mem dual hME h.1 a b, fun c y hy => ?_⟩
  have hsc : ∀ d, (Pi.single c y : Fin n → D) d ∈ M := tset_mem.1 (adjA_single_mem c hy)
  have e1 := adjSg_mul_self ε c
  rw [hU a b x, ← hps2 b a _ (adjA_single_mem c hy), adjSign_eq_adjSg]
  cases dual
  · have hT : tensF false E b a (Pi.single c y) =
        Pi.single c (E b a y) + Pi.single b ((Pi.single c y : Fin n → D) a) := by
      funext d
      simp only [tensF, cond_false, tensV_coord, Pi.add_apply, Pi.single_apply]
      split_ifs <;> simp_all
    rw [hT, map_add, inner_add_right, adjR_inv h c (hME b a y hy), adjR_inv h b (hsc a)]
    simp only [tensF, cond_false, tensV_coord, inner_add_left, hU a b (u c) y, adjSign_eq_adjSg]
    by_cases hca : c = a
    · subst hca
      have e2 := adjSg_mul_self ε b
      simp only [Pi.single_eq_same, if_true]
      linear_combination (-(adjSg ε c * adjSg ε b * inner ℂ (u c) (E b c y)) -
        inner ℂ (u b) y * adjSg ε b * adjSg ε b) * e1 + (-inner ℂ (u b) y) * e2
    · have hac : a ≠ c := Ne.symm hca
      simp only [hca, if_false, inner_zero_left, inner_zero_right, add_zero, mul_zero, Pi.single_apply, hac]
      linear_combination (-(adjSg ε a * adjSg ε b * inner ℂ (u c) (E b a y))) * e1
  · have hT : tensF true E b a (Pi.single c y) =
        Pi.single c (E b a y) - Pi.single a ((Pi.single c y : Fin n → D) b) := by
      funext d
      simp only [tensF, cond_true, tensVd_coord, Pi.sub_apply, Pi.single_apply]
      split_ifs <;> simp_all
    rw [hT, map_sub, inner_sub_right, adjR_inv h c (hME b a y hy), adjR_inv h a (hsc b)]
    simp only [tensF, cond_true, tensVd_coord, inner_sub_left, hU a b (u c) y, adjSign_eq_adjSg]
    by_cases hcb : c = b
    · subst hcb
      have e2 := adjSg_mul_self ε a
      simp only [Pi.single_eq_same, if_true]
      linear_combination (-(adjSg ε a * adjSg ε c * inner ℂ (u c) (E c a y)) +
        inner ℂ (u a) y * adjSg ε a * adjSg ε a) * e1 + (inner ℂ (u a) y) * e2
    · have hbc : b ≠ c := Ne.symm hcb
      simp only [hcb, if_false, inner_zero_left, inner_zero_right, sub_zero, mul_zero, Pi.single_apply, hbc]
      linear_combination (-(adjSg ε a * adjSg ε b * inner ℂ (u c) (E b a y))) * e1

theorem adjB_block {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {c d : Fin n} (h : ε c ≠ ε d) :
    k c d = 0 := by
  have h1 := congrFun (congrFun hk.2 c) d
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have key : ∀ s t : Bool, s ≠ t → k c d * (if t = true then 1 else -1) = (if s = true then 1 else -1) * k c d →
      k c d = 0 := by
    intro s t hst h2
    cases s <;> cases t
    · exact absurd rfl hst
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_one, one_mul] at h2
      first | exact h2 | linear_combination h2 / 2 | linear_combination -h2 / 2
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_one, one_mul] at h2
      first | exact h2 | linear_combination h2 / 2 | linear_combination -h2 / 2
    · exact absurd rfl hst
  exact key _ _ h h1

theorem adjB_sgn {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (dual : Bool) (c d : Fin n) :
    (starRingEnd ℂ) (cond dual (star (k c d)) (k c d)) * (adjSg ε c * adjSg ε d) =
      (starRingEnd ℂ) (cond dual (star (k c d)) (k c d)) := by
  by_cases h : ε c = ε d
  · rw [show adjSg ε c * adjSg ε d = 1 by unfold adjSg; rw [h]; split_ifs <;> norm_num, mul_one]
  · rw [adjB_block hk h]
    cases dual <;> simp

theorem adjB_star_Kset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : kᴴ ∈ Kset ε := by
  refine ⟨?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hk.1
  · have h := congrArg Matrix.conjTranspose hk.2
    simp only [Matrix.conjTranspose_mul] at h
    have hJ : (Jm ε)ᴴ = Jm ε := by
      rw [Jm, Matrix.diagonal_conjTranspose]
      congr 1
      funext a
      simp only [Pi.star_apply]
      split_ifs <;> simp
    rw [hJ] at h
    exact h.symm

theorem adjB_inner (hσ : IsURepOn (UJset ε) σ) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v w : H) :
    inner ℂ (σ k v) w = inner ℂ v (σ kᴴ w) := by
  have hkU : k ∈ UJset ε := smd_inUJ_of_Kset hk
  have hkhU : kᴴ ∈ UJset ε := smd_inUJ_of_Kset (adjB_star_Kset hk)
  have hkk : k * kᴴ = 1 := by
    have := hk.1
    rw [Matrix.mem_unitaryGroup_iff] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  have hinv : σ k (σ kᴴ w) = w := by
    have := hσ.1.2 k hkU kᴴ hkhU
    rw [hkk, hσ.1.1] at this
    exact (congrArg (fun T : H →L[ℂ] H => T w) this).symm
  conv_lhs => rw [← hinv]
  exact inner_map_map_of_isURep hσ hkU v (σ kᴴ w)

end Amb

end ReciprocityTheory.ChartRestriction.DS.G2
