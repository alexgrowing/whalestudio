import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.SatBlocks

def intRing {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) : Subring C where
  carrier := {z | (0 : WithTop ℝ) ≤ v z}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [v.map_mul]; exact add_nonneg ha hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    exact v.map_le_add ha hb
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rwa [v.map_neg]

theorem mem_intRing {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (z : C) :
    z ∈ intRing v ↔ ((0 : ℝ) : WithTop ℝ) ≤ v z := Iff.rfl

theorem ne_zero_of_val_zero {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {z : C}
    (h : v z = 0) : z ≠ 0 := by
  rintro rfl
  simp at h

theorem inv_mem_of_val_zero {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {z : C}
    (h : v z = 0) : z⁻¹ ∈ intRing v := by
  have h1 : v (z * z⁻¹) = 0 := by rw [mul_inv_cancel₀ (ne_zero_of_val_zero v h)]; simp
  rw [v.map_mul, h, zero_add] at h1
  exact h1.ge

theorem exists_projector {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {O A : Type}
    [DecidableEq A] {n : A → ℕ} {d : ℕ} (M : O → Matrix (Fin d) (Fin d) C) (em : A → O → C)
    (u : (Σ a : A, Fin (n a)) → Fin d → C)
    (hM : ∀ x i j, M x i j ∈ intRing v) (he : ∀ a x, em a x ∈ intRing v)
    (hu : ∀ x q, (M x).mulVec (u q) = em q.1 x • u q)
    (hs : ∀ a a', a ≠ a' → ∃ x, v (em a x - em a' x) = 0) (a : A) (S : Finset A) (ha : a ∉ S) :
    ∃ (P : Matrix (Fin d) (Fin d) C) (c : A → C), (∀ i j, P i j ∈ intRing v) ∧
      (∀ q, P.mulVec (u q) = c q.1 • u q) ∧ c a = 1 ∧ ∀ b ∈ S, c b = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, fun _ => 1, ?_, by simp, rfl, by simp⟩
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | insert b S hb ih =>
    rw [Finset.mem_insert, not_or] at ha
    obtain ⟨P, c, hP, hPu, hca, hcS⟩ := ih ha.2
    obtain ⟨x, hx⟩ := hs a b ha.1
    refine ⟨((em a x - em b x)⁻¹ • (M x - em b x • (1 : Matrix (Fin d) (Fin d) C))) * P,
      fun e => (em a x - em b x)⁻¹ * (em e x - em b x) * c e, ?_, ?_, ?_, ?_⟩
    · intro i j
      rw [Matrix.mul_apply]
      refine sum_mem fun k _ => mul_mem ?_ (hP k j)
      simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      refine mul_mem (inv_mem_of_val_zero v hx) (sub_mem (hM x i k) (mul_mem (he b x) ?_))
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro q
      rw [← Matrix.mulVec_mulVec, hPu, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.sub_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec, hu]
      ext k
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    · simp only [hca, mul_one]
      exact inv_mul_cancel₀ (ne_zero_of_val_zero v hx)
    · intro e he'
      rcases Finset.mem_insert.1 he' with rfl | h
      · simp
      · simp [hcS e h]

theorem saturated_blocks_summand : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (O A : Type) [Fintype A] [DecidableEq A] (n : A → ℕ) (d : ℕ) (M : O → Matrix (Fin d) (Fin d) C) (em : A → O → C) (u : (Σ a : A, Fin (n a)) → Fin d → C), (∀ x i j, ((0 : ℝ) : WithTop ℝ) ≤ v (M x i j)) → (∀ a x, ((0 : ℝ) : WithTop ℝ) ≤ v (em a x)) → (∀ x q, (M x).mulVec (u q) = em q.1 x • u q) → (∀ a a', a ≠ a' → ∃ x, v (em a x - em a' x) = 0) → (∀ a, ∃ w : Fin d → Fin (n a) → C, (∀ s i, ((0 : ℝ) : WithTop ℝ) ≤ v (w s i)) ∧ ∀ i i', ∑ s, u ⟨a, i⟩ s * w s i' = if i = i' then 1 else 0) → ∃ w : Fin d → (Σ a : A, Fin (n a)) → C, (∀ s q, ((0 : ℝ) : WithTop ℝ) ≤ v (w s q)) ∧ ∀ q q', ∑ s, u q s * w s q' = if q = q' then 1 else 0 := by
  intro C _ v O A _ _ n d M em u hM he hu hs hw
  choose w hwi hw using hw
  have key := fun a : A => exists_projector v M em u hM he hu hs a (Finset.univ.erase a)
    (Finset.notMem_erase a _)
  choose P c hP hPu hca hcS using key
  refine ⟨fun s q => ∑ t, P q.1 t s * w q.1 t q.2, ?_, ?_⟩
  · intro s q
    exact (mem_intRing v _).1
      (sum_mem fun t _ => mul_mem (hP _ _ _) ((mem_intRing v _).2 (hwi _ _ _)))
  · rintro ⟨b, j⟩ ⟨a, i⟩
    have h1 : ∑ s, u ⟨b, j⟩ s * ∑ t, P a t s * w a t i
        = ∑ t, (P a).mulVec (u ⟨b, j⟩) t * w a t i := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring
    dsimp only
    rw [h1, hPu]
    by_cases hba : b = a
    · subst hba
      simp only [hca, one_smul, hw]
      simp
    · have h0 : c a b = 0 := hcS a b (by simp [hba])
      rw [if_neg (fun h => hba (congrArg Sigma.fst h))]
      simp [h0]

end GlobalTheory.SatBlocks
