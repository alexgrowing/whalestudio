import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.GramConv

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem hform_add_left' (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (u u' w : Fin n → L) :
    Formalism.UG.hform σ J (u + u') w = Formalism.UG.hform σ J u w + Formalism.UG.hform σ J u' w := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_add_right' (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (u w w' : Fin n → L) :
    Formalism.UG.hform σ J u (w + w') = Formalism.UG.hform σ J u w + Formalism.UG.hform σ J u w' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right' (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (c : L) (u w : Fin n → L) :
    Formalism.UG.hform σ J u (c • w) = c * Formalism.UG.hform σ J u w := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_smul_left' (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (c : L)
    (u w : Fin n → L) : Formalism.UG.hform σ J (σ c • u) w = c * Formalism.UG.hform σ J u w := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, hσ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_sub_mat (σ : L →+* L) {n : ℕ} (J J' : Matrix (Fin n) (Fin n) L) (u w : Fin n → L) :
    Formalism.UG.hform σ (J - J') u w = Formalism.UG.hform σ J u w - Formalism.UG.hform σ J' u w := by
  simp only [Formalism.UG.hform, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_eq_dot (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (u w : Fin n → L) :
    Formalism.UG.hform σ J u w = (fun i => σ (u i)) ⬝ᵥ (J *ᵥ w) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec_mulVec (σ : L →+* L) {n r : ℕ} (J : Matrix (Fin n) (Fin n) L) (B : Matrix (Fin n) (Fin r) L)
    (α β : Fin r → L) :
    Formalism.UG.hform σ J (B *ᵥ α) (B *ᵥ β) = Formalism.UG.hform σ (Formalism.UG.cT σ B * J * B) α β := by
  have hs : (fun i => σ ((B *ᵥ α) i)) = (fun k => σ (α k)) ᵥ* Formalism.UG.cT σ B := by
    ext i
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Formalism.UG.cT, map_sum, map_mul, Matrix.transpose_apply,
      Matrix.map_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hform_eq_dot, hform_eq_dot, hs, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

theorem mulVec_int' {a b : ℕ} {A : Matrix (Fin a) (Fin b) L} (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) {w : Fin b → L}
    (hw : ∀ j, w j ∈ Formalism.UG.intL L) (i : Fin a) : (A *ᵥ w) i ∈ Formalism.UG.intL L := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hw j)

theorem hform_int' (σ : L →+* L) (hv : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} {J : Matrix (Fin n) (Fin n) L}
    (hJ : ∀ i j, J i j ∈ Formalism.UG.intL L) {u w : Fin n → L} (hu : ∀ i, u i ∈ Formalism.UG.intL L)
    (hw : ∀ i, w i ∈ Formalism.UG.intL L) : Formalism.UG.hform σ J u w ∈ Formalism.UG.intL L := by
  have hsu : ∀ i, σ (u i) ∈ Formalism.UG.intL L := fun i => by
    show Valued.v (σ (u i)) ≤ 1
    rw [hv]; exact hu i
  exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
    Subring.mul_mem _ (Subring.mul_mem _ (hsu i) (hJ i j)) (hw j)

theorem gramEq_of_gram_bounds : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ϖ ∈ Formalism.UG.intL L →
  ∀ (n n' r : ℕ) (JT : GL (Fin n') L) (a : GL (Fin n) L) (x y : Matrix (Fin n') (Fin n) L)
    (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
  (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
    ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔ ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) → (∀ i j, (x * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) → (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (∀ i k, M i k ∈ Formalism.UG.intL L) → (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → (∀ m : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → ∃ α : Fin r → L, (∀ k, α k ∈ Formalism.UG.intL L) ∧
      ∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (m - M *ᵥ α)) i ∈ Formalism.UG.intL L) → (∀ β : Fin r → L, (∀ k, β k ∈ Formalism.UG.intL L) → (∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (M *ᵥ β)) i ∈ Formalism.UG.intL L) →
      ∀ k, Valued.v (β k) ≤ Valued.v ϖ ^ e k) →
  (∀ j k, ((Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M)) - (Formalism.UG.cT σ (x * M) * (JT : Matrix (Fin n') (Fin n') L) * (x * M))) j k * ϖ ^ max (e j) (e k) ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.HoweG.GramEq σ JT x y := by
  intro L _ _ ϖ σ hσ hv hϖ n n' r JT a x y M e hJ hJh hiff hxa hya hM hAM hdec hbd hG
  intro m m' hm hm' c hc hxm hxm'
  have toV : ∀ t : L, t ∈ Formalism.UG.intL L → Valued.v t ≤ 1 := fun t h => h
  have ofV : ∀ t : L, Valued.v t ≤ 1 → t ∈ Formalism.UG.intL L := fun t h => h
  set A : Matrix (Fin n) (Fin n) L := (a : Matrix (Fin n) (Fin n) L) with hA
  set Ai : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hAi
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  have hAAi : A * Ai = 1 := by rw [hA, hAi]; exact a.mul_inv
  have hAiA : Ai * A = 1 := by rw [hA, hAi]; exact a.inv_mul

  have key : ∀ μ : Fin n → L, (∀ i, μ i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ (c • μ)) i ∈ Formalism.UG.intL L) →
      ∃ α : Fin r → L, (∀ k, α k ∈ Formalism.UG.intL L) ∧ (∀ i, (Ai *ᵥ (μ - M *ᵥ α)) i ∈ Formalism.UG.intL L) ∧
        (∀ i, (Ai *ᵥ (M *ᵥ (c • α))) i ∈ Formalism.UG.intL L) ∧ ∀ k, Valued.v (c * α k) ≤ Valued.v ϖ ^ e k := by
    intro μ hμ hxμ
    obtain ⟨α, hα, hν⟩ := hdec μ hμ
    have hcμ : ∀ i, (c • μ) i ∈ Formalism.UG.intL L := fun i => Subring.mul_mem _ hc (hμ i)
    obtain ⟨u, hu, hcu⟩ := (hiff (c • μ) hcμ).2 hxμ
    have heq : Ai *ᵥ (M *ᵥ (c • α)) = u - c • (Ai *ᵥ (μ - M *ᵥ α)) := by
      have h1 : M *ᵥ (c • α) = c • μ - c • (μ - M *ᵥ α) := by
        rw [Matrix.mulVec_smul, smul_sub, sub_sub_cancel]
      rw [h1, Matrix.mulVec_sub, hcu, Matrix.mulVec_mulVec, hAiA, Matrix.one_mulVec, Matrix.mulVec_smul]
    have hint : ∀ i, (Ai *ᵥ (M *ᵥ (c • α))) i ∈ Formalism.UG.intL L := by
      intro i
      rw [heq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact Subring.sub_mem _ (hu i) (Subring.mul_mem _ hc (hν i))
    have hcα : ∀ k, (c • α) k ∈ Formalism.UG.intL L := fun k => Subring.mul_mem _ hc (hα k)
    refine ⟨α, hα, hν, hint, fun k => ?_⟩
    have := hbd (c • α) hcα hint k
    simpa only [Pi.smul_apply, smul_eq_mul] using this
  obtain ⟨α, hα, hν, hcαA, hbdα⟩ := key m hm hxm
  obtain ⟨α', hα', hν', hcα'A, hbdα'⟩ := key m' hm' hxm'

  have hσcα : ∀ i, (Ai *ᵥ (M *ᵥ (σ c • α))) i ∈ Formalism.UG.intL L := by
    intro i
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    refine Subring.sum_mem _ fun k _ => ofV _ ?_
    calc Valued.v ((Ai * M) i k * (σ c * α k)) = Valued.v ((Ai * M) i k) * Valued.v (c * α k) := by
          rw [map_mul, map_mul, map_mul, hv]
      _ ≤ Valued.v ((Ai * M) i k) * Valued.v ϖ ^ e k := mul_le_mul' le_rfl (hbdα k)
      _ = Valued.v ((Ai * M) i k * ϖ ^ e k) := by rw [map_mul, map_pow]
      _ ≤ 1 := toV _ (hAM i k)

  have hz : ∀ z : Matrix (Fin n') (Fin n) L, (∀ i j, (z * A) i j ∈ Formalism.UG.intL L) →
      c * Formalism.UG.hform σ J (z *ᵥ m) (z *ᵥ m') - c * Formalism.UG.hform σ J (z *ᵥ (M *ᵥ α)) (z *ᵥ (M *ᵥ α'))
        ∈ Formalism.UG.intL L := by
    intro z hzA
    have hzw : ∀ w : Fin n → L, (∀ i, (Ai *ᵥ w) i ∈ Formalism.UG.intL L) → ∀ i, (z *ᵥ w) i ∈ Formalism.UG.intL L := by
      intro w hw
      have : z *ᵥ w = (z * A) *ᵥ (Ai *ᵥ w) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hAAi, Matrix.mul_one]
      rw [this]; exact mulVec_int' hzA hw
    have e1 : z *ᵥ m = z *ᵥ (M *ᵥ α) + z *ᵥ (m - M *ᵥ α) := by
      rw [← Matrix.mulVec_add, add_sub_cancel]
    have e2 : z *ᵥ m' = z *ᵥ (M *ᵥ α') + z *ᵥ (m' - M *ᵥ α') := by
      rw [← Matrix.mulVec_add, add_sub_cancel]
    have s1 : σ c • (z *ᵥ (M *ᵥ α)) = z *ᵥ (M *ᵥ (σ c • α)) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    have s2 : c • (z *ᵥ (M *ᵥ α')) = z *ᵥ (M *ᵥ (c • α')) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    have hexp : c * Formalism.UG.hform σ J (z *ᵥ m) (z *ᵥ m') - c * Formalism.UG.hform σ J (z *ᵥ (M *ᵥ α)) (z *ᵥ (M *ᵥ α')) =
        Formalism.UG.hform σ J (σ c • (z *ᵥ (M *ᵥ α))) (z *ᵥ (m' - M *ᵥ α')) +
        Formalism.UG.hform σ J (z *ᵥ (m - M *ᵥ α)) (c • (z *ᵥ (M *ᵥ α'))) +
        c * Formalism.UG.hform σ J (z *ᵥ (m - M *ᵥ α)) (z *ᵥ (m' - M *ᵥ α')) := by
      rw [hform_smul_left' σ hσ, hform_smul_right', e1, e2, hform_add_left', hform_add_right', hform_add_right']
      ring
    rw [hexp, s1, s2]
    have hJi : ∀ i j, J i j ∈ Formalism.UG.intL L := hJ
    refine Subring.add_mem _ (Subring.add_mem _ ?_ ?_) (Subring.mul_mem _ hc ?_)
    · exact hform_int' σ hv hJi (hzw _ hσcα) (hzw _ hν')
    · exact hform_int' σ hv hJi (hzw _ hν) (hzw _ hcα'A)
    · exact hform_int' σ hv hJi (hzw _ hν) (hzw _ hν')

  have hmain : c * (Formalism.UG.hform σ J (y *ᵥ (M *ᵥ α)) (y *ᵥ (M *ᵥ α')) -
      Formalism.UG.hform σ J (x *ᵥ (M *ᵥ α)) (x *ᵥ (M *ᵥ α'))) ∈ Formalism.UG.intL L := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hform_mulVec_mulVec, hform_mulVec_mulVec, ← hform_sub_mat, ← hform_smul_right']
    set D := Formalism.UG.cT σ (y * M) * J * (y * M) - Formalism.UG.cT σ (x * M) * J * (x * M) with hD
    refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ofV _ ?_
    have h1 : Valued.v (α i) * Valued.v (c * α' j) ≤ Valued.v ϖ ^ max (e i) (e j) := by
      rcases le_total (e i) (e j) with h | h
      · rw [max_eq_right h]
        calc Valued.v (α i) * Valued.v (c * α' j) ≤ 1 * Valued.v ϖ ^ e j := mul_le_mul' (toV _ (hα i)) (hbdα' j)
          _ = _ := one_mul _
      · rw [max_eq_left h]
        calc Valued.v (α i) * Valued.v (c * α' j) = Valued.v (c * α i) * Valued.v (α' j) := by
              rw [map_mul, map_mul, mul_left_comm, ← mul_assoc]
          _ ≤ Valued.v ϖ ^ e i * 1 := mul_le_mul' (hbdα i) (toV _ (hα' j))
          _ = _ := mul_one _
    calc Valued.v (σ (α i) * D i j * (c • α') j) = (Valued.v (α i) * Valued.v (c * α' j)) * Valued.v (D i j) := by
          rw [Pi.smul_apply, smul_eq_mul, map_mul, map_mul, hv, mul_right_comm]
      _ ≤ Valued.v ϖ ^ max (e i) (e j) * Valued.v (D i j) := mul_le_mul' h1 le_rfl
      _ = Valued.v (D i j * ϖ ^ max (e i) (e j)) := by rw [map_mul, map_pow, mul_comm]
      _ ≤ 1 := toV _ (hG i j)
  have hfin : c * (Formalism.UG.hform σ J (y *ᵥ m) (y *ᵥ m') - Formalism.UG.hform σ J (x *ᵥ m) (x *ᵥ m')) =
      (c * Formalism.UG.hform σ J (y *ᵥ m) (y *ᵥ m') - c * Formalism.UG.hform σ J (y *ᵥ (M *ᵥ α)) (y *ᵥ (M *ᵥ α'))) -
      (c * Formalism.UG.hform σ J (x *ᵥ m) (x *ᵥ m') - c * Formalism.UG.hform σ J (x *ᵥ (M *ᵥ α)) (x *ᵥ (M *ᵥ α'))) +
      c * (Formalism.UG.hform σ J (y *ᵥ (M *ᵥ α)) (y *ᵥ (M *ᵥ α')) -
        Formalism.UG.hform σ J (x *ᵥ (M *ᵥ α)) (x *ᵥ (M *ᵥ α'))) := by ring
  rw [hfin]
  exact Subring.add_mem _ (Subring.sub_mem _ (hz y hya) (hz x hxa)) hmain

end GlobalTheory.Hk3.GramConv

end
