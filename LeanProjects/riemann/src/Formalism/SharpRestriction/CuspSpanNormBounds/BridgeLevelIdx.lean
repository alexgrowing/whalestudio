import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

noncomputable section

namespace Formalism.MainNotions.BridgeLevelIdx

open MeasureTheory Formalism.MainNotions.S Matrix
open scoped ENNReal TensorProduct

variable (I : AutInst)

def LevelGen (g : ℕ) : Prop :=
  ∃ (m : ℕ) (l : Fin m → (Fin I.n → I.E ⊗[I.F] Af I.F)) (S : Finset (Fin I.n → I.E ⊗[I.F] Af I.F)),
    m ≤ I.n ∧ S.card ≤ g ^ (2 * I.f * I.n) ∧ (∀ j, l j ∈ I.Lf) ∧
    (∀ y ∈ I.Lf, ∃ (a : Fin m → IntAf I.F I.E) (z : Fin I.n → I.E ⊗[I.F] Af I.F), z ∈ I.Lf ∧
      y = ∑ j, (a j : I.E ⊗[I.F] Af I.F) • l j + (g : I.E ⊗[I.F] Af I.F) • z) ∧
    ∀ y ∈ I.Lf, ∃ s ∈ S, ∃ z ∈ I.Lf, y = s + (g : I.E ⊗[I.F] Af I.F) • z

variable {I}

theorem lf_csmul (a : IntAf I.F I.E) {z : Fin I.n → I.E ⊗[I.F] Af I.F} (hz : z ∈ I.Lf) :
    (a : I.E ⊗[I.F] Af I.F) • z ∈ I.Lf :=
  I.Lf.smul_mem a hz

theorem kset_mulVec {x : I.Gf} (hx : x ∈ I.Kset) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    I.fmat x *ᵥ y ∈ I.Lf :=
  (hx y).1 hy

theorem kset_inv_mulVec {x : I.Gf} (hx : x ∈ I.Kset) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    I.fmat x⁻¹ *ᵥ y ∈ I.Lf := by
  have h : x⁻¹ ∈ I.Kset := by
    show ((x⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
    rw [Subgroup.coe_inv]
    exact (Formalism.UG.stabGL I.Lf).inv_mem hx
  exact (h y).1 hy

theorem kset_mul {x x' : I.Gf} (hx : x ∈ I.Kset) (hx' : x' ∈ I.Kset) : x⁻¹ * x' ∈ I.Kset := by
  show ((x⁻¹ * x' : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [Subgroup.coe_mul, Subgroup.coe_inv]
  exact (Formalism.UG.stabGL I.Lf).mul_mem ((Formalism.UG.stabGL I.Lf).inv_mem hx) hx'

theorem kg_of_gen {g : ℕ} {m : ℕ} {l : Fin m → (Fin I.n → I.E ⊗[I.F] Af I.F)}
    (hgen : ∀ y ∈ I.Lf, ∃ (a : Fin m → IntAf I.F I.E) (z : Fin I.n → I.E ⊗[I.F] Af I.F), z ∈ I.Lf ∧
      y = ∑ j, (a j : I.E ⊗[I.F] Af I.F) • l j + (g : I.E ⊗[I.F] Af I.F) • z)
    {x x' : I.Gf} (hx : x ∈ I.Kset) (hx' : x' ∈ I.Kset)
    (hd : ∀ j, ∃ w ∈ I.Lf, (I.fmat x' - I.fmat x) *ᵥ l j = (g : I.E ⊗[I.F] Af I.F) • w) :
    x⁻¹ * x' ∈ I.Kg g := by
  refine ⟨kset_mul hx hx', fun y hy => ?_⟩
  set D := I.fmat x' - I.fmat x with hD

  have hDy : ∃ w ∈ I.Lf, D *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • w := by
    obtain ⟨a, z, hz, rfl⟩ := hgen y hy
    have hsum : ∀ s : Finset (Fin m), ∃ w ∈ I.Lf,
        D *ᵥ (∑ j ∈ s, (a j : I.E ⊗[I.F] Af I.F) • l j) = (g : I.E ⊗[I.F] Af I.F) • w := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨0, I.Lf.zero_mem, by simp⟩
      | insert j s hj ih =>
        obtain ⟨w, hw, e⟩ := ih
        obtain ⟨w', hw', e'⟩ := hd j
        refine ⟨(a j : I.E ⊗[I.F] Af I.F) • w' + w, I.Lf.add_mem (lf_csmul _ hw') hw, ?_⟩
        rw [Finset.sum_insert hj, Matrix.mulVec_add, Matrix.mulVec_smul, e, e', smul_add, smul_comm]
    obtain ⟨w, hw, e⟩ := hsum Finset.univ
    refine ⟨w + D *ᵥ z, I.Lf.add_mem hw ?_, ?_⟩
    · rw [hD, Matrix.sub_mulVec]
      exact I.Lf.sub_mem (kset_mulVec hx' hz) (kset_mulVec hx hz)
    · rw [Matrix.mulVec_add, e, Matrix.mulVec_smul, smul_add]
  obtain ⟨w, hw, e⟩ := hDy
  refine ⟨I.fmat x⁻¹ *ᵥ w, kset_inv_mulVec hx hw, ?_⟩
  have hm : I.fmat (x⁻¹ * x') - 1 = I.fmat x⁻¹ * D := by
    have h1 : I.fmat (x⁻¹ * x') = I.fmat x⁻¹ * I.fmat x' := by
      simp only [AutInst.fmat, Subgroup.coe_mul, Units.val_mul]
    have h2 : I.fmat x⁻¹ * I.fmat x = 1 := by
      simp only [AutInst.fmat, Subgroup.coe_inv, Units.inv_mul]
    rw [hD, Matrix.mul_sub, h1, h2]
  rw [hm, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_smul]

theorem card_reduction {g : ℕ} (hg : 1 ≤ g) (hG : LevelGen I g) :
    ∃ (α : Type) (_ : Fintype α) (ρ : I.Gf → α), Fintype.card α ≤ g ^ (2 * I.n ^ 2 * I.f) ∧
      ∀ x ∈ I.Kset, ∀ x' ∈ I.Kset, ρ x = ρ x' → x⁻¹ * x' ∈ I.Kg g := by
  classical
  obtain ⟨m, l, S, hm, hS, hl, hgen, hrep⟩ := hG
  obtain ⟨s0, hs0, -⟩ := hrep 0 I.Lf.zero_mem
  let r : (Fin I.n → I.E ⊗[I.F] Af I.F) → S := fun v =>
    if h : v ∈ I.Lf then ⟨(hrep v h).choose, (hrep v h).choose_spec.1⟩ else ⟨s0, hs0⟩
  have hr : ∀ v ∈ I.Lf, ∃ z ∈ I.Lf, v = (r v : Fin I.n → I.E ⊗[I.F] Af I.F) + (g : I.E ⊗[I.F] Af I.F) • z := by
    intro v hv
    simp only [r, dif_pos hv]
    exact (hrep v hv).choose_spec.2
  refine ⟨Fin m → S, inferInstance, fun x j => r (I.fmat x *ᵥ l j), ?_, ?_⟩
  · rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    calc S.card ^ m ≤ (g ^ (2 * I.f * I.n)) ^ m := Nat.pow_le_pow_left hS m
      _ ≤ (g ^ (2 * I.f * I.n)) ^ I.n := Nat.pow_le_pow_right (pow_pos (by omega) _) hm
      _ = g ^ (2 * I.n ^ 2 * I.f) := by rw [← pow_mul]; congr 1; ring
  · intro x hx x' hx' hρ
    refine kg_of_gen hgen hx hx' fun j => ?_
    have e : r (I.fmat x *ᵥ l j) = r (I.fmat x' *ᵥ l j) := congrFun hρ j
    obtain ⟨z, hz, ez⟩ := hr _ (kset_mulVec hx (hl j))
    obtain ⟨z', hz', ez'⟩ := hr _ (kset_mulVec hx' (hl j))
    refine ⟨z' - z, I.Lf.sub_mem hz' hz, ?_⟩
    rw [Matrix.sub_mulVec, ez, ez', e, smul_sub]
    abel

theorem levelIdx_holds (μf : Measure I.Gf) [μf.IsMulLeftInvariant] {g : ℕ} (hg : 1 ≤ g) (hG : LevelGen I g) :
    μf I.Kset ≤ ((g ^ (2 * I.n ^ 2 * I.f) : ℕ) : ℝ≥0∞) * μf (I.Kg g) := by
  classical
  obtain ⟨α, _, ρ, hcard, hρ⟩ := card_reduction hg hG
  let rp : α → I.Gf := fun a => if h : ∃ x ∈ I.Kset, ρ x = a then h.choose else 1
  have hcov : I.Kset ⊆ ⋃ a, (fun h => rp a * h) '' I.Kg g := by
    intro x hx
    have hex : ∃ x₀ ∈ I.Kset, ρ x₀ = ρ x := ⟨x, hx, rfl⟩
    refine Set.mem_iUnion.2 ⟨ρ x, (rp (ρ x))⁻¹ * x, ?_, by simp⟩
    have e : rp (ρ x) = hex.choose := by simp only [rp, dif_pos hex]
    rw [e]
    exact hρ _ hex.choose_spec.1 x hx hex.choose_spec.2
  have hone : ∀ a, μf ((fun h => rp a * h) '' I.Kg g) = μf (I.Kg g) := by
    intro a
    rw [Set.image_mul_left]
    exact measure_preimage_mul μf _ _
  calc μf I.Kset ≤ μf (⋃ a, (fun h => rp a * h) '' I.Kg g) := measure_mono hcov
    _ ≤ ∑ a, μf ((fun h => rp a * h) '' I.Kg g) := measure_iUnion_fintype_le _ _
    _ = (Fintype.card α : ℝ≥0∞) * μf (I.Kg g) := by
        simp only [hone, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := by gcongr

end Formalism.MainNotions.BridgeLevelIdx

end
