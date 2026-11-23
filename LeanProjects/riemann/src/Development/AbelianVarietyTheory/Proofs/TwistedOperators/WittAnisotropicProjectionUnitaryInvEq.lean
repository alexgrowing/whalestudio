import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JacProj

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem coords {m : ℕ} (v : Mx D S.rank m) :
    v = d.jX ⬝ (d.pX ⬝ v) + d.j0 ⬝ (d.p0 ⬝ v) + d.jY ⬝ (d.pY ⬝ v) := by
  conv_lhs => rw [← Matrix.one_mul v, ← d.sum_eq_one]
  simp only [Matrix.add_mul, Matrix.mul_assoc]

theorem pY_inv (g : GA D S) : d.pY ⬝ mt S g⁻¹ = adj (mt S g ⬝ d.jX) ⬝ gA S := by
  rw [mt_inv, d.pY_eq, adj_mul]
  simp only [Matrix.mul_assoc, gA_giA_cancel]

theorem witt_anisotropic_projection_unitary_inv_eq (g : GA D S) : d.p0 ⬝ mt S g⁻¹ = giA S₀ ⬝ (adj (mt S g ⬝ d.j0) ⬝ gA S) := by
  rw [mt_inv, d.p0_eq, adj_mul]
  simp only [Matrix.mul_assoc, gA_giA_cancel]

def Keeps (g : GA D S) : Prop :=
  d.p0 ⬝ (mt S g ⬝ d.jX) = 0 ∧ d.pY ⬝ (mt S g ⬝ d.jX) = 0 ∧ d.pY ⬝ (mt S g ⬝ d.j0) = 0

theorem expand {k m : ℕ} (Q : Mx D k S.rank) (A B : Mx D S.rank S.rank) (v : Mx D S.rank m) :
    Q ⬝ ((A * B) ⬝ v) = Q ⬝ (A ⬝ d.jX) ⬝ (d.pX ⬝ (B ⬝ v)) + Q ⬝ (A ⬝ d.j0) ⬝ (d.p0 ⬝ (B ⬝ v)) +
      Q ⬝ (A ⬝ d.jY) ⬝ (d.pY ⬝ (B ⬝ v)) := by
  conv_lhs => rw [← Matrix.mul_one A, ← d.sum_eq_one]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem keeps_jX {g : GA D S} (h : Keeps d g) : mt S g ⬝ d.jX = d.jX ⬝ (d.pX ⬝ (mt S g ⬝ d.jX)) := by
  have e := coords d (mt S g ⬝ d.jX)
  rw [h.1, h.2.1] at e
  simpa only [Matrix.mul_zero, add_zero] using e

theorem preserves_flag_anisotropic_action {g : GA D S} (h : Keeps d g) :
    mt S g ⬝ d.j0 = d.jX ⬝ (d.pX ⬝ (mt S g ⬝ d.j0)) + d.j0 ⬝ (d.p0 ⬝ (mt S g ⬝ d.j0)) := by
  have e := coords d (mt S g ⬝ d.j0)
  rw [h.2.2] at e
  simpa only [Matrix.mul_zero, add_zero] using e

theorem keeps_unitary {g : GA D S} (h : Keeps d g) :
    adj (d.p0 ⬝ (mt S g ⬝ d.j0)) ⬝ (gA S₀ ⬝ (d.p0 ⬝ (mt S g ⬝ d.j0))) = gA S₀ := by
  have hXX : ∀ {k : ℕ} (M : Mx D ρ k), adj d.jX ⬝ (gA S ⬝ (d.jX ⬝ M)) = 0 := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.gram_XX, Matrix.zero_mul]
  have hX0 : ∀ {k : ℕ} (M : Mx D S₀.rank k), adj d.jX ⬝ (gA S ⬝ (d.j0 ⬝ M)) = 0 := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.wittDecomp_gram_X_anisotropic, Matrix.zero_mul]
  have h0X : ∀ {k : ℕ} (M : Mx D ρ k), adj d.j0 ⬝ (gA S ⬝ (d.jX ⬝ M)) = 0 := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.gram_0X, Matrix.zero_mul]
  have h00 : ∀ {k : ℕ} (M : Mx D S₀.rank k), adj d.j0 ⬝ (gA S ⬝ (d.j0 ⬝ M)) = gA S₀ ⬝ M := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.gram_00]
  have hu : adj (mt S g ⬝ d.j0) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = gA S₀ := by
    calc adj (mt S g ⬝ d.j0) ⬝ (gA S ⬝ (mt S g ⬝ d.j0))
        = adj d.j0 ⬝ ((adj (mt S g) * (gA S * mt S g)) ⬝ d.j0) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = gA S₀ := by rw [mt_unitary, d.gram_00]
  rw [preserves_flag_anisotropic_action d h] at hu
  generalize d.pX ⬝ (mt S g ⬝ d.j0) = P at hu
  generalize d.p0 ⬝ (mt S g ⬝ d.j0) = C at hu ⊢
  simpa only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hXX, hX0, h0X, h00,
    Matrix.mul_zero, zero_add, add_zero] using hu

theorem keeps_mul {g g' : GA D S} (h : Keeps d g) (h' : Keeps d g') : Keeps d (g * g') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mt_mul, expand, h.1, h'.1, h'.2.1]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  · rw [mt_mul, expand, h.2.1, h'.1, h'.2.1]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  · rw [mt_mul, expand, h.2.1, h.2.2, h'.2.2]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem keeps_inv {g : GA D S} (h : Keeps d g) : Keeps d g⁻¹ := by
  obtain ⟨P, hP⟩ : ∃ P : Mx D ρ ρ, mt S g ⬝ d.jX = d.jX ⬝ P := ⟨_, keeps_jX d h⟩
  obtain ⟨P', C, hC⟩ : ∃ (P' : Mx D ρ S₀.rank) (C : Mx D S₀.rank S₀.rank), mt S g ⬝ d.j0 = d.jX ⬝ P' + d.j0 ⬝ C := ⟨_, _, preserves_flag_anisotropic_action d h⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, witt_anisotropic_projection_unitary_inv_eq, hC]
    simp only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, d.gram_XX, d.gram_0X,
      Matrix.mul_zero, add_zero]
  · rw [← Matrix.mul_assoc, pY_inv, hP]
    simp only [adj_mul, Matrix.mul_assoc, d.gram_XX, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, pY_inv, hP]
    simp only [adj_mul, Matrix.mul_assoc, d.wittDecomp_gram_X_anisotropic, Matrix.mul_zero]

theorem preserves_flag_anisotropic_block_one_inv {g : GA D S} (h : Keeps d g) (h1 : d.p0 ⬝ (mt S g ⬝ d.j0) = 1) : d.p0 ⬝ (mt S g⁻¹ ⬝ d.j0) = 1 := by
  have e := preserves_flag_anisotropic_action d h
  rw [h1, Matrix.mul_one] at e
  obtain ⟨P, hP⟩ : ∃ P : Mx D ρ S₀.rank, mt S g ⬝ d.j0 = d.jX ⬝ P + d.j0 := ⟨_, e⟩
  rw [← Matrix.mul_assoc, witt_anisotropic_projection_unitary_inv_eq, hP]
  simp only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, d.wittDecomp_gram_X_anisotropic, d.gram_00,
    Matrix.mul_zero, zero_add]
  exact giA_mul_gA S₀

theorem keeps_one : Keeps d 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [mt_one, Matrix.one_mul]
  · exact d.p0_jX
  · exact d.pY_jX
  · exact d.pY_j0

def keepSub : Subgroup (GA D S) where
  carrier := {g | Keeps d g}
  one_mem' := keeps_one d
  mul_mem' := keeps_mul d
  inv_mem' := keeps_inv d

def keepSub1 : Subgroup (GA D S) where
  carrier := {g | Keeps d g ∧ d.p0 ⬝ (mt S g ⬝ d.j0) = 1}
  one_mem' := ⟨keeps_one d, by rw [mt_one, Matrix.one_mul, HypDec.p0_j0]⟩
  mul_mem' := fun {a b} ha hb => ⟨keeps_mul d ha.1 hb.1, by
    rw [mt_mul, expand, ha.1.1, ha.2, hb.1.2.2, hb.2]
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Matrix.one_mul]⟩
  inv_mem' := fun {a} ha => ⟨keeps_inv d ha.1, preserves_flag_anisotropic_block_one_inv d ha.1 ha.2⟩

theorem flag_le : flagN d ≤ keepSub1 d := by
  intro n hn
  obtain ⟨T, b, -, hX, h0⟩ := exists_blocks d hn
  have eX : ∀ {k : ℕ} (Q : Mx D k S.rank), Q ⬝ (mt S n ⬝ d.jX) = Q ⬝ d.jX + Q ⬝ d.jX ⬝ T := fun Q => by
    rw [hX, Matrix.mul_add, Matrix.mul_assoc]
  have e0 : ∀ {k : ℕ} (Q : Mx D k S.rank), Q ⬝ (mt S n ⬝ d.j0) = Q ⬝ d.j0 + Q ⬝ d.jX ⬝ b := fun Q => by
    rw [h0, Matrix.mul_add, Matrix.mul_assoc]
  show (_ ∧ _ ∧ _) ∧ _
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [eX, d.p0_jX, Matrix.zero_mul, add_zero]
  · rw [eX, d.pY_jX, Matrix.zero_mul, add_zero]
  · rw [e0, d.pY_j0, d.pY_jX, Matrix.zero_mul, add_zero]
  · rw [e0, d.p0_j0, d.p0_jX, Matrix.zero_mul, add_zero]

theorem range_le : d.emb0.range ≤ keepSub d := by
  rintro _ ⟨h, rfl⟩
  show _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [d.wittDecomp_anisotropicEmbedding_inclX, d.p0_jX]
  · rw [d.wittDecomp_anisotropicEmbedding_inclX, d.pY_jX]
  · rw [d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, d.pY_j0, Matrix.zero_mul]

theorem jac_le : (flagN d ⊔ d.emb0.range : Subgroup (GA D S)) ≤ keepSub d :=
  sup_le (fun _ hg => (flag_le d hg).1) (range_le d)

theorem witt_anisotropic_block_flag_mul_embedded {n : GA D S} (hn : n ∈ flagN d) (h : GA D S₀) :
    d.p0 ⬝ (mt S (n * d.emb0 h) ⬝ d.j0) = mt S₀ h := by
  have h1 : d.p0 ⬝ (mt S n ⬝ d.j0) = 1 := (flag_le d hn).2
  rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt S n), ← Matrix.mul_assoc d.p0, h1,
    Matrix.one_mul]

def proj (g : (flagN d ⊔ d.emb0.range : Subgroup (GA D S))) : GA D S₀ :=
  ofMat S₀ (d.p0 ⬝ (mt S g.1 ⬝ d.j0)) (keeps_unitary d (jac_le d g.2))

theorem continuous_proj : Continuous (proj d) := by
  apply continuous_of_mt
  simp only [proj, mt_ofMat]
  exact continuous_const.matrix_mul (((continuous_mt S).comp continuous_subtype_val).matrix_mul continuous_const)

theorem proj_mul (h : GA D S₀) (n : flagN d) :
    proj d ⟨n.1 * d.emb0 h, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h := by
  apply mt_injective S₀
  simp only [proj, mt_ofMat]
  exact witt_anisotropic_block_flag_mul_embedded d n.2 h

theorem exists_continuous_proj : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ),
    ∃ p : (flagN d ⊔ d.emb0.range : Subgroup (GA D S)) → GA D S₀, Continuous p ∧
      ∀ (h : GA D S₀) (n : flagN d),
        p ⟨n.1 * d.emb0 h, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h := by
  intro D S S₀ ρ d
  exact ⟨proj d, continuous_proj d, proj_mul d⟩

end GlobalTheory.JacProj
