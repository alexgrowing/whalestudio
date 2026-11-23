import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ProjSt

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.AbsSt.Proj

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem shape_mul (A B A' B' : Matrix (Fin n) (Fin n) ℂ) :
    fromBlocks A B (-B) A * fromBlocks A' B' (-B') A' =
      fromBlocks (A * A' - B * B') (A * B' + B * A') (-(A * B' + B * A')) (A * A' - B * B') := by
  rw [fromBlocks_multiply]
  congr 1 <;> noncomm_ring

theorem kM_mul (a b a' b' : Matrix (Fin n) (Fin n) ℂ) : kM a b * kM a' b' = kM (a * a') (b * b') := by
  simp only [kM]
  rw [shape_mul]
  congr 1 <;>
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul, smul_add, smul_sub, smul_neg, neg_add, neg_sub] <;>
    match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring

theorem kM_one : kM (1 : Matrix (Fin n) (Fin n) ℂ) 1 = 1 := by
  simp only [kM, sub_self, smul_zero, neg_zero]
  rw [← fromBlocks_one]
  congr 1 <;> rw [← two_smul ℂ (1 : Matrix (Fin n) (Fin n) ℂ), smul_smul] <;> norm_num

theorem kM_conjTranspose (a b : Matrix (Fin n) (Fin n) ℂ) : (kM a b)ᴴ = kM aᴴ bᴴ := by
  simp only [kM, fromBlocks_conjTranspose, conjTranspose_smul, conjTranspose_add, conjTranspose_sub,
    conjTranspose_neg]
  congr 1 <;> simp [Complex.conj_ofReal, map_div₀] <;> module

theorem JJ_comm_shape (A B : Matrix (Fin n) (Fin n) ℂ) :
    JJ n * fromBlocks A B (-B) A = fromBlocks A B (-B) A * JJ n := by
  simp only [JJ, fromBlocks_multiply]
  congr 1 <;> simp

theorem JJ_comm_kM (a b : Matrix (Fin n) (Fin n) ℂ) : JJ n * kM a b = kM a b * JJ n := by
  unfold kM
  exact JJ_comm_shape _ _

theorem first_unitary_block_of_pair (a b : Matrix (Fin n) (Fin n) ℂ) : u1 (kM a b) = a := by
  simp only [u1, kM, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_neg, smul_smul]
  rw [show Complex.I * (Complex.I / 2) = -(1/2 : ℂ) by
    rw [mul_div_assoc', Complex.I_mul_I]; ring]
  module

theorem second_unitary_block_of_pair (a b : Matrix (Fin n) (Fin n) ℂ) : u2 (kM a b) = b := by
  simp only [u2, kM, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_neg, smul_smul, neg_neg]
  rw [show Complex.I * (Complex.I / 2) = -(1/2 : ℂ) by
    rw [mul_div_assoc', Complex.I_mul_I]; ring]
  module

theorem kM_low (a : Matrix (Fin n) (Fin n) ℂ) : (kM a a).toBlocks₂₁ = 0 := by
  unfold kM
  rw [toBlocks_fromBlocks₂₁]
  simp

theorem kM_of_unitary (a b : Matrix (Fin n) (Fin n) ℂ) (ha : a ∈ unitaryGroup (Fin n) ℂ)
    (hb : b ∈ unitaryGroup (Fin n) ℂ) : ∃ k : GR n, k ∈ KR n ∧ mR k = kM a b := by
  have ha1 : aᴴ * a = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp ha
  have ha2 : a * aᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp ha
  have hb1 : bᴴ * b = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hb
  have hb2 : b * bᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hb
  let u : GL (Fin n ⊕ Fin n) ℂ :=
    ⟨kM a b, kM aᴴ bᴴ, by rw [kM_mul, ha2, hb2, kM_one], by rw [kM_mul, ha1, hb1, kM_one]⟩
  have hG : u ∈ GR n := by
    show InG (kM a b)
    unfold InG
    rw [kM_conjTranspose, Matrix.mul_assoc, JJ_comm_kM, ← Matrix.mul_assoc, kM_mul, ha1, hb1,
      kM_one, Matrix.one_mul]
  refine ⟨⟨u, hG⟩, ?_, rfl⟩
  show InK (kM a b)
  exact ⟨hG, by rw [kM_conjTranspose, kM_mul, ha1, hb1, kM_one]⟩

theorem KR_shape (k : GR n) (hk : k ∈ KR n) :
    u1 (mR k) ∈ unitaryGroup (Fin n) ℂ ∧ u2 (mR k) ∈ unitaryGroup (Fin n) ℂ ∧
      mR k = kM (u1 (mR k)) (u2 (mR k)) := by
  have hk' : InK (mR k) := hk
  obtain ⟨hG, hU⟩ := hk'
  unfold InG at hG
  set g := mR k with hg
  have hU' : g * gᴴ = 1 := mul_eq_one_comm.mp hU
  have hc : JJ n * g = g * JJ n := by
    calc JJ n * g = (g * gᴴ) * JJ n * g := by rw [hU', Matrix.one_mul]
      _ = g * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
      _ = g * JJ n := by rw [hG]
  have hc' := hc
  rw [← fromBlocks_toBlocks g] at hc'
  simp only [JJ, fromBlocks_multiply, Matrix.zero_mul, Matrix.one_mul, zero_add, add_zero,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, Matrix.mul_zero, neg_zero] at hc'
  rw [fromBlocks_inj] at hc'
  obtain ⟨h1, h2, -, -⟩ := hc'
  have hshape : g = kM (u1 g) (u2 g) := by
    conv_lhs => rw [← fromBlocks_toBlocks g]
    simp only [kM, u1, u2, h1, h2]
    congr 1 <;> match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring
  have hx : kM ((u1 g)ᴴ * u1 g) ((u2 g)ᴴ * u2 g) = kM 1 1 := by
    rw [← kM_mul, ← kM_conjTranspose, ← hshape, hU, kM_one]
  have e1 : (u1 g)ᴴ * u1 g = 1 := by
    have := congrArg u1 hx
    rwa [first_unitary_block_of_pair, first_unitary_block_of_pair] at this
  have e2 : (u2 g)ᴴ * u2 g = 1 := by
    have := congrArg u2 hx
    rwa [second_unitary_block_of_pair, second_unitary_block_of_pair] at this
  exact ⟨Matrix.mem_unitaryGroup_iff'.mpr e1, Matrix.mem_unitaryGroup_iff'.mpr e2, hshape⟩

theorem kIso : KIso := by
  intro n
  exact ⟨fun a b ha hb => kM_of_unitary a b ha hb, kM_mul, kM_one, fun a b => ⟨first_unitary_block_of_pair a b, second_unitary_block_of_pair a b⟩,
    kM_low, KR_shape⟩

end PositivityTheory.Rg.Sw.AbsSt.Proj
