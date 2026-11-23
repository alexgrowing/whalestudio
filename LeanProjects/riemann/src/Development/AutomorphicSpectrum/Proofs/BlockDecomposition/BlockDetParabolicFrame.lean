import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDeterminantLaw
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviDecompOfBlockDet

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelFrameDet

theorem mul_fromRows_apply {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β]
    (M : Matrix (β ⊕ β) (β ⊕ β) R) (C : Matrix (β ⊕ β) β R) (hC : C = Matrix.fromRows (1 : Matrix β β R) 0)
    (i : β ⊕ β) (j : β) : (M * C : Matrix (β ⊕ β) β R) i j = M i (Sum.inl j) := by
  subst hC
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem corner_conj {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β]
    (B P Bi : Matrix (β ⊕ β) (β ⊕ β) R) (T Ti s : Matrix β β R) (C D : Matrix (β ⊕ β) β R)
    (hC : C = Matrix.fromRows (1 : Matrix β β R) 0)
    (hBi : Bi * B = 1) (hTi : T * Ti = 1)
    (hB : (B * C : Matrix (β ⊕ β) β R) = (D * T : Matrix (β ⊕ β) β R))
    (hP : (P * D : Matrix (β ⊕ β) β R) = (D * s : Matrix (β ⊕ β) β R)) (r c : β) :
    (Bi * P * B) (Sum.inl r) (Sum.inl c) = (Ti * s * T) r c := by
  have hD : D = B * C * Ti := by rw [hB, Matrix.mul_assoc, hTi, Matrix.mul_one]
  have key : Bi * P * B * C = C * (Ti * s * T) := by
    calc Bi * P * B * C = Bi * ((P * D) * T) := by
          rw [Matrix.mul_assoc (Bi * P) B C, hB]; simp only [Matrix.mul_assoc]
      _ = Bi * (D * s * T) := by rw [hP]
      _ = Bi * (B * C * Ti * s * T) := by rw [← hD]
      _ = (Bi * B) * C * (Ti * s * T) := by simp only [Matrix.mul_assoc]
      _ = C * (Ti * s * T) := by rw [hBi, Matrix.one_mul]
  have h1 := congrFun (congrFun key (Sum.inl r)) c
  rw [mul_fromRows_apply _ C hC] at h1
  rw [h1, hC, Matrix.fromRows_mul, Matrix.fromRows_apply_inl, Matrix.one_mul]

theorem bdet_frameEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n), ∀ (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E) (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (t₀ : GL (Fin n) E), b.1.toCols₁ = diagCols (Fin n) * t₀.1 → ∀ (p : G2 σ Y) (t : GL (Fin n) (AE F E)), IsPar p t → bdet (Sum.inl '' (Set.univ : Set (Fin n))) (frameEquiv χ ε b hb p).1 = Matrix.GeneralLinearGroup.det t := by
  intro F E _ _ _ _ _ σ n Y χ ε b hb t₀ ht₀ p t hp
  obtain ⟨t₀A, ht₀A⟩ : ∃ g : GL (Fin n) (AE F E),
      g = Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) t₀ := ⟨_, rfl⟩
  have hent : ∀ r c : Fin n, (((frameEquiv χ ε b hb p).1 : GL (Fin n ⊕ Fin n) (AE F E)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (Sum.inl r) (Sum.inl c) =
      ((t₀A⁻¹ * t * t₀A : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) r c := by
    intro r c
    rw [frameEquiv_val]
    simp only [Units.val_mul]
    refine corner_conj _ _ _ _ _ _ _ _ rfl (Units.inv_mul _) (Units.mul_inv _) ?_ hp r c
    refine Matrix.ext fun i j => ?_
    rw [mul_fromRows_apply _ _ rfl, bA_val]
    have hij := congrFun (congrFun ht₀ i) j
    rw [Matrix.toCols₁_apply] at hij
    subst ht₀A
    show inclR (F := F) (E := E) (AF F) (b.1 i (Sum.inl j)) = _
    rw [hij]
    cases i with
    | inl r' =>
      show inclR (F := F) (E := E) (AF F)
        (∑ k, Matrix.fromRows (1 : Matrix (Fin n) (Fin n) E) 1 (Sum.inl r') k * t₀.1 k j) = _
      simp [diagCols, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type]
    | inr r' =>
      show inclR (F := F) (E := E) (AF F)
        (∑ k, Matrix.fromRows (1 : Matrix (Fin n) (Fin n) E) 1 (Sum.inr r') k * t₀.1 k j) = _
      simp [diagCols, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type]
  rw [GlobalTheory.CompanionTheory.RgEisLevi.bdet_inl Set.univ _ (t₀A⁻¹ * t * t₀A) hent, GlobalTheory.CompanionTheory.RgEis.bdet_univ,
    map_mul, map_mul, mul_comm, ← mul_assoc, map_inv, mul_inv_cancel, one_mul]

end GlobalTheory.CompanionTheory.SiegelFrameDet
