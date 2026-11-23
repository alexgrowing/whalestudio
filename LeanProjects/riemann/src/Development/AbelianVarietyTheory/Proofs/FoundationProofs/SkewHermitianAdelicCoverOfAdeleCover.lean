import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValHalfInf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

noncomputable section

namespace GlobalTheory.Eis.Conv.CovSkew

theorem exists_delta (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    ∃ δ : E, σ δ = -δ ∧ ∀ z : E, ∃ a b : F, z = a • (1 : E) + b • δ := by
  obtain ⟨-, hc, h2, hσ⟩ := h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hnr : ¬ ComplexEmbedding.IsReal τ := IsTotallyComplex.complexEmbedding_not_isReal τ
  obtain ⟨x, hx⟩ : ∃ x, star (τ x) ≠ τ x := by
    by_contra hcon
    push Not at hcon
    apply hnr
    rw [ComplexEmbedding.isReal_iff]
    ext x
    exact hcon x
  have hδ : σ (x - σ x) = -(x - σ x) := by
    apply τ.injective
    rw [hσ, map_neg, map_sub, hσ, star_sub, star_star, neg_sub]
  have h0 : x - σ x ≠ 0 := by
    intro h0
    apply hx
    rw [← hσ, ← sub_eq_zero.mp h0]
  refine ⟨x - σ x, hδ, ?_⟩
  generalize x - σ x = δ at hδ h0
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg σ hst
    have hsm : ∀ (a : F) (z : E), σ (a • z) = a • σ z := fun a z => σ.toLinearMap.map_smul a z
    rw [map_add, hsm, hsm, map_one, hδ, map_zero, smul_neg] at h1
    have hs : (2 * s) • (1 : E) = 0 := by
      rw [two_mul, add_smul]; linear_combination hst + h1
    have hs0 : s = 0 := by simpa using hs
    refine ⟨hs0, ?_⟩
    rw [hs0, zero_smul, zero_add] at hst
    exact (smul_eq_zero.mp hst).resolve_right h0
  intro z
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp [h2])
  have hz : z ∈ Submodule.span F (Set.range ![(1 : E), δ]) := by rw [hsp]; trivial
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Submodule.mem_span_pair] at hz
  obtain ⟨a, b, hab⟩ := hz
  exact ⟨a, b, hab.symm⟩

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]

theorem exists_coords (δ : E) (h : ∀ z : E, ∃ a b : F, z = a • (1 : E) + b • δ) (z : R ⊗[F] E) :
    ∃ u v : R, z = u ⊗ₜ[F] (1 : E) + v ⊗ₜ[F] δ := by
  induction z with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul r e =>
    obtain ⟨a, b, rfl⟩ := h e
    exact ⟨a • r, b • r, by
      rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul]⟩
  | add x y hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    exact ⟨u + u', v + v', by simp only [TensorProduct.add_tmul]; abel⟩

def psi (δ : E) (a a' : R) : R ⊗[F] E := (a - a') • (1 : R ⊗[F] E) + (a + a') • ((1 : R) ⊗ₜ[F] δ)

theorem psi_eq (δ : E) (a a' : R) :
    psi δ a a' = (a - a') ⊗ₜ[F] (1 : E) + (a + a') ⊗ₜ[F] δ := by
  simp [psi, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']

theorem exists_psi [CharZero F] (σ : E →ₐ[F] E) (δ : E) (hδ : σ δ = -δ)
    (h : ∀ z : E, ∃ a b : F, z = a • (1 : E) + b • δ) {n : ℕ}
    (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (hS : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) S = -S) :
    ∃ T : Fin n → Fin n → R, ∀ i j, S i j = psi δ (T i j) (T j i) := by
  choose U V hUV using fun i j => exists_coords δ h (S i j)
  set c : R := algebraMap F R 2⁻¹ with hc
  have h2 : 2 * c = 1 := by
    rw [hc, ← map_ofNat (algebraMap F R) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  refine ⟨fun i j => c * c * (U i j - U j i + V i j + V j i), fun i j => ?_⟩
  have h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (S j i) = - S i j := congrFun (congrFun hS i) j
  have e1 : ∀ k l, S k l = U k l • (1 : R ⊗[F] E) + V k l • ((1 : R) ⊗ₜ[F] δ) := fun k l => by
    rw [hUV]; simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
  have e2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (S j i)
      = U j i • (1 : R ⊗[F] E) - V j i • ((1 : R) ⊗ₜ[F] δ) := by
    rw [hUV, map_add]
    change U j i ⊗ₜ[F] σ 1 + V j i ⊗ₜ[F] σ δ = _
    simp [hδ, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.tmul_neg,
      sub_eq_add_neg]
  rw [e2] at h1
  have e3 := e1 i j
  have h2' : 2 * algebraMap R (R ⊗[F] E) c = 1 := by
    rw [← map_ofNat (algebraMap R (R ⊗[F] E)) 2, ← map_mul, h2, map_one]
  unfold psi
  simp only [Algebra.smul_def, map_add, map_sub, map_mul] at h1 e3 ⊢
  generalize algebraMap R (R ⊗[F] E) = f at *
  generalize ((1 : R) ⊗ₜ[F] δ) = d at *
  linear_combination (f c) * e3 + (f c) * h1 - S i j * h2'
    - f c * (f (U i j) - f (U j i) + (f (V i j) + f (V j i)) * d) * h2'

theorem psi_split (δ : E) (x x' : F) (y y' t w w' : R) :
    psi δ (algebraMap F R x + y + t * w) (algebraMap F R x' + y' + t * w')
      = inclR (F := F) R ((x - x') • (1 : E) + (x + x') • δ) + psi δ y y'
        + algebraMap R (R ⊗[F] E) t * psi δ w w' := by
  have : inclR (F := F) R ((x - x') • (1 : E) + (x + x') • δ)
      = psi δ (algebraMap F R x) (algebraMap F R x') := by
    rw [psi_eq, ← map_sub, ← map_add, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.smul_tmul,
      ← TensorProduct.tmul_add]
    rfl
  rw [this]
  unfold psi
  simp only [Algebra.smul_def, map_add, map_sub, map_mul]
  ring

end

theorem cover_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (b C₀ : ℝ) (Ω₀ : Set (AF F)), IsCompact Ω₀ → (∀ m : ℕ, ∃ Y : Finset (AF F), (Y.card : ℝ) ≤ C₀ * b ^ m ∧ ∀ a : AF F, ∃ x : F, ∃ y ∈ Y, ∃ ω ∈ Ω₀, a = algebraMap F (AF F) x + y + (halfInf F).1 ^ m * ω) → ∀ n : ℕ, ∃ (Ω : Set (AF F ⊗[F] E)) (C : ℝ), IsCompact Ω ∧ ∀ m : Fin n → ℕ, ∃ Y : Finset (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ C * ∏ i, (b ^ 2) ^ (n * m i) ∧ ∀ S : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) S = -S → ∃ S₀ : Matrix (Fin n) (Fin n) E, ∃ y ∈ Y, ∃ ω : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), (∀ i j, ω i j ∈ Ω) ∧ S = S₀.map (inclR (F := F) (AF F)) + y + Matrix.diagonal (fun i => (halfE F E).1 ^ m i) * ω * Matrix.diagonal (fun i => (halfE F E).1 ^ m i) := by
  intro F E _ _ _ _ _ σ hσ b C₀ Ω₀ hΩ₀ hcov n
  classical
  obtain ⟨δ, hδ, hsp⟩ := exists_delta F E σ hσ
  choose Y hY hYc using hcov
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := isTopologicalRing_tens
  have hcont : Continuous fun p : AF F × AF F => psi (F := F) δ p.1 p.2 := by
    unfold psi
    fun_prop
  refine ⟨_, C₀ ^ (n * n), (hΩ₀.prod hΩ₀).image hcont, fun m => ?_⟩
  refine ⟨(Fintype.piFinset fun p : Fin n × Fin n => Y (m p.1 + m p.2)).image
    (fun y => Matrix.of fun i j => psi δ (y (i, j)) (y (j, i))), ?_, fun S hS => ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Fintype.card_piFinset, Nat.cast_prod]
    refine (Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun p _ => hY _)).trans (le_of_eq ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Finset.prod_pow_eq_pow_sum]
    congr 1
    simp only [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum, Fintype.sum_prod_type]
    congr 1
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, ← Finset.mul_sum]
    ring
  · obtain ⟨T, hT⟩ := exists_psi σ δ hδ hsp S hS
    choose x y hy ω hω hTe using fun i j => hYc (m i + m j) (T i j)
    refine ⟨Matrix.of fun i j => (x i j - x j i) • (1 : E) + (x i j + x j i) • δ, _,
      Finset.mem_image.mpr ⟨fun p => y p.1 p.2, Fintype.mem_piFinset.mpr fun p => hy _ _, rfl⟩,
      Matrix.of fun i j => psi δ (ω i j) (ω j i),
      fun i j => ⟨(ω i j, ω j i), ⟨hω _ _, hω _ _⟩, rfl⟩, ?_⟩
    ext i j
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hT,
      hTe i j, hTe j i, add_comm (m j) (m i), psi_split]
    have : (halfE F E).1 = algebraMap (AF F) (AF F ⊗[F] E) (halfInf F).1 := rfl
    rw [this, map_pow]
    simp only [Matrix.map_apply, Matrix.of_apply]
    ring

end GlobalTheory.Eis.Conv.CovSkew

end
