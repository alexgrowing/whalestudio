import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference

open AlgebraicGeometry CategoryTheory Matrix
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

namespace N1

section

variable {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] {r : ℕ}

theorem mat_unique {b₀ : Fin r → V} (h₀ : LinearIndependent Ω b₀) {T T' : Matrix (Fin r) (Fin r) Ω}
    (h : ∀ k, ∑ k', T k' k • b₀ k' = ∑ k', T' k' k • b₀ k') : T = T' := by
  ext k' k
  exact (Fintype.linearIndependent_iffₛ.1 h₀) (fun a => T a k) (fun a => T' a k) (h k) k'

theorem mat_comp {b₀ b b' : Fin r → V} {T A : Matrix (Fin r) (Fin r) Ω}
    (h : ∀ k, b k = ∑ k', T k' k • b₀ k') (h' : ∀ k, b' k = ∑ k', A k' k • b k') (k : Fin r) :
    b' k = ∑ k', (T * A) k' k • b₀ k' := by
  rw [h' k]
  simp only [h, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem exists_mat (R : Subring Ω) {b b' : Fin r → V} (h : ∀ k, b' k ∈ Submodule.span R (Set.range b)) :
    ∃ A : Matrix (Fin r) (Fin r) Ω, (∀ k, b' k = ∑ k', A k' k • b k') ∧ A.det ∈ R := by
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun R).1 (h k)
  refine ⟨R.subtype.mapMatrix (Matrix.of fun k' k => c k k'), fun k => ?_, ?_⟩
  · rw [← hc k]; rfl
  · rw [← RingHom.map_det]; exact SetLike.coe_mem _

theorem det_ne_zero {b₀ b : Fin r → V} {T : Matrix (Fin r) (Fin r) Ω} (hb : LinearIndependent Ω b)
    (h : ∀ k, b k = ∑ k', T k' k • b₀ k') : T.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hT⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  refine hv (funext (Fintype.linearIndependent_iff.1 hb v ?_))
  simp only [h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k' _ => ?_
  rw [← Finset.sum_smul]
  have := congrFun hT k'
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
  rw [show ∑ i, v i * T k' i = 0 from by rw [← this]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _, zero_smul]

end

end N1

open N1

theorem determinant_lattice_generator : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (b₀ b : Fin r → V) (T : Matrix (Fin r) (Fin r) Ω) (p : Cpt ξ), LinearIndependent Ω b₀ → L.IsFrameAt b p → (∀ k, b k = ∑ k', T k' k • b₀ k') → (detLat L b₀).IsGenAt p T.det := by
  intro X Ω _ ξ V _ _ L r b₀ b T p h₀ hb hT
  refine ⟨det_ne_zero hb.1 hT, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b', T', hb', hT', rfl⟩
    obtain ⟨A, hA, hd⟩ := exists_mat (regAt ξ p) (b := b) (b' := b') fun k => by
      rw [← hb.2, hb'.2]; exact Submodule.subset_span ⟨k, rfl⟩
    have e : T' = T * A := mat_unique h₀ fun k => by rw [← hT' k, ← mat_comp hT hA k]
    rw [e, Matrix.det_mul, mul_comm]
    exact Submodule.mem_span_singleton.2 ⟨⟨A.det, hd⟩, rfl⟩
  · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 (SncPiece.det_mem_detLat hb hT))

end LevelTowerAlt
