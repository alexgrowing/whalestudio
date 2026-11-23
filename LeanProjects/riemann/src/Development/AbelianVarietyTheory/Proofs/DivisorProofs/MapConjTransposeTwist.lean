import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix ComplexOrder

namespace GlobalTheory.QuotRational

theorem gram_of_quotMet {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (G : Matrix (Fin d) (Fin d) ℂ)
    (hG : IsUnit G.det) (P : Matrix (Fin d) (Fin n) ℂ) (D : Matrix (Fin n) (Fin d) ℂ) (h1 : G * P = Dᴴ * A)
    (h2 : (P * A⁻¹ * Pᴴ)⁻¹ = G) : Dᴴ * A * D = G := by
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hM : IsUnit (P * A⁻¹ * Pᴴ).det := by
    by_contra h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h] at h2
    subst h2
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact h (by simp)
    · have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      simp at hG
  have h3 : G * (P * A⁻¹ * Pᴴ) = 1 := by rw [← h2]; exact Matrix.nonsing_inv_mul _ hM
  have h4 : Dᴴ * Pᴴ = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc Dᴴ, Matrix.mul_nonsing_inv _ hAu,
      Matrix.mul_one] at h3
    exact h3
  have h5 : P * D = 1 := by
    have := congrArg Matrix.conjTranspose h4
    simpa [Matrix.conjTranspose_mul] using this
  rw [← h1, Matrix.mul_assoc, h5, Matrix.mul_one]

theorem eq_of_gram {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (G : Matrix (Fin d) (Fin d) ℂ)
    (C D : Matrix (Fin n) (Fin d) ℂ) (h1 : Dᴴ * A * D = G) (h2 : Cᴴ * A * C = G) (h3 : Dᴴ * A * C = G) : C = D := by
  have hG : Gᴴ = G := by
    rw [← h1]; simp [Matrix.conjTranspose_mul, hA.isHermitian.eq, Matrix.mul_assoc]
  have h4 : Cᴴ * A * D = G := by
    have := congrArg Matrix.conjTranspose h3
    rw [hG] at this
    simpa [Matrix.conjTranspose_mul, hA.isHermitian.eq, Matrix.mul_assoc] using this
  have h5 : (C - D)ᴴ * A * (C - D) = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, h1, h2, h3, h4]
    simp
  have h6 : ∀ x, (C - D) *ᵥ x = 0 := by
    intro x
    by_contra hx
    have := hA.dotProduct_mulVec_pos hx
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h5] at this
    simp at this
  rw [← sub_eq_zero]
  ext i j
  simpa using congrFun (h6 (Pi.single j 1)) i

variable {K : Type} [Field K] [StarRing K]

theorem map_conjTranspose_twist (σ : K →+* ℂ) {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) :
    (Eᴴ).map σ = (E.map (twist σ))ᴴ := by
  ext a i
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, twist, RingHom.comp_apply, starRingEnd_apply, star_star]

theorem twist_twist (σ : K →+* ℂ) : twist (twist σ) = σ := by
  ext a
  simp [twist]

theorem map_twist_of_mem (σ : K →+* ℂ) {n d : ℕ} (H : Matrix (Fin n) (Fin d) K) (hH : ∀ i j, H i j ∈ cmMax K) :
    H.map (twist σ) = H.map σ := by
  ext i j
  have : σ (star (H i j)) = starRingEnd ℂ (σ (H i j)) := hH i j σ
  simp only [Matrix.map_apply, twist, RingHom.comp_apply, starRingEnd_apply (R := K), this, Complex.conj_conj]

theorem entries_mem_cmMax [NumberField K] {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (hH : ∀ i j, H i j ∈ cmMax K)
    (hpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef) (E : Matrix (Fin n) (Fin d) K)
    (Pr : Matrix (Fin d) (Fin n) K) (hP : IsOrthProj H E Pr)
    (hR : IsRatHerm (cmMax K) (Eᴴ * H * E) (quotFrame Pr H)) : ∀ i a, E i a ∈ cmMax K := by
  have hsurj : Function.Surjective Pr.mulVec :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨E, hP.1⟩
  have hGP : Eᴴ * H * E * Pr = Eᴴ * H := by
    have h2 := hP.2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2
    rw [Matrix.mul_assoc (Eᴴ * H), ← h2]
  have hv : ∀ v : InfinitePlace K, (Eᴴ).map v.embedding * H.map v.embedding * E.map (twist v.embedding) =
      (Eᴴ * H * E).map v.embedding := by
    intro v
    have hq := (quotFrameIsQuot K n d H hpos Pr hsurj v).2
    have hr := (hR.2 v).2
    rw [map_conjTranspose_twist]
    refine gram_of_quotMet _ (hpos v) _ ?_ (Pr.map v.embedding) _ ?_ (hq.symm.trans hr)
    · rw [← hr]
      exact (Matrix.isUnit_iff_isUnit_det _).mp (metOfSpec d _ (hR.2 v).1).1.isUnit
    · rw [← Matrix.map_mul, hGP, Matrix.map_mul, map_conjTranspose_twist]
  have hall : ∀ σ : K →+* ℂ, (Eᴴ).map σ * H.map σ * E.map (twist σ) = (Eᴴ * H * E).map σ := by
    intro σ
    rcases InfinitePlace.mk_eq_iff.mp (InfinitePlace.mk_embedding (InfinitePlace.mk σ)) with h | h
    · rw [← h]; exact hv _
    · have h1 := congrArg (fun M => M.map (starRingEnd ℂ)) (hv (InfinitePlace.mk σ))
      simp only [Matrix.map_mul (f := starRingEnd ℂ), Matrix.map_map] at h1
      rw [← h]
      exact h1
  have hE : ∀ v : InfinitePlace K, E.map v.embedding = E.map (twist v.embedding) := by
    intro v
    refine eq_of_gram _ (hpos v) ((Eᴴ * H * E).map v.embedding) _ _ ?_ ?_ ?_
    · rw [← map_conjTranspose_twist]; exact hall _
    · have h1 := hall (twist v.embedding)
      rwa [map_conjTranspose_twist, twist_twist, map_twist_of_mem _ H hH, map_twist_of_mem _ _ hR.1] at h1
    · rw [Matrix.map_mul, Matrix.map_mul, map_conjTranspose_twist]
  intro i a σ
  have h1 := congrFun (congrFun (hE (InfinitePlace.mk σ)) i) a
  simp only [Matrix.map_apply, twist, RingHom.comp_apply, starRingEnd_apply] at h1
  rcases InfinitePlace.mk_eq_iff.mp (InfinitePlace.mk_embedding (InfinitePlace.mk σ)) with h | h
  · rw [h] at h1
    rw [h1, starRingEnd_apply, star_star]
  · rw [← h, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, h1]
    simp

theorem fE_mem_cmMax : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (v0 : InfinitePlace K) (s : ℕ), BlockHyp B ℓ v0 s → IsRatHerm (cmMax K) (B.HZ ℓ Z) (B.XQ ℓ Z) → ∀ a k, B.fE ℓ Z a k ∈ cmMax K := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z v0 s h hR a k
  have hE := entries_mem_cmMax (B.HV ℓ) (BlockDat.HV_rat h.conj h.ok h.irr) (BlockDat.HV_pos h.conj h.ok h.irr)
    (B.zE ℓ Z) (B.Pq ℓ Z) (BlockDat.Pq_orth h.conj h.ok h.irr) hR
  rw [BlockDat.fE, Matrix.mul_apply]
  exact Subfield.sum_mem _ fun j _ => Subfield.mul_mem _ (BlockDat.vE_rat h.conj h.ok h.irr a j) (hE j k)

end GlobalTheory.QuotRational
