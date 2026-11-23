import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne
open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls

noncomputable section
namespace GlobalTheory.UCls
open scoped TensorProduct
open IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem isKM_mul {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    {k k' : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) (hk' : IsKM c G L M k') :
    IsKM c G L M (k * k') := by
  obtain ⟨⟨hd, hh⟩, h2, h3⟩ := hk
  obtain ⟨⟨hd', hh'⟩, h2', h3'⟩ := hk'
  refine ⟨⟨by rw [det_mul]; exact hd.mul hd', fun x y => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · rw [← mulVec_mulVec, ← mulVec_mulVec, hh, hh']
  · obtain ⟨y2, hy2, e2⟩ := h2' x hx
    have hx' : k' *ᵥ x ∈ hat F L := by
      have : k' *ᵥ x = x + M • y2 := by rw [← e2]; abel
      rw [this]; exact add_mem hx (nsmul_mem hy2 _)
    obtain ⟨y1, hy1, e1⟩ := h2 _ hx'
    refine ⟨y1 + y2, add_mem hy1 hy2, ?_⟩
    rw [← mulVec_mulVec, smul_add, ← e1, ← e2]; abel
  · obtain ⟨y1, hy1, e1⟩ := h3 x hx
    obtain ⟨y2, hy2, e2⟩ := h3' y1 hy1
    exact ⟨y2, hy2, by rw [← mulVec_mulVec, e2, e1]⟩

theorem isKM_inv {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) :
    IsKM c G L M k⁻¹ := by
  obtain ⟨⟨hd, hh⟩, h2, h3⟩ := hk
  have hkk : k * k⁻¹ = 1 := mul_nonsing_inv k hd
  have hkk' : k⁻¹ * k = 1 := nonsing_inv_mul k hd
  have hmem : ∀ x ∈ hat F L, k *ᵥ x ∈ hat F L := by
    intro x hx
    obtain ⟨y, hy, e⟩ := h2 x hx
    have : k *ᵥ x = x + M • y := by rw [← e]; abel
    rw [this]; exact add_mem hx (nsmul_mem hy _)
  refine ⟨⟨?_, fun x y => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · rw [det_nonsing_inv]; exact hd.ringInverse
  · rw [← hh, mulVec_mulVec, mulVec_mulVec, hkk, one_mulVec, one_mulVec]
  · obtain ⟨y, hy, e⟩ := h3 x hx
    obtain ⟨z, hz, ez⟩ := h2 y hy
    refine ⟨-z, neg_mem hz, ?_⟩
    have : k⁻¹ *ᵥ x = y := by rw [← e, mulVec_mulVec, hkk', one_mulVec]
    rw [this, ← e, smul_neg, ← ez]; abel
  · exact ⟨k *ᵥ x, hmem x hx, by rw [mulVec_mulVec, hkk', one_mulVec]⟩

theorem tEquiv_refl (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) (t : RA F E) :
    TEquiv c G L M t t :=
  ⟨1, by simp, 1, isKM_one c G L M, by simp [Algebra.TensorProduct.one_def.symm]⟩

theorem tEquiv_symm {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ} {t t' : RA F E}
    (h : TEquiv c G L M t t') : TEquiv c G L M t' t := by
  obtain ⟨u, hu, k, hk, rfl⟩ := h
  have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one hu
  refine ⟨u⁻¹, by rw [map_inv₀, ← mul_inv, hu, inv_one], k⁻¹, isKM_inv hk, ?_⟩
  have hd : IsUnit k.det := hk.1.1
  have e1 : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hu0, Algebra.TensorProduct.one_def]
  have e2 : k.det * k⁻¹.det = 1 := by rw [det_nonsing_inv, Ring.mul_inverse_cancel _ hd]
  calc t = (((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u)) * t * (k.det * k⁻¹.det) := by
        rw [e1, e2, one_mul, mul_one]
    _ = _ := by ring

theorem tEquiv_trans {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ} {t t' t'' : RA F E}
    (h : TEquiv c G L M t t') (h' : TEquiv c G L M t' t'') : TEquiv c G L M t t'' := by
  obtain ⟨u, hu, k, hk, rfl⟩ := h
  obtain ⟨u', hu', k', hk', rfl⟩ := h'
  refine ⟨u' * u, ?_, k * k', isKM_mul hk hk', ?_⟩
  · rw [map_mul]
    calc u' * u * (c u' * c u) = (u' * c u') * (u * c u) := by ring
      _ = 1 := by rw [hu, hu', one_mul]
  · have e : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (u' * u)) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u') * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [det_mul, e]; ring

theorem tEquiv_of_eqvGen {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    (a b : {t : RA F E // IsTA c t})
    (h : Relation.EqvGen (fun a b : {t : RA F E // IsTA c t} => TEquiv c G L M a.1 b.1) a b) :
    TEquiv c G L M a.1 b.1 :=
  (Equivalence.eqvGen_iff (r := fun a b : {t : RA F E // IsTA c t} => TEquiv c G L M a.1 b.1)
    ⟨fun a => tEquiv_refl c G L M a.1, fun h => tEquiv_symm h, fun h h' => tEquiv_trans h h'⟩).1 h

end GlobalTheory.UCls
end

theorem GlobalTheory.UCls.torus_eqvGen_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t}), Relation.EqvGen (fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} => TEquiv (IsCMField.complexConj E) G L M a.1 b.1) a b → TEquiv (IsCMField.complexConj E) G L M a.1 b.1 :=
  by intro E _ _ _ r M G L a b h; exact GlobalTheory.UCls.tEquiv_of_eqvGen a b h
