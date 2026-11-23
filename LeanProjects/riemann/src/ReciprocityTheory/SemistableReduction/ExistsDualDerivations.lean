import Mathlib
import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
import ReciprocityTheory.SemistableReduction.AlgebraicIndependentOfDerivations

namespace ReciprocityTheory.MultiplicativeHeights

namespace DerivationAlgebraicIndependence

open MvPolynomial

section CoeffDer

variable {K Ω σ : Type*} [CommRing K] [CommRing Ω] [Algebra K Ω]

noncomputable def coeffMap (δ : Derivation K Ω Ω) (P : MvPolynomial σ Ω) : MvPolynomial σ Ω :=
  ∑ n ∈ P.support, monomial n (δ (coeff n P))

theorem coeff_coeffMap (δ : Derivation K Ω Ω) (P : MvPolynomial σ Ω) (n : σ →₀ ℕ) :
    coeff n (coeffMap δ P) = δ (coeff n P) := by
  classical
  unfold coeffMap
  rw [coeff_sum]
  by_cases h : n ∈ P.support
  · rw [Finset.sum_eq_single n]
    · rw [coeff_monomial, if_pos rfl]
    · intro b _ hb
      rw [coeff_monomial, if_neg hb]
    · intro hn
      exact absurd h hn
  · have h0 : coeff n P = 0 := by
      by_contra hc
      exact h (mem_support_iff.mpr hc)
    rw [h0, map_zero]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [coeff_monomial, if_neg]
    rintro rfl
    exact h hb

theorem coeffMap_monomial (δ : Derivation K Ω Ω) (n : σ →₀ ℕ) (a : Ω) :
    coeffMap δ (monomial n a) = monomial n (δ a) := by
  classical
  ext m
  rw [coeff_coeffMap, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

theorem coeffMap_add (δ : Derivation K Ω Ω) (P Q : MvPolynomial σ Ω) :
    coeffMap δ (P + Q) = coeffMap δ P + coeffMap δ Q := by
  ext m
  simp only [coeff_add, coeff_coeffMap, map_add]

theorem coeffMap_smul (δ : Derivation K Ω Ω) (k : K) (P : MvPolynomial σ Ω) :
    coeffMap δ (k • P) = k • coeffMap δ P := by
  ext m
  rw [coeff_coeffMap, coeff_smul, coeff_smul, coeff_coeffMap,
    Derivation.map_smul]

theorem coeffMap_mul (δ : Derivation K Ω Ω) (P Q : MvPolynomial σ Ω) :
    coeffMap δ (P * Q) = P * coeffMap δ Q + Q * coeffMap δ P := by
  induction P using MvPolynomial.induction_on'
  · rename_i u a
    induction Q using MvPolynomial.induction_on'
    · rename_i v b
      rw [monomial_mul, coeffMap_monomial, coeffMap_monomial,
        coeffMap_monomial, monomial_mul, monomial_mul, Derivation.leibniz, smul_eq_mul,
        smul_eq_mul, map_add, add_comm v u]
    · rename_i p q hp hq
      simp only [mul_add, add_mul, coeffMap_add, hp, hq]
      ring
  · rename_i p q hp hq
    simp only [add_mul, mul_add, coeffMap_add, hp, hq]
    ring

noncomputable def coeffDer (δ : Derivation K Ω Ω) :
    Derivation K (MvPolynomial σ Ω) (MvPolynomial σ Ω) :=
  Derivation.mk' { toFun := coeffMap δ, map_add' := coeffMap_add δ, map_smul' := coeffMap_smul δ }
    (fun P Q => by simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]; exact coeffMap_mul δ P Q)

theorem coeffDer_apply (δ : Derivation K Ω Ω) (P : MvPolynomial σ Ω) :
    coeffDer δ P = coeffMap δ P := rfl

theorem coeffDer_C (δ : Derivation K Ω Ω) (a : Ω) :
    coeffDer (σ := σ) δ (C a) = C (δ a) := by
  simp only [coeffDer_apply, C_apply, coeffMap_monomial]

theorem coeffDer_X (δ : Derivation K Ω Ω) (v : σ) : coeffDer δ (X v : MvPolynomial σ Ω) = 0 := by
  rw [coeffDer_apply]
  show coeffMap δ (monomial (Finsupp.single v 1) 1) = 0
  rw [coeffMap_monomial, Derivation.map_one_eq_zero, map_zero]

end CoeffDer

private theorem exists_linearMap_dual_of_linearIndependent {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    {D : ℕ} (v : Fin D → V) (hli : LinearIndependent Ω v) (a : Fin D) :
    ∃ g : V →ₗ[Ω] Ω, ∀ b, g (v b) = if a = b then 1 else 0 := by
  open Module in
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Basis.span hli).coord a)
  refine ⟨g, fun b => ?_⟩
  have hmem : v b ∈ Submodule.span Ω (Set.range v) := Submodule.subset_span ⟨b, rfl⟩
  have h1 : g (v b) = (Basis.span hli).coord a ⟨v b, hmem⟩ := LinearMap.congr_fun hg ⟨v b, hmem⟩
  have h2 : (⟨v b, hmem⟩ : Submodule.span Ω (Set.range v)) = Basis.span hli b :=
    Subtype.ext (by rw [Basis.span_apply])
  rw [h1, h2, Basis.coord_apply, Basis.repr_self]
  by_cases h : a = b
  · subst h
    simp
  · simp [h]

theorem exists_dual_derivations {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
    (x : Fin m → Ω) (J : Fin D → Fin m)
    (hli : LinearIndependent Ω fun a => KaehlerDifferential.D K Ω (x (J a))) :
    ∃ δ : Fin D → Derivation K Ω Ω, ∀ a b, δ a (x (J b)) = if a = b then 1 else 0 := by
  choose g hg using exists_linearMap_dual_of_linearIndependent (fun a => KaehlerDifferential.D K Ω (x (J a))) hli
  exact ⟨fun a => (g a).compDer (KaehlerDifferential.D K Ω), fun a b => hg a b⟩

noncomputable def yPoly {Ω : Type*} [CommRing Ω] {D m : ℕ} (x : Fin m → Ω) (b : Fin D) :
    MvPolynomial (SVars D m) Ω :=
  -∑ k, X (Sum.inr (b.succ, k)) * C (x k)

noncomputable def gFam {Ω : Type*} [CommRing Ω] {D m : ℕ} (x : Fin m → Ω) :
    SVars D m ⊕ Fin D → MvPolynomial (SVars D m) Ω :=
  Sum.elim X (yPoly x)

private theorem coeffDer_linearCombinationPoly_apply {K Ω : Type*} [CommRing K] [CommRing Ω]
    [Algebra K Ω] {D m : ℕ} (δ : Derivation K Ω Ω) (x : Fin m → Ω) (b : Fin D) :
    coeffDer (σ := ReciprocityTheory.MultiplicativeHeights.SVars D m) δ (yPoly x b) =
      -∑ k, X (Sum.inr (b.succ, k)) * C (δ (x k)) := by
  simp only [yPoly, map_neg, map_sum, Derivation.leibniz, coeffDer_X,
    coeffDer_C, smul_eq_mul, mul_zero, add_zero]

private theorem restrictScalars_pderiv_apply {K Ω σ : Type*} [CommRing K] [CommRing Ω]
    [Algebra K Ω] (w : σ) (f : MvPolynomial σ Ω) :
    ((pderiv w : Derivation Ω (MvPolynomial σ Ω) (MvPolynomial σ Ω)).restrictScalars K) f =
      pderiv w f := by
  exact congrFun (Derivation.coe_restrictScalars K _) f

set_option maxHeartbeats 800000 in

private theorem det_sum_X_mul_C_ne_zero_of_dual_family {Ω : Type*} [Field Ω] {D m : ℕ} (y : Fin D → Fin m → Ω)
    (J : Fin D → Fin m) (hy : ∀ a b, y a (J b) = if a = b then 1 else 0) :
    (Matrix.of fun a b : Fin D =>
      ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (y a k)).det ≠ 0 := by
  classical
  obtain ⟨p, hp⟩ : ∃ p : ReciprocityTheory.MultiplicativeHeights.SVars D m → Ω, ∀ (b : Fin D) (k : Fin m),
      p (Sum.inr (b.succ, k)) = if k = J b then 1 else 0 :=
    ⟨Sum.elim (fun _ => 0)
      (fun q => Fin.cases (motive := fun _ => Ω) 0 (fun b => if q.2 = J b then 1 else 0) q.1),
      fun b k => by simp⟩
  intro h0
  have hmap : (eval p).mapMatrix (Matrix.of fun a b : Fin D =>
      ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (y a k)) = 1 := by
    ext a b
    simp [RingHom.mapMatrix_apply, hp, hy, Matrix.one_apply]
  have h1 := RingHom.map_det (eval p) (Matrix.of fun a b : Fin D =>
      ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (y a k))
  rw [h0, map_zero, hmap, Matrix.det_one] at h1
  exact zero_ne_one h1

set_option maxHeartbeats 800000 in

theorem gFam_indep {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] {D m : ℕ}
    (x : Fin m → Ω) (J : Fin D → Fin m) (δ : Fin D → Derivation K Ω Ω)
    (hδ : ∀ a b, δ a (x (J b)) = if a = b then 1 else 0) :
    AlgebraicIndependent K (gFam (D := D) x) := by
  classical
  have hz_inl : ∀ w, gFam (D := D) x (Sum.inl w) = X w := fun _ => rfl
  have hz_inr : ∀ b, gFam (D := D) x (Sum.inr b) = yPoly x b :=
    fun _ => rfl
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin D) (Fin D) (MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω),
      N = Matrix.of fun a b : Fin D =>
        ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (δ a (x k)) :=
    ⟨_, rfl⟩
  have hNe : ∀ a b, N a b =
      ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (δ a (x k)) := by
    intro a b
    rw [hN]
    rfl
  have hcd : ∀ a b, coeffDer (σ := ReciprocityTheory.MultiplicativeHeights.SVars D m) (δ a) (yPoly x b) =
      -N a b := by
    intro a b
    rw [hNe, coeffDer_linearCombinationPoly_apply]
  have hdet : N.det ≠ 0 := by
    rw [hN]
    exact det_sum_X_mul_C_ne_zero_of_dual_family (fun a k => δ a (x k)) J hδ
  refine algebraicIndependent_of_derivations (gFam (D := D) x)
    (Sum.elim (fun w : ReciprocityTheory.MultiplicativeHeights.SVars D m => (pderiv w : Derivation Ω (MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω)
        (MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω)).restrictScalars K)
      (fun a : Fin D => coeffDer (σ := ReciprocityTheory.MultiplicativeHeights.SVars D m) (δ a))) ?_
  intro c hc
  have hmv : Matrix.mulVec N (fun b => c (Sum.inr b)) = 0 := by
    funext a
    have h1 := hc (Sum.inr a)
    simp only [Sum.elim_inr, Fintype.sum_sum_type, hz_inl, hz_inr, coeffDer_X, mul_zero,
      Finset.sum_const_zero, zero_add, hcd, mul_neg, Finset.sum_neg_distrib, neg_eq_zero] at h1
    show ∑ b, N a b * c (Sum.inr b) = 0
    exact (Finset.sum_congr rfl fun b _ => mul_comm (N a b) (c (Sum.inr b))).trans h1
  have hinr : ∀ b, c (Sum.inr b) = 0 := fun b =>
    congr_fun (Matrix.eq_zero_of_mulVec_eq_zero hdet hmv) b
  intro i
  rcases i with w | b
  · have h2 := hc (Sum.inl w)
    rw [Fintype.sum_sum_type] at h2
    simp only [Sum.elim_inl, hinr, zero_mul, Finset.sum_const_zero, add_zero,
      restrictScalars_pderiv_apply, hz_inl] at h2
    rw [Finset.sum_eq_single w] at h2
    · rw [pderiv_X_self, mul_one] at h2
      exact h2
    · intro w' _ hw'
      rw [pderiv_X_of_ne hw', mul_zero]
    · intro h
      exact absurd (Finset.mem_univ w) h
  · exact hinr b

def eIdx (D m : ℕ) (p : Fin (D + 1) × Fin (m + 1)) : SVars D m ⊕ Fin D :=
  Fin.cases (motive := fun _ => SVars D m ⊕ Fin D)
    (Fin.cases (motive := fun _ => SVars D m ⊕ Fin D) (Sum.inl (Sum.inl ())) Sum.inr p.1)
    (fun j => Sum.inl (Sum.inr (p.1, j))) p.2

theorem eIdx_injective (D m : ℕ) : Function.Injective (eIdx D m) := by
  rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
  induction j₁ using Fin.cases <;> induction j₂ using Fin.cases <;>
    induction i₁ using Fin.cases <;> induction i₂ using Fin.cases <;>
    simp_all [eIdx]

theorem sImage_eq {Ω : Type} [Field Ω] {D m : ℕ} (x : Fin m → Ω) (p : Fin (D + 1) × Fin (m + 1)) :
    sImage (D := D) x p =
      algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) (gFam x (eIdx D m p)) := by
  rcases p with ⟨i, j⟩
  induction j using Fin.cases <;> induction i using Fin.cases <;>
    simp [ReciprocityTheory.MultiplicativeHeights.sImage, eIdx, gFam, yPoly]

end DerivationAlgebraicIndependence

end ReciprocityTheory.MultiplicativeHeights
