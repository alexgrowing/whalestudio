import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetChangeOfBasesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAevalOrthogonalRangeUnitarySelfReciprocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetNeZeroOfKerOrthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryConjMapsKerAevalBasisAndGramStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.KapSignMul

variable {K : Type} [Field K]

theorem ordL_mul [Valued K (WithZero (Multiplicative ℤ))] {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hxy' : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
  unfold ordL
  rw [dif_neg hx', dif_neg hy', dif_neg hxy']
  have : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, Valuation.map_mul]
  rw [this, toAdd_mul]
  ring

theorem sign_norm [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    {d : K} (hd : d ≠ 0) (x : K) : (-1 : ℂ) ^ ordL (σ d * d * x) = (-1 : ℂ) ^ ordL x := by
  by_cases hx : x = 0
  · simp [hx]
  have hσd : σ d ≠ 0 := (map_ne_zero σ).2 hd
  have hσo : ordL (σ d) = ordL d := by
    unfold ordL
    simp only [hσ]
  rw [ordL_mul (mul_ne_zero hσd hd) hx, ordL_mul hσd hd, hσo, zpow_add₀ (by norm_num), ← two_mul,
    (even_two_mul (ordL d)).neg_one_zpow, one_mul]

theorem li_coe {n : ℕ} {W : Submodule K (Fin n → K)} {ι : Type} (b : Module.Basis ι K W) :
    LinearIndependent K (fun i => (b i : Fin n → K)) :=
  b.linearIndependent.map' W.subtype W.ker_subtype

theorem span_coe {n : ℕ} {W : Submodule K (Fin n → K)} {ι : Type} (b : Module.Basis ι K W) :
    Submodule.span K (Set.range fun i => (b i : Fin n → K)) = W := by
  have : (Set.range fun i => (b i : Fin n → K)) = W.subtype '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem gram_change (σ : K →+* K) {n : ℕ} (W : Submodule K (Fin n → K)) {ι ι' : Type} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι'] (u : ι → Fin n → K) (u' : ι' → Fin n → K) (hu : LinearIndependent K u)
    (hsu : Submodule.span K (Set.range u) = W) (hu' : LinearIndependent K u')
    (hsu' : Submodule.span K (Set.range u') = W) :
    ∃ d : K, d ≠ 0 ∧ (Matrix.of fun i j => ∑ k, σ (u' i k) * u' j k).det =
      σ d * d * (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det :=
  GlobalTheory.T.gram_det_change_of_basis' σ W u u' hu hsu hu' hsu'

theorem csr_orth (σ : K →+* K) {n : ℕ} (γ : Matrix (Fin n) (Fin n) K) (hγ : (γ.map σ)ᵀ * γ = 1) (Q : K[X])
    (hQ : C (σ (Q.coeff 0)) * Q = (Q.map σ).reverse) (x z : Fin n → K) (hx : aeval γ Q *ᵥ x = 0) :
    ∑ k, σ ((aeval γ Q *ᵥ z) k) * x k = 0 :=
  GlobalTheory.T.ker_aeval_orthogonal_range_unitary_selfReciprocal σ γ hγ Q hQ x z hx

theorem gram_ne_zero (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : ι → Fin n → K) (hu : LinearIndependent K u)
    (hsu : Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' A))
    (horth : ∀ x z, A *ᵥ x = 0 → ∑ k, σ ((A *ᵥ z) k) * x k = 0)
    (hdec : ∀ v, ∃ z y, A *ᵥ y = 0 ∧ v = A *ᵥ z + y) :
    (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det ≠ 0 :=
  GlobalTheory.T.gram_det_ne_zero_of_ker_orth' σ A u hu hsu horth hdec

theorem conj_ker (σ : K →+* K) {n : ℕ} (γ g : GL (Fin n) K) (hg : ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * g = 1)
    (Q : K[X]) {ι : Type} (u : ι → Fin n → K) (hu : LinearIndependent K u)
    (hsu : Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Q))) :
    LinearIndependent K (fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) ∧
      Submodule.span K (Set.range fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) =
        LinearMap.ker (Matrix.toLin' (aeval (γ : Matrix (Fin n) (Fin n) K) Q)) ∧
      (Matrix.of fun i j => ∑ k, σ (((g : Matrix (Fin n) (Fin n) K) *ᵥ u i) k) * ((g : Matrix (Fin n) (Fin n) K) *ᵥ u j) k) =
        Matrix.of fun i j => ∑ k, σ (u i k) * u j k :=
  GlobalTheory.T.unitary_conj_maps_ker_aeval_basis_and_gram σ γ g hg Q u hu hsu

end GlobalTheory.KapSignMul

namespace GlobalTheory.KapSignMul

variable {K : Type} [Field K]

theorem dec_of_dvd {n : ℕ} (γ : Matrix (Fin n) (Fin n) K) (Q : K[X]) (hsep : γ.charpoly.Separable)
    (hQ : Q ∣ γ.charpoly) : ∀ v, ∃ z y, aeval γ Q *ᵥ y = 0 ∧ v = aeval γ Q *ᵥ z + y := by
  obtain ⟨R, hR⟩ := hQ
  have hcop : IsCoprime Q R := Polynomial.Separable.isCoprime (by rw [← hR]; exact hsep)
  obtain ⟨a, c, hac⟩ := hcop
  intro v
  refine ⟨aeval γ a *ᵥ v, aeval γ (c * R) *ᵥ v, ?_, ?_⟩
  · rw [mulVec_mulVec, ← map_mul, show Q * (c * R) = c * (Q * R) by ring, ← hR, map_mul, aeval_self_charpoly,
      mul_zero, zero_mulVec]
  · rw [mulVec_mulVec, ← map_mul, ← add_mulVec, ← map_add, show Q * a + c * R = a * Q + c * R by ring, hac, map_one,
      one_mulVec]

theorem mem_im_of_coprime {n : ℕ} (γ : Matrix (Fin n) (Fin n) K) {Q₁ Q₂ : K[X]} (hcop : IsCoprime Q₁ Q₂)
    {y : Fin n → K} (hy : aeval γ Q₂ *ᵥ y = 0) : ∃ z, y = aeval γ Q₁ *ᵥ z := by
  obtain ⟨a, c, hac⟩ := hcop
  refine ⟨aeval γ a *ᵥ y, ?_⟩
  have : y = aeval γ (a * Q₁ + c * Q₂) *ᵥ y := by rw [hac, map_one, one_mulVec]
  rw [mulVec_mulVec, ← map_mul, mul_comm Q₁ a]
  conv_lhs => rw [this]
  rw [map_add, add_mulVec, map_mul (aeval γ) c, ← mulVec_mulVec, hy, mulVec_zero, add_zero]

theorem ker_toLin' {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (P : K[X]) :
    LinearMap.ker (Matrix.toLin' (aeval M P)) = LinearMap.ker (aeval (Matrix.toLin' M) P) := by
  congr 1
  exact (aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] _).toAlgHom M P).symm

theorem mem_UL {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E} (hs : ¬ IsSplitAt w) (γ : UL n w) :
    (((γ.1 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map (cj w))ᵀ * (γ.1 : GLw n w) = 1 := by
  have := γ.2
  simp only [UL, if_neg hs] at this
  simpa [UJ, cT] using this

theorem mul_sign [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (hM : (M.map σ)ᵀ * M = 1) {Q₁ Q₂ : K[X]} (hsep : M.charpoly.Separable)
    (hdvd : Q₁ * Q₂ ∣ M.charpoly) (hcop : IsCoprime Q₁ Q₂) (hQ₁ : C (σ (Q₁.coeff 0)) * Q₁ = (Q₁.map σ).reverse)
    (hQ₂ : C (σ (Q₂.coeff 0)) * Q₂ = (Q₂.map σ).reverse) {ι₁ ι₂ ι : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι]
    [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι]
    (b₁ : Module.Basis ι₁ K (LinearMap.ker (Matrix.toLin' (aeval M Q₁))))
    (b₂ : Module.Basis ι₂ K (LinearMap.ker (Matrix.toLin' (aeval M Q₂))))
    (b : Module.Basis ι K (LinearMap.ker (Matrix.toLin' (aeval M (Q₁ * Q₂))))) :
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b i : Fin n → K) k) * (b j : Fin n → K) k).det =
      (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b₁ i : Fin n → K) k) * (b₁ j : Fin n → K) k).det *
      (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b₂ i : Fin n → K) k) * (b₂ j : Fin n → K) k).det := by
  have hsup : LinearMap.ker (Matrix.toLin' (aeval M Q₁)) ⊔ LinearMap.ker (Matrix.toLin' (aeval M Q₂)) =
      LinearMap.ker (Matrix.toLin' (aeval M (Q₁ * Q₂))) := by
    simp only [ker_toLin']
    exact sup_ker_aeval_eq_ker_aeval_mul_of_coprime _ hcop
  have hdis : Disjoint (LinearMap.ker (Matrix.toLin' (aeval M Q₁))) (LinearMap.ker (Matrix.toLin' (aeval M Q₂))) := by
    simp only [ker_toLin']
    exact disjoint_ker_aeval_of_isCoprime _ hcop
  have hli : LinearIndependent K (Sum.elim (fun i => (b₁ i : Fin n → K)) (fun i => (b₂ i : Fin n → K))) :=
    (li_coe b₁).sum_type (li_coe b₂) (by rw [span_coe, span_coe]; exact hdis)
  have hsp : Submodule.span K (Set.range (Sum.elim (fun i => (b₁ i : Fin n → K)) (fun i => (b₂ i : Fin n → K)))) =
      LinearMap.ker (Matrix.toLin' (aeval M (Q₁ * Q₂))) := by
    rw [Set.Sum.elim_range, Submodule.span_union, span_coe, span_coe, hsup]
  obtain ⟨d, hd, hdet⟩ := gram_change σ _ _ (fun i => (b i : Fin n → K)) hli hsp (li_coe b) (span_coe b)
  have hblk : (Matrix.of fun i j => ∑ k, σ ((Sum.elim (fun i => (b₁ i : Fin n → K)) (fun i => (b₂ i : Fin n → K)) i) k) *
      (Sum.elim (fun i => (b₁ i : Fin n → K)) (fun i => (b₂ i : Fin n → K)) j) k) =
      fromBlocks (Matrix.of fun i j => ∑ k, σ ((b₁ i : Fin n → K) k) * (b₁ j : Fin n → K) k)
        (Matrix.of fun i j => ∑ k, σ ((b₁ i : Fin n → K) k) * (b₂ j : Fin n → K) k) 0
        (Matrix.of fun i j => ∑ k, σ ((b₂ i : Fin n → K) k) * (b₂ j : Fin n → K) k) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · simp only [fromBlocks_apply₂₁, Matrix.zero_apply, of_apply, Sum.elim_inr, Sum.elim_inl]
      have hy : aeval M Q₂ *ᵥ (b₂ i : Fin n → K) = 0 := by
        have := (b₂ i).2; rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
      have hx : aeval M Q₁ *ᵥ (b₁ j : Fin n → K) = 0 := by
        have := (b₁ j).2; rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
      obtain ⟨z, hz⟩ := mem_im_of_coprime M hcop hy
      rw [hz]
      exact csr_orth σ M hM Q₁ hQ₁ _ z hx
    · rfl
  rw [hblk, det_fromBlocks_zero₂₁] at hdet
  have h1 := gram_ne_zero σ (aeval M Q₁) _ (li_coe b₁) (span_coe b₁)
    (fun x z hx => csr_orth σ M hM Q₁ hQ₁ x z hx) (dec_of_dvd M Q₁ hsep (dvd_trans (dvd_mul_right _ _) hdvd))
  have h2 := gram_ne_zero σ (aeval M Q₂) _ (li_coe b₂) (span_coe b₂)
    (fun x z hx => csr_orth σ M hM Q₂ hQ₂ x z hx) (dec_of_dvd M Q₂ hsep (dvd_trans (dvd_mul_left _ _) hdvd))
  rw [hdet, sign_norm σ hσ hd, ordL_mul h1 h2, zpow_add₀ (by norm_num)]

theorem conj_sign [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    {n : ℕ} (γ g : GL (Fin n) K) (hg : ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * g = 1) (Q : K[X])
    {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (b' : Module.Basis ι' K (LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Q))))
    (b : Module.Basis ι K (LinearMap.ker (Matrix.toLin' (aeval (γ : Matrix (Fin n) (Fin n) K) Q)))) :
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b' i : Fin n → K) k) * (b' j : Fin n → K) k).det =
      (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b i : Fin n → K) k) * (b j : Fin n → K) k).det := by
  obtain ⟨hli, hsp, hgr⟩ := conj_ker σ γ g hg Q _ (li_coe b') (span_coe b')
  obtain ⟨d, hd, hdet⟩ := gram_change σ _ _ _ (li_coe b) (span_coe b) hli hsp
  rw [hgr] at hdet
  rw [hdet, sign_norm σ hσ hd]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (w : Pl E) (Q₁ Q₂ Q₃ : (w.adicCompletion E)[X]) (γ g : UL n w), γ.1.val.charpoly.Separable → Q₁ * Q₂ ∣ γ.1.val.charpoly → IsCoprime Q₁ Q₂ → IsCsr w Q₁ → IsCsr w Q₂ → kapSign n w (Q₁ * Q₂) γ.1 = kapSign n w Q₁ γ.1 * kapSign n w Q₂ γ.1 ∧ kapSign n w Q₃ (g⁻¹ * γ * g).1 = kapSign n w Q₃ γ.1 ∧ (kapSign n w Q₃ γ.1 = 1 ∨ kapSign n w Q₃ γ.1 = -1) := by
  intro E _ _ _ hU n _ w Q₁ Q₂ Q₃ γ g hsep hdvd hcop hc1 hc2
  by_cases hs : IsSplitAt w
  · simp [kapSign, hs]
  have hv := (GlobalTheory.ConjAtPlace.main E hU w).2.2.1
  have hQ₁ : C (cj w (Q₁.coeff 0)) * Q₁ = (Q₁.map (cj w)).reverse := hc1.resolve_left hs
  have hQ₂ : C (cj w (Q₂.coeff 0)) * Q₂ = (Q₂.map (cj w)).reverse := hc2.resolve_left hs
  refine ⟨?_, ?_, ?_⟩
  · simp only [kapSign, if_neg hs]
    exact mul_sign (cj w) hv _ (mem_UL hs γ) hsep hdvd hcop hQ₁ hQ₂ _ _ _
  · simp only [kapSign, if_neg hs]
    have hg' : ((g⁻¹ * γ * g : UL n w) : GLw n w) = (g : GLw n w)⁻¹ * γ * g := by simp
    rw [hg']
    exact conj_sign (cj w) hv γ.1 g.1 (mem_UL hs g) Q₃ _ _
  · simp only [kapSign, if_neg hs]
    rcases Int.even_or_odd (ordL (Matrix.of fun i j => ∑ k, cj w ((Module.finBasis (w.adicCompletion E)
      (LinearMap.ker (Matrix.toLin' (aeval γ.1.val Q₃))) i).1 k) * (Module.finBasis (w.adicCompletion E)
      (LinearMap.ker (Matrix.toLin' (aeval γ.1.val Q₃))) j).1 k).det) with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow

end GlobalTheory.KapSignMul
