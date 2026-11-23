import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PeriodChange

open Complex Matrix NumberField in
private theorem matrix_eq_of_dotProduct_mulVec_eq {n : Type*} [Fintype n] [DecidableEq n] (M K : Matrix n n ℤ)
    (h : ∀ a b : n → ℤ, a ⬝ᵥ (M *ᵥ b) = a ⬝ᵥ (K *ᵥ b)) : M = K := by
  ext i j
  simpa [mulVec_single_one, single_one_dotProduct] using h (Pi.single i 1) (Pi.single j 1)

open Complex Matrix NumberField in
private theorem omegaStd_eq_neg_dotProduct_J {g : ℕ} (a b : Fin g ⊕ Fin g → ℤ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b = -(a ⬝ᵥ (J (Fin g) ℤ *ᵥ b)) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd
  simp [Matrix.J, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_mulVec, Finset.sum_sub_distrib,
    neg_mulVec, one_mulVec, Finset.sum_neg_distrib, mul_comm]
  ring

open Complex Matrix NumberField in
private theorem fromBlocks_swap_mul_J_mul_swap {g : ℕ} :
    fromBlocks (0 : Matrix (Fin g) (Fin g) ℤ) 1 1 0 * J (Fin g) ℤ * fromBlocks 0 1 1 0 =
      -J (Fin g) ℤ := by
  simp [Matrix.J, fromBlocks_multiply, fromBlocks_neg]

open Complex Matrix NumberField in

theorem _root_.GlobalTheory.PeriodChange.swap_mem_symplectic {g : ℕ} (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hN : ∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd (N *ᵥ a) (N *ᵥ b) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) :
    Matrix.fromBlocks N.toBlocks₂₂ᵀ N.toBlocks₁₂ᵀ N.toBlocks₂₁ᵀ N.toBlocks₁₁ᵀ ∈
      Matrix.symplecticGroup (Fin g) ℤ := by
  set S : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ := fromBlocks 0 1 1 0 with hS
  have hNJN : Nᵀ * J (Fin g) ℤ * N = J (Fin g) ℤ := by
    apply matrix_eq_of_dotProduct_mulVec_eq
    intro a b
    have := hN a b
    rw [omegaStd_eq_neg_dotProduct_J, omegaStd_eq_neg_dotProduct_J, neg_inj] at this
    rw [← this, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
      vecMul_transpose]
  have hSt : Sᵀ = S := by simp [hS, fromBlocks_transpose]
  have hM : Matrix.fromBlocks N.toBlocks₂₂ᵀ N.toBlocks₁₂ᵀ N.toBlocks₂₁ᵀ N.toBlocks₁₁ᵀ =
      S * Nᵀ * S := by
    conv_rhs => rw [← fromBlocks_toBlocks N]
    simp [hS, fromBlocks_transpose, fromBlocks_multiply]
  rw [hM, SymplecticGroup.mem_iff]
  calc S * Nᵀ * S * J (Fin g) ℤ * (S * Nᵀ * S)ᵀ
      = S * (Nᵀ * ((S * J (Fin g) ℤ * S) * N)) * S := by
        simp only [transpose_mul, transpose_transpose, hSt, Matrix.mul_assoc]
    _ = -(S * (Nᵀ * J (Fin g) ℤ * N) * S) := by
        rw [fromBlocks_swap_mul_J_mul_swap]; simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
    _ = J (Fin g) ℤ := by rw [hNJN, fromBlocks_swap_mul_J_mul_swap, neg_neg]

open Complex Matrix NumberField in

theorem _root_.GlobalTheory.PeriodChange.change_of_normalisation {g : ℕ} (h h' τ' A B L R : Matrix (Fin g) (Fin g) ℂ)
    (hA : h * L = A) (hB : h * R = B) (hL : h' * L = 1) (hR : h' * R = τ') (hs : τ'.IsSymm)
    (hu : IsUnit h.det) :
    τ' = Bᵀ * (Aᵀ)⁻¹ ∧ h' = ((Aᵀ)⁻¹)ᵀ * h ∧ h.det = (Aᵀ).det * h'.det := by
  have hL' : L = h⁻¹ * A := by
    rw [← hA, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
  have hAh : h' * h⁻¹ * A = 1 := by rw [Matrix.mul_assoc, ← hL', hL]
  have hA1 : A * (h' * h⁻¹) = 1 := mul_eq_one_comm.mp hAh
  have hAu : IsUnit A.det := isUnit_det_of_right_inverse hA1
  have hAinv : A⁻¹ = h' * h⁻¹ := inv_eq_right_inv hA1
  have hh' : h' = A⁻¹ * h := by
    rw [hAinv, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · calc τ' = τ'ᵀ := hs.eq.symm
      _ = Bᵀ * (Aᵀ)⁻¹ := by
        rw [← hR, hh', Matrix.mul_assoc, hB, transpose_mul, transpose_nonsing_inv]
  · rw [← transpose_nonsing_inv, transpose_transpose]; exact hh'
  · have : h = A * h' := by
      rw [hh', ← Matrix.mul_assoc, mul_nonsing_inv _ hAu, Matrix.one_mul]
    conv_lhs => rw [this]
    rw [det_mul, det_transpose]

open Complex Matrix NumberField in
private theorem addMonoidHom_eq_matrix_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {g : ℕ}
    (Q : (ι → ℤ) →+ (Fin g → ℂ)) (x : ι → ℤ) :
    Q x = (Matrix.of fun i u => Q (Pi.single u 1) i) *ᵥ fun u => (x u : ℂ) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  funext i
  simp only [Finset.sum_apply, mulVec, dotProduct, of_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hs : Pi.single u (x u) = x u • (Pi.single u 1 : ι → ℤ) := by
    ext v; by_cases hv : v = u <;> simp [hv]
  rw [hs, map_zsmul, Pi.smul_apply, zsmul_eq_mul, mul_comm]

open Complex Matrix NumberField in

theorem _root_.GlobalTheory.PeriodChange.period_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (gam : D.La ≃ₗ[𝓞 E] D.La) (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (P P' : D.La →+ (Fin g → ℂ)) (h h' τ τ' : Matrix (Fin g) (Fin g) ℂ), (∀ a b, D.EF (bas a) (bas b) = -_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) → (∀ a b, D.EF (gam a) (gam b) = D.EF a b) → (∀ u v, N u v = bas.symm (gam (bas (Pi.single v 1))) u) → (∀ a, P' a = P (gam a)) → (∀ k, h *ᵥ P (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h *ᵥ P (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1) → (∀ k, h' *ᵥ P' (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h' *ᵥ P' (bas (Pi.single (Sum.inr k) 1)) = τ' *ᵥ Pi.single k 1) → τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → τ' ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → IsUnit h.det → ∃ γ ∈ Matrix.symplecticGroup (Fin g) ℤ, γ = Matrix.fromBlocks N.toBlocks₂₂ᵀ N.toBlocks₁₂ᵀ N.toBlocks₂₁ᵀ N.toBlocks₁₁ᵀ ∧ τ' = _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct γ τ ∧ h' = ((_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut γ τ)⁻¹)ᵀ * h ∧ h.det = (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut γ τ).det * h'.det := by
  intro E _ _ _ H D g bas gam N P P' h h' τ τ' hEF hgam hNdef hP' hnorm hnorm' hτ hτ' hu
  have hτs : τ.IsSymm := by unfold _root_.ReciprocityTheory.PTheta.SiegelH at hτ; exact hτ.1
  have hτs' : τ'.IsSymm := by unfold _root_.ReciprocityTheory.PTheta.SiegelH at hτ'; exact hτ'.1
  have hNv : ∀ a, bas (N *ᵥ a) = gam (bas a) := by
    intro a
    let f₁ : (Fin g ⊕ Fin g → ℤ) →+ (Fin g ⊕ Fin g → ℤ) := (Matrix.mulVecLin N).toAddMonoidHom
    let f₂ : (Fin g ⊕ Fin g → ℤ) →+ (Fin g ⊕ Fin g → ℤ) :=
      bas.symm.toLinearMap.toAddMonoidHom.comp
        (gam.toAddEquiv.toAddMonoidHom.comp bas.toLinearMap.toAddMonoidHom)
    have hf : f₁ = f₂ := by
      refine AddMonoidHom.functions_ext _ _ _ fun v x => ?_
      have hs : Pi.single v x = x • (Pi.single v 1 : Fin g ⊕ Fin g → ℤ) := by
        ext u; by_cases hu : u = v <;> simp [hu]
      rw [hs, map_zsmul, map_zsmul]
      congr 1
      funext u
      simp [f₁, f₂, hNdef, mulVec_single_one]
    have := DFunLike.congr_fun hf a
    change N *ᵥ a = bas.symm (gam (bas a)) at this
    rw [this, LinearEquiv.apply_symm_apply]
  have hγ := _root_.GlobalTheory.PeriodChange.swap_mem_symplectic N fun a b => by
    have := hEF (N *ᵥ a) (N *ᵥ b)
    rw [hNv, hNv, hgam, hEF] at this
    exact (neg_inj.mp this).symm
  have hcol : ∀ v, h *ᵥ P' (bas (Pi.single v 1)) =
      fun i => (N (Sum.inl i) v : ℂ) + ∑ j, τ i j * N (Sum.inr j) v := by
    intro v
    have hPb : ∀ x, P (bas x) =
        (Matrix.of fun i u => P (bas (Pi.single u 1)) i) *ᵥ fun u => (x u : ℂ) :=
      fun x => addMonoidHom_eq_matrix_mulVec (P.comp bas.toLinearMap.toAddMonoidHom) x
    rw [hP', ← hNv, hPb, mulVec_mulVec]
    funext i
    have hc : ∀ u, (h * Matrix.of fun i u => P (bas (Pi.single u 1)) i) i u
        = (h *ᵥ P (bas (Pi.single u 1))) i := by
      intro u; simp [mul_apply, mulVec, dotProduct]
    rw [mulVec, dotProduct, Fintype.sum_sum_type]
    simp only [hc, (hnorm _).1, (hnorm _).2]
    simp [mulVec_single_one, Pi.single_apply]
  let A₀ : Matrix (Fin g) (Fin g) ℂ :=
    N.toBlocks₁₁.map (fun x : ℤ => (x : ℂ)) + τ * N.toBlocks₂₁.map (fun x : ℤ => (x : ℂ))
  let B₀ : Matrix (Fin g) (Fin g) ℂ :=
    N.toBlocks₁₂.map (fun x : ℤ => (x : ℂ)) + τ * N.toBlocks₂₂.map (fun x : ℤ => (x : ℂ))
  have hAL : h * (Matrix.of fun i k => P' (bas (Pi.single (Sum.inl k) 1)) i) = A₀ := by
    ext i k
    have := congrFun (hcol (Sum.inl k)) i
    simp only [mulVec, dotProduct] at this
    simp [A₀, mul_apply, this, toBlocks₁₁, toBlocks₂₁]
  have hBR : h * (Matrix.of fun i k => P' (bas (Pi.single (Sum.inr k) 1)) i) = B₀ := by
    ext i k
    have := congrFun (hcol (Sum.inr k)) i
    simp only [mulVec, dotProduct] at this
    simp [B₀, mul_apply, this, toBlocks₁₂, toBlocks₂₂]
  have hL1 : h' * (Matrix.of fun i k => P' (bas (Pi.single (Sum.inl k) 1)) i) = 1 := by
    ext i k
    have := congrFun (hnorm' k).1 i
    simp only [mulVec, dotProduct] at this
    simp [mul_apply, this, one_apply, Pi.single_apply]
  have hRτ : h' * (Matrix.of fun i k => P' (bas (Pi.single (Sum.inr k) 1)) i) = τ' := by
    ext i k
    have := congrFun (hnorm' k).2 i
    simp only [mulVec, dotProduct] at this
    simp [mul_apply, this, Pi.single_apply]
  obtain ⟨e₁, e₂, e₃⟩ :=
    _root_.GlobalTheory.PeriodChange.change_of_normalisation h h' τ' A₀ B₀ _ _ hAL hBR hL1 hRτ hτs' hu
  have hj : _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut (Matrix.fromBlocks N.toBlocks₂₂ᵀ N.toBlocks₁₂ᵀ N.toBlocks₂₁ᵀ N.toBlocks₁₁ᵀ) τ =
      A₀ᵀ := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat
    simp [A₀, fromBlocks_map, transpose_add, transpose_mul, hτs.eq, transpose_map, add_comm]
  refine ⟨_, hγ, rfl, ?_, ?_, ?_⟩
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct
    rw [hj, e₁]
    congr 1
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat
    simp [B₀, fromBlocks_map, transpose_add, transpose_mul, hτs.eq, transpose_map, add_comm]
  · rw [hj]; exact e₂
  · rw [hj]; exact e₃

end GlobalTheory.PeriodChange
