import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementS
import Formalism.LocalToGlobal.CMDeterminantIdeals.CmNumbersLink
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain IsLocalRing Matrix
open scoped nonZeroDivisors ComplexOrder

theorem dot_basis_vector_diag {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (j : Fin k) :
    star ((1 : Matrix (Fin k) (Fin k) ℂ) j) ⬝ᵥ (M *ᵥ (1 : Matrix (Fin k) (Fin k) ℂ) j) = M j j := by
  simp [dotProduct, mulVec, Matrix.one_apply]

section Gram

variable {K : Type} [Field K] [NumberField K] {B : Type} {m : B → ℕ} {g : ℕ}

theorem gramBlock_eq (e : (Σ b, Fin (m b)) ≃ Fin g) (U : Matrix (Fin g) (Fin g) K) (H : Matrix (Fin g) (Fin g) ℂ)
    (σ : K →+* ℂ) (b : B) :
    gramBlock e U H σ b = (((U.map σ).submatrix (fun j => e ⟨b, j⟩) id)ᵀ)ᴴ * H *
      ((U.map σ).submatrix (fun j => e ⟨b, j⟩) id)ᵀ := by
  rw [Matrix.mul_assoc]
  ext j j'
  simp [gramBlock, Matrix.mul_apply, dotProduct, mulVec, ReciprocityTheory.MultiplicativeHeights.embVec]

theorem gramBlock_posDef (e : (Σ b, Fin (m b)) ≃ Fin g) (U : Matrix (Fin g) (Fin g) K)
    (H : Matrix (Fin g) (Fin g) ℂ) (σ : K →+* ℂ) (b : B) (hH : H.PosDef) (hU : U.det ≠ 0) :
    (gramBlock e U H σ b).PosDef := by
  classical
  rw [gramBlock_eq]
  refine hH.conjTranspose_mul_mul_same ?_
  rw [Matrix.mulVec_injective_iff]
  have hdet : (U.map σ).det ≠ 0 := by
    rw [show U.map σ = σ.mapMatrix U from rfl, ← RingHom.map_det]
    exact (map_ne_zero σ).mpr hU
  have hli : LinearIndependent ℂ (U.map σ).row :=
    Matrix.linearIndependent_rows_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  have hinj : Function.Injective (fun j : Fin (m b) => e ⟨b, j⟩) := fun j j' h =>
    eq_of_heq (Sigma.mk.inj_iff.mp (e.injective h)).2
  exact hli.comp _ hinj

theorem hermitian_form_gramBlock_basis (e : (Σ b, Fin (m b)) ≃ Fin g) (U : Matrix (Fin g) (Fin g) K) (H : Matrix (Fin g) (Fin g) ℂ)
    (σ : K →+* ℂ) (b : B) (j : Fin (m b)) :
    ReciprocityTheory.MultiplicativeHeights.hq (gramBlock e U H σ b) ((1 : Matrix (Fin (m b)) (Fin (m b)) ℂ) j) =
      ReciprocityTheory.MultiplicativeHeights.hq H (ReciprocityTheory.MultiplicativeHeights.embVec σ (U (e ⟨b, j⟩))) := by
  simp only [ReciprocityTheory.MultiplicativeHeights.hq, dot_basis_vector_diag]
  rfl

end Gram

theorem Step5_of (hLK : LamKey) : Step5 := by
  intro hKC hH K _ _ x T abelian₂ B _ _ m e ℓ U G a n r La logOm S hT hLam hloc harch hℓ hℓdeg hU hG hLa hr hmr hS hS5L hS5A
  classical
  obtain ⟨μ, hμ⟩ := MvPolynomial.ne_zero_iff.mp hG
  have hTd : T.dual.Good := (degree_algebraic K T T hT hT).2.2.1
  obtain ⟨σ₀⟩ : Nonempty (K →+* ℂ) := inferInstance

  have hsum : ∑ v, μ v = ∑ b, ∑ i, a b i := by
    obtain ⟨H₀, -, -, -, heq, -⟩ := hS5A σ₀
    refine subst_homogeneous B m a (MvPolynomial.map σ₀ G) (fun _ => 1) heq μ ?_
    rw [substFr_one, MvPolynomial.coeff_map]
    exact (map_ne_zero σ₀).mpr hμ
  unfold Step5Arch at hS5A
  choose Hs hHs using hS5A
  have hRr : (0 : ℝ) < (r : ℝ) * La := mul_pos (Nat.cast_pos.mpr hr) (by linarith)

  have hmem : MvPolynomial.coeff μ G ∈ (lineNN T.dual ℓ (fun v : FrVar m => e ⟨v.1, v.2.2⟩) μ n).I := by
    refine coeff_mem_of_local K x.P.g ℓ T.dual (FrVar m) _ μ n _ hTd hℓ fun p => ?_
    obtain ⟨t, cd, cl, ht, hcd, hcl, hv, V, K', _, _, _, _, _, _, f, Ub, hVc, hfin, hind, hUb, hclUb, hW⟩ := hS5L p
    refine ⟨t, cl, ht, hcl, ?_⟩
    have htn : t ^ n ≠ 0 := pow_ne_zero _ ht.1
    have hftn : f (t ^ n) ≠ 0 := (map_ne_zero f).mpr htn
    obtain ⟨w, hw⟩ := coeff_integral_local V K' B m (MvPolynomial.map f G) Ub (fun b j => f (cl (e ⟨b, j⟩)))
      (f (t ^ n)) hVc hfin hftn hUb hclUb hW μ
    have hrange : f (MvPolynomial.coeff μ G * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) ∈
        Set.range (algebraMap V K') := by
      refine ⟨w, ?_⟩
      rw [map_div₀, map_mul, map_prod]
      simp only [map_pow]
      rw [← map_pow f t n, ← MvPolynomial.coeff_map, hw, mul_div_cancel_left₀ _ hftn]
    have h1 := (hind _).mp hrange
    calc p.valuation K (MvPolynomial.coeff μ G * ∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v)
        = p.valuation K (MvPolynomial.coeff μ G * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) *
            p.valuation K (t ^ n) := by
          rw [← map_mul, div_mul_cancel₀ _ htn]
      _ ≤ p.valuation K (t ^ n) := mul_le_of_le_one_left' h1

  have harch' : ∀ (σ : K →+* ℂ) (z : FrVar m → ℂ),
      (∀ v, ‖z v‖ * (ℓ ((fun v : FrVar m => e ⟨v.1, v.2.2⟩) v)).n σ ≤ 1) →
      ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * ((r : ℝ) * La) ^ (∑ v, μ v) := by
    intro σ z hz
    obtain ⟨hpd, -, hbd, heq, hY⟩ := hHs σ
    have hTn : 0 < T.dual.n σ ^ n := pow_pos (hTd.2 σ) n
    have hA := ArchTie_of hH B m a (MvPolynomial.map σ G) (fun b => gramBlock e U (Hs σ) σ b) (fun _ => 1)
      (fun b j => (ℓ (e ⟨b, j⟩)).n σ) (S σ / T.dual.n σ ^ n) La r
      (fun b => gramBlock_posDef e U (Hs σ) σ b hpd hU) heq
      (fun X hX => by rw [le_div_iff₀ hTn]; exact hY X hX)
      (fun b j => (hℓ _).2 σ) (by linarith) hmr
      (fun b j => (hermitian_form_gramBlock_basis e U (Hs σ) σ b j).le.trans (hbd _)) z hz
    rw [substFr_one] at hA
    rw [hsum]
    calc ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n
        ≤ S σ / T.dual.n σ ^ n * ((r : ℝ) * La) ^ (∑ b, ∑ i, a b i) * T.dual.n σ ^ n :=
          mul_le_mul_of_nonneg_right hA hTn.le
      _ = S σ * ((r : ℝ) * La) ^ (∑ b, ∑ i, a b i) := by
          rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hTn.ne']
  unfold Step5Loc at hS5L
  have key := hLK hKC K x T abelian₂ ℓ U Hs La logOm (FrVar m) (fun v => e ⟨v.1, v.2.2⟩) G μ n S ((r : ℝ) * La)
    hT hLam hloc harch hℓ hU hLa (fun σ => (hHs σ).1) (fun σ => (hHs σ).2.1)
    (fun p => by
      obtain ⟨t, cd, cl, ht, hcd, hcl, hv, -⟩ := hS5L p
      exact ⟨cd, cl, hcd, hcl, hv⟩)
    (fun σ j => (hHs σ).2.2.1 j) hℓdeg hμ hmem hS hRr harch'
  have hc : (∑ v, (μ v : ℝ)) = ((∑ b, ∑ i, a b i : ℕ) : ℝ) := by
    rw [← hsum, Nat.cast_sum]
  rw [hc] at key
  exact key

end Formalism.L2.LamCM
