import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergOperatorRationalPointLawsStatement

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (omegaStd)

namespace GlobalTheory.SW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

theorem vecQ_add (m m' : Fin g ⊕ Fin g → ℚ) :
    vecQ X bas (m + m') = vecQ X bas m + vecQ X bas m' := by
  simp only [vecQ, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem vecQ_smul (q : ℚ) (m : Fin g ⊕ Fin g → ℚ) : vecQ X bas (q • m) = q • vecQ X bas m := by
  simp only [vecQ, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem vecQ_zero : vecQ X bas 0 = 0 := by simp [vecQ]

theorem vecQ_intCast (m : Fin g ⊕ Fin g → ℤ) :
    vecQ X bas (fun j => (m j : ℚ)) = (bas m : Fin r → E) := by
  have hm : m = ∑ j, m j • Pi.single j (1 : ℤ) := by
    funext j; simp [Pi.single_apply]
  conv_rhs => rw [hm, map_sum, AddSubmonoidClass.coe_finset_sum]
  simp only [vecQ, map_zsmul, AddSubgroupClass.coe_zsmul, Int.cast_smul_eq_zsmul]

theorem vecQ_surjective : Function.Surjective (vecQ X bas) := by
  intro v
  obtain ⟨k, hk, hv⟩ := GlobalTheory.LatFin.exists_int_smul_mem X.Λ X.Λ_span v
  refine ⟨(k : ℚ)⁻¹ • fun j => (bas.symm ⟨_, hv⟩ j : ℚ), ?_⟩
  rw [vecQ_smul, vecQ_intCast, LinearEquiv.apply_symm_apply]
  change (k : ℚ)⁻¹ • k • v = v
  rw [← Int.cast_smul_eq_zsmul ℚ, inv_smul_smul₀ (Int.cast_ne_zero.2 hk)]

theorem vecQ_crd (v : Fin r → E) : vecQ X bas (crd X bas v) = v :=
  Function.rightInverse_invFun (vecQ_surjective X bas) v

noncomputable def EFBil : (Fin r → E) →ₗ[ℚ] (Fin r → E) →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (EF X)
    (fun u u' v => by
      simp only [EF_def, ← map_add, herm, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add])
    (fun q u v => by
      simp only [EF_def, ← map_smul, herm, Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum,
        mul_smul_comm])
    (fun u v v' => by
      simp only [EF_def, herm, cc, Pi.add_apply, map_add, Finset.sum_add_distrib, mul_add])
    (fun q u v => by
      simp only [EF_def, herm, cc, Pi.smul_apply, map_rat_smul, ← Finset.smul_sum,
        mul_smul_comm])

variable {X bas}

theorem EF_vecQ (hs : IsSympl X bas) (m m' : Fin g ⊕ Fin g → ℚ) :
    EF X (vecQ X bas m) (vecQ X bas m') =
      -∑ i, (m (Sum.inl i) * m' (Sum.inr i) - m (Sum.inr i) * m' (Sum.inl i)) := by
  change EFBil X _ _ = _
  have h (j k) : EFBil X (bas (Pi.single j 1)) (bas (Pi.single k 1)) =
      -(omegaStd (Pi.single j 1) (Pi.single k 1) : ℤ) := hs _ _
  simp only [vecQ, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, h]
  simp [Fintype.sum_sum_type, omegaStd, Pi.single_apply, Finset.sum_sub_distrib, mul_comm]
  ring

theorem vecQ_injective (hs : IsSympl X bas) : Function.Injective (vecQ X bas) := by
  intro m m' h
  have h' (t) := (EF_vecQ hs m t).symm.trans (h ▸ EF_vecQ hs m' t)
  funext j
  rcases j with j | j
  · simpa [Pi.single_apply] using h' (Pi.single (Sum.inr j) 1)
  · simpa [Pi.single_apply] using h' (Pi.single (Sum.inl j) 1)

theorem crd_vecQ (hs : IsSympl X bas) (m : Fin g ⊕ Fin g → ℚ) : crd X bas (vecQ X bas m) = m :=
  Function.leftInverse_invFun (vecQ_injective hs) m

theorem crd_add (hs : IsSympl X bas) (u v : Fin r → E) :
    crd X bas (u + v) = crd X bas u + crd X bas v :=
  vecQ_injective hs (by rw [vecQ_add, vecQ_crd, vecQ_crd, vecQ_crd])

theorem crd_smul (hs : IsSympl X bas) (q : ℚ) (v : Fin r → E) :
    crd X bas (q • v) = q • crd X bas v :=
  vecQ_injective hs (by rw [vecQ_smul, vecQ_crd, vecQ_crd])

theorem crd_zero (hs : IsSympl X bas) : crd X bas 0 = 0 :=
  vecQ_injective hs (by rw [vecQ_crd, vecQ_zero])

theorem EF_crd (hs : IsSympl X bas) (u v : Fin r → E) :
    EF X u v = -∑ i, (crd X bas u (Sum.inl i) * crd X bas v (Sum.inr i) -
      crd X bas u (Sum.inr i) * crd X bas v (Sum.inl i)) := by
  rw [← EF_vecQ hs, vecQ_crd, vecQ_crd]

theorem hMat_mulVec_per_crd (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (v : Fin r → E) :
    hMat X bas idx x *ᵥ (per X x v ∘ idx) = qv (fun i => crd X bas v (Sum.inl i)) +
      tauMat X bas idx x *ᵥ qv fun i => crd X bas v (Sum.inr i) := by
  have h : per X x v ∘ idx =
      perMat X bas idx Sum.inl x *ᵥ qv (fun i => crd X bas v (Sum.inl i)) +
      perMat X bas idx Sum.inr x *ᵥ qv fun i => crd X bas v (Sum.inr i) := by
    funext i
    conv_lhs => rw [← vecQ_crd X bas v, vecQ, per_sum]
    simp only [per_ratSmul, Fintype.sum_sum_type]
    simp [mulVec, dotProduct, mul_comm, qv, Rat.smul_def]
  rw [h, mulVec_add, mulVec_mulVec, mulVec_mulVec, tauMat, hMat_mul_perMat idx hs hx, one_mulVec]

theorem heis_exponent {ι : Type} [Fintype ι] [DecidableEq ι] (τ W : Matrix ι ι ℂ)
    (hτ : τ.IsSymm) (hW : W.IsSymm) (hY : W * τ.map (fun z => (z.im : ℂ)) = 1) (a b : ι → ℚ)
    (u : ι → ℂ) :
    π / 2 * (u ⬝ᵥ W *ᵥ u) + π * I * (qv b ⬝ᵥ τ *ᵥ qv b + 2 * (qv b ⬝ᵥ u) + qv a ⬝ᵥ qv b) =
      -(π * ((u + (1 / 2 : ℂ) • (qv a + τ *ᵥ qv b)) ⬝ᵥ W *ᵥ star (qv a + τ *ᵥ qv b))) +
        π / 2 * ((u + (qv a + τ *ᵥ qv b)) ⬝ᵥ W *ᵥ (u + (qv a + τ *ᵥ qv b))) := by
  have h1 : star (qv a + τ *ᵥ qv b) =
      (qv a + τ *ᵥ qv b) - (2 * I) • (τ.map (fun z => (z.im : ℂ)) *ᵥ qv b) := by
    funext i
    simp only [Pi.star_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, mulVec, dotProduct, qv,
      star_add, star_sum, star_mul', RCLike.star_def, map_ratCast, map_apply, smul_eq_mul,
      Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have := Complex.sub_conj (τ i j)
    push_cast at this
    linear_combination (-(b j : ℂ)) * this
  have h2 : qv b ⬝ᵥ (qv a + τ *ᵥ qv b) = qv a ⬝ᵥ qv b + qv b ⬝ᵥ τ *ᵥ qv b := by
    rw [dotProduct_add, dotProduct_comm]
  generalize qv a + τ *ᵥ qv b = w at h1 h2 ⊢
  have h3 : w ⬝ᵥ W *ᵥ u = u ⬝ᵥ W *ᵥ w := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hW.eq, dotProduct_comm]
  rw [h1, mulVec_sub, mulVec_smul, mulVec_mulVec, hY, one_mulVec]
  simp only [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, h3, dotProduct_comm u (qv b), dotProduct_comm w (qv b), h2]
  ring

theorem heisG_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → (∀ v, vecQ X bas (crd X bas v) = v) ∧ (∀ u v, crd X bas (u + v) = crd X bas u + crd X bas v) ∧ (∀ u v, EF X u v = -∑ i, (crd X bas u (Sum.inl i) * crd X bas v (Sum.inr i) - crd X bas u (Sum.inr i) * crd X bas v (Sum.inl i))) ∧ ∀ (y : Matrix (Fin n) (Fin r) E) (φ : TF n g), IsSB φ → IsSB (heisG X bas y φ) ∧ heisG X bas 0 φ = φ ∧ (∀ y', heisG X bas y (heisG X bas y' φ) = cexp (-(π * I * ((∑ k, EF X (y k) (y' k) : ℚ) : ℂ))) • heisG X bas (y + y') φ) ∧ (∀ ψ, IsSB ψ → ip (heisG X bas y φ) (heisG X bas y ψ) = ip φ ψ) ∧ ∀ x ∈ X.dom, ∀ z : Fin n → Fin g → ℂ, thA X bas idx (heisG X bas y φ) x z = cexp (-(π * ∑ k, (hMat X bas idx x *ᵥ (z k + (1 / 2 : ℂ) • (per X x (y k) ∘ idx))) ⬝ᵥ imInv X bas idx x *ᵥ star (hMat X bas idx x *ᵥ (per X x (y k) ∘ idx)))) * thA X bas idx φ x (fun k => z k + per X x (y k) ∘ idx) := by
  intro E _ _ _ r X g bas idx n hs _
  refine ⟨vecQ_crd X bas, crd_add hs, EF_crd hs, fun y φ hφ => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.T.heisenbergOperatorRationalPoint_laws _ _
    (Matrix.of fun k i => crd X bas (y k) (Sum.inl i))
    (Matrix.of fun k i => crd X bas (y k) (Sum.inr i)) φ hφ
  refine ⟨h1, ?_, fun y' => ?_, h5, fun x hx z => ?_⟩
  · simp only [heisG, Matrix.zero_apply, crd_zero hs, show ∀ k, (0 : Matrix (Fin n) (Fin r) E) k = 0
      from fun _ => rfl]
    exact h4
  · rw [heisG, heisG, h3, heisG]
    congr 2
    · rw [← mul_neg, ← Rat.cast_neg, ← Finset.sum_neg_distrib]
      congr 2
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [EF_crd hs, neg_neg, Finset.sum_sub_distrib]
      simp only [dotProduct, of_apply, mul_comm]
    · ext k i
      exact (congrFun (crd_add hs (y k) (y' k)) _).symm
    · ext k i
      exact (congrFun (crd_add hs (y k) (y' k)) _).symm
  · have hz (w v) : hMat X bas idx x *ᵥ (w + per X x v ∘ idx) = hMat X bas idx x *ᵥ w +
        (qv (fun i => crd X bas v (Sum.inl i)) +
          tauMat X bas idx x *ᵥ qv fun i => crd X bas v (Sum.inr i)) := by
      rw [mulVec_add, hMat_mulVec_per_crd idx hs hx]
    have hz' (w v) : hMat X bas idx x *ᵥ (w + (1 / 2 : ℂ) • (per X x v ∘ idx)) =
        hMat X bas idx x *ᵥ w + (1 / 2 : ℂ) • (qv (fun i => crd X bas v (Sum.inl i)) +
          tauMat X bas idx x *ᵥ qv fun i => crd X bas v (Sum.inr i)) := by
      rw [mulVec_add, mulVec_smul, hMat_mulVec_per_crd idx hs hx]
    rw [thA, thA, heisG, h2 _ ⟨tauMat_isSymm idx hs hx, tauMat_im_posDef idx hs hx⟩]
    change Fin n → Fin r → E at y
    simp only [hz, hz', hMat_mulVec_per_crd idx hs hx]
    have he := Finset.sum_congr (s₁ := Finset.univ) rfl fun (k : Fin n) _ =>
      heis_exponent _ _ (tauMat_isSymm idx hs hx) (imInv_isSymm idx hs hx) (imInv_mul_im idx hs hx)
        (fun i => crd X bas (y k) (Sum.inl i)) (fun i => crd X bas (y k) (Sum.inr i))
        (hMat X bas idx x *ᵥ z k)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_add_distrib (f := fun k => -_),
      Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at he
    have he' := congrArg cexp he
    rw [Complex.exp_add, Complex.exp_add] at he'
    simp only [← add_assoc (hMat X bas idx x *ᵥ z _)] at he' ⊢
    rw [mul_assoc, ← mul_assoc (cexp _)]
    erw [he']
    rw [mul_assoc, mul_left_comm, ← mul_assoc _ (cexp (π / 2 * _))]
    rfl

end GlobalTheory.SW
