import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsReflection

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.IsotropicWitt

open Formalism.UG GlobalTheory.WittTransitivity

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  have key : (Aᵀ.submatrix e.symm id) * M * (A.map star).submatrix id e.symm
      = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA, ← Matrix.submatrix_mul_equiv _ _ e.symm (Equiv.refl _) e.symm,
      ← Matrix.submatrix_mul_equiv _ _ e.symm (Equiv.refl _) (Equiv.refl _)]
    simp
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0] at hd
  simp [Matrix.det_neg] at hd
  exact pow_ne_zero s (neg_ne_zero.2 one_ne_zero) hd.symm

section Field

variable {A : Type} [Field A] [CharZero A] (c : A →+* A) {M : ℕ} (K : Matrix (Fin M) (Fin M) A)

theorem hform_add_left' (x y z : Fin M → A) : hform c K (x + y) z = hform c K x z + hform c K y z := by
  simp [hform, add_mul, Finset.sum_add_distrib]

theorem hform_add_right' (x y z : Fin M → A) : hform c K x (y + z) = hform c K x y + hform c K x z := by
  simp [hform, mul_add, Finset.sum_add_distrib]

theorem exists_move_isotropic (hc : ∀ a, c (c a) = a) (hK : ∀ i j, c (K j i) = K i j) (hdet : K.det ≠ 0)
    (x x' : Fin M → A) (hx : x ≠ 0) (hx' : x' ≠ 0) (hxx : hform c K x x = 0) (hxx' : hform c K x' x' = 0) :
    ∃ g ∈ UJ c K, (g : Matrix (Fin M) (Fin M) A) *ᵥ x = x' := by
  have hdetU : IsUnit K.det := isUnit_iff_ne_zero.2 hdet
  have nd : ∀ v, v ≠ 0 → ∃ u, hform c K u v ≠ 0 := by
    intro v hv
    by_contra hcon
    push_neg at hcon
    apply hv
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    ext i
    have := hcon (Pi.single i 1)
    simpa [hform, Pi.single_apply, Matrix.mulVec, dotProduct] using this
  have nd' : ∀ v, v ≠ 0 → ∃ u, hform c K v u ≠ 0 := by
    intro v hv
    obtain ⟨u, hu⟩ := nd v hv
    refine ⟨u, fun h0 => hu ?_⟩
    rw [← conj_hform c K hc hK, h0, map_zero]
  have refl : ∀ y y', hform c K y y = 0 → hform c K y' y' = 0 → hform c K y' y ≠ 0 →
      ∃ g ∈ UJ c K, (g : Matrix (Fin M) (Fin M) A) *ᵥ y = y' := by
    intro y y' hy hy' hne
    exact exists_reflection c K hc hK hdetU y y' (by rw [hy, hy'])
      (by rw [hy, zero_sub]; exact (neg_ne_zero.2 hne).isUnit)
  by_cases h0 : hform c K x' x ≠ 0
  · exact refl x x' hxx hxx' h0
  push_neg at h0
  obtain ⟨u, hu1, hu2⟩ : ∃ u, hform c K u x ≠ 0 ∧ hform c K x' u ≠ 0 := by
    obtain ⟨u₁, h₁⟩ := nd x hx
    obtain ⟨u₂, h₂⟩ := nd' x' hx'
    by_cases a : hform c K x' u₁ ≠ 0
    · exact ⟨u₁, h₁, a⟩
    by_cases b : hform c K u₂ x ≠ 0
    · exact ⟨u₂, b, h₂⟩
    push_neg at a b
    refine ⟨u₁ + u₂, ?_, ?_⟩
    · rw [hform_add_left', b, add_zero]; exact h₁
    · rw [hform_add_right', a, zero_add]; exact h₂
  have hcb : c (hform c K u x) = hform c K x u := conj_hform c K hc hK u x
  have huu : c (hform c K u u) = hform c K u u := conj_hform c K hc hK u u
  have hcb0 : c (hform c K u x) ≠ 0 := (map_ne_zero c).2 hu1
  set t : A := -(hform c K u u) / (2 * hform c K u x) with ht
  set z : Fin M → A := u + t • x with hz
  have hzz : hform c K z z = 0 := by
    rw [hz, hform_add_left', hform_add_right', hform_add_right', hform_smul_left, hform_smul_left,
      hform_smul_right, hform_smul_right, hxx, ← hcb, ht, map_div₀, map_neg, map_mul, huu, map_ofNat]
    field_simp
    ring
  have hzx : hform c K z x ≠ 0 := by
    rw [hz, hform_add_left', hform_smul_left, hxx, mul_zero, add_zero]; exact hu1
  have hxz : hform c K x' z ≠ 0 := by
    rw [hz, hform_add_right', hform_smul_right, h0, mul_zero, add_zero]; exact hu2
  obtain ⟨g₁, hg₁, e₁⟩ := refl x z hxx hzz hzx
  obtain ⟨g₂, hg₂, e₂⟩ := refl z x' hzz hxx' hxz
  exact ⟨g₂ * g₁, mul_mem hg₂ hg₁, by rw [Units.val_mul, ← Matrix.mulVec_mulVec, e₁, e₂]⟩

end Field

end GlobalTheory.IsotropicWitt

namespace GlobalTheory.IsotropicWitt

open Formalism.UG

theorem form_eq_hform {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : form σ J x y = hform (σ : E →+* E) Jᵀ y x := by
  simp only [form, hform, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [AlgHom.coe_toRingHom]
  ring

theorem exists_rat_unitary_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ r s : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B X X₁ j₀ j₁ → ∀ x : Fin n → E, x ≠ 0 → form σ X.J x x = 0 →
    ∃ γ ∈ ratU σ X.J, mat γ *ᵥ incV F x = incV F H.x := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ H j₀ j₁ r s hB hX hH x hx0 hxx
  have hc : ∀ a, (σ : E →+* E) ((σ : E →+* E) a) = a := by
    intro a
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    simp only [AlgHom.coe_toRingHom]
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hK : ∀ i j, (σ : E →+* E) (X.Jᵀ j i) = X.Jᵀ i j := by
    intro i j
    simpa using hX.herm j i
  have hdet : X.Jᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]
    obtain ⟨τ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h1 := det_ne_zero_of_hasSig (hX.sig (InfinitePlace.mk τ))
    intro h0
    apply h1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have hy0 : H.x ≠ 0 := by
    intro h0
    have := hH.xy
    rw [h0] at this
    simp [form] at this
  obtain ⟨g, hg, hgx⟩ := exists_move_isotropic (σ : E →+* E) X.Jᵀ hc hK hdet x H.x hx0 hy0
    (by rw [← form_eq_hform]; exact hxx) (by rw [← form_eq_hform]; exact hH.xx)
  have hgU : (g : Matrix (Fin n) (Fin n) E)ᵀ * X.J * (g : Matrix (Fin n) (Fin n) E).map σ = X.J := by
    have h2 := congrArg Matrix.transpose (show cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * X.Jᵀ *
      (g : Matrix (Fin n) (Fin n) E) = X.Jᵀ from hg)
    simp only [cT, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h2
    simpa using h2
  let i : E →+* AE F E := inclR (F := F) (AF F)
  have hci : ∀ e : E, cA σ (i e) = i (σ e) := by
    intro e
    simp [i, cA, inclR, Algebra.TensorProduct.map_tmul]
  let G := Matrix.GeneralLinearGroup.map (n := Fin n) i g
  have hGm : (G : Matrix (Fin n) (Fin n) (AE F E)) = (g : Matrix (Fin n) (Fin n) E).map i := rfl
  have hG : G ∈ UG (cA σ) (incM F X.J) := by
    show (G : Matrix (Fin n) (Fin n) (AE F E))ᵀ * incM F X.J * (G : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) =
      incM F X.J
    have h3 : ((g : Matrix (Fin n) (Fin n) E).map i).map (cA σ) = ((g : Matrix (Fin n) (Fin n) E).map σ).map i := by
      ext a b
      simp only [Matrix.map_apply, hci]
    rw [hGm, h3, incM, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hgU]
  refine ⟨⟨G, hG⟩, ?_, ?_⟩
  · rw [ratU, Subgroup.mem_subgroupOf]
    exact ⟨g, rfl⟩
  · show (G : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ incV F x = incV F H.x
    rw [hGm]
    funext k
    show ((g : Matrix (Fin n) (Fin n) E).map i *ᵥ (fun j => i (x j))) k = i (H.x k)
    rw [← hgx]
    exact (RingHom.map_mulVec i (g : Matrix (Fin n) (Fin n) E) x k).symm

end GlobalTheory.IsotropicWitt
