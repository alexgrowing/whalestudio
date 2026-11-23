import Formalism.LocalToGlobal.GlobalTheory.GL6.WeylLengthDiagonalUnitUniformiser
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwDecomp
import Formalism.LocalToGlobal.GlobalTheory.GL6.ValuationDetBasisChange
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLcInt
import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
import Formalism.LocalToGlobal.GlobalTheory.GL6.LinearIndependentProdRenameOfCard

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open MvPolynomial

section LenMap

theorem length_quotient_map_equiv {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] (e : M ≃ₗ[O] M)
    (A B : Submodule O M) :
    Module.length O (A.map (e : M →ₗ[O] M) ⧸ (B.map (e : M →ₗ[O] M)).comap (A.map (e : M →ₗ[O] M)).subtype) =
      Module.length O (A ⧸ B.comap A.subtype) := by
  refine (Submodule.Quotient.equiv (B.comap A.subtype)
    ((B.map (e : M →ₗ[O] M)).comap (A.map (e : M →ₗ[O] M)).subtype) (e.submoduleMap A) ?_).length_eq.symm
  ext ⟨y, hy⟩
  rw [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨⟨x, hxA⟩, hxB, hxy⟩
    rw [Submodule.mem_comap, Submodule.subtype_apply] at hxB
    have hx : e x = y := congrArg Subtype.val hxy
    exact Submodule.mem_map.2 ⟨x, hxB, hx⟩
  · intro hyB
    obtain ⟨b, hbB, rfl⟩ := Submodule.mem_map.1 hyB
    obtain ⟨a, haA, hab⟩ := Submodule.mem_map.1 hy
    have hab' : a = b := e.injective hab
    subst hab'
    exact ⟨⟨a, haA⟩, hbB, rfl⟩

theorem length_quotient_map_of_inverse {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] (f g : M →ₗ[O] M)
    (h1 : ∀ x, f (g x) = x) (h2 : ∀ x, g (f x) = x) (A B : Submodule O M) :
    Module.length O (A.map f ⧸ (B.map f).comap (A.map f).subtype) = Module.length O (A ⧸ B.comap A.subtype) := length_quotient_map_equiv (LinearEquiv.ofLinear f g (LinearMap.ext h1) (LinearMap.ext h2)) A B

end LenMap

section Factor

variable (O : Subring ℂ) {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)

abbrev mvPolynomialRowLinearMap (g : Matrix (Fin r) (Fin r) ℂ) :
    MvPolynomial (Fin r × Fin n) ℂ →ₗ[O] MvPolynomial (Fin r × Fin n) ℂ :=
  (Formalism.GradedWeylDivisibility.rowAct ℂ g).toLinearMap.restrictScalars O

abbrev mvPolynomialScalingMap (c : ℂ) : MvPolynomial (Fin r × Fin n) ℂ →ₗ[O] MvPolynomial (Fin r × Fin n) ℂ :=
  (c • LinearMap.id : MvPolynomial (Fin r × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin r × Fin n) ℂ).restrictScalars O

variable {O}

theorem row_action_comp (g h : Matrix (Fin r) (Fin r) ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    mvPolynomialRowLinearMap O h (mvPolynomialRowLinearMap O g f) = mvPolynomialRowLinearMap O (g * h) f := by
  show Formalism.GradedWeylDivisibility.rowAct ℂ h (Formalism.GradedWeylDivisibility.rowAct ℂ g f) = Formalism.GradedWeylDivisibility.rowAct ℂ (g * h) f
  have hcomp : (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) h).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g) = Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g * h) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Formalism.GradedWeylDivisibility.rowAct, AlgHom.comp_apply, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_assoc]
  rw [← AlgHom.comp_apply, hcomp]

theorem row_action_one (f : MvPolynomial (Fin r × Fin n) ℂ) : mvPolynomialRowLinearMap O (1 : Matrix (Fin r) (Fin r) ℂ) f = f := by
  show Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin r) (Fin r) ℂ) f = f
  have h : Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (1 : Matrix (Fin r) (Fin r) ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply]
  rw [h, AlgHom.id_apply]

def mvPolynomialRowLinearEquiv (g g' : Matrix (Fin r) (Fin r) ℂ) (h1 : g * g' = 1) (h2 : g' * g = 1) :
    MvPolynomial (Fin r × Fin n) ℂ ≃ₗ[O] MvPolynomial (Fin r × Fin n) ℂ :=
  LinearEquiv.ofLinear (mvPolynomialRowLinearMap O g) (mvPolynomialRowLinearMap O g')
    (LinearMap.ext fun f => by
      rw [LinearMap.comp_apply, row_action_comp, h2, row_action_one, LinearMap.id_apply])
    (LinearMap.ext fun f => by
      rw [LinearMap.comp_apply, row_action_comp, h1, row_action_one, LinearMap.id_apply])

theorem row_action_equiv_coe (g g' : Matrix (Fin r) (Fin r) ℂ) (h1 : g * g' = 1) (h2 : g' * g = 1) :
    ((mvPolynomialRowLinearEquiv (O := O) (n := n) g g' h1 h2 : _ ≃ₗ[O] _) : MvPolynomial (Fin r × Fin n) ℂ →ₗ[O] _) = mvPolynomialRowLinearMap O g := rfl

def mvPolynomialScalingEquiv (c : ℂ) (hc : c ≠ 0) : MvPolynomial (Fin r × Fin n) ℂ ≃ₗ[O] MvPolynomial (Fin r × Fin n) ℂ :=
  LinearEquiv.ofLinear (mvPolynomialScalingMap O c) (mvPolynomialScalingMap O c⁻¹)
    (LinearMap.ext fun f => by
      show c • (c⁻¹ • f) = f
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul])
    (LinearMap.ext fun f => by
      show c⁻¹ • (c • f) = f
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul])

theorem scalar_equiv_coe (c : ℂ) (hc : c ≠ 0) :
    ((mvPolynomialScalingEquiv (O := O) (r := r) (n := n) c hc : _ ≃ₗ[O] _) : MvPolynomial (Fin r × Fin n) ℂ →ₗ[O] _) = mvPolynomialScalingMap O c := rfl

theorem weyl_span_map_elementary (K K' : Matrix (Fin r) (Fin r) ℂ) (hK : K ∈ bwA_EO O r) (hK' : K' ∈ bwA_EO O r)
    (h2 : K' * K = 1) : (bwA_span O hn ν).map (mvPolynomialRowLinearMap O K) = bwA_span O hn ν := by
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    exact bwA_span_closure O hn ν K hK f hf
  · intro f hf
    refine ⟨mvPolynomialRowLinearMap O K' f, bwA_span_closure O hn ν K' hK' f hf, ?_⟩
    show mvPolynomialRowLinearMap O K (mvPolynomialRowLinearMap O K' f) = f
    rw [row_action_comp, h2, row_action_one]

theorem weyl_span_map_unit_scalar (η : Oˣ) : (bwA_span O hn ν).map (mvPolynomialScalingMap O ((η : O) : ℂ)) = bwA_span O hn ν := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    show (η : O) • x ∈ bwA_span O hn ν
    exact (bwA_span O hn ν).smul_mem (η : O) hx
  · intro x hx
    refine ⟨((η⁻¹ : Oˣ) : O) • x, (bwA_span O hn ν).smul_mem _ hx, ?_⟩
    show (η : O) • (((η⁻¹ : Oˣ) : O) • x) = x
    rw [smul_smul, Units.mul_inv, one_smul]

theorem elementary_product_integral (K : Matrix (Fin r) (Fin r) ℂ) (hK : K ∈ bwA_EO O r) : bwD_Int O K := by
  induction hK using Submonoid.closure_induction with
  | mem g hg =>
    obtain ⟨a, b, c, hc, rfl⟩ := hg
    intro i j
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    refine O.add_mem ?_ ?_
    · split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    · split_ifs
      · exact hc
      · exact O.zero_mem
  | one =>
    intro i j
    simp only [Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  | mul x y _ _ hx hy =>
    intro i j
    rw [Matrix.mul_apply]
    exact O.sum_mem fun k _ => O.mul_mem (hx i k) (hy k j)

theorem elementary_product_inv (hL : bwD_Loc O) (K : Matrix (Fin r) (Fin r) ℂ) (hK : K ∈ bwA_EO O r) (y : ℂ) (hy : y ∈ O)
    (hdet : K.det * y = 1) : ∃ K' ∈ bwA_EO O r, K * K' = 1 ∧ K' * K = 1 := by
  have hInt : bwD_Int O K := elementary_product_integral K hK
  set K' := y • K.adjugate with hK'
  have h1 : K * K' = 1 := by
    rw [hK', Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm, hdet, one_smul]
  have h2 : K' * K = 1 := by
    rw [hK', Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm, hdet, one_smul]
  have hInt' : bwD_Int O K' := fun a b => by
    rw [hK', Matrix.smul_apply, smul_eq_mul]
    exact O.mul_mem hy (bwD_Int_adj hInt a b)
  refine ⟨K', bwD_elim hL K' hInt' ⟨K, hInt, h1⟩, h1, h2⟩

theorem length_elementary_diag_elementary (K₁ K₂ K₁' K₂' Dm Dp : Matrix (Fin r) (Fin r) ℂ) (h₁ : K₁ ∈ bwA_EO O r) (h₂ : K₂ ∈ bwA_EO O r)
    (h₁' : K₁' ∈ bwA_EO O r) (h₂' : K₂' ∈ bwA_EO O r) (e12 : K₁' * K₁ = 1) (e21 : K₂ * K₂' = 1) (e22 : K₂' * K₂ = 1)
    (hDD : Dm * Dp = 1) (hDD' : Dp * Dm = 1) (c : ℂ) (hc : c ≠ 0) (η : Oˣ) :
    Module.length O (((bwA_span O hn ν).map (mvPolynomialRowLinearMap O (K₁ * Dm * K₂))).map (mvPolynomialScalingMap O c) ⧸
        ((bwA_span O hn ν).map (mvPolynomialScalingMap O (c * ((η : O) : ℂ)))).comap
          (((bwA_span O hn ν).map (mvPolynomialRowLinearMap O (K₁ * Dm * K₂))).map (mvPolynomialScalingMap O c)).subtype) =
      Module.length O (bwA_span O hn ν ⧸ ((bwA_span O hn ν).map (mvPolynomialRowLinearMap O Dp)).comap (bwA_span O hn ν).subtype) := by
  have e11 : K₁ * K₁' = 1 := by
    rw [← Matrix.inv_eq_left_inv e12]
    exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse e12)
  have hcompR : ∀ g h : Matrix (Fin r) (Fin r) ℂ,
      (mvPolynomialRowLinearMap O (n := n) h).comp (mvPolynomialRowLinearMap O g) = mvPolynomialRowLinearMap O (g * h) :=
    fun g h => LinearMap.ext fun f => row_action_comp g h f
  have hR1 : mvPolynomialRowLinearMap O (n := n) (1 : Matrix (Fin r) (Fin r) ℂ) = LinearMap.id :=
    LinearMap.ext fun f => row_action_one f
  have hSS : ∀ a b : ℂ, (mvPolynomialScalingMap O (r := r) (n := n) a).comp (mvPolynomialScalingMap O b) = mvPolynomialScalingMap O (a * b) := by
    intro a b
    refine LinearMap.ext fun f => ?_
    show a • (b • f) = (a * b) • f
    rw [smul_smul]
  have hNiN : K₂' * Dp * K₁' * (K₁ * Dm * K₂) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc K₁' K₁, e12, Matrix.one_mul, ← Matrix.mul_assoc Dp Dm, hDD', Matrix.one_mul, e22]
  have hNNi : K₁ * Dm * K₂ * (K₂' * Dp * K₁') = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc K₂ K₂', e21, Matrix.one_mul, ← Matrix.mul_assoc Dm Dp, hDD, Matrix.one_mul, e11]
  have h1 : ∀ x, ((mvPolynomialScalingMap O c).comp (mvPolynomialRowLinearMap O (n := n) (K₁ * Dm * K₂)))
      (((mvPolynomialRowLinearMap O (n := n) (K₂' * Dp * K₁')).comp (mvPolynomialScalingMap O c⁻¹)) x) = x := by
    intro x
    show mvPolynomialScalingMap O c (mvPolynomialRowLinearMap O (K₁ * Dm * K₂) (mvPolynomialRowLinearMap O (K₂' * Dp * K₁') (mvPolynomialScalingMap O c⁻¹ x))) = x
    rw [row_action_comp, hNiN, row_action_one]
    show c • (c⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  have h2 : ∀ x, ((mvPolynomialRowLinearMap O (n := n) (K₂' * Dp * K₁')).comp (mvPolynomialScalingMap O c⁻¹))
      (((mvPolynomialScalingMap O c).comp (mvPolynomialRowLinearMap O (n := n) (K₁ * Dm * K₂))) x) = x := by
    intro x
    show mvPolynomialRowLinearMap O (K₂' * Dp * K₁') (mvPolynomialScalingMap O c⁻¹ (mvPolynomialScalingMap O c (mvPolynomialRowLinearMap O (K₁ * Dm * K₂) x))) = x
    have hcc : mvPolynomialScalingMap O c⁻¹ (mvPolynomialScalingMap O c (mvPolynomialRowLinearMap O (n := n) (K₁ * Dm * K₂) x)) = mvPolynomialRowLinearMap O (K₁ * Dm * K₂) x := by
      show c⁻¹ • (c • mvPolynomialRowLinearMap O (n := n) (K₁ * Dm * K₂) x) = mvPolynomialRowLinearMap O (n := n) (K₁ * Dm * K₂) x
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hcc, row_action_comp, hNNi, row_action_one]
  have hA : ((bwA_span O hn ν).map (mvPolynomialRowLinearMap O (K₁ * Dm * K₂))).map (mvPolynomialScalingMap O c) =
      (bwA_span O hn ν).map ((mvPolynomialScalingMap O c).comp (mvPolynomialRowLinearMap O (n := n) (K₁ * Dm * K₂))) := by
    rw [Submodule.map_comp]
  have hB : (bwA_span O hn ν).map (mvPolynomialScalingMap O (c * ((η : O) : ℂ))) =
      ((bwA_span O hn ν).map (mvPolynomialRowLinearMap O (n := n) (K₂' * Dp * K₁'))).map
        ((mvPolynomialScalingMap O c).comp (mvPolynomialRowLinearMap O (n := n) (K₁ * Dm * K₂))) := by
    rw [← Submodule.map_comp]
    have hF : ((mvPolynomialScalingMap O c).comp (mvPolynomialRowLinearMap O (n := n) (K₁ * Dm * K₂))).comp (mvPolynomialRowLinearMap O (n := n) (K₂' * Dp * K₁')) =
        mvPolynomialScalingMap O c := by
      rw [LinearMap.comp_assoc, hcompR, hNiN, hR1, LinearMap.comp_id]
    rw [hF, ← hSS, Submodule.map_comp, weyl_span_map_unit_scalar hn ν η]
  rw [hA, hB, length_quotient_map_of_inverse _ _ h1 h2]
  have hRNi : (bwA_span O hn ν).map (mvPolynomialRowLinearMap O (n := n) (K₂' * Dp * K₁')) =
      ((bwA_span O hn ν).map (mvPolynomialRowLinearMap O Dp)).map (mvPolynomialRowLinearMap O K₁') := by
    have hc3 : mvPolynomialRowLinearMap O (n := n) (K₂' * Dp * K₁') = (mvPolynomialRowLinearMap O K₁').comp ((mvPolynomialRowLinearMap O Dp).comp (mvPolynomialRowLinearMap O K₂')) := by
      rw [hcompR, hcompR]
    rw [hc3, Submodule.map_comp, Submodule.map_comp, weyl_span_map_elementary hn ν K₂' K₂ h₂' h₂ e21]
  rw [hRNi]
  have hfix : (bwA_span O hn ν).map (mvPolynomialRowLinearMap O (n := n) K₁') = bwA_span O hn ν := weyl_span_map_elementary hn ν K₁' K₁ h₁' h₁ e11
  have hlen := length_quotient_map_equiv (mvPolynomialRowLinearEquiv (O := O) (n := n) K₁' K₁ e12 e11) (bwA_span O hn ν)
    ((bwA_span O hn ν).map (mvPolynomialRowLinearMap O Dp))
  rw [row_action_equiv_coe, hfix] at hlen
  exact hlen

theorem diagonal_update_inv (j : Fin r) (p : ℂ) (hp0 : p ≠ 0) :
    Matrix.diagonal (Function.update (1 : Fin r → ℂ) j p⁻¹) * Matrix.diagonal (Function.update 1 j p) = 1 ∧
    Matrix.diagonal (Function.update (1 : Fin r → ℂ) j p) * Matrix.diagonal (Function.update 1 j p⁻¹) = 1 := by
  constructor <;> rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] <;> congr 1 <;> funext i <;>
    by_cases hi : i = j <;> simp [hi, Function.update_apply, hp0]

theorem length_factor_elementary_diag (hν : Antitone ν) [IsDiscreteValuationRing O] (hL : bwD_Loc O) (ϖ : O) (hϖ : Irreducible ϖ)
    (ε : Oˣ) (a : ℕ) (j : Fin r) (K₁ K₂ : Matrix (Fin r) (Fin r) ℂ) (h₁ : K₁ ∈ bwA_EO O r) (h₂ : K₂ ∈ bwA_EO O r)
    (hK : K₁.det * K₂.det = 1) (c : ℂ) (hc : c ≠ 0) (η : Oˣ) :
    ∃ N : ℕ, Module.length O (((bwA_span O hn ν).map
          (mvPolynomialRowLinearMap O (K₁ * Matrix.diagonal (Function.update 1 j (((ε : O) * ϖ ^ a : O) : ℂ)⁻¹) * K₂))).map (mvPolynomialScalingMap O c) ⧸
        ((bwA_span O hn ν).map (mvPolynomialScalingMap O (c * ((η : O) : ℂ)))).comap
          (((bwA_span O hn ν).map
            (mvPolynomialRowLinearMap O (K₁ * Matrix.diagonal (Function.update 1 j (((ε : O) * ϖ ^ a : O) : ℂ)⁻¹) * K₂))).map
              (mvPolynomialScalingMap O c)).subtype) = N ∧
      r * N = a * Module.finrank ℤ (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) * ∑ b, Formalism.GradedWeylDivisibility.rowNu (r := r) ν b := by
  have hp0 : (((ε : O) * ϖ ^ a : O) : ℂ) ≠ 0 := by
    intro h
    have h' : ((ε : O) * ϖ ^ a : O) = 0 := Subtype.ext h
    rcases mul_eq_zero.1 h' with h'' | h''
    · exact ε.ne_zero h''
    · exact hϖ.ne_zero (pow_eq_zero_iff'.1 h'' |>.1)
  obtain ⟨hDD, hDD'⟩ := diagonal_update_inv j _ hp0
  obtain ⟨K₁', h₁', -, e12⟩ :=
    elementary_product_inv hL K₁ h₁ K₂.det (bwD_det_mem (elementary_product_integral K₂ h₂)) hK
  obtain ⟨K₂', h₂', e21, e22⟩ :=
    elementary_product_inv hL K₂ h₂ K₁.det (bwD_det_mem (elementary_product_integral K₁ h₁)) (by rw [mul_comm]; exact hK)
  rw [length_elementary_diag_elementary hn ν K₁ K₂ K₁' K₂' _ _ h₁ h₂ h₁' h₂' e12 e21 e22 hDD hDD' c hc η]
  exact weyl_length_diagonal_unit_uniformiser hn ν hν ℂ O ϖ hϖ ε j a

end Factor

section Tied

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField
open scoped Matrix

theorem local_ring_is_dvr (D : D7) (w : D.what₂.places.Pl) : IsDiscreteValuationRing (bwA_Ow D w) := by
  haveI := D.intW_dvr w
  let e : intW D.what₂.places w ≃+* bwA_Ow D w :=
    (intW D.what₂.places w).equivMapOfInjective D.what₂.embLL D.what₂.embLL.injective
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (intW D.what₂.places w)
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨e ϖ, ?_, ?_⟩
  · exact (MulEquiv.irreducible_iff e).2 hϖ
  · intro y hy
    have hx : e.symm y ≠ 0 := fun h => hy (by simpa using congrArg e h)
    obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    refine ⟨n, Units.map (e : intW D.what₂.places w →* bwA_Ow D w) v, ?_⟩
    have h2 := congrArg e hv
    rw [RingEquiv.apply_symm_apply, map_mul, map_pow] at h2
    rw [h2, mul_comm, Units.coe_map]
    rfl

variable (D : D7) (u : D.what₂.Word)

theorem local_basis_change_decomp (A : AtTTied u) (w : D.what₂.places.Pl) (hw : OverT D u w) (v : (D.mem u).A.vT)
    (i : ℕ) (hi : i ≤ D.R.m) (Lv : LvTied u A i hi) (c : (D.mem u).C.cls i)
    (hLc0 : clsCrd D u i hi c ≤ Ld D u i hi c) (B B' : GL (Fin (D.R.N i)) D.host.E)
    (hB : IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B)
    (hB' : IsLocBasis (D.mem u).A.T (Lk A i hi v c : Set _) B')
    (hunit : ((((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det * (((D.mem u).A.T : ℂ))⁻¹ ∈ bwA_Ow D w ∧
      ((D.mem u).A.T : ℂ) * (((((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det)⁻¹ ∈ bwA_Ow D w) :
    ∃ (K₁ K₂ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ) (j : Fin (D.R.N i)) (ϖ : bwA_Ow D w)
      (ε η : (bwA_Ow D w)ˣ), Irreducible ϖ ∧
      K₁ ∈ bwA_EO (bwA_Ow D w) (D.R.N i) ∧ K₂ ∈ bwA_EO (bwA_Ow D w) (D.R.N i) ∧ K₁.det * K₂.det = 1 ∧
      ((D.mem u).A.T : ℂ) = ((η : bwA_Ow D w) : ℂ) *
        (((ε : bwA_Ow D w) * ϖ ^ D.what₂.places.ramIdx w : bwA_Ow D w) : ℂ) ∧
      bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v) =
        K₁ * Matrix.diagonal (Function.update 1 j
          ((((ε : bwA_Ow D w) * ϖ ^ D.what₂.places.ramIdx w : bwA_Ow D w) : ℂ))⁻¹) * K₂ := by
  have hLk : Lk A i hi v c ≤ Ld D u i hi c := sup_le hLc0 Submodule.smul_le_right
  have hNe : bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v) =
      (((B'⁻¹ * B : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v)) := by
    simp only [bwA_N, atInf, ↓reduceIte]
  rw [hNe]
  set σ := embT D ((D.fm u).tauOf w v) with hσ
  set N := (((B'⁻¹ * B : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map σ
    with hNdef
  set M := (((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map σ
    with hMdef
  set colB : Fin (D.R.N i) → Fin (D.R.N i) → D.host.E :=
    fun k r => (B : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) r k with hcolB
  have hNa : ∀ a k, N a k = σ ((((B'⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix _ _ D.host.E) *ᵥ colB k) a) := by
    intro a k; rw [hcolB, bwD_mulVec_col, ← Units.val_mul]; rfl
  have hNM : N * M = 1 := by
    rw [hNdef, hMdef, ← Matrix.map_mul, ← Units.val_mul,
      show B'⁻¹ * B * (B⁻¹ * B') = 1 by group, Units.val_one, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have hMI : bwD_Int (bwA_Ow D w) M := by
    intro a k
    obtain ⟨s, hs, hsL⟩ := bwD_col_loc D u w hw hB' k
    have := bwD_locBasis_int D u w hw ((D.fm u).tauOf w v) hB _ s hs (hLk hsL) a
    rw [bwD_mulVec_col, ← Units.val_mul] at this
    exact this
  choose sB hsB hsBL using fun k => bwD_col_loc D u w hw hB k
  have hT0 : ∀ k, (sB k : D.host.E) ≠ 0 := fun k => Nat.cast_ne_zero.2 (fun h => hsB k (h ▸ dvd_zero _))
  have htN : ∀ a b, ((D.mem u).A.T : ℂ) * N a b ∈ bwA_Ow D w := by
    intro a b
    have hL : (sB b : D.host.E) • (((D.mem u).A.T : D.host.E) • colB b) ∈ (Lk A i hi v c : Set _) := by
      rw [smul_comm]
      have := bwA_T_smul_Ld_mem_Lk D u A i hi v c _ (hsBL b)
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.E] at this
      exact this
    have := bwD_locBasis_int D u w hw ((D.fm u).tauOf w v) hB' _ (sB b) (hsB b) hL a
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast] at this
    rw [hNa]; exact this
  obtain ⟨j, av, hav, hcol⟩ : ∃ (j : Fin (D.R.N i)) (av : Fin (D.R.N i) → ℂ), (∀ k, av k ∈ bwA_Ow D w) ∧
      ∀ k, k ≠ j → ∀ a, N a k - N a j * av k ∈ bwA_Ow D w := by
    set φ : Fin (D.R.N i) → (D.mem u).A.Fv v := fun k => (D.fm u).fv i v c (Lv.pr v c ⟨_, hsBL k⟩) with hφ
    by_cases hex : ∃ j, φ j ≠ 0
    · obtain ⟨j, hj⟩ := hex
      choose α hα using fun k => A.res_surj v (φ k / φ j)
      refine ⟨j, fun k => σ ((α k : D.host.E) * (sB j : D.host.E) / (sB k : D.host.E)), fun k => ?_, fun k _ a => ?_⟩
      · refine bwD_mem_Ow D u w hw _ _ (sB k) (hsB k) ⟨α k * (sB j : 𝓞 D.host.E), ?_⟩
        rw [map_mul, map_natCast]; field_simp [hT0 k]
      · set q : D.host.E := (α k : D.host.E) * (sB j : D.host.E) / (sB k : D.host.E) with hq
        have hz : (D.fm u).fv i v c (Lv.pr v c (⟨_, hsBL k⟩ - α k • ⟨_, hsBL j⟩)) = 0 := by
          rw [map_sub, map_sub, Lv.pr_smul, map_smul, hα k, smul_eq_mul, div_mul_cancel₀ _ hj, sub_self]
        have hzL := (Lv.fv_ker v c _).1 hz
        have hx : (sB k : D.host.E) • (colB k - q • colB j) ∈ (Lk A i hi v c : Set _) := by
          have e : (sB k : D.host.E) • (colB k - q • colB j) =
              ((⟨_, hsBL k⟩ - α k • ⟨_, hsBL j⟩ : Ld D u i hi c) : Fin (D.R.N i) → D.host.E) := by
            ext r
            simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hq]
            rw [Algebra.smul_def]
            field_simp [hT0 k]
            ring
          rw [e]; exact hzL
        have := bwD_locBasis_int D u w hw ((D.fm u).tauOf w v) hB' _ (sB k) (hsB k) hx a
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul] at this
        rw [hNa, hNa, mul_comm (σ _)]; exact this
    · push Not at hex
      refine ⟨⟨0, D.R.N_pos i⟩, 0, fun _ => (bwA_Ow D w).zero_mem, fun k _ a => ?_⟩
      rw [Pi.zero_apply, mul_zero, sub_zero, hNa]
      exact bwD_locBasis_int D u w hw ((D.fm u).tauOf w v) hB' _ (sB k) (hsB k)
        ((Lv.fv_ker v c _).1 (hex k)) a
  obtain ⟨K₁, K₂, hK₁, hK₂, hpO, hp0, hdet, -, hdec⟩ :=
    bwD_decomp (bwD_loc_Ow D w) N M _ hMI hNM htN j av hav hcol

  have hKK : K₁.det * K₂.det = 1 := by
    have h1 := congrArg Matrix.det hdec
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
      Finset.prod_update_of_mem (Finset.mem_univ j)] at h1
    simp only [Pi.one_apply, Finset.prod_const_one, mul_one] at h1
    rw [h1] at hdet
    have : K₁.det * M.det⁻¹ * K₂.det * M.det = K₁.det * K₂.det := by field_simp
    rw [← this]; exact hdet

  obtain ⟨ϖ₀, hϖ₀, ε₀, hT⟩ := Formalism.MainNotions.product_first_zeroth_parts.exists_unif (D := D) (u := u) w hw
  let e : intW D.what₂.places w ≃+* bwA_Ow D w :=
    (intW D.what₂.places w).equivMapOfInjective D.what₂.embLL D.what₂.embLL.injective
  have hTne : ((D.mem u).A.T : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  obtain ⟨h1, h2⟩ := hunit
  let uu : (bwA_Ow D w)ˣ :=
    { val := ⟨M.det * ((D.mem u).A.T : ℂ)⁻¹, h1⟩
      inv := ⟨((D.mem u).A.T : ℂ) * M.det⁻¹, h2⟩
      val_inv := by apply Subtype.ext; show M.det * ((D.mem u).A.T : ℂ)⁻¹ * (((D.mem u).A.T : ℂ) * M.det⁻¹) = 1
                    field_simp
      inv_val := by apply Subtype.ext; show ((D.mem u).A.T : ℂ) * M.det⁻¹ * (M.det * ((D.mem u).A.T : ℂ)⁻¹) = 1
                    field_simp }
  have hTe : ((D.mem u).A.T : ℂ) = (((Units.map (e : intW D.what₂.places w →* bwA_Ow D w) ε₀ : bwA_Ow D w) *
      (e ϖ₀) ^ D.what₂.places.ramIdx w : bwA_Ow D w) : ℂ) := by
    have h3 := congrArg (fun x => ((e x : bwA_Ow D w) : ℂ)) hT
    simp only [map_mul, map_pow, map_natCast] at h3
    rw [Units.coe_map]
    exact_mod_cast h3
  have hval : (((uu * Units.map (e : intW D.what₂.places w →* bwA_Ow D w) ε₀ : (bwA_Ow D w)ˣ) : bwA_Ow D w) *
      (e ϖ₀) ^ D.what₂.places.ramIdx w : bwA_Ow D w) = M.det := by
    rw [Units.val_mul, mul_assoc, Subring.coe_mul, ← hTe]
    show M.det * ((D.mem u).A.T : ℂ)⁻¹ * ((D.mem u).A.T : ℂ) = M.det
    field_simp
  refine ⟨K₁, K₂, j, e ϖ₀, uu * Units.map (e : intW D.what₂.places w →* bwA_Ow D w) ε₀, uu⁻¹,
    (MulEquiv.irreducible_iff e).2 hϖ₀, hK₁, hK₂, hKK, ?_, ?_⟩
  · rw [hval]
    show ((D.mem u).A.T : ℂ) = ((D.mem u).A.T : ℂ) * M.det⁻¹ * M.det
    field_simp
  · rw [hval]
    exact hdec

theorem local_basis_change_decomp_compatible (Tt : FormsTied D u) (hU : UnramifiedAtLevelPrimes D u Tt.atT) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (hs : (D.fm u).seenP w = true) (v : (D.mem u).A.vT)
    (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E)
    (hB : IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B)
    (hB' : IsLocBasis (D.mem u).A.T (Lk Tt.atT i hi v c : Set _) B') :
    ∃ (K₁ K₂ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ) (j : Fin (D.R.N i)) (ϖ : bwA_Ow D w)
      (ε η : (bwA_Ow D w)ˣ), Irreducible ϖ ∧
      K₁ ∈ bwA_EO (bwA_Ow D w) (D.R.N i) ∧ K₂ ∈ bwA_EO (bwA_Ow D w) (D.R.N i) ∧ K₁.det * K₂.det = 1 ∧
      ((D.mem u).A.T : ℂ) = ((η : bwA_Ow D w) : ℂ) *
        (((ε : bwA_Ow D w) * ϖ ^ D.what₂.places.ramIdx w : bwA_Ow D w) : ℂ) ∧
      bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v) =
        K₁ * Matrix.diagonal (Function.update 1 j
          ((((ε : bwA_Ow D w) * ϖ ^ D.what₂.places.ramIdx w : bwA_Ow D w) : ℂ))⁻¹) * K₂ :=
  local_basis_change_decomp D u Tt.atT w hw v i hi (Tt.lv i hi) c (bwL_lcInt D u Tt i hi c) B B' hB hB'
    (det_basis_change_div_prime_and_inv_integral D u Tt hU w hw hs v i hi c B B' hB hB')

theorem length_factor_local_basis (A : AtTTied u) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (v : (D.mem u).A.vT) (Lv : LvTied u A 0 (Nat.zero_le _)) (c : (D.mem u).C.cls 0)
    (hLc0 : clsCrd D u 0 (Nat.zero_le _) c ≤ Ld D u 0 (Nat.zero_le _) c) (B B' : GL (Fin (D.R.N 0)) D.host.E)
    (hB : IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) B)
    (hB' : IsLocBasis (D.mem u).A.T (Lk A 0 (Nat.zero_le _) v c : Set _) B')
    (hunit : ((((B⁻¹ * B' : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det * (((D.mem u).A.T : ℂ))⁻¹ ∈ bwA_Ow D w ∧
      ((D.mem u).A.T : ℂ) * (((((B⁻¹ * B' : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det)⁻¹ ∈ bwA_Ow D w)
    (Nτ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ)
    (hN : Nτ = bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v)) :
    ∃ n : ℕ, Module.length (bwA_Ow D w)
      (((bwA_span (bwA_Ow D w) le_rfl ((D.fm u).lam 0 ((D.fm u).tauOf w v)).natW).map (mvPolynomialRowLinearMap (bwA_Ow D w) Nτ)).map
          (mvPolynomialScalingMap (bwA_Ow D w) (Nτ.det ^ ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift)) ⧸
        ((bwA_span (bwA_Ow D w) le_rfl ((D.fm u).lam 0 ((D.fm u).tauOf w v)).natW).map
          (mvPolynomialScalingMap (bwA_Ow D w) (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)))).comap
          (((bwA_span (bwA_Ow D w) le_rfl ((D.fm u).lam 0 ((D.fm u).tauOf w v)).natW).map
            (mvPolynomialRowLinearMap (bwA_Ow D w) Nτ)).map
              (mvPolynomialScalingMap (bwA_Ow D w) (Nτ.det ^ ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift))).subtype) = n ∧
      (D.R.k : ℚ) * n = (D.what₂.places.ramIdx w : ℚ) *
        (Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 ((D.fm u).tauOf w v))) : ℚ) *
        ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) := by
  haveI := local_ring_is_dvr D w
  obtain ⟨K₁, K₂, j, ϖ, ε, η, hϖ, h₁, h₂, hKK, hTη, hdec⟩ :=
    local_basis_change_decomp D u A w hw v 0 (Nat.zero_le _) Lv c hLc0 B B' hB hB' hunit
  set lam := (D.fm u).lam 0 ((D.fm u).tauOf w v) with hlam
  set p : ℂ := (((ε : bwA_Ow D w) * ϖ ^ D.what₂.places.ramIdx w : bwA_Ow D w) : ℂ) with hp
  have hp0 : p ≠ 0 := by
    rw [hp]
    intro h
    have h' : ((ε : bwA_Ow D w) * ϖ ^ D.what₂.places.ramIdx w : bwA_Ow D w) = 0 := Subtype.ext h
    rcases mul_eq_zero.1 h' with h'' | h''
    · exact ε.ne_zero h''
    · exact hϖ.ne_zero (pow_eq_zero_iff'.1 h'' |>.1)
  have hNe : Nτ = K₁ * Matrix.diagonal (Function.update 1 j p⁻¹) * K₂ := by rw [hN, hdec]
  have hdetN : Nτ.det = p⁻¹ := by
    rw [hNe, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ j)]
    simp only [Pi.one_apply, Finset.prod_const_one, mul_one]
    linear_combination p⁻¹ * hKK
  set s := lam.detShift with hsdef
  have hb : (D.fm u).bTop ((D.fm u).tauOf w v) = -s := rfl

  let f : (bwA_Ow D w)ˣ →* ℂˣ := Units.map ((bwA_Ow D w).subtype : bwA_Ow D w →* ℂ)
  set η' : (bwA_Ow D w)ˣ := η ^ (-s) with hη'
  have hη'c : (((η' : bwA_Ow D w)) : ℂ) = (((η : bwA_Ow D w)) : ℂ) ^ (-s) := by
    have e1 : (((η' : bwA_Ow D w)) : ℂ) = ((f η' : ℂˣ) : ℂ) := rfl
    have e2 : (((η : bwA_Ow D w)) : ℂ) = ((f η : ℂˣ) : ℂ) := rfl
    rw [e1, e2, hη', map_zpow, Units.val_zpow_eq_zpow_val]
  have hT : (((D.mem u).A.T : ℂ)) ^ (D.fm u).bTop ((D.fm u).tauOf w v) =
      Nτ.det ^ s * (((η' : bwA_Ow D w)) : ℂ) := by
    rw [hb, hTη, hdetN, hη'c, mul_zpow, inv_zpow', mul_comm]
  have hc0 : Nτ.det ^ s ≠ 0 := zpow_ne_zero _ (by rw [hdetN]; exact inv_ne_zero hp0)
  rw [hT, show mvPolynomialRowLinearMap (bwA_Ow D w) (n := D.R.N 0) Nτ =
      mvPolynomialRowLinearMap (bwA_Ow D w) (K₁ * Matrix.diagonal (Function.update 1 j p⁻¹) * K₂) by rw [hNe]]
  obtain ⟨n, hn, hrn⟩ := length_factor_elementary_diag (O := bwA_Ow D w) le_rfl lam.natW (dominant_natWeight_antitone lam) (bwD_loc_Ow D w) ϖ hϖ
    ε (D.what₂.places.ramIdx w) j K₁ K₂ h₁ h₂ hKK (Nτ.det ^ s) hc0 η'
  refine ⟨n, hn, ?_⟩
  have hk : D.R.N 0 = D.R.k := D.R.N_zero
  have hsum := dominant_natWeight_sum lam
  simp only [rowNu_self_alt] at hrn
  have hq : (D.R.N 0 : ℚ) * n = (D.what₂.places.ramIdx w : ℚ) *
      (Module.finrank ℤ (Formalism.GradedWeylDivisibility.weyl ℤ (D.R.N 0) (D.R.N 0) le_rfl lam.natW) : ℚ) * ((∑ a, lam.natW a : ℕ) : ℚ) := by
    exact_mod_cast hrn
  have hsumQ : ((∑ a, lam.natW a : ℕ) : ℚ) = ((∑ a, lam.w a : ℤ) : ℚ) - (D.R.N 0 : ℚ) * s := by exact_mod_cast hsum
  rw [hsumQ] at hq
  have hdel : delSq ℤ (D.R.N 0) lam = Formalism.GradedWeylDivisibility.weyl ℤ (D.R.N 0) (D.R.N 0) le_rfl lam.natW := rfl
  rw [hdel, hb, ← hk, hq]
  simp only [wsum]
  push_cast
  ring

theorem length_factor_compatible_forms (Tt : FormsTied D u) (hU : UnramifiedAtLevelPrimes D u Tt.atT) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (hs : (D.fm u).seenP w = true) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (B B' : GL (Fin (D.R.N 0)) D.host.E)
    (hB : IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) B)
    (hB' : IsLocBasis (D.mem u).A.T (Lk Tt.atT 0 (Nat.zero_le _) v c : Set _) B')
    (Nτ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ)
    (hN : Nτ = bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v)) :
    ∃ n : ℕ, Module.length (bwA_Ow D w)
      (((bwA_span (bwA_Ow D w) le_rfl ((D.fm u).lam 0 ((D.fm u).tauOf w v)).natW).map (mvPolynomialRowLinearMap (bwA_Ow D w) Nτ)).map
          (mvPolynomialScalingMap (bwA_Ow D w) (Nτ.det ^ ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift)) ⧸
        ((bwA_span (bwA_Ow D w) le_rfl ((D.fm u).lam 0 ((D.fm u).tauOf w v)).natW).map
          (mvPolynomialScalingMap (bwA_Ow D w) (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)))).comap
          (((bwA_span (bwA_Ow D w) le_rfl ((D.fm u).lam 0 ((D.fm u).tauOf w v)).natW).map
            (mvPolynomialRowLinearMap (bwA_Ow D w) Nτ)).map
              (mvPolynomialScalingMap (bwA_Ow D w) (Nτ.det ^ ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift))).subtype) = n ∧
      (D.R.k : ℚ) * n = (D.what₂.places.ramIdx w : ℚ) *
        (Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 ((D.fm u).tauOf w v))) : ℚ) *
        ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) :=
  length_factor_local_basis D u Tt.atT w hw v (Tt.lv 0 (Nat.zero_le _)) c (bwL_lcInt D u Tt 0 (Nat.zero_le _) c) B B' hB hB'
    (det_basis_change_div_prime_and_inv_integral D u Tt hU w hw hs v 0 (Nat.zero_le _) c B B' hB hB') Nτ hN

theorem tensor_weyl_basis_lin_indep {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (lam : ι → DomWeight N) (κ : ι → Type)
    (b : ∀ τ, Module.Basis (κ τ) ℤ (delSq ℤ N (lam τ))) :
    LinearIndependent ℂ (fun g : (∀ τ, κ τ) => Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ)
      ((b τ (g τ) : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ))) := by
  have hb : ∀ τ, LinearIndependent ℂ (fun i : κ τ => MvPolynomial.map (Int.castRingHom ℂ)
      ((b τ i : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ)) := fun τ =>
    weyl_basis_lin_indep_field le_rfl (lam τ).natW (dominant_natWeight_antitone (lam τ)) ℂ (b τ)
  exact linearIndependent_prod_rename_of_forall κ (fun τ (i : κ τ) => MvPolynomial.map (Int.castRingHom ℂ)
      ((b τ i : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ)) hb

end Tied

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
