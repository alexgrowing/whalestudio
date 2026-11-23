import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalingVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryLeviLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMapPreservesRationalPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterMultiplicativeStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConeRepresentatives
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatUOfForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

noncomputable section

namespace GlobalTheory.MidLineWitt

open GlobalTheory.PlaneLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem form_skew {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = -J i j)
    (a b : Fin n → E) : form σ J a b = -σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem two_mulVec {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (p q a b v : Fin n → E) :
    (1 + Matrix.vecMulVec p (J *ᵥ fun i => σ (a i)) + Matrix.vecMulVec q (J *ᵥ fun i => σ (b i))) *ᵥ v =
      v + form σ J v a • p + form σ J v b • q := by
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, form, dotProduct_comm v]
  ext i
  simp [mul_comm]

theorem exists_eichler {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = -J i j)
    {x y p : Fin n → E} (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hpp : form σ J p p = 0)
    (hxy : form σ J x y = 1) (hxp : form σ J x p = 1) :
    ∃ U : Matrix (Fin n) (Fin n) E, (∀ u v, form σ J (U *ᵥ u) (U *ᵥ v) = form σ J u v) ∧ U *ᵥ y = p := by
  have sk := form_skew hσ hJ
  have hyx : form σ J y x = -1 := by rw [sk, hxy, map_one]
  have hpx : form σ J p x = -1 := by rw [sk, hxp, map_one]
  obtain ⟨k, hk⟩ : ∃ k, k = form σ J y p := ⟨_, rfl⟩
  have hpy : form σ J p y = -σ k := by rw [hk]; exact sk _ _
  refine ⟨1 + Matrix.vecMulVec ((-1 : E) • x) (J *ᵥ fun i => σ ((p + (-1 : E) • y) i)) +
      Matrix.vecMulVec ((-1 : E) • p + y + (-k) • x) (J *ᵥ fun i => σ (x i)), fun a b => ?_, ?_⟩
  · rw [two_mulVec, two_mulVec]
    simp only [form_add_left, form_smul_left, form_add_right, form_smul_right, hxx, hyy, hxy, hyx, map_neg, map_one,
      hpx, hxp, hpp, hpy, ← hk, map_add, map_mul]
    rw [sk x b, sk y b, sk p b]
    ring
  · rw [two_mulVec, form_add_right, form_smul_right, hyy, hyx, ← hk]
    module

theorem exists_form_ne {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hσ : ∀ x, σ (σ x) = x) (hd : J.det ≠ 0)
    {z : Fin n → E} (hz : z ≠ 0) : ∃ u, form σ J u z ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply hz
  have h1 : J *ᵥ (fun i => σ (z i)) = 0 := by
    funext i
    have := hc (Pi.single i 1)
    rw [form, single_one_dotProduct] at this
    exact this
  have h2 := Matrix.eq_zero_of_mulVec_eq_zero hd h1
  funext i
  have h3 : σ (z i) = 0 := congrFun h2 i
  rw [← hσ (z i), h3, map_zero]
  rfl

theorem exists_partner {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = -J i j)
    (hd : J.det ≠ 0) {x y z : Fin n → E} (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (hz : z ≠ 0) (hzz : form σ J z z = 0) :
    ∃ q, form σ J q q = 0 ∧ form σ J q z ≠ 0 ∧ form σ J q x ≠ 0 := by
  have sk := form_skew hσ hJ
  have hyx : form σ J y x = -1 := by rw [sk, hxy, map_one]
  by_cases hyz : form σ J y z = 0
  swap
  · exact ⟨y, hyy, hyz, by rw [hyx]; simp⟩
  by_cases hxz : form σ J x z = 0
  swap
  · refine ⟨x + y, ?_, ?_, ?_⟩
    · simp only [form_add_left, form_add_right, hxx, hyy, hxy, hyx]; ring
    · rwa [form_add_left, hyz, add_zero]
    · rw [form_add_left, hxx, hyx]; simp
  obtain ⟨u, hu⟩ := exists_form_ne hσ hd hz
  obtain ⟨q, hq⟩ : ∃ q, q = u + (form σ J u x + 1) • y := ⟨_, rfl⟩
  have hqx : form σ J q x = -1 := by rw [hq, form_add_left, form_smul_left, hyx]; ring
  have hqz : form σ J q z ≠ 0 := by rwa [hq, form_add_left, form_smul_left, hyz, mul_zero, add_zero]
  have hzx : form σ J z x = 0 := by rw [sk, hxz, map_zero, neg_zero]
  have hσz : σ (form σ J q z) ≠ 0 := fun h => hqz (by rw [← hσ (form σ J q z), h, map_zero])
  have hN : σ (form σ J q q) = -form σ J q q := by
    have := sk q q
    linear_combination this
  refine ⟨q + (form σ J q q / (2 * σ (form σ J q z))) • z, ?_, ?_, ?_⟩
  · simp only [form_add_left, form_add_right, form_smul_left, form_smul_right, hzz]
    rw [sk z q, map_div₀, map_mul, hσ, hN, map_ofNat]
    field_simp
    ring
  · rwa [form_add_left, form_smul_left, hzz, mul_zero, add_zero]
  · rw [form_add_left, form_smul_left, hzx, hqx]; simp

theorem exists_ratU_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E), (∀ e, σ (σ e) = e) → (∀ i j, σ (J j i) = -J i j) → J.det ≠ 0 →
    form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 → z ≠ 0 → form σ J z z = 0 →
    ∃ g ∈ ratU σ J, ∃ μ : E, μ ≠ 0 ∧ mat g *ᵥ incV F z = incV F (μ • x) := by
  intro F E _ _ _ _ _ σ n J x y z hσ hJ hd hxx hyy hxy hz hzz
  obtain ⟨q, hqq, hqz, hqx⟩ := exists_partner hσ hJ hd hxx hyy hxy hz hzz
  have hne : ∀ a : E, a ≠ 0 → σ a ≠ 0 := fun a ha h => ha (by rw [← hσ a, h, map_zero])
  have hiso : ∀ (c : E) (w : Fin n → E), form σ J w w = 0 → form σ J (c • w) (c • w) = 0 := fun c w hw => by
    rw [form_smul_left, form_smul_right, hw, mul_zero, mul_zero]
  have hone : ∀ w : Fin n → E, form σ J q w ≠ 0 → form σ J q ((σ (form σ J q w))⁻¹ • w) = 1 := fun w hw => by
    rw [form_smul_right, map_inv₀, hσ, inv_mul_cancel₀ hw]
  obtain ⟨U, hU, hUz⟩ := exists_eichler hσ hJ hqq (hiso _ _ hzz) (hiso _ _ hxx) (hone z hqz) (hone x hqx)
  obtain ⟨g, hg, hm⟩ := GlobalTheory.MidLineParam.exists_ratU_of_form (F := F) (σ := σ) hd U hU
  refine ⟨g, hg, σ (form σ J q z) * (σ (form σ J q x))⁻¹, mul_ne_zero (hne _ hqz) (inv_ne_zero (hne _ hqx)), ?_⟩
  rw [hm, GlobalTheory.MidLineParam.incM_mulVec, mul_smul, ← hUz, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ (hne _ hqz), one_smul]

end GlobalTheory.MidLineWitt

end
