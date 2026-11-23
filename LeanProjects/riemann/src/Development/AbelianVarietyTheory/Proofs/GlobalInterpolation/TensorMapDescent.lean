import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InterlacingEquivariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.OnePlaceBranchStatement
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor

open MvPolynomial NumberField

noncomputable section

namespace GlobalTheory.Proof.TensorMapDescent

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

section BaseChange

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

theorem fockB_map {σ : Type} (f g : MvPolynomial σ K) : fockB (map φ f) (map φ g) = φ (fockB f g) := by
  rw [fockB_eq_sum _ _ f.support (support_map_subset _ _), fockB, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [coeff_map]

theorem map_ten {ι : Type} [Fintype ι] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) K) :
    map φ (ten f) = ten fun τ => map φ (f τ) := by
  unfold ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => fk_map_blockEmb φ τ _

theorem ten_mem {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (f : ι → MvPolynomial (Fin n × Fin n) K)
    (hf : ∀ τ, f τ ∈ nablaSq K n (lam τ)) : ten f ∈ VV K lam :=
  Submodule.subset_span ⟨f, hf, rfl⟩

theorem ten_ne_zero {ι : Type} [Fintype ι] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) K) (hf : ∀ τ, f τ ≠ 0) :
    ten f ≠ 0 := by
  unfold ten
  rw [Finset.prod_ne_zero_iff]
  intro τ _
  have hinj : Function.Injective (Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ) :=
    MvPolynomial.rename_injective _ (fun a b h => (Prod.mk.inj h).2)
  exact (map_ne_zero_iff _ hinj).mpr (hf τ)

theorem map_mem_VV {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (F : Pol K ι n) (hF : F ∈ VV K lam) :
    map φ F ∈ VV K' lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    have h := map_ten φ f
    unfold ten at h
    rw [h]
    exact ten_mem lam _ fun τ => Formalism.GradedWeylDivisibility.dualWeylMap K K' φ n n _ _ (hf τ)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

theorem ssB_desc {n : ℕ} (ν : Fin n → ℕ) (m : Formalism.GradedWeylDivisibility.ssIdx n n ν) :
    ∃ f ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n ν, ssB K' ν m = map φ f := by
  obtain ⟨k, sz, hsz, I, hsh, -, h⟩ := ((Formalism.GradedWeylDivisibility.sSBasis K' n n ν).choose_spec.2 m).2.2
  refine ⟨Formalism.GradedWeylDivisibility.bideterminant K sz hsz I, ?_, by rw [fk_map_bidet]; exact h⟩
  rw [← hsh]
  exact Formalism.GradedWeylDivisibility.bidetMem K n n k sz hsz I

theorem bVVfun_desc {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (i : VVIdx lam) :
    ∃ F ∈ VV K lam, bVVfun K' lam i = map φ F := by
  choose f hf hf' using fun τ => ssB_desc φ (lam τ).natW (i τ)
  refine ⟨ten f, ten_mem lam f hf, ?_⟩
  rw [map_ten]
  exact congrArg ten (funext hf')

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem eq_zero_of_fockB [CharZero K] (sg : ι → DomWeight n) (x : VV K sg)
    (h : ∀ i, fockB (bVVfun K sg i) (x : Pol K ι n) = 0) : x = 0 := by
  refine (pairingBNondegenerate_holds K ι n sg).2 x fun y => ?_
  have : (pairBK sg).flip x = 0 := by
    refine (bVV K sg).ext fun i => ?_
    rw [LinearMap.flip_apply, pairBK_apply, pairB_apply, bVV_coe, h i, mul_zero, LinearMap.zero_apply]
  exact LinearMap.congr_fun this y

open Classical in
theorem gramB_det_ne_zero [CharZero K] (sg : ι → DomWeight n) : (Br.gramB (K := K) sg).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have h1 : ∑ j, v j • bVV K sg j = 0 := by
    refine eq_zero_of_fockB sg _ fun i => ?_
    have := congrFun hv0 i
    simp only [Matrix.mulVec, dotProduct, Br.gramB, Matrix.of_apply, Pi.zero_apply] at this
    rw [← fockBL_apply, Submodule.coe_sum, map_sum, ← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, map_smul, bVV_coe, fockBL_apply, smul_eq_mul, mul_comm]
  exact hv (funext (Fintype.linearIndependent_iff.mp (bVV K sg).linearIndependent v h1))

theorem fockB_projVV_basis [CharZero K] (sg : ι → DomWeight n) (F : Pol K ι n) (k : VVIdx sg) :
    fockB (bVVfun K sg k) (Br.projVV sg F : Pol K ι n) = fockB (bVVfun K sg k) F := by
  classical
  have hG := Matrix.mul_nonsing_inv (Br.gramB (K := K) sg) (Ne.isUnit (gramB_det_ne_zero sg))
  have h1 : fockB (bVVfun K sg k) (Br.projVV sg F : Pol K ι n) =
      ∑ i, ∑ j, Br.gramB (K := K) sg k i * (Br.gramB (K := K) sg)⁻¹ i j * fockB (bVVfun K sg j) F := by
    rw [← fockBL_apply]
    simp only [Br.projVV, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, Submodule.coe_sum,
      Submodule.coe_smul, map_sum, map_smul, bVV_coe, fockBL_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show Br.gramB (K := K) sg k i = fockB (bVVfun K sg k) (bVVfun K sg i) from rfl]
    ring
  rw [h1, Finset.sum_comm]
  simp only [← Finset.sum_mul, ← Matrix.mul_apply, hG, Matrix.one_apply]
  simp

theorem fockB_projVV [CharZero K] (sg : ι → DomWeight n) (F y : Pol K ι n) (hy : y ∈ VV K sg) :
    fockB y (Br.projVV sg F : Pol K ι n) = fockB y F := by
  rw [← (bVVfun_spec K sg).2] at hy
  simp only [← fockBL_apply]
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact fockB_projVV_basis sg F k
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | smul c x _ hx => simp only [map_smul, LinearMap.smul_apply, hx]

theorem projVV_map [CharZero K] [CharZero K'] (sg : ι → DomWeight n) (F : Pol K ι n) :
    (Br.projVV sg (map φ F) : Pol K' ι n) = map φ (Br.projVV sg F : Pol K ι n) := by
  have h := eq_zero_of_fockB sg
    (Br.projVV sg (map φ F) - ⟨map φ (Br.projVV sg F : Pol K ι n), map_mem_VV φ sg _ (Br.projVV sg F).2⟩) fun i => by
      rw [← fockBL_apply, Submodule.coe_sub, map_sub, fockBL_apply, fockBL_apply, fockB_projVV_basis]
      obtain ⟨Y, hY, hY'⟩ := bVVfun_desc φ sg i
      rw [hY', fockB_map, fockB_map, fockB_projVV sg F Y hY, sub_self]
  exact congrArg Subtype.val (sub_eq_zero.mp h)

variable {N : ℕ} (hN : N = n + 1)

omit [Fintype ι] in
theorem coefLast_map (b : ι → Fin n → ℕ) (F : Pol K ι N) :
    Br.coefLast hN b (map φ F) = map φ (Br.coefLast hN b F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial m a =>
    have h1 : (monomial m a : Pol K ι N) = a • monomial m 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
    have h2 : (monomial m (φ a) : Pol K' ι N) = φ a • monomial m 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [map_monomial, h2, h1, map_smul, map_smul, Br.coefLast_monomial, Br.coefLast_monomial]
    split_ifs
    · simp [smul_monomial, map_monomial]
    · simp
  | add p q hp hq => simp only [map_add, hp, hq]

theorem xiBr_map (lam : DomWeight N) (sg : DomWeight n) : map φ (Br.xiBr K hN lam sg) = Br.xiBr K' hN lam sg := by
  simp only [Br.xiBr, Br.zMinor, map_prod, map_mul, map_pow, fk_map_initMinor, Formalism.GradedWeylDivisibility.lclosedeq_lpMinor_map]

theorem brConst_map (lam : ι → DomWeight N) (sg : ι → DomWeight n) :
    φ (Br.brConst hN K lam sg) = Br.brConst hN K' lam sg := by
  simp only [Br.brConst, Br.kapBr, map_prod, map_mul, map_div₀, map_intCast, ← fockB_map, xiBr_map, extremal,
    Formalism.GradedWeylDivisibility.lclosedeq_hw_map]

theorem branchingProjection_map [CharZero K] [CharZero K'] (lam : ι → DomWeight N) (sg : ι → DomWeight n) (F : Pol K ι N) :
    (Br.brStdP hN lam sg (map φ F) : Pol K' ι n) = map φ (Br.brStdP hN lam sg F : Pol K ι n) := by
  simp only [Br.brStdP, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul]
  rw [coefLast_map, projVV_map, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, map_C, brConst_map]

theorem brOne_map [CharZero K] [CharZero K'] (lam : DomWeight N) (sg : DomWeight n) (f : MvPolynomial (Fin N × Fin N) K) :
    GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne K' hN lam sg (map φ f) = map φ (GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne K hN lam sg f) := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Submodule.subtype_apply]
  rw [← map_rename, branchingProjection_map, map_rename]

end BaseChange

theorem baseChange : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.BaseChange := by
  intro K K' _ _ _ φ N n hN lam sg _ _ f _
  haveI : CharZero K' := (RingHom.charZero_iff φ.injective).mp inferInstance
  exact brOne_map φ hN lam sg f

def FamilyNonzero : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → (∀ τ, Br.SameShift (lam τ) (sg τ)) → Br.brStd (K := K) hN lam sg ≠ 0

end GlobalTheory.Proof.TensorMapDescent
