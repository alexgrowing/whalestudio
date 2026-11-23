import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.IdeleAction
import GroundTheory.GlobalFields.Adele.Approximation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem exists_sub_mem_localIdeal {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (a : FiniteAdeleRing (𝓞 K) K) :
    ∃ k : K, ∀ v : HeightOneSpectrum (𝓞 K), a v - (k : v.adicCompletion K) ∈ localIdeal I v := by
  obtain ⟨d, hdI, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (coeToSubmodule_ne_bot.2 hI)
  obtain ⟨k', hk'⟩ := exists_sub_mem_integralFiniteAdeles
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) d⁻¹ * a)
  refine ⟨d * k', fun v ↦ ?_⟩
  have ht : ((d⁻¹ : K) : v.adicCompletion K) * a v - (k' : v.adicCompletion K) ∈
      v.adicCompletionIntegers K :=
    (mem_integralFiniteAdeles.1 hk') v
  have h1 : (d : v.adicCompletion K) * ((d⁻¹ : K) : v.adicCompletion K) = 1 := by
    rw [← adicCompletion.coe_mul, mul_inv_cancel₀ hd0, adicCompletion.coe_one]
  have h : a v - ((d * k' : K) : v.adicCompletion K) =
      (⟨_, ht⟩ : v.adicCompletionIntegers K) • (d : v.adicCompletion K) := by
    change _ = (((d⁻¹ : K) : v.adicCompletion K) * a v - (k' : v.adicCompletion K)) *
      (d : v.adicCompletion K)
    rw [adicCompletion.coe_mul]
    linear_combination -(a v) * h1
  rw [h]
  exact Submodule.smul_mem _ _ (coe_mem_localIdeal v hdI)

def dfinsuppOfFinite {ι : Type*} {β : ι → Type*} [∀ i, Zero (β i)] (f : ∀ i, β i)
    (hf : {i | f i ≠ 0}.Finite) : Π₀ i, β i :=
  ⟨f, Trunc.mk ⟨hf.toFinset.val, fun i ↦ by
    by_cases h : f i = 0
    · exact Or.inr h
    · left
      rw [Finset.mem_val]
      exact hf.mem_toFinset.2 h⟩⟩

@[simp]
theorem dfinsuppOfFinite_apply {ι : Type*} {β : ι → Type*} [∀ i, Zero (β i)] (f : ∀ i, β i)
    (hf : {i | f i ≠ 0}.Finite) (i : ι) : dfinsuppOfFinite f hf i = f i :=
  rfl

instance (v : HeightOneSpectrum (𝓞 K)) :
    IsScalarTower (𝓞 K) (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  adicCompletion.instIsScalarTower' (𝓞 K) K v

abbrev LocalQuotient (I : FractionalIdeal (𝓞 K)⁰ K) (v : HeightOneSpectrum (𝓞 K)) :=
  v.adicCompletion K ⧸ localIdeal I v

def toLocalQuotients {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    K →ₗ[𝓞 K] DirectSum (HeightOneSpectrum (𝓞 K)) (LocalQuotient I) where
  toFun x := dfinsuppOfFinite (fun v ↦ Submodule.Quotient.mk (x : v.adicCompletion K))
    (Filter.eventually_cofinite.1 ((eventually_coe_mem_localIdeal hI x).mono fun v hv ↦
      (Submodule.Quotient.mk_eq_zero _).2 hv))
  map_add' x y := by
    refine DFinsupp.ext fun v ↦ ?_
    rw [DirectSum.add_apply]
    change Submodule.Quotient.mk ((x + y : K) : v.adicCompletion K) =
      Submodule.Quotient.mk (x : v.adicCompletion K) + Submodule.Quotient.mk (y : v.adicCompletion K)
    rw [adicCompletion.coe_add, Submodule.Quotient.mk_add]
  map_smul' r x := by
    refine DFinsupp.ext fun v ↦ ?_
    rw [RingHom.id_apply, DirectSum.smul_apply]
    change Submodule.Quotient.mk ((r • x : K) : v.adicCompletion K) =
      r • Submodule.Quotient.mk (p := localIdeal I v) (x : v.adicCompletion K)
    rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, Algebra.smul_def (A := v.adicCompletion K),
      adicCompletion.coe_mul]
    rfl

theorem toLocalQuotients_apply {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (x : K)
    (v : HeightOneSpectrum (𝓞 K)) :
    toLocalQuotients hI x v = Submodule.Quotient.mk (x : v.adicCompletion K) :=
  rfl

theorem toLocalQuotients_eq_zero_iff {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) {x : K} :
    toLocalQuotients hI x = 0 ↔ x ∈ I := by
  rw [mem_iff_forall_mem_localIdeal hI, DFinsupp.ext_iff]
  simp only [toLocalQuotients_apply, DFinsupp.coe_zero, Pi.zero_apply,
    Submodule.Quotient.mk_eq_zero]

theorem ker_toLocalQuotients {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    LinearMap.ker (toLocalQuotients hI) = (I : Submodule (𝓞 K) K) := by
  ext x
  rw [LinearMap.mem_ker, toLocalQuotients_eq_zero_iff, mem_coe]

theorem toLocalQuotients_surjective {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    Function.Surjective (toLocalQuotients hI) := by
  classical
  intro f
  choose y hy using fun v ↦ Submodule.Quotient.mk_surjective _ (f v)
  let z : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K := fun v ↦ if f v = 0 then 0 else y v
  have hz : ∀ v, Submodule.Quotient.mk (p := localIdeal I v) (z v) = f v := by
    intro v
    by_cases h : f v = 0
    · simp only [z, h, if_true, Submodule.Quotient.mk_zero]
    · simp only [z, h, if_false, hy]
  have hfin : {v | f v ≠ 0}.Finite :=
    f.support.finite_toSet.subset fun v hv ↦ DFinsupp.mem_support_iff.2 hv
  let a : FiniteAdeleRing (𝓞 K) K := ⟨z, Filter.eventually_cofinite.2 (hfin.subset fun v hv h ↦
    hv (by simp only [z, h, if_true]; exact (v.adicCompletionIntegers K).zero_mem))⟩
  obtain ⟨k, hk⟩ := exists_sub_mem_localIdeal hI a
  refine ⟨k, DFinsupp.ext fun v ↦ ?_⟩
  rw [toLocalQuotients_apply, ← hz v]
  exact ((Submodule.Quotient.eq _).2 (hk v)).symm

def quotientToLocalQuotients {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    (K ⧸ (I : Submodule (𝓞 K) K)) →ₗ[𝓞 K] DirectSum (HeightOneSpectrum (𝓞 K)) (LocalQuotient I) where
  toFun q := Quotient.liftOn' q (toLocalQuotients hI) fun a b h ↦ by
    rw [Submodule.quotientRel_def] at h
    have h0 := (toLocalQuotients_eq_zero_iff hI).2 h
    calc toLocalQuotients hI a = toLocalQuotients hI (b + (a - b)) :=
          congrArg (toLocalQuotients hI) (by abel)
      _ = toLocalQuotients hI b + toLocalQuotients hI (a - b) := map_add _ _ _
      _ = toLocalQuotients hI b := by rw [h0, add_zero]
  map_add' := by
    rintro ⟨a⟩ ⟨b⟩
    exact map_add (toLocalQuotients hI) a b
  map_smul' := by
    rintro r ⟨a⟩
    exact map_smul (toLocalQuotients hI) r a

theorem quotientToLocalQuotients_mk {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (x : K) :
    quotientToLocalQuotients hI (Submodule.Quotient.mk x) = toLocalQuotients hI x :=
  rfl

def quotientEquivLocalQuotients {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    (K ⧸ (I : Submodule (𝓞 K) K)) ≃ₗ[𝓞 K] DirectSum (HeightOneSpectrum (𝓞 K)) (LocalQuotient I) :=
  LinearEquiv.ofBijective (quotientToLocalQuotients hI) ⟨by
      rw [injective_iff_map_eq_zero]
      rintro ⟨a⟩ h
      have h' : toLocalQuotients hI a = 0 := h
      exact (Submodule.Quotient.mk_eq_zero _).2 ((toLocalQuotients_eq_zero_iff hI).1 h'), by
      intro y
      obtain ⟨x, rfl⟩ := toLocalQuotients_surjective hI y
      exact ⟨Submodule.Quotient.mk x, rfl⟩⟩

@[simp]
theorem quotientEquivLocalQuotients_mk {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (x : K) :
    quotientEquivLocalQuotients hI (Submodule.Quotient.mk x) = toLocalQuotients hI x :=
  rfl

namespace IdeleGroup

local notation "𝓘" => (FractionalIdeal (𝓞 K)⁰ K)ˣ

def localMul (s : IdeleGroup K) (I : 𝓘) (v : HeightOneSpectrum (𝓞 K)) :
    LocalQuotient (I : FractionalIdeal (𝓞 K)⁰ K) v ≃ₗ[𝓞 K]
      LocalQuotient ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v :=
  (Submodule.Quotient.equiv (localIdeal (I : FractionalIdeal (𝓞 K)⁰ K) v)
    (localIdeal ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v)
    ((finiteProj v s).mulLeftLinearEquiv (v.adicCompletionIntegers K) (v.adicCompletion K))
    (by
      rw [localIdeal_smul, Units.toLinearMap_mulLeftLinearEquiv, coe_finiteProj])).restrictScalars
    (𝓞 K)

theorem localMul_mk (s : IdeleGroup K) (I : 𝓘) (v : HeightOneSpectrum (𝓞 K))
    (y : v.adicCompletion K) :
    localMul s I v (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((finiteProj v s : v.adicCompletion K) * y) :=
  rfl

def smulQuotient (s : IdeleGroup K) (I : 𝓘) :
    (K ⧸ ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) ≃ₗ[𝓞 K]
      K ⧸ (((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) :=
  (quotientEquivLocalQuotients I.ne_zero).trans
    ((DFinsupp.mapRange.linearEquiv (localMul s I)).trans
      (quotientEquivLocalQuotients (s • I).ne_zero).symm)

theorem quotientEquivLocalQuotients_smulQuotient (s : IdeleGroup K) (I : 𝓘)
    (q : K ⧸ ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    quotientEquivLocalQuotients (s • I).ne_zero (smulQuotient s I q) =
      DFinsupp.mapRange.linearEquiv (localMul s I) (quotientEquivLocalQuotients I.ne_zero q) := by
  rw [smulQuotient, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

theorem smulQuotient_mk_eq_mk_iff (s : IdeleGroup K) (I : 𝓘) (x y : K) :
    smulQuotient s I (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
      ∀ v : HeightOneSpectrum (𝓞 K), (finiteProj v s : v.adicCompletion K) * (x : v.adicCompletion K) -
        (y : v.adicCompletion K) ∈ localIdeal ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v := by
  rw [← (quotientEquivLocalQuotients (s • I).ne_zero).injective.eq_iff,
    quotientEquivLocalQuotients_smulQuotient, quotientEquivLocalQuotients_mk,
    quotientEquivLocalQuotients_mk, DFinsupp.ext_iff]
  refine forall_congr' fun v ↦ ?_
  rw [DFinsupp.mapRange.linearEquiv_apply, DFinsupp.mapRange_apply, toLocalQuotients_apply,
    toLocalQuotients_apply, localMul_mk, Submodule.Quotient.eq]

theorem mul_mem_localIdeal_smul (s : IdeleGroup K) (I : 𝓘) (v : HeightOneSpectrum (𝓞 K))
    {w : v.adicCompletion K} (hw : w ∈ localIdeal (I : FractionalIdeal (𝓞 K)⁰ K) v) :
    (finiteProj v s : v.adicCompletion K) * w ∈
      localIdeal ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v := by
  rw [localIdeal_smul]
  exact ⟨w, hw, by simp only [LinearMap.mulLeft_apply, coe_finiteProj]⟩

theorem smulQuotient_one_apply (I : 𝓘)
    (q : K ⧸ ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    smulQuotient 1 I q = Submodule.quotEquivOfEq _ _ (by rw [one_smul]) q := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [Submodule.quotEquivOfEq_mk, smulQuotient_mk_eq_mk_iff]
  intro v
  rw [map_one, Units.val_one, one_mul, sub_self]
  exact zero_mem _

theorem smulQuotient_mul_apply (s t : IdeleGroup K) (I : 𝓘)
    (q : K ⧸ ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    smulQuotient (s * t) I q =
      Submodule.quotEquivOfEq _ _ (by rw [mul_smul]) (smulQuotient s (t • I) (smulQuotient t I q)) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (smulQuotient t I (Submodule.Quotient.mk x))
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _
    (smulQuotient s (t • I) (Submodule.Quotient.mk y))
  rw [← hy, ← hz, Submodule.quotEquivOfEq_mk, smulQuotient_mk_eq_mk_iff]
  have hy' := (smulQuotient_mk_eq_mk_iff t I x y).1 hy.symm
  have hz' := (smulQuotient_mk_eq_mk_iff s (t • I) y z).1 hz.symm
  intro v
  have h := add_mem (mul_mem_localIdeal_smul s (t • I) v (hy' v)) (hz' v)
  have e : ((finiteProj v (s * t) : (v.adicCompletion K)ˣ) : v.adicCompletion K) *
      (x : v.adicCompletion K) - (z : v.adicCompletion K) =
      (finiteProj v s : v.adicCompletion K) * ((finiteProj v t : v.adicCompletion K) *
        (x : v.adicCompletion K) - (y : v.adicCompletion K)) +
      ((finiteProj v s : v.adicCompletion K) * (y : v.adicCompletion K) -
        (z : v.adicCompletion K)) := by
    rw [map_mul, Units.val_mul]
    ring
  rw [e, mul_smul]
  exact h

theorem smulQuotient_diagonal_mk (a : Kˣ) (I : 𝓘) (x : K) :
    smulQuotient (diagonal K a) I (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((a : K) * x) := by
  rw [smulQuotient_mk_eq_mk_iff]
  intro v
  rw [coe_finiteProj_diagonal, ← adicCompletion.coe_mul, sub_self]
  exact zero_mem _

end IdeleGroup

end

end GroundTheory.Global
