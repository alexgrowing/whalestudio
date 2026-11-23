import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NsmulApplyMemOfMemTensorLat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSmulMemOfMemSpanFraction
import ReciprocityTheory.SemistableReduction.ExistsIntSmulMemSpan
import ReciprocityTheory.SemistableReduction.SemiDegCE
import ReciprocityTheory.DualLattices.WedgeNeZeroOfLinearIndependent

namespace GlobalTheory.TensorLat

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
open scoped nonZeroDivisors

theorem relIndex_eq_of_hom {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    {A₁ A₂ : AddSubgroup M} {B₁ B₂ : AddSubgroup M'} (f : M →+ M')
    (hf : ∀ v ∈ A₂, f v ∈ B₂) (hker : ∀ v ∈ A₂, f v ∈ B₁ ↔ v ∈ A₁)
    (hsurj : ∀ u ∈ B₂, ∃ v ∈ A₂, u - f v ∈ B₁) : A₁.relIndex A₂ = B₁.relIndex B₂ := by
  have h1 : A₁ ⊓ A₂ = B₁.comap f ⊓ A₂ := by
    ext v
    simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap]
    exact ⟨fun h => ⟨(hker v h.2).2 h.1, h.2⟩, fun h => ⟨(hker v h.2).1 h.1, h.2⟩⟩
  have h2 : B₁ ⊔ A₂.map f = B₁ ⊔ B₂ := by
    refine le_antisymm (sup_le_sup_left ?_ _) (sup_le le_sup_left fun u hu => ?_)
    · rintro _ ⟨v, hv, rfl⟩
      exact hf v hv
    · obtain ⟨v, hv, h⟩ := hsurj u hu
      exact AddSubgroup.mem_sup.2 ⟨_, h, f v, ⟨v, hv, rfl⟩, sub_add_cancel _ _⟩
  rw [← AddSubgroup.inf_relIndex_right, h1, AddSubgroup.inf_relIndex_right,
    AddSubgroup.relIndex_comap, ← AddSubgroup.relIndex_sup_left, h2,
    AddSubgroup.relIndex_sup_left]

theorem relIndex_pi_univ {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, AddCommGroup (G i)]
    (L' L : ∀ i, AddSubgroup (G i)) :
    (AddSubgroup.pi Set.univ L').relIndex (AddSubgroup.pi Set.univ L) =
      ∏ i, (L' i).relIndex (L i) := by
  let f : (AddSubgroup.pi Set.univ L) →+ (∀ i, L i ⧸ (L' i).addSubgroupOf (L i)) :=
    { toFun := fun x i => QuotientAddGroup.mk ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := fun y =>
    ⟨⟨fun i => (y i).out, fun i _ => (y i).out.2⟩, funext fun i => (y i).out_eq⟩
  have hc : (AddSubgroup.pi Set.univ L').addSubgroupOf (AddSubgroup.pi Set.univ L) = f.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, funext_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    refine forall_congr' fun i => ?_
    change _ ↔ (QuotientAddGroup.mk ⟨x.1 i, x.2 i (Set.mem_univ i)⟩ :
      L i ⧸ (L' i).addSubgroupOf (L i)) = 0
    simp [AddSubgroup.mem_addSubgroupOf]
  rw [AddSubgroup.relIndex, hc, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
    AddSubgroup.card_top, Nat.card_pi]
  rfl

theorem card_eq_relIndex_of_reps {M : Type*} [AddCommGroup M] {A B : AddSubgroup M} {R : Finset M}
    (hR : ∀ y ∈ R, y ∈ B) (hR' : ∀ y ∈ B, ∃! r ∈ R, y - r ∈ A) : R.card = A.relIndex B := by
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  refine Nat.card_eq_of_bijective
    (fun y : R => (QuotientAddGroup.mk ⟨y, hR y y.2⟩ : B ⧸ A.addSubgroupOf B)) ⟨?_, ?_⟩
  · intro y y' h
    have h1 : (y : M) - y' ∈ A := by
      simpa [AddSubgroup.mem_addSubgroupOf] using QuotientAddGroup.eq_iff_sub_mem.1 h
    exact Subtype.ext ((hR' y (hR y y.2)).unique ⟨y.2, by simp⟩ ⟨y'.2, h1⟩)
  · intro q
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨r, ⟨hr, h⟩, -⟩ := hR' y y.2
    refine ⟨⟨r, hr⟩, (QuotientAddGroup.eq_iff_sub_mem.2 ?_).symm⟩
    simpa [AddSubgroup.mem_addSubgroupOf] using h

theorem exists_reps_of_relIndex_ne_zero {M : Type*} [AddCommGroup M] {A B : AddSubgroup M}
    (h : A.relIndex B ≠ 0) :
    ∃ R : Finset M, (∀ y ∈ R, y ∈ B) ∧ ∀ y ∈ B, ∃! r ∈ R, y - r ∈ A := by
  classical
  haveI : Fintype (B ⧸ A.addSubgroupOf B) := AddSubgroup.fintypeOfIndexNeZero h
  refine ⟨Finset.univ.image fun q : B ⧸ A.addSubgroupOf B => (q.out : M), ?_, fun y hy => ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact q.out.2
  · have key : ∀ q : B ⧸ A.addSubgroupOf B,
        y - (q.out : M) ∈ A ↔ QuotientAddGroup.mk ⟨y, hy⟩ = q := fun q => by
      conv_rhs => rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_iff_sub_mem]
      simp [AddSubgroup.mem_addSubgroupOf]
    refine ⟨_, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key _).2 rfl⟩, ?_⟩
    rintro r ⟨hr, h⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    rw [(key q).1 h]

section Period

variable {E : Type} [Field E] [NumberField E]

end Period

section Index

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end Index

section Modulus

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

variable [IsGalois ℚ E]

variable {K : Type*} [Field K] [Algebra E K]

end Modulus

section IndexIdeal

open ReciprocityTheory.MultiplicativeHeights.SemiDegIdx ReciprocityTheory.PGsh

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem exists_coe_eq_span_det_of_intVec_le (X : Submodule (𝓞 K) (Fin n → K)) (hfg : X.FG)
    (hstd : intVec K n ≤ X) :
    ∃ J : FractionalIdeal (𝓞 K)⁰ K, (J : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ X) ∧ d = (Matrix.of v).det} ∧
      FractionalIdeal.absNorm J * ((intVec K n).toAddSubgroup.relIndex X.toAddSubgroup : ℚ) = 1 := by
  obtain ⟨C, z, hfgC, h1, htri, hdiag, hin, hdec, hidx⟩ := lattice_split K n X hfg hstd
  let CF : Fin n → FractionalIdeal (𝓞 K)⁰ K := fun i =>
    ⟨C i, FractionalIdeal.isFractional_of_fg (hfgC i)⟩
  refine ⟨∏ i, CF i, ?_, ?_⟩
  · rw [coe_prod_frac]
    change ∏ i, C i = _
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rw [prod_eq_span_prod]
      refine Submodule.span_mono fun x hx => ?_
      obtain ⟨t, ht, rfl⟩ := (Set.mem_fintype_prod _ _).1 hx
      refine ⟨fun i => t i • z i, fun i => smul_mem_of_split hin i (ht i), ?_⟩
      have : (Matrix.of fun i => t i • z i) = Matrix.diagonal t * rowMat z := by
        ext i j
        simp [rowMat, Matrix.diagonal_mul]
      rw [this, Matrix.det_mul, det_rowMat z htri hdiag, Matrix.det_diagonal, mul_one]
    · rintro _ ⟨v, hv, rfl⟩
      choose T hT hTv using fun i => hdec (v i) (hv i)
      have : Matrix.of v = Matrix.of T * rowMat z := by
        ext i j
        rw [Matrix.of_apply, hTv i]
        simp [rowMat, Matrix.mul_apply, Finset.sum_apply]
      rw [this, Matrix.det_mul, det_rowMat z htri hdiag, mul_one, ← Matrix.det_transpose]
      exact det_mem_prod_sub C _ fun i j => hT j i
  · rw [hidx, map_prod, Nat.cast_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => absNorm_mul_relIndex_one (C i) (hfgC i) (h1 i)

theorem exists_coe_eq_span_det {Λ Λ' : Submodule (𝓞 K) (Fin n → K)} (hle : Λ ≤ Λ') (hfg : Λ'.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) :
    ∃ J J' : FractionalIdeal (𝓞 K)⁰ K, J ≠ 0 ∧ J' ≠ 0 ∧
      (J : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Λ) ∧ d = (Matrix.of v).det} ∧
      (J' : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Λ') ∧ d = (Matrix.of v).det} ∧
      FractionalIdeal.absNorm J =
        (Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup : ℚ) * FractionalIdeal.absNorm J' := by
  classical
  choose d hd0 hd using fun k : Fin n => exists_smul_mem_of_mem_span_fraction (K := K) Λ
    (Pi.single k (1 : K)) (hsp ▸ Submodule.mem_top)
  set δ : K := algebraMap (𝓞 K) K (∏ k, d k) with hδ
  have hδ0 : δ ≠ 0 := by simpa [hδ, Finset.prod_ne_zero_iff] using hd0
  let μ : (Fin n → K) →ₗ[𝓞 K] (Fin n → K) := (LinearMap.lsmul K _ δ).restrictScalars (𝓞 K)
  have hμ : ∀ x, μ x = δ • x := fun _ => rfl
  have hinj : Function.Injective μ := smul_right_injective _ hδ0
  have hsurj : Function.Surjective μ := fun x => ⟨δ⁻¹ • x, by rw [hμ, smul_inv_smul₀ hδ0]⟩
  have hstd : intVec K n ≤ Λ.comap μ := by
    intro x hx
    choose c hc using fun k => Submodule.mem_one.1 (mem_intVec.1 hx k)
    have : x = ∑ k, c k • (Pi.single k (1 : K) : Fin n → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hc]
    rw [this]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    rw [Submodule.mem_comap, hμ, hδ, algebraMap_smul,
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ k), mul_smul]
    exact Λ.smul_mem _ (hd k)
  have key : ∀ Y : Submodule (𝓞 K) (Fin n → K), Λ ≤ Y → Y.FG →
      ∃ J : FractionalIdeal (𝓞 K)⁰ K, (J : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Y) ∧ d = (Matrix.of v).det} ∧
      FractionalIdeal.absNorm J * ((intVec K n).toAddSubgroup.relIndex
        (Y.comap μ).toAddSubgroup : ℚ) = |Algebra.norm ℚ (δ ^ n)| := by
    intro Y hY hYfg
    obtain ⟨J, hJ, hN⟩ := exists_coe_eq_span_det_of_intVec_le (Y.comap μ)
      (Submodule.fg_of_fg_map_injective μ hinj
        (by rwa [Submodule.map_comap_eq_of_surjective hsurj]))
      (hstd.trans (Submodule.comap_mono hY))
    refine ⟨FractionalIdeal.spanSingleton _ (δ ^ n) * J, ?_, ?_⟩
    · rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton, hJ, Submodule.span_mul_span,
        Set.singleton_mul]
      congr 1
      ext x
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        refine ⟨δ • v, hv, ?_⟩
        change _ = (δ • Matrix.of v).det
        rw [Matrix.det_smul, Fintype.card_fin]
      · rintro ⟨v, hv, rfl⟩
        refine ⟨_, ⟨δ⁻¹ • v, fun i => ?_, rfl⟩, ?_⟩
        · rw [Submodule.mem_comap, hμ, Pi.smul_apply, smul_inv_smul₀ hδ0]
          exact hv i
        · change _ * (δ⁻¹ • Matrix.of v).det = _
          rw [Matrix.det_smul, Fintype.card_fin, inv_pow, mul_inv_cancel_left₀ (pow_ne_zero _ hδ0)]
    · rw [map_mul, mul_assoc, hN, mul_one, FractionalIdeal.absNorm_span_singleton]
  obtain ⟨J, hJ, hN⟩ := key Λ le_rfl (hfg.of_le hle)
  obtain ⟨J', hJ', hN'⟩ := key Λ' hle hfg
  have hn0 : |Algebra.norm ℚ (δ ^ n)| ≠ 0 :=
    abs_ne_zero.2 (Algebra.norm_ne_zero_iff.2 (pow_ne_zero _ hδ0))
  have hidx : (Λ.comap μ).toAddSubgroup.relIndex (Λ'.comap μ).toAddSubgroup =
      Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup := by
    change (Λ.toAddSubgroup.comap μ.toAddMonoidHom).relIndex
      (Λ'.toAddSubgroup.comap μ.toAddMonoidHom) = _
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hsurj]
  have htower := AddSubgroup.relIndex_mul_relIndex (intVec K n).toAddSubgroup
    (Λ.comap μ).toAddSubgroup (Λ'.comap μ).toAddSubgroup hstd (Submodule.comap_mono hle)
  refine ⟨J, J', ?_, ?_, hJ, hJ', ?_⟩
  · rintro rfl
    rw [map_zero, zero_mul] at hN
    exact hn0 hN.symm
  · rintro rfl
    rw [map_zero, zero_mul] at hN'
    exact hn0 hN'.symm
  · rw [← htower, hidx, Nat.cast_mul, ← hN] at hN'
    refine mul_right_cancel₀ (right_ne_zero_of_mul (hN ▸ hn0)) ?_
    linear_combination -hN'

theorem smul_coe_fractionalIdeal (𝔫 : Ideal (𝓞 K)) (J : FractionalIdeal (𝓞 K)⁰ K) :
    𝔫 • (J : Submodule (𝓞 K) K) =
      (((𝔫 : FractionalIdeal (𝓞 K)⁰ K) * J : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  rw [FractionalIdeal.coe_mul]
  refine le_antisymm (Submodule.smul_le.2 fun a ha x hx => ?_)
    (Submodule.mul_le.2 fun a ha x hx => ?_)
  · rw [Algebra.smul_def]
    exact Submodule.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ ha) hx
  · obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem_smul hb hx

theorem exists_indexIdeal_span_det {Λ Λ' : Submodule (𝓞 K) (Fin n → K)} (hle : Λ ≤ Λ')
    (hfg : Λ'.FG) (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) :
    ∃ 𝔫 : Ideal (𝓞 K), 𝔫 ≠ ⊥ ∧ Ideal.absNorm 𝔫 = Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup ∧
      ∀ 𝔪 : Ideal (𝓞 K), Submodule.span (𝓞 K)
          {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Λ) ∧ d = (Matrix.of v).det} =
        𝔪 • Submodule.span (𝓞 K)
          {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Λ') ∧ d = (Matrix.of v).det} ↔ 𝔪 = 𝔫 := by
  obtain ⟨J, J', h0, h0', hJ, hJ', hN⟩ := exists_coe_eq_span_det hle hfg hsp
  have hJJ : J ≤ J' := by
    rw [← FractionalIdeal.coe_le_coe, hJ, hJ']
    exact Submodule.span_mono fun _ ⟨v, hv, h⟩ => ⟨v, fun i => hle (hv i), h⟩
  have h1 : J * J'⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ h0']
    gcongr
  obtain ⟨𝔫, h𝔫⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 h1
  have h2 : J = 𝔫 * J' := by rw [h𝔫, inv_mul_cancel_right₀ h0']
  refine ⟨𝔫, ?_, ?_, fun 𝔪 => ?_⟩
  · rintro rfl
    simp [h0] at h2
  · rw [h2, map_mul, FractionalIdeal.coeIdeal_absNorm] at hN
    exact_mod_cast mul_right_cancel₀ (FractionalIdeal.absNorm_eq_zero_iff.not.2 h0') hN
  · rw [← hJ, ← hJ', smul_coe_fractionalIdeal, FractionalIdeal.coeToSubmodule_inj, h2,
      mul_left_inj' h0', FractionalIdeal.coeIdeal_inj, eq_comm]

attribute [local instance] extModR

end IndexIdeal

section Main

open ReciprocityTheory.PGsh

attribute [local instance] extModR

end Main

end GlobalTheory.TensorLat
