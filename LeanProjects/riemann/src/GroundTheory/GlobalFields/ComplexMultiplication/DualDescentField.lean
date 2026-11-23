import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialBaseChange

namespace GroundTheory.Global

open Polynomial GroundTheory.Arith.Abelian IntermediateField
open WeierstrassCurve.Affine (Point equation_iff CoordinateRing)
open scoped Polynomial.Bivariate

universe u

section Coord

theorem eq_zero_of_aeval_genX_add_mul_genY {K : Type*} [Field K] (V : WeierstrassCurve K)
    {P Q : K[X]} (h : aeval (genX V) P + aeval (genX V) Q * genY V = 0) : P = 0 ∧ Q = 0 := by
  apply CoordinateRing.smul_basis_eq_zero (W' := V.toAffine)
  apply IsFractionRing.injective V.toAffine.CoordinateRing V.toAffine.FunctionField
  rw [map_zero, ← h, map_add, Algebra.smul_def, Algebra.smul_def, mul_one, map_mul,
    genX_eq, aeval_algebraMap_apply, aeval_algebraMap_apply, aeval_X_left_apply,
    aeval_X_left_apply, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rfl

end Coord

section LinearDisjoint

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] (W : WeierstrassCurve F)

theorem bcEmb_algebraMap_smul_basis (p q : F[X]) :
    bcEmb (F' := Ω) W (algebraMap W.toAffine.CoordinateRing _
      (p • 1 + q • CoordinateRing.mk W.toAffine Y)) =
      aeval (genX (W.baseChange Ω)) (p.map (algebraMap F Ω)) +
        aeval (genX (W.baseChange Ω)) (q.map (algebraMap F Ω)) * genY (W.baseChange Ω) := by
  have e : ∀ t : F[X], algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (algebraMap F[X] W.toAffine.CoordinateRing t) = aeval (genX W) t := by
    intro t
    rw [← IsScalarTower.algebraMap_apply, genX_eq, aeval_algebraMap_apply, aeval_X_left_apply]
  rw [map_add, Algebra.smul_def, Algebra.smul_def, mul_one, map_add, map_mul, e, e,
    show algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (CoordinateRing.mk W.toAffine Y) = genY W from rfl, map_mul, ← aeval_algHom_apply,
    ← aeval_algHom_apply, bcEmb_genX, bcEmb_genY, aeval_map_algebraMap, aeval_map_algebraMap]

theorem coordinateRing_eq_zero_of_sum {ι : Type*} (s : Finset ι) {ω : ι → Ω}
    (hω : LinearIndependent F ω) (r : ι → W.toAffine.CoordinateRing)
    (h : ∑ i ∈ s, bcEmb (F' := Ω) W (algebraMap _ _ (r i)) * algebraMap Ω _ (ω i) = 0) :
    ∀ i ∈ s, r i = 0 := by
  choose p q hpq using fun i => CoordinateRing.exists_smul_basis_eq (r i)
  have e : ∀ i, bcEmb (F' := Ω) W (algebraMap _ _ (r i)) * algebraMap Ω _ (ω i) =
      aeval (genX (W.baseChange Ω)) (C (ω i) * (p i).map (algebraMap F Ω)) +
        aeval (genX (W.baseChange Ω)) (C (ω i) * (q i).map (algebraMap F Ω)) *
          genY (W.baseChange Ω) := by
    intro i
    rw [← hpq i, bcEmb_algebraMap_smul_basis]
    simp only [map_mul, aeval_C]
    ring
  simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, ← map_sum] at h
  obtain ⟨hP, hQ⟩ := eq_zero_of_aeval_genX_add_mul_genY _ h
  have hcoef : ∀ (t : ι → F[X]), ∑ i ∈ s, C (ω i) * (t i).map (algebraMap F Ω) = 0 →
      ∀ i ∈ s, t i = 0 := by
    intro t ht i hi
    ext n
    have hn := congrArg (coeff · n) ht
    simp only [finsetSum_coeff, coeff_C_mul, coeff_map, coeff_zero] at hn
    have hn' : ∑ j ∈ s, (t j).coeff n • ω j = 0 := by
      rw [← hn]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    rw [coeff_zero]
    exact linearIndependent_iff'.mp hω s (fun j => (t j).coeff n) hn' i hi
  intro i hi
  rw [← hpq i, hcoef p hP i hi, hcoef q hQ i hi, zero_smul, zero_smul, add_zero]

theorem linearDisjoint_bcEmb : (bcEmb (F' := Ω) W).fieldRange.LinearDisjoint Ω := by
  classical
  apply LinearDisjoint.of_basis_right' (Module.Basis.ofVectorSpace F Ω)
  rw [linearIndependent_iff']
  intro s g hg i hi
  choose α hα using fun j => AlgHom.mem_fieldRange.mp (g j).2
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples
    (nonZeroDivisors W.toAffine.CoordinateRing) s α
  choose! r hr using hc
  have hc0 : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (c : _) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors c.2
  have hsum : ∑ j ∈ s, bcEmb (F' := Ω) W (algebraMap _ _ (r j)) *
      algebraMap Ω _ (Module.Basis.ofVectorSpace F Ω j) = 0 := by
    have : ∀ j ∈ s, bcEmb (F' := Ω) W (algebraMap _ _ (r j)) *
        algebraMap Ω _ (Module.Basis.ofVectorSpace F Ω j) =
        bcEmb (F' := Ω) W (algebraMap W.toAffine.CoordinateRing _ c) *
          (g j • (algebraMap Ω _ ∘ Module.Basis.ofVectorSpace F Ω) j) := by
      intro j hj
      rw [hr j hj, Algebra.smul_def, map_mul, Function.comp_apply, Algebra.smul_def,
        mul_assoc]
      congr 2
      exact hα j
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hg, mul_zero]
  have h0 := coordinateRing_eq_zero_of_sum W s (Module.Basis.ofVectorSpace F Ω).linearIndependent r hsum i hi
  have : α i = 0 := by
    have := hr i hi
    rw [h0, map_zero, Algebra.smul_def] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hc0
  exact Subtype.ext (by rw [← hα i, this, map_zero]; rfl)

end LinearDisjoint

section Sup

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] (W : WeierstrassCurve F)

theorem sup_bcEmb_eq_top :
    (bcEmb (F' := Ω) W).fieldRange ⊔
      (IsScalarTower.toAlgHom F Ω (W.baseChange Ω).toAffine.FunctionField).fieldRange = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  have hz : z ∈ IntermediateField.adjoin Ω {genX (W.baseChange Ω), genY (W.baseChange Ω)} := by
    rw [adjoin_genX_genY]; trivial
  induction hz using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact (le_sup_left : (bcEmb (F' := Ω) W).fieldRange ≤ _) ⟨genX W, bcEmb_genX W⟩
    · exact (le_sup_left : (bcEmb (F' := Ω) W).fieldRange ≤ _) ⟨genY W, bcEmb_genY W⟩
  | algebraMap x =>
    exact (le_sup_right : (IsScalarTower.toAlgHom F Ω _).fieldRange ≤ _) ⟨x, rfl⟩
  | add x y _ _ hx hy => exact add_mem hx hy
  | inv x _ hx => exact inv_mem hx
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem sup_toSubalgebra_bcEmb_eq_top [Algebra.IsAlgebraic F Ω] :
    (bcEmb (F' := Ω) W).fieldRange.toSubalgebra ⊔
      (IsScalarTower.toAlgHom F Ω (W.baseChange Ω).toAffine.FunctionField).fieldRange.toSubalgebra =
        ⊤ := by
  have : Algebra.IsAlgebraic F
      (IsScalarTower.toAlgHom F Ω (W.baseChange Ω).toAffine.FunctionField).fieldRange :=
    ⟨fun ⟨x, hx⟩ => by
      obtain ⟨ω, rfl⟩ := AlgHom.mem_fieldRange.mp hx
      exact isAlgebraic_iff.mpr ((Algebra.IsAlgebraic.isAlgebraic ω).algHom _)⟩
  rw [← sup_toSubalgebra_of_isAlgebraic_right, sup_bcEmb_eq_top, top_toSubalgebra]

end Sup

section Descent

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
  {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem comap_isogBaseChange_bcEmb (φ : Isogeny E E') (g : E'.toAffine.FunctionField) :
    (isogBaseChange (F' := Ω) φ).comap (bcEmb (F' := Ω) E' g) = bcEmb (F' := Ω) E (φ.comap g) := by
  obtain ⟨⟨x, y, h, he, -⟩, -⟩ := φ.2
  have hx : (isogBaseChange (F' := Ω) φ).x = bcEmb (F' := Ω) E φ.x := by
    simp only [Isogeny.x, isogBaseChange_val, he]
    rfl
  have hy : (isogBaseChange (F' := Ω) φ).y = bcEmb (F' := Ω) E φ.y := by
    simp only [Isogeny.y, isogBaseChange_val, he]
    rfl
  have : ((isogBaseChange (F' := Ω) φ).comap.restrictScalars F).comp (bcEmb (F' := Ω) E') =
      (bcEmb (F' := Ω) E).comp φ.comap := by
    apply algHom_ext_gen E'
    · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, bcEmb_genX, Isogeny.comap_genX, hx]
    · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, bcEmb_genY, Isogeny.comap_genY, hy]
  exact DFunLike.congr_fun this g

theorem mem_fieldRange_comap_of_bcEmb [Algebra.IsAlgebraic F Ω] (φ : Isogeny E E')
    {f : E.toAffine.FunctionField}
    (hf : bcEmb (F' := Ω) E f ∈ (isogBaseChange (F' := Ω) φ).comap.fieldRange) :
    f ∈ φ.comap.fieldRange := by
  classical
  set ι := bcEmb (F' := Ω) E
  set ψ := isogBaseChange (F' := Ω) φ
  set Ω₁ := (IsScalarTower.toAlgHom F Ω (E.baseChange Ω).toAffine.FunctionField).fieldRange
  have H : ι.fieldRange.LinearDisjoint Ω₁ :=
    linearDisjoint_iff'.2 (by rw [AlgHom.fieldRange_toSubalgebra]; exact linearDisjoint_bcEmb E)
  set b := Module.Basis.ofVectorSpace F Ω₁
  set bb := H.basisOfBasisRight (sup_toSubalgebra_bcEmb_eq_top E) b
  have hrepr : ∀ (x : Ω₁) (i : Module.Basis.ofVectorSpaceIndex F Ω₁),
      ((bb.repr (x : (E.baseChange Ω).toAffine.FunctionField) i : ι.fieldRange) :
        (E.baseChange Ω).toAffine.FunctionField) = algebraMap F _ (b.repr x i) :=
    fun x i => H.algebraMap_basisOfBasisRight_repr_apply _ b x i
  obtain ⟨i, hi⟩ : ∃ i, b.repr 1 i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : b.repr 1 = 0 := Finsupp.ext hcon
    exact one_ne_zero (b.repr.injective (h1.trans (map_zero _).symm))
  set N₁ := (ι.comp φ.comap).fieldRange
  set c : (E.baseChange Ω).toAffine.FunctionField →ₗ[ι.fieldRange] ι.fieldRange := bb.coord i
  have hc : ∀ (a : ι.fieldRange) (z : (E.baseChange Ω).toAffine.FunctionField),
      ((c ((a : (E.baseChange Ω).toAffine.FunctionField) * z) : ι.fieldRange) :
        (E.baseChange Ω).toAffine.FunctionField) = a * (c z : (E.baseChange Ω).toAffine.FunctionField) := by
    intro a z
    change ((c (a • z) : ι.fieldRange) : (E.baseChange Ω).toAffine.FunctionField) = _
    rw [map_smul, smul_eq_mul, IntermediateField.coe_mul]
  have hcΩ : ∀ ω : Ω, ((c (algebraMap Ω (E.baseChange Ω).toAffine.FunctionField ω) : ι.fieldRange) :
      (E.baseChange Ω).toAffine.FunctionField) ∈ N₁ := by
    intro ω
    have := hrepr ⟨algebraMap Ω _ ω, ⟨ω, rfl⟩⟩ i
    change ((c (algebraMap Ω (E.baseChange Ω).toAffine.FunctionField ω) : ι.fieldRange) :
      (E.baseChange Ω).toAffine.FunctionField) = _ at this
    rw [this]
    exact IntermediateField.algebraMap_mem N₁ _

  set T : (E'.baseChange Ω).toAffine.FunctionField →ₗ[F] (E.baseChange Ω).toAffine.FunctionField :=
    (ι.fieldRange.val.toLinearMap.comp (c.restrictScalars F)).comp
      (ψ.comap.restrictScalars F).toLinearMap
  have hT : ∀ z, T z = ((c (ψ.comap z) : ι.fieldRange) : (E.baseChange Ω).toAffine.FunctionField) :=
    fun z => rfl
  have hle : Subalgebra.toSubmodule (bcEmb (F' := Ω) E').fieldRange.toSubalgebra *
      Subalgebra.toSubmodule
        (IsScalarTower.toAlgHom F Ω (E'.baseChange Ω).toAffine.FunctionField).fieldRange.toSubalgebra ≤
      (Subalgebra.toSubmodule N₁.toSubalgebra).comap T := by
    rw [Submodule.mul_le]
    intro m hm n hn
    obtain ⟨a, rfl⟩ := AlgHom.mem_fieldRange.mp hm
    obtain ⟨ω, rfl⟩ := AlgHom.mem_fieldRange.mp hn
    rw [Submodule.mem_comap, Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra]
    have e1 : ψ.comap (bcEmb (F' := Ω) E' a *
        IsScalarTower.toAlgHom F Ω (E'.baseChange Ω).toAffine.FunctionField ω) =
        ι (φ.comap a) * algebraMap Ω (E.baseChange Ω).toAffine.FunctionField ω := by
      rw [map_mul, comap_isogBaseChange_bcEmb, IsScalarTower.coe_toAlgHom', AlgHom.commutes]
    rw [hT, e1, hc ⟨ι (φ.comap a), ⟨φ.comap a, rfl⟩⟩]
    exact mul_mem ⟨a, rfl⟩ (hcΩ ω)
  obtain ⟨z, hz⟩ := AlgHom.mem_fieldRange.mp hf
  have hzT : T z ∈ N₁ := by
    have h3 : z ∈ Subalgebra.toSubmodule (bcEmb (F' := Ω) E').fieldRange.toSubalgebra *
        Subalgebra.toSubmodule
          (IsScalarTower.toAlgHom F Ω (E'.baseChange Ω).toAffine.FunctionField).fieldRange.toSubalgebra := by
      rw [Subalgebra.mul_toSubmodule, sup_toSubalgebra_bcEmb_eq_top]
      trivial
    have h4 := hle h3
    rwa [Submodule.mem_comap, Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra] at h4
  have e2 : T z = ι f * algebraMap F _ (b.repr 1 i) := by
    have h1 := hc ⟨ι f, ⟨f, rfl⟩⟩ 1
    rw [mul_one] at h1
    rw [hT, hz, h1]
    congr 1
    exact hrepr 1 i
  have hmem : ι f ∈ N₁ := by
    have := mul_mem hzT (IntermediateField.algebraMap_mem N₁ (b.repr 1 i)⁻¹)
    rwa [e2, mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, mul_one] at this
  obtain ⟨g, hg⟩ := AlgHom.mem_fieldRange.mp hmem
  exact ⟨g, ι.injective hg⟩

end Descent

end GroundTheory.Global
