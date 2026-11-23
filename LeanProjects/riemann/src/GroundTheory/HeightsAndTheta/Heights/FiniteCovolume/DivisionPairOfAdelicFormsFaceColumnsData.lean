import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.IsClosedUnitaryOfComplex
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StDualIndexFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FiniteCovolume.HermitianSpaceComparison

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal ComplexOrder Pointwise

noncomputable section

set_option linter.unusedSectionVars false

theorem unitaryGroupMatrix_eq_unitaryOf {A : Type*} [CommRing A] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : A →+* A) (H : Matrix ι ι A) :
    unitaryGroupMatrix s H = IndefiniteRowSideFullHecke.FiniteCovolume.unitaryOf s Hᵀ := by
  ext g
  rw [mem_unitaryGroupMatrix]
  change _ ↔ (g : Matrix ι ι A)ᵀ * Hᵀ * (g : Matrix ι ι A).map s = Hᵀ
  constructor
  · intro hg
    have := congrArg Matrix.transpose hg
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  · intro hg
    have := congrArg Matrix.transpose hg
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this

theorem mul_inv_mul_swap {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : IsUnit A.det) (hB : IsUnit B.det) (h : A * B⁻¹ * A = B) : B * A⁻¹ * B = A := by
  calc B * A⁻¹ * B = (A * B⁻¹ * A) * A⁻¹ * (A * B⁻¹ * A) := by rw [h]
    _ = A * B⁻¹ * (A * A⁻¹) * (A * B⁻¹) * A := by simp only [Matrix.mul_assoc]
    _ = (A * B⁻¹ * A) * B⁻¹ * A := by
        rw [Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = A := by rw [h, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul]

def subgroupHomeo {G : Type*} [Group G] [TopologicalSpace G] {S T : Subgroup G} (e : S = T) :
    S ≃ₜ T :=
  Homeomorph.setCongr (congrArg SetLike.coe e)

theorem subgroupHomeo_apply {G : Type*} [Group G] [TopologicalSpace G] {S T : Subgroup G}
    (e : S = T) (x : S) : subgroupHomeo e x = MulEquiv.subgroupCongr e x := rfl

section HidaSetting

variable {F : Type*} {E : Type} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]

omit [NumberField F] in
include F in

theorem isCMField : IsCMField E := IsCMField.ofCMExtension F E

variable [IsCMField E]

theorem conjHom_eq_conjE : conjHom F E = IndefiniteRowSideFullHecke.FiniteCovolume.conjE E := by
  ext x
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  apply w.embedding.injective
  rw [IndefiniteRowSideFullHecke.FiniteCovolume.conjE_apply, IsCMField.complexEmbedding_complexConj]
  exact embedding_conj w.embedding x

theorem fDeg.equiv : finrank ℚ F = IndefiniteRowSideFullHecke.FiniteCovolume.fDeg E :=
  (CMExtension.equivMaximalRealSubfield F E).toRatAlgEquiv.toLinearEquiv.finrank_eq

variable {W : Type*} [AddCommGroup W] [Module E W] {N : ℕ}

def divisionPairOfAdelicFormsFaceColumnsData (h : HermitianForm F E W) (v : Basis (Fin N) E W) :
    IndefiniteRowSideFullHecke.FiniteCovolume.HermSpace E N where
  J := (gram h.toSesq v)ᵀ
  herm := by
    rw [Matrix.transpose_transpose, Matrix.transpose_map, ← conjHom_eq_conjE (F := F)]
    exact (isHermitianFor_gram h v).symm
  nondeg := by
    rw [Matrix.det_transpose]
    exact isUnit_det_gram h v

theorem matrixHermSpace_gram (h : HermitianForm F E W) (v : Basis (Fin N) E W) :
    (divisionPairOfAdelicFormsFaceColumnsData h v).J = (gram h.toSesq v)ᵀ := rfl

theorem HermSpace.h.equiv (h : HermitianForm F E W) (v : Basis (Fin N) E W) (x y : W) :
    (divisionPairOfAdelicFormsFaceColumnsData h v).h (v.equivFun x) (v.equivFun y) = h.toSesq y x := by
  rw [sesq_eq_sum h.toSesq v y x, Finset.sum_comm]
  simp only [IndefiniteRowSideFullHecke.FiniteCovolume.HermSpace.h, ReciprocityTheory.ChartRestriction.G.SA.hf, matrixHermSpace_gram,
    Matrix.transpose_apply, Basis.equivFun_apply, ← conjHom_eq_conjE (F := F)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change _ = (conjHom F E) ((v.repr y) j) * _ * _
  ring

variable (h : HermitianForm F E W) (v : Basis (Fin N) E W)

theorem unitaryGroup.equiv :
    unitaryGroupMatrix (conjHom F E) (gram h.toSesq v) =
      IndefiniteRowSideFullHecke.FiniteCovolume.unitaryGroup (divisionPairOfAdelicFormsFaceColumnsData h v) := by
  rw [unitaryGroupMatrix_eq_unitaryOf, conjHom_eq_conjE]
  rfl

def unitaryEquiv : h.unitaryGroup ≃* IndefiniteRowSideFullHecke.FiniteCovolume.unitaryGroup (divisionPairOfAdelicFormsFaceColumnsData h v) :=
  (unitaryGroupEquivMatrix h v).trans (MulEquiv.subgroupCongr (unitaryGroup.equiv h v))

theorem unitaryEquiv_coe (g : h.unitaryGroup) :
    (unitaryEquiv h v g : GL (Fin N) E) = (unitaryGroupEquivMatrix h v g : GL (Fin N) E) :=
  MulEquiv.subgroupCongr_apply (unitaryGroup.equiv h v) _

theorem unitaryEquiv_apply (g : h.unitaryGroup) :
    ((unitaryEquiv h v g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) =
      LinearMap.toMatrix v v ((g : W ≃ₗ[E] W) : W →ₗ[E] W) :=
  unitaryGroupEquivMatrix_apply h v g

theorem unitaryEquiv_mulVec (g : h.unitaryGroup) (x : W) :
    ((unitaryEquiv h v g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ v.equivFun x =
      v.equivFun ((g : W ≃ₗ[E] W) x) := by
  rw [unitaryEquiv_apply]
  simp only [Basis.equivFun_apply]
  exact LinearMap.toMatrix_mulVec_repr v v _ x

theorem archUnitary.equiv : archUnitary h v = IndefiniteRowSideFullHecke.FiniteCovolume.realPoints (divisionPairOfAdelicFormsFaceColumnsData h v) := by
  unfold archUnitary IndefiniteRowSideFullHecke.FiniteCovolume.realPoints
  congr 1
  funext w
  rw [unitaryGroupMatrix_eq_unitaryOf]
  congr 1

def realEquiv : archUnitary h v ≃* IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v) :=
  MulEquiv.subgroupCongr (archUnitary.equiv h v)

@[simp]
theorem coe_realEquiv (g : archUnitary h v) :
    ((realEquiv h v g : IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v)) :
      InfinitePlace E → GL (Fin N) ℂ) = g :=
  MulEquiv.subgroupCongr_apply _ g

def realHomeo : archUnitary h v ≃ₜ IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v) :=
  subgroupHomeo (archUnitary.equiv h v)

def realMeas : archUnitary h v ≃ᵐ IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v) :=
  (realHomeo h v).toMeasurableEquiv

theorem realHomeo_apply (g : archUnitary h v) : realHomeo h v g = realEquiv h v g :=
  subgroupHomeo_apply _ g

theorem realMeas_apply (g : archUnitary h v) : realMeas h v g = realEquiv h v g :=
  realHomeo_apply h v g

omit [IsCMField E] in
theorem archEmbed_apply (γ : h.unitaryGroup) (w : InfinitePlace E) :
    ((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL (Fin N) ℂ) w =
      Matrix.GeneralLinearGroup.map w.embedding (unitaryGroupEquivMatrix h v γ : GL (Fin N) E) :=
  rfl

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in
theorem toReal_apply (V : IndefiniteRowSideFullHecke.FiniteCovolume.HermSpace E N)
    (g : IndefiniteRowSideFullHecke.FiniteCovolume.unitaryGroup V) (w : InfinitePlace E) :
    ((IndefiniteRowSideFullHecke.FiniteCovolume.toReal V g : IndefiniteRowSideFullHecke.FiniteCovolume.RealPts V) :
      InfinitePlace E → GL (Fin N) ℂ) w = Matrix.GeneralLinearGroup.map w.embedding (g : GL (Fin N) E) :=
  rfl

theorem archEmbed.equiv (γ : h.unitaryGroup) :
    realEquiv h v (archEmbed h v γ) = IndefiniteRowSideFullHecke.FiniteCovolume.toReal (divisionPairOfAdelicFormsFaceColumnsData h v) (unitaryEquiv h v γ) :=
  by
    apply Subtype.ext
    rw [coe_realEquiv]
    funext w
    rw [archEmbed_apply, toReal_apply, unitaryEquiv_coe]

theorem archEmbed_comp :
    (realEquiv h v).toMonoidHom.comp (archEmbed h v) =
      (IndefiniteRowSideFullHecke.FiniteCovolume.toReal (divisionPairOfAdelicFormsFaceColumnsData h v)).comp (unitaryEquiv h v).toMonoidHom :=
  MonoidHom.ext (archEmbed.equiv h v)

omit [NumberField E] [IsTotallyComplex E] [IsCMField E] in

theorem vecAt.equiv (x : W) : vecAt v x = IndefiniteRowSideFullHecke.FiniteCovolume.realVec (v.equivFun x) := rfl

theorem invApply.equiv (g : archUnitary h v) (y : InfinitePlace E → Fin N → ℂ) :
    invApply g y = IndefiniteRowSideFullHecke.FiniteCovolume.gAct (realEquiv h v g)⁻¹ y := rfl

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] [IsCMField E] in
theorem isUnit_det_gramAt (w : InfinitePlace E) : IsUnit (gramAt h v w).det := by
  have := (isUnit_det_gram h v).map w.embedding
  rw [RingHom.map_det] at this
  exact this

theorem placeGram_matrixHermSpace (w : InfinitePlace E) :
    IndefiniteRowSideFullHecke.FiniteCovolume.placeJ (divisionPairOfAdelicFormsFaceColumnsData h v) w = (gramAt h v w)ᵀ := by
  simp [gramAt, IndefiniteRowSideFullHecke.FiniteCovolume.placeJ, matrixHermSpace_gram, Matrix.transpose_map]

variable {h v}

def majOf (M : Majorant h v) : IndefiniteRowSideFullHecke.FiniteCovolume.Majorant (divisionPairOfAdelicFormsFaceColumnsData h v) where
  H w := (M.P w)ᵀ
  posDef w := (M.posDef w).transpose
  involution w := by
    have key := mul_inv_mul_swap ((Matrix.isUnit_iff_isUnit_det _).mp (M.posDef w).isUnit)
      (isUnit_det_gramAt h v w) (M.siegel w)
    rw [placeGram_matrixHermSpace]
    calc (gramAt h v w)ᵀ * (M.P w)ᵀ⁻¹ * (gramAt h v w)ᵀ
        = (gramAt h v w * (M.P w)⁻¹ * gramAt h v w)ᵀ := by
          simp [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.mul_assoc]
      _ = (M.P w)ᵀ := by rw [key]

def majorantOfMatrixForm (M : IndefiniteRowSideFullHecke.FiniteCovolume.Majorant (divisionPairOfAdelicFormsFaceColumnsData h v)) : Majorant h v where
  P w := (M.H w)ᵀ
  posDef w := (M.posDef w).transpose
  siegel w := by
    have hP : IsUnit ((M.H w)ᵀ).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (M.posDef w).transpose.isUnit
    refine mul_inv_mul_swap (isUnit_det_gramAt h v w) hP ?_
    have := congrArg Matrix.transpose (M.involution w)
    rw [placeGram_matrixHermSpace] at this
    simpa [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.mul_assoc] using this

def majEquiv : Majorant h v ≃ IndefiniteRowSideFullHecke.FiniteCovolume.Majorant (divisionPairOfAdelicFormsFaceColumnsData h v) where
  toFun := majOf
  invFun := majorantOfMatrixForm
  left_inv M := by
    cases M
    simp [majOf, majorantOfMatrixForm]
  right_inv M := by
    cases M
    simp [majOf, majorantOfMatrixForm]

theorem Majorant.equiv : Function.Bijective (majOf (h := h) (v := v)) :=
  majEquiv.bijective

theorem Majorant.len.equiv (M : Majorant h v) (y : InfinitePlace E → Fin N → ℂ) :
    M.len y = (majOf M).norm y := by
  unfold Majorant.len IndefiniteRowSideFullHecke.FiniteCovolume.Majorant.norm
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  simp only [majOf, ReciprocityTheory.ChartRestriction.G.SA.hf, dotProduct, mulVec, Matrix.transpose_apply,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.star_def]
  ring

variable (v) in

def latOf (L : Submodule (𝓞 E) (Fin N → E)) : AddSubgroup W :=
  L.toAddSubgroup.comap (v.equivFun : W →+ (Fin N → E))

theorem mem_latOf {L : Submodule (𝓞 E) (Fin N → E)} {x : W} :
    x ∈ latOf v L ↔ v.equivFun x ∈ L := Iff.rfl

theorem latOf_injective : Function.Injective (latOf (W := W) v) := by
  intro L L' hLL
  ext y
  have := SetLike.ext_iff.mp hLL (v.equivFun.symm y)
  rwa [mem_latOf, mem_latOf, LinearEquiv.apply_symm_apply] at this

theorem relIndex_latOf (A B : Submodule (𝓞 E) (Fin N → E)) :
    (latOf v A).relIndex (latOf v B) = A.toAddSubgroup.relIndex B.toAddSubgroup := by
  unfold latOf
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective
    (fun y => v.equivFun.surjective y)]

theorem exists_latOf {La : AddSubgroup W} (hLa : ∀ (a : 𝓞 E) (x : W), x ∈ La → (a : E) • x ∈ La) :
    ∃ L : Submodule (𝓞 E) (Fin N → E), latOf v L = La := by
  refine ⟨{ carrier := {y | v.equivFun.symm y ∈ La}
            add_mem' := fun {a b} ha hb => by
              simp only [Set.mem_ofPred_eq, map_add] at *
              exact La.add_mem ha hb
            zero_mem' := by simp
            smul_mem' := fun c y hy => by
              simp only [Set.mem_ofPred_eq] at *
              rw [← IsScalarTower.algebraMap_smul E c y, map_smul]
              exact hLa c _ hy }, ?_⟩
  ext x
  change v.equivFun.symm (v.equivFun x) ∈ La ↔ x ∈ La
  rw [LinearEquiv.symm_apply_apply]

theorem coe_latOf (L : Submodule (𝓞 E) (Fin N → E)) :
    (latOf v L : Set W) = v.equivFun.symm '' (L : Set (Fin N → E)) := by
  ext x
  simp only [Set.mem_image, SetLike.mem_coe, mem_latOf]
  constructor
  · intro hx
    exact ⟨_, hx, v.equivFun.symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [LinearEquiv.apply_symm_apply]

theorem latOf_eq_map (L : Submodule (𝓞 E) (Fin N → E)) :
    latOf v L = ((L.restrictScalars ℤ).map
      (((v.equivFun.symm : (Fin N → E) ≃ₗ[E] W) : (Fin N → E) →ₗ[E] W).restrictScalars ℤ)).toAddSubgroup := by
  apply SetLike.coe_injective
  rw [coe_latOf, Submodule.coe_toAddSubgroup, Submodule.map_coe]
  rfl

theorem IsLattice.equiv :
    (∀ L : Submodule (𝓞 E) (Fin N → E),
      FiniteCovolume.IsLattice E (latOf v L) ↔ IndefiniteRowSideFullHecke.FiniteCovolume.IsLattice L) ∧
    ∀ La : AddSubgroup W, FiniteCovolume.IsLattice E La →
      ∃ L : Submodule (𝓞 E) (Fin N → E), latOf v L = La := by
  refine ⟨fun L => ?_, fun La hLa => exists_latOf hLa.smul_mem⟩
  have hfg : (latOf v L).FG ↔ L.FG := by
    rw [latOf_eq_map, ← Submodule.fg_iff_addSubgroup_fg]
    exact (Submodule.fg_map_iff ((((v.equivFun.symm : (Fin N → E) ≃ₗ[E] W) :
      (Fin N → E) →ₗ[E] W).restrictScalars ℤ)) (fun a b hab => v.equivFun.symm.injective hab)).trans
      (Submodule.FG.restrictScalars_iff (R := ℤ) (A := 𝓞 E) (S := L))
  have hspan : Submodule.span E (latOf v L : Set W) = ⊤ ↔
      Submodule.span E (L : Set (Fin N → E)) = ⊤ := by
    rw [coe_latOf]
    change Submodule.span E (((v.equivFun.symm : (Fin N → E) ≃ₗ[E] W) : (Fin N → E) →ₗ[E] W) ''
      (L : Set (Fin N → E))) = ⊤ ↔ _
    rw [Submodule.span_image, Submodule.map_eq_top_iff]
  have hsmul : ∀ (a : 𝓞 E) (x : W), x ∈ latOf v L → (a : E) • x ∈ latOf v L := by
    intro a x hx
    rw [mem_latOf, map_smul]
    exact L.smul_mem a hx
  constructor
  · intro hL
    exact ⟨hfg.1 hL.fg, hspan.1 hL.span_eq_top⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hsmul, hfg.2 h1, hspan.2 h2⟩

theorem isIntegral_conj_iff (a : E) :
    IsIntegral ℤ (conjHom F E a) ↔ IsIntegral ℤ a := by
  constructor
  · intro ha
    have := ha.map (conjHom F E).toIntAlgHom
    simpa [conj_conj] using this
  · intro ha
    exact ha.map (conjHom F E).toIntAlgHom

theorem dual.equiv (L : Submodule (𝓞 E) (Fin N → E)) :
    latOf v (IndefiniteRowSideFullHecke.FiniteCovolume.dual (divisionPairOfAdelicFormsFaceColumnsData h v) L) = dualLattice h (latOf v L) := by
  ext y
  change (∀ x ∈ L, IsIntegral ℤ ((divisionPairOfAdelicFormsFaceColumnsData h v).h (v.equivFun y) x)) ↔
    ∀ x ∈ latOf v L, h.toSesq y x ∈ integralClosure ℤ E
  constructor
  · intro hy x hx
    have := hy _ (mem_latOf.mp hx)
    rw [HermSpace.h.equiv, ← h.isSymm.eq y x, isIntegral_conj_iff] at this
    exact this
  · intro hy x hx
    have := hy (v.equivFun.symm x) (by rwa [mem_latOf, LinearEquiv.apply_symm_apply])
    rw [← v.equivFun.apply_symm_apply x, HermSpace.h.equiv, ← h.isSymm.eq, isIntegral_conj_iff]
    exact this

theorem relIndex_dual_latOf (L : Submodule (𝓞 E) (Fin N → E)) :
    (latOf v L).relIndex (dualLattice h (latOf v L)) =
      L.toAddSubgroup.relIndex (IndefiniteRowSideFullHecke.FiniteCovolume.dual (divisionPairOfAdelicFormsFaceColumnsData h v) L).toAddSubgroup := by
  rw [← dual.equiv, relIndex_latOf]

theorem isIntegralOn_latOf_iff (L : Submodule (𝓞 E) (Fin N → E)) :
    IsIntegralOn h (latOf v L) ↔ ∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ ((divisionPairOfAdelicFormsFaceColumnsData h v).h x y) := by
  constructor
  · intro hL x hx y hy
    rw [← v.equivFun.apply_symm_apply x, ← v.equivFun.apply_symm_apply y, HermSpace.h.equiv]
    exact hL _ (by rwa [mem_latOf, LinearEquiv.apply_symm_apply]) _
      (by rwa [mem_latOf, LinearEquiv.apply_symm_apply])
  · intro hL x hx y hy
    have := hL _ (mem_latOf.mp hy) _ (mem_latOf.mp hx)
    rw [HermSpace.h.equiv] at this
    exact this

theorem IsDIntegral.equiv (D : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) :
    IsDIntegral h D (latOf v L) ↔
      IndefiniteRowSideFullHecke.FiniteCovolume.IsDIntegral (divisionPairOfAdelicFormsFaceColumnsData h v) D L ∧
        L.toAddSubgroup.relIndex (IndefiniteRowSideFullHecke.FiniteCovolume.dual (divisionPairOfAdelicFormsFaceColumnsData h v) L).toAddSubgroup ≠ 0 := by
  have hidx := relIndex_dual_latOf (h := h) (v := v) L
  have hint := isIntegralOn_latOf_iff (h := h) (v := v) L
  constructor
  · intro hD
    exact ⟨⟨(IsLattice.equiv (v := v)).1 L |>.1 hD.isLattice, hint.1 hD.integral, hidx ▸ hD.index_le⟩,
      hidx ▸ hD.index_ne_zero⟩
  · rintro ⟨⟨hL, hI, hle⟩, hne⟩
    exact ⟨(IsLattice.equiv (v := v)).1 L |>.2 hL, hint.2 hI, hidx ▸ hne, hidx ▸ hle⟩

theorem IsDIntegral.equiv_of_dualIndexFinite (hfin : DualIndexFinite.Statement h) (D : ℕ)
    (L : Submodule (𝓞 E) (Fin N → E)) :
    IsDIntegral h D (latOf v L) ↔ IndefiniteRowSideFullHecke.FiniteCovolume.IsDIntegral (divisionPairOfAdelicFormsFaceColumnsData h v) D L := by
  rw [IsDIntegral.equiv]
  refine ⟨And.left, fun hT => ⟨hT, ?_⟩⟩
  rw [← relIndex_dual_latOf]
  exact hfin _ ((IsLattice.equiv (v := v)).1 L |>.2 hT.1)
    ((isIntegralOn_latOf_iff (h := h) (v := v) L).2 hT.2.1)

theorem IsIsotropicLine.equiv (l : Submodule E W) :
    FiniteCovolume.IsIsotropicLine h l ↔
      IndefiniteRowSideFullHecke.FiniteCovolume.IsIsotropicLine (divisionPairOfAdelicFormsFaceColumnsData h v)
        (l.map (v.equivFun : W →ₗ[E] (Fin N → E))) := by
  unfold FiniteCovolume.IsIsotropicLine IndefiniteRowSideFullHecke.FiniteCovolume.IsIsotropicLine
  rw [LinearEquiv.finrank_map_eq]
  refine and_congr_right fun hl => ?_
  constructor
  · intro h0 y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    rw [LinearEquiv.coe_coe, HermSpace.h.equiv]
    exact h0 x hx x hx
  · intro h0 x hx y hy
    have hxx : h.toSesq x x = 0 := by
      have := h0 (v.equivFun x) (Submodule.mem_map_of_mem hx)
      rwa [HermSpace.h.equiv] at this
    by_cases hx0 : x = 0
    · subst hx0
      rw [map_zero, LinearMap.zero_apply]
    · have hne : (⟨x, hx⟩ : l) ≠ 0 := fun e => hx0 (congrArg Subtype.val e)
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hl ⟨y, hy⟩
      have hy' : y = c • x := by
        have := congrArg Subtype.val hc
        simpa using this.symm
      rw [hy', map_smul, hxx, smul_zero]

theorem unitary_smul (γ : h.unitaryGroup) (x : W) : γ • x = (γ : W ≃ₗ[E] W) x := rfl

theorem smul_latOf (γ : h.unitaryGroup) (L : Submodule (𝓞 E) (Fin N → E)) :
    γ • latOf v L = latOf v (IndefiniteRowSideFullHecke.FiniteCovolume.act (unitaryEquiv h v γ : GL (Fin N) E) L) := by
  ext x
  change x ∈ ((γ : h.unitaryGroup) : W ≃ₗ[E] W) • latOf v L ↔ _
  rw [AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem,
    show ((γ : W ≃ₗ[E] W))⁻¹ • x = γ⁻¹ • x from rfl, mem_latOf, mem_latOf]
  change _ ↔ v.equivFun x ∈ L.map (IndefiniteRowSideFullHecke.FiniteCovolume.linO (unitaryEquiv h v γ : GL (Fin N) E))
  rw [Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    change ((unitaryEquiv h v γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ _ = _
    rw [unitaryEquiv_mulVec, ← unitary_smul, smul_inv_smul]
  · rintro ⟨z, hz, hzx⟩
    change ((unitaryEquiv h v γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ z = _ at hzx
    rw [← v.equivFun.apply_symm_apply z, unitaryEquiv_mulVec, ← unitary_smul] at hzx
    have := v.equivFun.injective hzx
    rw [← this, inv_smul_smul, LinearEquiv.apply_symm_apply]
    exact hz

theorem latticeStab.equiv (L : Submodule (𝓞 E) (Fin N → E)) (γ : h.unitaryGroup) :
    γ ∈ latticeStab h (latOf v L) ↔ unitaryEquiv h v γ ∈ IndefiniteRowSideFullHecke.FiniteCovolume.stab (divisionPairOfAdelicFormsFaceColumnsData h v) L := by
  rw [latticeStab, MulAction.mem_stabilizer_iff, smul_latOf]
  exact latOf_injective.eq_iff

theorem latticeStab_eq_comap (L : Submodule (𝓞 E) (Fin N → E)) :
    latticeStab h (latOf v L) =
      (IndefiniteRowSideFullHecke.FiniteCovolume.stab (divisionPairOfAdelicFormsFaceColumnsData h v) L).comap (unitaryEquiv h v).toMonoidHom := by
  ext γ
  exact latticeStab.equiv L γ

theorem archLatticeGroup.equiv (L : Submodule (𝓞 E) (Fin N → E)) :
    (archLatticeGroup h v (latOf v L)).map (realEquiv h v).toMonoidHom =
      IndefiniteRowSideFullHecke.FiniteCovolume.gammaInf (divisionPairOfAdelicFormsFaceColumnsData h v) L := by
  unfold archLatticeGroup IndefiniteRowSideFullHecke.FiniteCovolume.gammaInf
  rw [Subgroup.map_map, archEmbed_comp, ← Subgroup.map_map, latticeStab_eq_comap,
    Subgroup.map_comap_eq_self_of_surjective (unitaryEquiv h v).surjective]

theorem lineIndex.equiv (L : Submodule (𝓞 E) (Fin N → E)) (x : W) :
    FiniteCovolume.lineIndex E (latOf v L) x = IndefiniteRowSideFullHecke.FiniteCovolume.lineIndex L (v.equivFun x) := by
  have h1 : ringMultiples E x = latOf v (Submodule.span (𝓞 E) {v.equivFun x}) := by
    ext y
    rw [mem_latOf, Submodule.mem_span_singleton]
    simp only [ringMultiples, AddMonoidHom.mem_range, AddMonoidHom.coe_comp,
      Function.comp_apply, AddMonoidHom.flip_apply, smulAddHom_apply]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, by rw [map_smul]; rfl⟩
    · rintro ⟨a, ha⟩
      refine ⟨a, v.equivFun.injective ?_⟩
      rw [← ha, map_smul]
      rfl
  have h2 : latOf v L ⊓ (Submodule.span E {x}).toAddSubgroup =
      latOf v (L ⊓ (Submodule.span E {v.equivFun x}).restrictScalars (𝓞 E)) := by
    ext y
    simp only [AddSubgroup.mem_inf, mem_latOf, Submodule.mem_toAddSubgroup, Submodule.mem_inf,
      Submodule.restrictScalars_mem, Submodule.mem_span_singleton]
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, (map_smul _ _ _).symm⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, v.equivFun.injective (by rw [map_smul, hc])⟩
  unfold FiniteCovolume.lineIndex IndefiniteRowSideFullHecke.FiniteCovolume.lineIndex
  rw [h1, h2, relIndex_latOf]

theorem countBelow.equiv (M : Majorant h v) (VV : Set (Fin N → E)) (g : archUnitary h v) (t : ℝ) :
    FiniteCovolume.countBelow M (v.equivFun ⁻¹' VV) g t =
      IndefiniteRowSideFullHecke.FiniteCovolume.countBelow (majOf M) VV t (realEquiv h v g) := by
  have hset : {x ∈ v.equivFun ⁻¹' VV | M.len (invApply g (vecAt v x)) < t} =
      v.equivFun ⁻¹' {y | y ∈ VV ∧
        (majOf M).norm (IndefiniteRowSideFullHecke.FiniteCovolume.gAct (realEquiv h v g)⁻¹
          (IndefiniteRowSideFullHecke.FiniteCovolume.realVec y)) < t} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Majorant.len.equiv, invApply.equiv,
      vecAt.equiv]
  unfold FiniteCovolume.countBelow IndefiniteRowSideFullHecke.FiniteCovolume.countBelow
  rw [hset, Set.encard_preimage_of_injective_subset_range v.equivFun.injective
    (by rw [v.equivFun.surjective.range_eq]; exact Set.subset_univ _)]

theorem massBelow.equiv (M : Majorant h v) (μ : Measure (archUnitary h v))
    (FD : Set (archUnitary h v)) (VV : Set (Fin N → E)) (t : ℝ) :
    massBelow M μ FD (v.equivFun ⁻¹' VV) t =
      ∫⁻ g in realMeas h v '' FD, IndefiniteRowSideFullHecke.FiniteCovolume.countBelow (majOf M) VV t g
        ∂(μ.map (realMeas h v)) := by
  rw [MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image,
    lintegral_map_equiv]
  unfold massBelow
  refine lintegral_congr fun g => ?_
  rw [realMeas_apply, countBelow.equiv]

theorem vecStabGroup.equiv (L : Submodule (𝓞 E) (Fin N → E)) (x : W) :
    (vecStabGroup h v (latOf v L) x).map (realEquiv h v).toMonoidHom =
      IndefiniteRowSideFullHecke.FiniteCovolume.gammaVecInf (divisionPairOfAdelicFormsFaceColumnsData h v) L (v.equivFun x) := by
  have hK : (MulAction.stabilizer (latticeStab h (latOf v L)) x).map (latticeStab h (latOf v L)).subtype =
      (IndefiniteRowSideFullHecke.FiniteCovolume.stab (divisionPairOfAdelicFormsFaceColumnsData h v) L ⊓
        IndefiniteRowSideFullHecke.FiniteCovolume.fixVec (divisionPairOfAdelicFormsFaceColumnsData h v) (v.equivFun x)).comap (unitaryEquiv h v).toMonoidHom := by
    ext γ
    simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
      Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      refine ⟨(latticeStab.equiv L _).1 δ.2, ?_⟩
      change ((unitaryEquiv h v (δ : h.unitaryGroup) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ
        v.equivFun x = v.equivFun x
      rw [unitaryEquiv_mulVec]
      exact congrArg v.equivFun hδ
    · rintro ⟨h1, h2⟩
      refine ⟨⟨γ, (latticeStab.equiv L γ).2 h1⟩, ?_, rfl⟩
      change ((unitaryEquiv h v γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ
        v.equivFun x = v.equivFun x at h2
      rw [unitaryEquiv_mulVec] at h2
      exact v.equivFun.injective h2
  unfold vecStabGroup IndefiniteRowSideFullHecke.FiniteCovolume.gammaVecInf
  rw [← Subgroup.map_map, hK, Subgroup.map_map, archEmbed_comp, ← Subgroup.map_map,
    Subgroup.map_comap_eq_self_of_surjective (unitaryEquiv h v).surjective]

theorem matrixHermSpace_form_eq (V : IndefiniteRowSideFullHecke.FiniteCovolume.HermSpace E N) (y x : Fin N → E) :
    V.h y x = y ⬝ᵥ (V.J *ᵥ fun j => IndefiniteRowSideFullHecke.FiniteCovolume.conjE E (x j)) := by
  simp [IndefiniteRowSideFullHecke.FiniteCovolume.HermSpace.h, ReciprocityTheory.ChartRestriction.G.SA.hf, dotProduct, mulVec,
    Finset.mul_sum, mul_assoc]

theorem matrixHermSpace_form_single (V : IndefiniteRowSideFullHecke.FiniteCovolume.HermSpace E N) (i : Fin N) (a : E)
    (x : Fin N → E) :
    V.h (Pi.single i a) x = a * (V.J *ᵥ fun j => IndefiniteRowSideFullHecke.FiniteCovolume.conjE E (x j)) i := by
  rw [matrixHermSpace_form_eq, single_dotProduct]

theorem conj_matrixHermSpace_form (V : IndefiniteRowSideFullHecke.FiniteCovolume.HermSpace E N) (x y : Fin N → E) :
    IndefiniteRowSideFullHecke.FiniteCovolume.conjE E (V.h y x) = V.h x y := by
  have hJ : ∀ i j, IndefiniteRowSideFullHecke.FiniteCovolume.conjE E (V.J i j) = V.J j i := fun i j =>
    (congrFun (congrFun V.herm i) j).symm
  simp only [IndefiniteRowSideFullHecke.FiniteCovolume.HermSpace.h, ReciprocityTheory.ChartRestriction.G.SA.hf, map_sum, map_mul, hJ,
    IndefiniteRowSideFullHecke.FiniteCovolume.conjE_apply, IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem matrixSesq_apply (V : IndefiniteRowSideFullHecke.FiniteCovolume.HermSpace E N) (x y : Fin N → E) :
    Matrix.toLinearMapₛₗ₂' E (conjHom F E) (RingHom.id E) V.Jᵀ x y = V.h y x := by
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp only [IndefiniteRowSideFullHecke.FiniteCovolume.HermSpace.h, ReciprocityTheory.ChartRestriction.G.SA.hf, Matrix.transpose_apply,
    smul_eq_mul, RingHom.id_apply, conjHom_eq_conjE]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable (F) in

def hermitianFormOfMatrix (V : IndefiniteRowSideFullHecke.FiniteCovolume.HermSpace E N) : HermitianForm F E (Fin N → E) where
  toSesq := Matrix.toLinearMapₛₗ₂' E (conjHom F E) (RingHom.id E) V.Jᵀ
  isSymm := ⟨fun x y => by
    have key := matrixSesq_apply (F := F) V
    rw [key, key, conjHom_eq_conjE, conj_matrixHermSpace_form]⟩
  nonsingular := by
    have key := matrixSesq_apply (F := F) V
    have hJ : IsUnit V.J.det := V.nondeg
    have cc : ∀ a : E, IndefiniteRowSideFullHecke.FiniteCovolume.conjE E (IndefiniteRowSideFullHecke.FiniteCovolume.conjE E a) = a := fun a => by
      simp [IndefiniteRowSideFullHecke.FiniteCovolume.conjE_apply, IsCMField.complexConj_apply_apply]
    constructor
    · intro x x' hxx
      have hv : (V.J *ᵥ fun j => IndefiniteRowSideFullHecke.FiniteCovolume.conjE E (x j)) =
          V.J *ᵥ fun j => IndefiniteRowSideFullHecke.FiniteCovolume.conjE E (x' j) := by
        funext i
        have := LinearMap.congr_fun hxx (Pi.single i 1)
        rw [key, key, matrixHermSpace_form_single, matrixHermSpace_form_single, one_mul, one_mul] at this
        exact this
      have hc := congrArg (fun u => V.J⁻¹ *ᵥ u) hv
      simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hJ, Matrix.one_mulVec] at hc
      funext j
      rw [← cc (x j), ← cc (x' j), congrFun hc j]
    · intro f
      refine ⟨fun j => IndefiniteRowSideFullHecke.FiniteCovolume.conjE E ((V.J⁻¹ *ᵥ fun i => f (Pi.single i 1)) j), ?_⟩
      refine LinearMap.pi_ext fun i a => ?_
      rw [key, matrixHermSpace_form_single]
      rw [show (fun j => IndefiniteRowSideFullHecke.FiniteCovolume.conjE E (IndefiniteRowSideFullHecke.FiniteCovolume.conjE E
          ((V.J⁻¹ *ᵥ fun i => f (Pi.single i 1)) j))) = V.J⁻¹ *ᵥ fun i => f (Pi.single i 1) from
        funext fun j => cc _]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mulVec]
      rw [show (Pi.single i a : Fin N → E) = a • Pi.single i 1 by
        ext k
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk], map_smul, smul_eq_mul]

theorem hermitianFormOfMatrix_apply (V : IndefiniteRowSideFullHecke.FiniteCovolume.HermSpace E N) (x y : Fin N → E) :
    (hermitianFormOfMatrix F V).toSesq x y = V.h y x :=
  matrixSesq_apply V x y

theorem matrixHermSpace_surjective (V : IndefiniteRowSideFullHecke.FiniteCovolume.HermSpace E N) :
    divisionPairOfAdelicFormsFaceColumnsData (hermitianFormOfMatrix F V) (Pi.basisFun E (Fin N)) = V := by
  obtain ⟨J, hJ, hJ'⟩ := V
  unfold divisionPairOfAdelicFormsFaceColumnsData
  congr 1
  ext i j
  rw [Matrix.transpose_apply, Automorphic.gram_apply, hermitianFormOfMatrix_apply, Pi.basisFun_apply, Pi.basisFun_apply,
    matrixHermSpace_form_single, one_mul]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

end HidaSetting

universe u w

theorem Objects.equiv :
    (∀ (F : Type u) (E : Type) [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
      [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E], IsCMField E) ∧
    (∀ (F : Type u) (E : Type) [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
      [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E] [IsCMField E]
      (W : Type w) [AddCommGroup W] [Module E W] (N : ℕ) (h : HermitianForm F E W)
      (v : Basis (Fin N) E W),

      finrank ℚ F = IndefiniteRowSideFullHecke.FiniteCovolume.fDeg E ∧ finrank E W = N ∧

      (∀ x y, (divisionPairOfAdelicFormsFaceColumnsData h v).h (v.equivFun x) (v.equivFun y) = h.toSesq y x) ∧

      unitaryGroupMatrix (conjHom F E) (gram h.toSesq v) =
        IndefiniteRowSideFullHecke.FiniteCovolume.unitaryGroup (divisionPairOfAdelicFormsFaceColumnsData h v) ∧
      (∀ (g : h.unitaryGroup) (x : W),
        ((unitaryEquiv h v g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ v.equivFun x =
          v.equivFun ((g : W ≃ₗ[E] W) x)) ∧

      archUnitary h v = IndefiniteRowSideFullHecke.FiniteCovolume.realPoints (divisionPairOfAdelicFormsFaceColumnsData h v) ∧
      (∀ γ : h.unitaryGroup, realEquiv h v (archEmbed h v γ) =
        IndefiniteRowSideFullHecke.FiniteCovolume.toReal (divisionPairOfAdelicFormsFaceColumnsData h v) (unitaryEquiv h v γ)) ∧
      (∀ x : W, vecAt v x = IndefiniteRowSideFullHecke.FiniteCovolume.realVec (v.equivFun x)) ∧
      (∀ (g : archUnitary h v) (y : InfinitePlace E → Fin N → ℂ),
        invApply g y = IndefiniteRowSideFullHecke.FiniteCovolume.gAct (realEquiv h v g)⁻¹ y) ∧

      Function.Bijective (majOf (h := h) (v := v)) ∧
      (∀ (M : Majorant h v) (y : InfinitePlace E → Fin N → ℂ), M.len y = (majOf M).norm y) ∧

      (∀ L : Submodule (𝓞 E) (Fin N → E),
        FiniteCovolume.IsLattice E (latOf v L) ↔ IndefiniteRowSideFullHecke.FiniteCovolume.IsLattice L) ∧
      (∀ La : AddSubgroup W, FiniteCovolume.IsLattice E La →
        ∃ L : Submodule (𝓞 E) (Fin N → E), latOf v L = La) ∧
      (∀ L : Submodule (𝓞 E) (Fin N → E),
        latOf v (IndefiniteRowSideFullHecke.FiniteCovolume.dual (divisionPairOfAdelicFormsFaceColumnsData h v) L) = dualLattice h (latOf v L)) ∧
      (∀ (D : ℕ) (L : Submodule (𝓞 E) (Fin N → E)), IsDIntegral h D (latOf v L) ↔
        IndefiniteRowSideFullHecke.FiniteCovolume.IsDIntegral (divisionPairOfAdelicFormsFaceColumnsData h v) D L ∧
          L.toAddSubgroup.relIndex (IndefiniteRowSideFullHecke.FiniteCovolume.dual (divisionPairOfAdelicFormsFaceColumnsData h v) L).toAddSubgroup ≠ 0) ∧

      (∀ (L : Submodule (𝓞 E) (Fin N → E)) (γ : h.unitaryGroup),
        γ ∈ latticeStab h (latOf v L) ↔
          unitaryEquiv h v γ ∈ IndefiniteRowSideFullHecke.FiniteCovolume.stab (divisionPairOfAdelicFormsFaceColumnsData h v) L) ∧
      (∀ L : Submodule (𝓞 E) (Fin N → E),
        (archLatticeGroup h v (latOf v L)).map (realEquiv h v).toMonoidHom =
          IndefiniteRowSideFullHecke.FiniteCovolume.gammaInf (divisionPairOfAdelicFormsFaceColumnsData h v) L) ∧

      (∀ l : Submodule E W, FiniteCovolume.IsIsotropicLine h l ↔
        IndefiniteRowSideFullHecke.FiniteCovolume.IsIsotropicLine (divisionPairOfAdelicFormsFaceColumnsData h v)
          (l.map (v.equivFun : W →ₗ[E] (Fin N → E)))) ∧
      (∀ (L : Submodule (𝓞 E) (Fin N → E)) (x : W),
        FiniteCovolume.lineIndex E (latOf v L) x =
          IndefiniteRowSideFullHecke.FiniteCovolume.lineIndex L (v.equivFun x)) ∧

      (∀ (M : Majorant h v) (VV : Set (Fin N → E)) (g : archUnitary h v) (t : ℝ),
        FiniteCovolume.countBelow M (v.equivFun ⁻¹' VV) g t =
          IndefiniteRowSideFullHecke.FiniteCovolume.countBelow (majOf M) VV t (realEquiv h v g)) ∧
      (∀ (M : Majorant h v) (μ : Measure (archUnitary h v)) (FD : Set (archUnitary h v))
        (VV : Set (Fin N → E)) (t : ℝ),
        massBelow M μ FD (v.equivFun ⁻¹' VV) t =
          ∫⁻ g in realMeas h v '' FD, IndefiniteRowSideFullHecke.FiniteCovolume.countBelow (majOf M) VV t g
            ∂(μ.map (realMeas h v))) ∧

      (∀ (L : Submodule (𝓞 E) (Fin N → E)) (x : W),
        (vecStabGroup h v (latOf v L) x).map (realEquiv h v).toMonoidHom =
          IndefiniteRowSideFullHecke.FiniteCovolume.gammaVecInf (divisionPairOfAdelicFormsFaceColumnsData h v) L (v.equivFun x))) ∧
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
      (V : IndefiniteRowSideFullHecke.FiniteCovolume.HermSpace E N),
      ∃ h : HermitianForm (NumberField.maximalRealSubfield E) E (Fin N → E),
        divisionPairOfAdelicFormsFaceColumnsData h (Pi.basisFun E (Fin N)) = V) := by
  refine ⟨fun F E _ _ _ _ _ _ _ _ => isCMField (F := F),
    fun F E _ _ _ _ _ _ _ _ _ W _ _ N h v => ?_,
    fun E _ _ _ N V => ⟨hermitianFormOfMatrix _ V, matrixHermSpace_surjective V⟩⟩
  exact ⟨fDeg.equiv, by rw [Module.finrank_eq_card_basis v, Fintype.card_fin],
    HermSpace.h.equiv h v, unitaryGroup.equiv h v, unitaryEquiv_mulVec h v, archUnitary.equiv h v,
    archEmbed.equiv h v, vecAt.equiv v, invApply.equiv h v,
    Majorant.equiv, Majorant.len.equiv, (IsLattice.equiv (v := v)).1,
    (IsLattice.equiv (v := v)).2, dual.equiv, IsDIntegral.equiv, latticeStab.equiv,
    archLatticeGroup.equiv, IsIsotropicLine.equiv, lineIndex.equiv, countBelow.equiv,
    massBelow.equiv, vecStabGroup.equiv⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume.HermitianSpaceComparison
