import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowForm.ClassFrameOperators

open Formalism.L2.SG.PackageTie

section HS

variable {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem norm_hsEmb_sq_sum (A : Wq →L[ℂ] Wp) :
    ‖hsEmb A‖ ^ 2 = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [hsEmb]

theorem sum_norm_sq_indep {ι ι' : Type} [Fintype ι] [Fintype ι'] (A : Wq →L[ℂ] Wp)
    (e : OrthonormalBasis ι ℂ Wq) (e' : OrthonormalBasis ι' ℂ Wq) :
    ∑ i, ‖A (e i)‖ ^ 2 = ∑ i, ‖A (e' i)‖ ^ 2 := by
  haveI : CompleteSpace Wq := FiniteDimensional.complete ℂ Wq
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp

  have key : ∀ {κ : Type} [Fintype κ] (b : OrthonormalBasis κ ℂ Wq),
      ∑ i, ‖A (b i)‖ ^ 2 = ∑ k, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ Wp k)‖ ^ 2 := by
    intro κ _ b
    calc ∑ i, ‖A (b i)‖ ^ 2
        = ∑ i, ∑ k, ‖inner ℂ (stdOrthonormalBasis ℂ Wp k) (A (b i))‖ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact ((stdOrthonormalBasis ℂ Wp).sum_sq_norm_inner_right (A (b i))).symm
      _ = ∑ k, ∑ i, ‖inner ℂ (stdOrthonormalBasis ℂ Wp k) (A (b i))‖ ^ 2 := Finset.sum_comm
      _ = ∑ k, ∑ i, ‖inner ℂ ((ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ Wp k)) (b i)‖ ^ 2 := by
          simp only [ContinuousLinearMap.adjoint_inner_left]
      _ = ∑ k, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ Wp k)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          exact b.sum_sq_norm_inner_left _
  rw [key e, key e']

theorem norm_hsEmb_conj (U : Wp ≃ₗᵢ[ℂ] Wp) (U' : Wq ≃ₗᵢ[ℂ] Wq) (A : Wq →L[ℂ] Wp) :
    ‖hsEmb ((U : Wp →L[ℂ] Wp).comp (A.comp (U'.symm : Wq →L[ℂ] Wq)))‖ = ‖hsEmb A‖ := by
  have h2 : ‖hsEmb ((U : Wp →L[ℂ] Wp).comp (A.comp (U'.symm : Wq →L[ℂ] Wq)))‖ ^ 2 = ‖hsEmb A‖ ^ 2 := by
    rw [norm_hsEmb_sq_sum, norm_hsEmb_sq_sum]
    have hU : ∀ i, ‖((U : Wp →L[ℂ] Wp).comp (A.comp (U'.symm : Wq →L[ℂ] Wq))) (stdOrthonormalBasis ℂ Wq i)‖ =
        ‖A (((stdOrthonormalBasis ℂ Wq).map U'.symm) i)‖ := by
      intro i
      simp [OrthonormalBasis.map_apply]
    simp_rw [hU]
    exact sum_norm_sq_indep A _ _
  have h3 := congrArg Real.sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3

def opOf (x : HS Wq Wp) : Wq →L[ℂ] Wp :=
  ∑ i, (innerSL ℂ (stdOrthonormalBasis ℂ Wq i)).smulRight (x i)

theorem opOf_apply (x : HS Wq Wp) (e : Wq) :
    opOf x e = ∑ i, inner ℂ (stdOrthonormalBasis ℂ Wq i) e • x i := by
  simp [opOf]

theorem hsEmb_opOf (x : HS Wq Wp) : hsEmb (opOf x) = x := by
  ext j
  simp [hsEmb, opOf_apply, orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ Wq).orthonormal]

theorem opOf_hsEmb (A : Wq →L[ℂ] Wp) : opOf (hsEmb A) = A := by
  ext e
  rw [opOf_apply]
  conv_rhs => rw [← (stdOrthonormalBasis ℂ Wq).sum_repr' e]
  simp [hsEmb, map_sum, map_smul]

def opOfL : HS Wq Wp →ₗ[ℂ] (Wq →L[ℂ] Wp) where
  toFun := opOf
  map_add' x y := by
    ext e
    simp [opOf_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext e
    simp [opOf_apply, Finset.smul_sum, smul_comm c]

def conjOp (U : Wp ≃ₗᵢ[ℂ] Wp) (U' : Wq ≃ₗᵢ[ℂ] Wq) : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp) where
  toFun A := (U : Wp →L[ℂ] Wp).comp (A.comp (U'.symm : Wq →L[ℂ] Wq))
  map_add' A B := by
    ext e
    simp
  map_smul' c A := by
    ext e
    simp

def conjL (U : Wp ≃ₗᵢ[ℂ] Wp) (U' : Wq ≃ₗᵢ[ℂ] Wq) : HS Wq Wp →ₗᵢ[ℂ] HS Wq Wp where
  toLinearMap := hsEmb ∘ₗ conjOp U U' ∘ₗ opOfL
  norm_map' x := by
    show ‖hsEmb ((U : Wp →L[ℂ] Wp).comp ((opOf x).comp (U'.symm : Wq →L[ℂ] Wq)))‖ = ‖x‖
    rw [norm_hsEmb_conj, hsEmb_opOf]

theorem conjL_hsEmb (U : Wp ≃ₗᵢ[ℂ] Wp) (U' : Wq ≃ₗᵢ[ℂ] Wq) (A : Wq →L[ℂ] Wp) :
    conjL U U' (hsEmb A) = hsEmb ((U : Wp →L[ℂ] Wp).comp (A.comp (U'.symm : Wq →L[ℂ] Wq))) := by
  show hsEmb (conjOp U U' (opOf (hsEmb A))) = _
  rw [opOf_hsEmb]
  rfl

theorem norm_tsum_conj {ι : Type*} (U : Wp ≃ₗᵢ[ℂ] Wp) (U' : Wq ≃ₗᵢ[ℂ] Wq) (k : ℂ) (x : ι → HS Wq Wp) :
    ‖∑' s, k • conjL U U' (x s)‖ = ‖k‖ * ‖∑' s, x s‖ := by

  have hmap : (∑' s, conjL U U' (x s)) = conjL U U' (∑' s, x s) := by
    have h : ((conjL U U').toLinearIsometryEquiv rfl).toContinuousLinearEquiv (∑' s, x s) =
        ∑' s, ((conjL U U').toLinearIsometryEquiv rfl).toContinuousLinearEquiv (x s) :=
      ContinuousLinearEquiv.map_tsum _
    simpa using h.symm
  rw [tsum_const_smul'', hmap, norm_smul, LinearIsometry.norm_map]

end HS

end Formalism.L2.SG.Pf.RowForm.ClassFrameOperators

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def ClassFrameU : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ),
    ∃ (U : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u) (U' : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u') (ζ : ℂ), ‖ζ‖ = 1 ∧
      ∀ s : LiftT X Y u u' κ R ρ,
        Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s.1 =
          (ζ * (((Real.sqrt ((bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0 *
              (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0'))⁻¹ : ℝ) : ℂ) *
            Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm) •
            ((U : X.Vpi u →L[ℂ] X.Vpi u).comp
              ((Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)).comp
                (U'.symm : X.Vpi u' →L[ℂ] X.Vpi u')))

theorem classFrameC_of
    (hU : ClassFrameU X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ)
    (hc : 0 ≤ (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0 *
      (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0') :
    ClassFrameC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ := by
  intro R ρ
  obtain ⟨U, U', ζ, hζ, hs⟩ := hU R ρ
  set B := bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq with hB
  set r : ℝ := (Real.sqrt (B.c0 * B.c0'))⁻¹ with hr

  have hsum : (∑' s : LiftT X Y u u' κ R ρ, liftVec X Y u u' s.1) =
      ∑' s : LiftT X Y u u' κ R ρ, (ζ * (r : ℂ)) • ClassFrameOperators.conjL U U'
        ((((Formalism.L2.SG.TermOp.wt s.1 : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm) •
          Formalism.L2.SG.PackageTie.hsEmb
            (Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))) := by
    congr 1
    funext s
    simp only [liftVec]
    rw [hs s]
    simp only [map_smul, ClassFrameOperators.conjL_hsEmb, smul_smul]
    congr 1
    ring
  rw [hsum, ClassFrameOperators.norm_tsum_conj, norm_mul, hζ, one_mul, mul_pow]
  congr 1
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, hr, inv_pow, Real.sq_sqrt hc]

def ClassFrameOO : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ),
    ∃ (U : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u) (U' : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u') (ζ : ℂ), ‖ζ‖ = 1 ∧
      ∀ s : LiftT X Y u u' κ R ρ,
        Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf)
                  ((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf) s.1.pt) • Formalism.L2.SG.TermOp.OOt s.1 =
          (ζ * Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm) •
            ((U : X.Vpi u →L[ℂ] X.Vpi u).comp
              ((Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)).comp
                (U'.symm : X.Vpi u' →L[ℂ] X.Vpi u')))

theorem classFrame_scl (hV : 0 < X.volK2) :
    Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 =
      (Real.sqrt ((bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0 *
        (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0'))⁻¹ := by
  simp only [Formalism.L2.SG.TermOp.scl]
  exact Formalism.L2.SG.MassDataConc.scaled_volume_level_subgroup X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (Formalism.L2.SG.LocVol.locOf X u u' ψ) hV
    (Formalism.L2.SG.MassDataConc.anOf (Y.tO u u') 0 0 0 0 0 0 0 0 0 0 ⟨0, 0⟩)

theorem classFrameU_of (hOO : ClassFrameOO X Y u u' vR i0 i0' νq κ) (hV : 0 < X.volK2) :
    ClassFrameU X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ := by
  intro R ρ
  obtain ⟨U, U', ζ, hζ, hs⟩ := hOO R ρ
  refine ⟨U, U', ζ, hζ, fun s => ?_⟩
  simp only [Formalism.L2.SG.TermOp.ampN]
  rw [hs s, ← classFrame_scl (hb := hb) (X0 := X0) (ψ := ψ) (sd := sd) (C := C) (Th := Th) (Q := Q) (M := M)
    (δ := δ) (hV := hV), smul_smul]
  congr 1
  ring

theorem classFrameC_of_OO (hOO : ClassFrameOO X Y u u' vR i0 i0' νq κ) (hV : 0 < X.volK2)
    (hc : 0 ≤ (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0 *
      (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0') :
    ClassFrameC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ := classFrameC_of X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ
  (classFrameU_of X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ hOO hV) hc

end Formalism.L2.SG.Pf.RowForm
