import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabelThetaLiftSpaceIffDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalRowPartsOfDistinctTypesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram evC dualC)
namespace GlobalTheory.OrthW

theorem evC_single {D : D7} {V : HSp D} {P : Pl D.host.E} {a : List ℤ → ℂ} {d : List ℤ} (hd : IsLab V P d) :
    evC V P a (Finsupp.single d 1) = a d := by
  unfold evC
  rw [Finsupp.sum_single_index] <;> simp [hd]

theorem dualC_single (d : List ℤ) :
    dualC (Finsupp.mapRange star (star_zero ℂ) (Finsupp.single d (1 : ℂ))) = Finsupp.single (dualLab d) 1 := by
  simp [dualC, Finsupp.mapRange_single, Finsupp.mapDomain_single]

theorem inner_eq_zero_of_eig {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (T S : H →ₗ[ℂ] H) (hadj : LinearMap.adjoint T = S) {a b b' : ℂ} {x y : H} (hx : T x = a • x) (hy : T y = b • y)
    (hy' : S y = b' • y) (hne : a ≠ b) : ⟪x, y⟫_ℂ = 0 := by
  have hxy : ⟪T x, y⟫_ℂ = ⟪x, S y⟫_ℂ := by rw [← hadj, LinearMap.adjoint_inner_right]
  have hyy : ⟪T y, y⟫_ℂ = ⟪y, S y⟫_ℂ := by rw [← hadj, LinearMap.adjoint_inner_right]
  rw [hx, hy'] at hxy
  rw [hy, hy'] at hyy
  rw [inner_smul_left, inner_smul_right] at hxy hyy
  by_cases hy0 : y = 0
  · simp [hy0]
  have hyy0 : ⟪y, y⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hy0
  have hconj : (starRingEnd ℂ) b = b' := mul_right_cancel₀ hyy0 hyy
  rw [← hconj] at hxy
  have hne' : (starRingEnd ℂ) a ≠ (starRingEnd ℂ) b := fun h => hne ((starRingEnd ℂ).injective h)
  have := sub_eq_zero.mpr hxy
  rw [← sub_mul] at this
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne')

theorem inner_wp3_eq_zero_of_ne : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → ∀ i p q, p ≠ q → ∀ w ∈ R.Wp3 i p, ∀ w' ∈ R.Wp3 i q, ⟪w, w'⟫_ℂ = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hW hEx hSch hOkH hPos hB i p q hpq
  obtain ⟨hCore, hSF, hE, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨hE', hOpsE, hNE, -, hEig, hMem⟩ := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R.toRealDat F.lv2 hCore hSch R.SF hSF
  obtain ⟨hw, -, hNW, -, -, -, hWEig, -⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hCore hSch hX R.SF hSF i
  have hLab := fun P d hP => GlobalTheory.T.isLabel_thetaLiftSpace_iff_dual (s := s) R.toRealDat F.lv2 hCore i P d hP
  have horthE := GlobalTheory.T.orthogonal_rowParts_of_distinct_types R F hOk hW hOkH hPos hB p q hpq
  have key : ∀ c c', R.Carries p c → R.Carries q c' → ∀ x ∈ R.Wc' i c, ∀ y ∈ R.Wc' i c', ⟪x, y⟫_ℂ = 0 := by
    intro c c' hc hc' x hx y hy
    rw [hWc] at hx hy
    rcases Classical.em (∃ P d, Good R.toRealDat A3.A.μ0 P ∧ IsLab (Wc D i) P d ∧ c P d ≠ c' P d) with hdiff | hdiff
    · obtain ⟨P, d, hP, hd, hne⟩ := hdiff
      have hd' : IsLab (Wc D i) P (dualLab d) := (hLab P (dualLab d) hP).2.mpr ((hLab P d hP).1.mp hd)
      have hadj := hNW.2 P hP (Finsupp.single d 1)
      rw [dualC_single] at hadj
      have ex := hWEig c P hP (Finsupp.single d 1) x hx
      have ey := hWEig c' P hP (Finsupp.single d 1) y hy
      have ey' := hWEig c' P hP (Finsupp.single (dualLab d) 1) y hy
      rw [evC_single hd] at ex ey
      rw [evC_single hd'] at ey'
      exact inner_eq_zero_of_eig _ _ hadj ex ey ey' hne
    · have hagree : ∀ P d, Good R.toRealDat A3.A.μ0 P → IsLab (Wc D i) P d → c P d = c' P d :=
        fun P d hP hd => Classical.byContradiction fun h => hdiff ⟨P, d, hP, hd, h⟩
      exfalso
      have hle : EEc R.toRealDat R.SF c ≤ EEc R.toRealDat R.SF c' := by
        intro e he
        apply hMem c' e
        intro P d hP hd
        rw [hEig c P hP _ e he, evC_single hd]
        congr 1
        apply hagree P (dualLab d) hP
        exact (hLab P (dualLab d) hP).2.mpr ((hLab P d hP).1.mp ((hLab P d hP).2.mpr hd))
      obtain ⟨e, he, he0⟩ := (Submodule.ne_bot_iff _).mp hc.1
      have hep : e ∈ R.EEp3 p := (le_iSup₂ (f := fun c (_ : R.Carries p c) => R.EEc c) c hc) he
      have he' : e ∈ R.EEc c' := by
        rw [hE] at he ⊢
        exact hle he
      have heq : e ∈ R.EEp3 q := (le_iSup₂ (f := fun c (_ : R.Carries q c) => R.EEc c) c' hc') he'
      exact he0 (inner_self_eq_zero.mp (horthE e hep e heq))
  have hort : R.Wp3 i p ⟂ R.Wp3 i q := by
    unfold RealDat3.Wp3
    refine Submodule.isOrtho_iSup_left.mpr fun c => Submodule.isOrtho_iSup_left.mpr fun hc => ?_
    refine Submodule.isOrtho_iSup_right.mpr fun c' => Submodule.isOrtho_iSup_right.mpr fun hc' => ?_
    exact Submodule.isOrtho_iff_inner_eq.mpr (key c c' hc hc')
  intro w hw' w' hw''
  exact Submodule.isOrtho_iff_inner_eq.mp hort w hw' w' hw''

end GlobalTheory.OrthW
