import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FiniteDegreeMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeAndEigenDegrees
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberFinitePushforward
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPointResidueNonzero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleOfDensePart

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurvePullDeg

variable {k : Type} [Field k] {C C' : Scheme.{0}} [Algebra k Γ(C, ⊤)] [IsIntegral C]
  [Algebra k Γ(C', ⊤)] [IsIntegral C']

theorem map_genericPoint (π : C' ⟶ C) [Surjective π] : π (genericPoint C') = genericPoint C := by
  obtain ⟨y, hy⟩ := π.surjective (genericPoint C)
  refine ((genericPoint_specializes _).antisymm ?_).eq.symm
  exact ((genericPoint_specializes y).map π.continuous).trans (specializes_of_eq hy)

theorem flat_of_surjective (hC : IsSmoothProjCurve k C) (π : C' ⟶ C) [Surjective π] : Flat π := by
  have hη := map_genericPoint π
  refine Flat.of_stalkMap π fun x => ?_
  have hF : IsField (C.presheaf.stalk (π (genericPoint C'))) := by
    rw [hη]; exact Field.toIsField C.functionField
  have hg : Function.Injective (π.stalkMap (genericPoint C')).hom := by
    refine (injective_iff_map_eq_zero _).2 fun a h0 => ?_
    by_contra ha
    obtain ⟨c, hc⟩ := hF.mul_inv_cancel ha
    have := congrArg (π.stalkMap (genericPoint C')).hom hc
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  have h : genericPoint C' ⤳ x := genericPoint_specializes x
  have hπ : π (genericPoint C') ⤳ π x := h.map π.continuous
  have hinj : Function.Injective (π.stalkMap x).hom := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    apply GlobalTheory.PushInv.stalkSpecializes_injective hπ
    rw [map_zero]
    apply hg
    rw [map_zero, Scheme.Hom.stalkSpecializes_stalkMap_apply π (genericPoint C') x h a, ha, map_zero]
  haveI := hC.isPrincipalIdealRing_stalk (π x)
  haveI : IsDedekindDomain (C.presheaf.stalk (π x)) := inferInstance
  letI := (π.stalkMap x).hom.toAlgebra
  show Module.Flat _ _
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  intro b hb
  obtain ⟨⟨a, ha⟩, hab⟩ := (Submodule.mem_torsion_iff b).1 hb
  have ha0 : (π.stalkMap x).hom a ≠ 0 := fun h0 =>
    nonZeroDivisors.ne_zero ha (hinj (h0.trans (map_zero _).symm))
  have : (π.stalkMap x).hom a * b = 0 := hab
  exact (Submodule.mem_bot _).2 ((mul_eq_zero.1 this).resolve_left ha0)

theorem deg_pullback_eq [IsAlgClosed k] (hC : IsSmoothProjCurve k C) (hC' : IsSmoothProjCurve k C')
    (π : C' ⟶ C) [IsFinite π] (hη : π (genericPoint C') = genericPoint C)
    (hf : ∀ a : k, π.appTop (algebraMap k Γ(C, ⊤) a) = algebraMap k Γ(C', ⊤) a)
    {E : C.Modules} {r : ℕ} (hE : IsVB E r) :
    deg k ((Scheme.Modules.pullback π).obj E) =
      (π.residueDegree (genericPoint C') : ℤ) * deg k E := by
  have hP := hC.toIsProjCurve
  have hP' := hC'.toIsProjCurve
  have hD := hE.isLB_det
  have hD' := (hE.pullback π).isLB_det
  have hDp := pull_isLB hD π
  have e₁ := ProjFin.interNumOn_eq_residueDegree_mul k C C' π hP.isProjOver hP.dim_eq hη _ hD
  rw [interNumOn_eq_interNum_pull hf (isLB_vecOne hD)] at e₁
  have e₂ : (fun j => ((![det E r] : Fin 1 → LB C) j).pull π) = ![(det E r).pull π] :=
    funext fun j => by fin_cases j; rfl
  rw [e₂] at e₁
  rw [← SlopeEigen.degLB_det hC' r (hE.pullback π), ← SlopeEigen.degLB_det hC r hE,
    ← degLB_congr hDp hD' (hE.lbIso_det_pullback π), hP'.degLB_eq_interNum hDp,
    hP.degLB_eq_interNum hD, e₁]

theorem exists_scalesDeg : ∀ (k : Type) [Field k] [IsAlgClosed k] (C C' : Scheme.{0})
    [Algebra k Γ(C, ⊤)] [IsIntegral C] [Algebra k Γ(C', ⊤)] [IsIntegral C'],
    IsSmoothProjCurve k C → IsSmoothProjCurve k C' → ∀ π : C' ⟶ C, IsCover k π →
      ∃ m : ℕ, 0 < m ∧ GlobalTheory.IndefiniteRowSideFullHecke.FiniteDegreeMorphisms.ScalesDeg k π m := by
  intro k _ _ C C' _ _ _ _ hC hC' π hπ
  obtain ⟨hfin, hsurj, hcomp⟩ := hπ
  haveI := hfin
  haveI := hsurj
  haveI : Flat π := flat_of_surjective hC π
  have hη := map_genericPoint π
  have hf : ∀ a : k, π.appTop (algebraMap k Γ(C, ⊤) a) = algebraMap k Γ(C', ⊤) a := fun a => by
    rw [algebraMap_eq_strHom k C a, algebraMap_eq_strHom k C' a, ← hcomp, Scheme.Hom.comp_appTop]
    rfl
  have hdeg : 0 < π.residueDegree (genericPoint C') := Nat.pos_of_ne_zero
    ((PullbackFinitePoint.residueDegree_ne_zero_iff_finite π _).2
      (residueFieldMap_finite_of_locallyQuasiFinite π _))
  refine ⟨_, hdeg, fun E r hE => ⟨deg_pullback_eq hC hC' π hη hf hE, fun G i hi => ?_⟩⟩
  haveI := hi.mono
  haveI := hi.isFiniteQC
  have hG := SlopeEigen.isVB_of_mono hC hE i
  haveI := hG.isQuasicoherent
  haveI := hE.isQuasicoherent
  exact ⟨⟨QCoh.mono_pullback_map π i, (hG.pullback π).isFiniteQC⟩, deg_pullback_eq hC hC' π hη hf hG⟩

end GlobalTheory.CurvePullDeg
