import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsProperCurveThroughPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmoothOfDedekindCharts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberFinitePushforward
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPointResidueNonzero
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.NefCurveTest

theorem smoothOfRelativeDimension_one {k : Type} [Field k] {C : Scheme.{0}} [IsIntegral C] (s : C ⟶ Sp k) [Smooth s]
    (hd : topologicalKrullDim C = 1) : SmoothOfRelativeDimension 1 s := by
  obtain ⟨n, hn⟩ : ∃ n, SmoothOfRelativeDimension n s := exists_dim_of_preconnected s (genericPoint C)
  obtain ⟨x, hx⟩ := ProperCurve.exists_ne_genericPoint hd
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  have e := (ProperCurve.ringKrullDim_eq_one hd hU hxU hx).symm.trans
    (SmoothDim.ringKrullDim_affineOpen k _ _ _ hn U hU ⟨x, hxU⟩)
  obtain rfl : 1 = n := by exact_mod_cast e
  exact hn

theorem exists_smooth_finite {k : Type} [Field k] [IsAlgClosed k] {D : Scheme.{0}} [IsIntegral D] (s : D ⟶ Sp k)
    [IsProper s] (hd : topologicalKrullDim D = 1) :
    ∃ (C : Scheme.{0}) (_ : IsIntegral C) (f : C ⟶ D), IsFinite f ∧ f (genericPoint C) = genericPoint D ∧
      topologicalKrullDim C = 1 ∧ Smooth (f ≫ s) := by
  let f := D.fromSpecResidueField (genericPoint D)
  let c := f.fromNormalization
  haveI : IsFinite c := NormCurve.isFinite_fromNormalization f s
  have htr : letI := (NormCurve.constHom (f ≫ s) ⊤).toAlgebra
      Algebra.trdeg k Γ(Spec (D.residueField (genericPoint D)), ⊤) ≤ 1 := by
    obtain ⟨x, hx⟩ := ProperCurve.exists_ne_genericPoint hd
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    have e : ⊤ ≤ f ⁻¹ᵁ U := fun z _ => by
      change f z ∈ U
      rw [Scheme.fromSpecResidueField_apply]
      exact VB.genericPoint_mem hxU
    letI := (NormCurve.constHom s U).toAlgebra
    haveI : Algebra.FiniteType k Γ(D, U) := NormCurve.finiteType_constHom s hU
    haveI : Nonempty (⊤ : (Spec (D.residueField (genericPoint D))).Opens) :=
      ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
    letI := (NormCurve.isField_sections (⊤ : (Spec (D.residueField (genericPoint D))).Opens)).toField
    letI := (NormCurve.constHom (f ≫ s) ⊤).toAlgebra
    letI := (f.appLE U ⊤ e).hom.toAlgebra
    haveI : IsScalarTower k Γ(D, U) Γ(Spec (D.residueField (genericPoint D)), ⊤) :=
      .of_algebraMap_eq' (NormCurve.appLE_comp_constHom s f U ⊤ e).symm
    exact (NormCurve.finite_integralClosure k (NormCurve.surjectiveOnStalks_appLE f hU ⊤ e)).2
      ((ringKrullDim_quotient_le _).trans (ProperCurve.ringKrullDim_eq_one hd hU hxU hx).le)
  have hξ : genericPoint D ∈ Set.range c := by
    refine ⟨f.toNormalization (Nonempty.some inferInstance), ?_⟩
    rw [← Scheme.Hom.comp_apply, f.toNormalization_fromNormalization, Scheme.fromSpecResidueField_apply]
  have hs : Function.Surjective c := fun y =>
    (genericPoint_specializes y).mem_closed c.isClosedMap.isClosed_range hξ
  have hη : c (genericPoint _) = genericPoint D := by
    obtain ⟨y, hy⟩ := hξ
    refine ((genericPoint_specializes _).antisymm ?_).eq.symm
    exact ((genericPoint_specializes y).map c.continuous).trans (specializes_of_eq hy)
  exact ⟨f.normalization, inferInstance, c, inferInstance, hη,
    ((Published.dim_le_of_isIntegralHom c).antisymm (PosBaseChange.dim_le_of_isClosedMap c.isClosedMap hs)).trans hd,
    CurveThrough.smooth_of_dedekind_charts k _ _ (NormCurve.isDedekindDomain_sections f s htr)⟩

def CurveTest (K : Type) [Field K] {X : Scheme.{0}} (L : LB X) : Prop :=
  ∀ (C : Scheme.{0}) [Algebra K Γ(C, ⊤)], SmoothOfRelativeDimension 1 (strHom K C) → IsProjOver (strHom K C) →
    GeometricallyConnected (strHom K C) → ∀ g : C ⟶ X, 0 ≤ interNum K (structureModule C) ![L.pull g]

theorem CurveTest.pull {K : Type} [Field K] {X Y : Scheme.{0}} {L : LB X} (h : CurveTest K L) (hL : L.IsLB)
    (π : Y ⟶ X) : CurveTest K (L.pull π) := fun C _ hs hp hc g => by
  refine (h C hs hp hc (g ≫ π)).trans_eq (interNum_congr_cls K _ (isLB_vecOne (LB.isLB_pull hL _))
    (isLB_vecOne (LB.isLB_pull (LB.isLB_pull hL _) _)) fun j => ?_)
  fin_cases j
  exact pull_comp g π (cls L hL)

theorem CurveTest.isNef_of_isAlgClosed {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} [Algebra K Γ(X, ⊤)]
    {L : LB X} (h : CurveTest K L) (hL : L.IsLB) : IsNef K L := by
  refine isNef_iff_isClosedImmersion.2 ⟨hL, fun D i _ _ hd hp => ?_⟩
  letI := algebraΓAlong K i
  have hi := appTop_algebraMap_along K i
  rw [comp_strHom hi] at hp
  obtain ⟨C, _, f, _, hη, hdC, hs⟩ := exists_smooth_finite (strHom K D) hd
  letI := algebraΓAlong K f
  have hf := appTop_algebraMap_along K f
  have hpC : IsProper (f ≫ strHom K D) := inferInstance
  rw [comp_strHom hf] at hs hpC
  have hM := LB.isLB_pull hL i
  have h₀ := h.pull hL i C (smoothOfRelativeDimension_one _ hdC) (ProperCurve.isProjOver_of_isProper _ hdC)
    (geometricallyConnected_of_isAlgClosed _) f
  have e₁ := ProjFin.interNumOn_eq_residueDegree_mul K D C f (ProperCurve.isProjOver_of_isProper _ hd) hd hη _ hM
  rw [interNumOn_eq_interNum_pull hf (isLB_vecOne hM)] at e₁
  rw [interNumOn_eq_interNum_pull hi (isLB_vecOne hL)]
  have hdeg : 0 < f.residueDegree (genericPoint C) := Nat.pos_of_ne_zero
    ((PullbackFinitePoint.residueDegree_ne_zero_iff_finite f _).2 (residueFieldMap_finite_of_locallyQuasiFinite f _))
  have e₂ : (fun j => ((![L.pull i] : Fin 1 → LB D) j).pull f) = ![(L.pull i).pull f] :=
    funext fun j => by fin_cases j; rfl
  have e₃ : (fun j => ((![L] : Fin 1 → LB X) j).pull i) = ![L.pull i] := funext fun j => by fin_cases j; rfl
  rw [e₂] at e₁
  rw [e₃]
  rw [e₁] at h₀
  exact nonneg_of_mul_nonneg_right h₀ (by exact_mod_cast hdeg)

theorem CurveTest.isNef (hN : Published.NefProductNonneg) {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
    {L : LB X} (h : CurveTest (AlgebraicClosure k) L) (hL : L.IsLB) : IsNef k L := by
  refine isNef_iff_isClosedImmersion.2 ⟨hL, fun D i _ _ hd hp => ?_⟩
  letI := algebraΓAlong k i
  have hi := appTop_algebraMap_along k i
  rw [comp_strHom hi] at hp
  have hM := LB.isLB_pull hL i
  obtain ⟨D', _, π, hp', hd', -, -, he⟩ :=
    Published.exists_algClosed_baseChange (ProperCurve.isProjOver_of_isProper (strHom k D) hd)
  rw [interNumOn_eq_interNum_pull hi (isLB_vecOne hL), ← he 1 _ fun j => LB.isLB_pull (isLB_vecOne hL j) i]
  refine hN _ D' 1 hp' (hd'.trans hd) _ fun j => ?_
  fin_cases j
  exact ((h.pull hL i).pull hM π).isNef_of_isAlgClosed (LB.isLB_pull hM π)

end GlobalTheory.NefCurveTest
