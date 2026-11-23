import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.LocusEqTopOfDualPow
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsIsoGrCechMapPolyToGamma

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Points GlobalTheory.Twist GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isStandardSmooth_mvPolynomial (R σ : Type) [CommRing R] [Finite σ] :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card σ) R (MvPolynomial σ R) := by
  let P₀ : Algebra.Presentation R (MvPolynomial σ R) σ Empty :=
    { __ := Algebra.Generators.mvPolynomial R σ
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation R (MvPolynomial σ R) σ Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation R (MvPolynomial σ R) σ Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  exact P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])

theorem smoothOfRelativeDimension_pspace (R : Type) [CommRing R] (M : ℕ) :
    SmoothOfRelativeDimension M (PSpace.str R M) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} M)
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension M))
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} M) (chartCover R M)
    fun (i : Fin (M + 1)) => ?_
  change SmoothOfRelativeDimension M (chartι R M i ≫ _)
  rw [chartι_str]
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension M)).2 ?_
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  have h := isStandardSmooth_mvPolynomial R {j : Fin (M + 1) // j ≠ i}
  rw [show Nat.card {j : Fin (M + 1) // j ≠ i} = M by simp] at h
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap M).2 h

variable (k : Type) [Field k] (M : ℕ)

theorem geometricallyConnected_pspace : GeometricallyConnected (PSpace.str k M) :=
  ⟨geometrically_iff_of_commRing.2 fun K _ _ _ _ _ h =>
    have e := (isPullback_baseChange M (algebraMap k K)).isoIsPullback _ _ h
    e.hom.homeomorph.surjective.connectedSpace e.hom.continuous⟩

abbrev projSys : LinSys k where
  Y := PSpace k M
  str := PSpace.str k M
  D := M
  L := O1 k M
  isLB := O1_isLB k M
  N := M + 1
  b := coord k M

namespace projSys

theorem algebraΓ_eq : (projSys k M).algebraΓ = algebraSections k M ⊤ :=
  Algebra.algebra_ext _ _ fun r => (LB.resG_self (X := PSpace k M) le_top _).symm

theorem isVariety (hM : 1 ≤ M) : (projSys k M).IsVariety :=
  ⟨smoothOfRelativeDimension_pspace k M, ⟨M, 𝟙 _, inferInstance, Category.id_comp _⟩,
    geometricallyConnected_pspace k M, hM⟩

theorem basePointFree : (projSys k M).BasePointFree := iSup_nonzeroLocus_coord k M

theorem form_eq {d : ℕ} {g : MvPolynomial (Fin (M + 1)) k} (hg : g.IsHomogeneous d) :
    (projSys k M).form hg = ProjSpace.formSec d g hg := by
  rw [ProjCoh.formSec_eq]
  exact congrArg (fun a : Algebra k Γ(PSpace k M, ⊤) =>
    letI := a; Twist.formSec (coord k M) (mem_polyGrading_natCast.2 hg)) (algebraΓ_eq k M)

theorem imageIdeal_eq_bot : (projSys k M).imageIdeal = ⊥ := by
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro g ⟨d, hg, h⟩
  refine (formSec_inj hg (isHomogeneous_zero _ k d)).1 ((form_eq k M hg).symm.trans (h.trans ?_))
  exact LB.f_injective (funext fun j => (formOn_zero (hi := (On_U k M d j).le)).symm)

theorem del_eq_one : (projSys k M).del = 1 := by
  have h := interNum_const_of_polynomial k (structureModule (PSpace k M)) (O1_isLB k M) (d := M)
    (Polynomial.preHilbertPoly ℚ M 0) (Polynomial.natDegree_preHilbertPoly ℚ M 0).le
    (ProjCoh.chi_sheafO_eq_eval k M)
  rw [Polynomial.coeff_preHilbertPoly_self, mul_inv_cancel₀ (Nat.cast_ne_zero.2 M.factorial_ne_zero)] at h
  rw [LinSys.del, algebraΓ_eq]
  exact_mod_cast h

theorem eq_of_sameImage {y y' : PSpace k M} (h : (projSys k M).SameImage y y') : y = y' := by
  refine ProjectiveSpectrum.ext (HomogeneousIdeal.ext' fun d g hg => ?_)
  replace hg : g.IsHomogeneous d := hg
  have := h d g hg
  rw [form_eq, nonzeroLocus_formSec] at this
  exact not_iff_not.1 this

theorem noContract (bd : Set (PSpace k M)) : (projSys k M).NoContract bd := fun C _ _ hC _ h => by
  have : Subsingleton C := ⟨fun a b => Subtype.ext (eq_of_sameImage k M (h _ a.2 _ b.2))⟩
  have := topologicalKrullDim_zero_of_discreteTopology C
  rw [hC] at this
  exact absurd this (by decide)

abbrev gen : PSpace k M := AmpleModel.genericPt k M

theorem gen_mem (i : Fin (M + 1)) : gen k M ∈ chart k M i := fun h => X_ne_zero (R := k) i h

theorem indep : (projSys k M).Indep := fun u hu => by
  have hg : (∑ j, C (u j) * X j : MvPolynomial (Fin (M + 1)) k).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X k j).C_mul _
  have h0 : (∑ j, C (u j) * X j : MvPolynomial (Fin (M + 1)) k) = 0 := by
    by_contra hne
    have h1 : ptOf (resPt (gen k M)) ∈ nonzeroLocus ((projSys k M).form hg) := by
      rw [ptOf_resPt, form_eq, nonzeroLocus_formSec]
      exact hne
    refine ((projSys k M).powVal_ne_zero_iff _ _).2 h1 ?_
    have h2 := (projSys k M).val_comb (resPt (gen k M)) u
    rw [hu, LinSys.val_zero] at h2
    rw [LinSys.powVal_form, h2, eval₂_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [eval₂_mul, eval₂_C, eval₂_X]
  funext j
  have := congrArg (eval (Pi.single j 1 : Fin (M + 1) → k)) h0
  simpa [Pi.single_apply] using this

theorem valR_resPt {Y : Scheme.{0}} (y : Y) (U : Y.Opens) (hy : y ∈ U) (f : Γ(Y, U)) :
    valR (resPt y) U f = Y.evaluation U y hy f := by
  have ht : ⊤ ≤ Y.fromSpecStalk y ⁻¹ᵁ U := (le_preimage_iff (C := Y.presheaf.stalk y) _ U).2 (by
    rw [show Y.fromSpecStalk y (IsLocalRing.closedPoint (Y.presheaf.stalk y)) = y from
      Scheme.fromSpecStalk_closedPoint]; exact hy)
  have e : valMap (C := Y.presheaf.stalk y) (Y.fromSpecStalk y) U ht = Y.presheaf.germ U y hy := by
    change (Y.fromSpecStalk y).appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).hom = _
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hy]
    simp only [Category.assoc]
    have e : (Spec (Y.presheaf.stalk y)).presheaf.map (homOfLE (le_top : Y.fromSpecStalk y ⁻¹ᵁ U ≤ ⊤)).op ≫
        (Spec (Y.presheaf.stalk y)).presheaf.map (homOfLE ht).op = 𝟙 _ := by
      rw [← Functor.map_comp]; exact CategoryTheory.Functor.map_id _ _
    rw [reassoc_of% e, Iso.inv_hom_id, Category.comp_id]
  exact (valR_spMap_comp (Y.residue y).hom (Y.fromSpecStalk y) U ht f).trans (congrArg (Y.residue y).hom
    ((valR_eq (C := Y.presheaf.stalk y) _ _ ht f).trans (congrArg (fun q => q.hom f) e)))

theorem birational : (projSys k M).Birational := by
  refine ⟨gen k M, ?_, eq_top_iff.2 fun r _ => ?_⟩
  · exact Set.eq_univ_of_forall fun x => (ProjectiveSpectrum.le_iff_mem_closure _ _ x).1
      (show ⊥ ≤ x.asHomogeneousIdeal from bot_le)
  have hx : ptOf (resPt (gen k M)) ∈ chart k M 0 := by rw [ptOf_resPt]; exact gen_mem k M 0
  have hx' := (le_iff_ptOf_mem _ _).2 hx
  obtain ⟨c, hc, h, -⟩ := (projSys k M).exists_frame_change (resPt (gen k M)) (0 : Fin (M + 1)) hx
  have key : ∀ f : Γ(PSpace k M, chart k M 0),
      valR (resPt (gen k M)) _ f ∈ (projSys k M).ratioField (resPt (gen k M)) := fun f => by
    obtain ⟨p, rfl⟩ := aeval_ratio_surjective k M 0 f
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine Subfield.subset_closure (Or.inl ⟨a, ?_⟩)
      rw [algHom_C, ← resG_algebraMap le_top, ← algebraΓ_eq]
      exact ((valR_res _ le_top hx' _).trans ((projSys k M).valR_algebraMap _ a)).symm
    | add p q hp hq => rw [map_add, valR_add _ _ hx']; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, valR_mul _ _ hx', aeval_X]
      refine mul_mem hp (Subfield.subset_closure (Or.inr ⟨j, (0 : Fin (M + 1)), ?_⟩))
      have h0 : 1 = c * (projSys k M).coords (resPt (gen k M)) (0 : Fin (M + 1)) :=
        (valR_one _ _ hx').symm.trans ((congrArg _ (ratioOn_self (hi := le_rfl)).symm).trans (h (coord k M 0)))
      rw [← mul_div_mul_left _ _ hc, ← h0, div_one]
      exact h (coord k M j)
  obtain ⟨t, rfl⟩ := (PSpace k M).residue_surjective _ r
  let := (PSpace k M).presheaf.algebra_section_stalk (U := chart k M 0) ⟨gen k M, gen_mem k M 0⟩
  have := (isAffineOpen_chart k M 0).isLocalization_stalk ⟨gen k M, gen_mem k M 0⟩
  obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj
    ((isAffineOpen_chart k M 0).primeIdealOf ⟨gen k M, gen_mem k M 0⟩).asIdeal.primeCompl t
  have hs := (IsLocalization.map_units ((PSpace k M).presheaf.stalk (gen k M)) s).map
    ((PSpace k M).residue (gen k M)).hom
  have e' := congrArg ((PSpace k M).residue (gen k M)).hom e
  rw [map_mul, ← eq_div_iff hs.ne_zero] at e'
  have ha := key a
  have hb := key s
  rw [valR_resPt _ _ (gen_mem k M 0)] at ha hb
  exact e' ▸ div_mem ha hb

end projSys
end GlobalTheory.Adelic
