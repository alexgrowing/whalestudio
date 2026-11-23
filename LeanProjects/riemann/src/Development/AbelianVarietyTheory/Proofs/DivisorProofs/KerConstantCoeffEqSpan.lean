import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.ChowHt GlobalTheory.ProjSpace

theorem isIso_of_ringEquiv_rat {Z : Scheme.{0}} [IsAffine Z] (f : Z ⟶ Sp ℚ) (e : Γ(Z, ⊤) ≃+* ℚ) : IsIso f := by
  have h : f = Z.isoSpec.hom ≫ Spec.map e.symm.toCommRingCatIso.hom := by
    refine ext_of_isAffine ((cancel_epi (Scheme.ΓSpecIso (.of ℚ)).inv).1 (CommRingCat.hom_ext ?_))
    exact Subsingleton.elim (α := ℚ →+* _) _ _
  rw [h]
  infer_instance

theorem isIso_subschemeι_comp_rat {Y : Scheme.{0}} (f : Y ⟶ Sp ℚ) (I : Y.IdealSheafData) (W : Y.affineOpens)
    (hW : ∀ y ∈ I.support, y ∈ W.1) (g : Γ(Y, W.1) →+* ℚ) (hg : RingHom.ker g = I.ideal W) :
    IsIso (I.subschemeι ≫ f) := by
  have ht : I.subschemeι ⁻¹ᵁ W.1 = ⊤ := top_le_iff.1 fun z _ => hW _ (I.range_subschemeι.le ⟨z, rfl⟩)
  have ha : IsAffineOpen (⊤ : I.subscheme.Opens) := ht ▸ W.2.preimage I.subschemeι
  have : IsAffine I.subscheme := by
    have : IsAffine (⊤ : I.subscheme.Opens) := ha
    exact .of_isIso I.subscheme.topIso.inv
  have hs : Function.Surjective g := fun q => ⟨((Scheme.ΓSpecIso (.of ℚ)).inv ≫ f.appLE ⊤ W.1 le_top).hom q,
    congrArg (fun t : ℚ →+* ℚ => t q) (Subsingleton.elim (g.comp ((Scheme.ΓSpecIso (.of ℚ)).inv ≫ f.appLE ⊤ W.1 le_top).hom) (RingHom.id ℚ))⟩
  have e : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ W.1) ≃+* ℚ :=
    (RingHom.quotientKerEquivOfSurjective (I.subschemeι_app_surjective W)).symm.trans
      ((Ideal.quotEquivOfEq ((I.ker_subschemeι_app W).trans hg.symm)).trans
        (RingHom.quotientKerEquivOfSurjective hs))
  exact isIso_of_ringEquiv_rat _ (ht ▸ e)

theorem LinSys.ncard_subPts_of_isIso {k : Type} [Field k] (S : LinSys k) (I : S.Y.IdealSheafData)
    [IsIso (I.subschemeι ≫ S.str)] (Ω : Type) [Field Ω] [Algebra k Ω] : (S.subPts I Ω).ncard = 1 := by
  refine Set.ncard_eq_one.2 ⟨⟨(spMap (algebraMap k Ω) ≫ inv (I.subschemeι ≫ S.str)) ≫ I.subschemeι, by
    simp⟩, Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, rfl⟩, ?_⟩⟩
  rintro x ⟨z, hz⟩
  refine Subtype.ext (hz.symm.trans (congrArg (· ≫ _) ?_))
  rw [IsIso.eq_comp_inv, ← Category.assoc, hz, x.2]

theorem ker_constantCoeff_eq_span (σ R : Type) [CommRing R] :
    RingHom.ker (constantCoeff : MvPolynomial σ R →+* R) = Ideal.span (Set.range X) := by
  ext p
  rw [RingHom.mem_ker, ← Set.image_univ, mem_ideal_span_X_image, constantCoeff_eq]
  refine ⟨fun h m hm => ?_, fun h => ?_⟩
  · by_contra! H
    obtain rfl : m = 0 := Finsupp.ext fun i => H i (Set.mem_univ i)
    exact mem_support_iff.1 hm h
  · by_contra H
    obtain ⟨i, -, hi⟩ := h 0 (mem_support_iff.2 H)
    exact hi rfl

namespace projTuple

abbrev lineBC : LinSys ℚ := (projSys ℚ 1).baseChange ℚ

theorem comb_one_zero : lineBC.comb ![1, 0] = secPull (coord ℚ 1 0) ((projSys ℚ 1).bcFst ℚ) := by
  refine (Fin.sum_univ_two _).trans ?_
  change algebraMap ℚ Γ(lineBC.Y, ⊤) 1 • _ + algebraMap ℚ Γ(lineBC.Y, ⊤) 0 • _ = _
  rw [map_one, map_zero, one_smul, zero_smul, add_zero]
  rfl

theorem mem_chart_of_mem_support (y : lineBC.Y) (hy : y ∈ (lineBC.cut fun _ : Fin 1 => ![1, 0]).support) :
    (projSys ℚ 1).bcFst ℚ y ∈ chart ℚ 1 1 := by
  have h := (mem_support_cutIdeal _ _ y).1 hy 0
  rw [comb_one_zero] at h
  replace h : (projSys ℚ 1).bcFst ℚ y ∉ chart ℚ 1 0 := fun hc =>
    h ((nonzeroLocus_secPull (coord ℚ 1 0) _).ge ((nonzeroLocus_coord ℚ 1 0).ge hc))
  obtain ⟨i, hi⟩ := exists_mem_chart ℚ 1 ((projSys ℚ 1).bcFst ℚ y)
  fin_cases i
  · exact (h hi).elim
  · exact hi

instance isIso_bcFst : IsIso ((projSys ℚ 1).bcFst ℚ) := by
  have : IsIso (spMap (algebraMap ℚ ℚ)) := by
    rw [show spMap (algebraMap ℚ ℚ) = 𝟙 _ from Spec.map_id _]
    infer_instance
  exact inferInstanceAs (IsIso (pullback.fst _ _))

theorem isIso_cut_line : IsIso ((lineBC.cut fun _ : Fin 1 => ![1, 0]).subschemeι ≫ lineBC.str) := by
  let p := (projSys ℚ 1).bcFst ℚ
  let W : lineBC.Y.affineOpens := ⟨p ⁻¹ᵁ chart ℚ 1 1, (isAffineOpen_chart ℚ 1 1).preimage p⟩
  let e : MvPolynomial {j : Fin 2 // j ≠ 1} ℚ ≃+* Γ(lineBC.Y, W.1) :=
    (chartAlgEquiv ℚ 1 1).toRingEquiv.trans (asIso (p.app (chart ℚ 1 1))).commRingCatIsoToRingEquiv
  have hW : W.1 ≤ lineBC.L.U fun _ => (1 : Fin 2) := fun _ hy => Set.mem_iInter.2 fun _ => hy
  refine isIso_subschemeι_comp_rat _ _ W mem_chart_of_mem_support (constantCoeff.comp e.symm.toRingHom) ?_
  have h₁ : resG lineBC.Y hW ((lineBC.comb ![1, 0]).f fun _ => (1 : Fin 2)) = e (X ⟨0, by decide⟩) := by
    rw [comb_one_zero]
    refine Eq.trans ?_ (congrArg (p.app (chart ℚ 1 1)).hom (chartAlgEquiv_X ℚ 1 1 ⟨0, by decide⟩).symm)
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun t => t.hom (ratio ℚ 1 1 0)) (p.appLE_map _ (homOfLE hW).op)
  refine Eq.trans ?_ (ideal_cutIdeal lineBC.isLB _ W _ hW).symm
  rw [← RingHom.comap_ker, ker_constantCoeff_eq_span]
  refine (Ideal.comap_symm e).trans ((Ideal.map_span _ _).trans (congrArg Ideal.span ?_))
  rw [← Set.range_comp]
  ext a
  refine ⟨?_, ?_⟩
  · rintro ⟨j, rfl⟩
    obtain rfl : j = ⟨0, by decide⟩ := by revert j; decide
    exact ⟨0, h₁⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, h₁.symm⟩

theorem isGoodSection_line : (projTuple 1).IsGoodSection ℚ (fun _ => ![1, 0]) ∧
    ((projTuple 1).geomPts ℚ ((projTuple 1).linSection ℚ fun _ => ![1, 0])).ncard = 1 := by
  have := isIso_cut_line
  refine ⟨⟨⟨?_, ?_⟩, fun y hy => ?_⟩, lineBC.ncard_subPts_of_isIso _ _⟩
  · exact inferInstanceAs (IsFinite ((lineBC.cut fun _ : Fin 1 => ![1, 0]).subschemeι ≫ lineBC.str))
  · exact inferInstanceAs (Etale ((lineBC.cut fun _ : Fin 1 => ![1, 0]).subschemeι ≫ lineBC.str))
  · exact (Opens.compl_compl (chart ℚ 1 1)).ge (mem_chart_of_mem_support y hy)

end projTuple

end GlobalTheory.Adelic
