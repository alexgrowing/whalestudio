import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.PosBaseChange

section Dim

variable {S T : Type*} [TopologicalSpace S] [TopologicalSpace T] [QuasiSober S] [T0Space S] [QuasiSober T] [T0Space T]
  {f : S → T}

section

attribute [local instance low] specializationOrder

theorem dim_eq_krullDim : topologicalKrullDim S = Order.krullDim S :=
  Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := S))

theorem dim_le_of_isClosedMap (hf : IsClosedMap f) (hs : Function.Surjective f) :
    topologicalKrullDim T ≤ topologicalKrullDim S := by
  have key : ∀ a : S, Order.height (f a) ≤ Order.height a := fun a => by
    refine Order.height_le_iff'.2 fun p hp => ?_
    induction p using RelSeries.inductionOn' generalizing a with
    | singleton x => simp
    | snoc p x hx ih =>
      simp only [RelSeries.last_snoc] at hp
      subst hp
      have hx' : p.last < f a := hx
      obtain ⟨a', ha, e⟩ := hf.specializingMap (show f a ⤳ p.last from hx'.le)
      have hlt : a' < a := lt_of_le_of_ne ha fun h => hx'.ne (by rw [← e, h])
      grw [RelSeries.snoc_length, Nat.cast_add, Nat.cast_one, ih a' e.symm]
      exact Order.height_add_one_le hlt
  rw [dim_eq_krullDim, dim_eq_krullDim, Order.krullDim_eq_iSup_height, Order.krullDim_eq_iSup_height]
  refine iSup_le fun b => ?_
  obtain ⟨a, rfl⟩ := hs b
  exact le_iSup_of_le a (WithBot.coe_le_coe.2 (key a))

theorem dim_le_of_isDiscrete (hf : Continuous f) (hd : ∀ y, _root_.IsDiscrete (f ⁻¹' {y})) :
    topologicalKrullDim S ≤ topologicalKrullDim T := by
  rw [dim_eq_krullDim, dim_eq_krullDim]
  refine Order.krullDim_le_of_strictMono f fun a b h => lt_of_le_of_ne (Specializes.map h.le hf) fun e => ?_
  exact h.ne' ((hd (f b)).eq_of_specializes h.le rfl e)

end

theorem dim_image_le (hf : IsClosedMap f) {C : Set S} (hC : IsClosed C) :
    topologicalKrullDim (f '' C) ≤ topologicalKrullDim C := by
  have := hC.isClosedEmbedding_subtypeVal.quasiSober
  have := (hf C hC).isClosedEmbedding_subtypeVal.quasiSober
  refine dim_le_of_isClosedMap (f := Set.imageFactorization f C) (fun A hA => ?_) Set.imageFactorization_surjective
  have := (hf _ (hC.isClosedMap_subtype_val A hA)).preimage (continuous_subtype_val (p := (· ∈ f '' C)))
  convert this using 1
  ext ⟨y, hy⟩
  simp [Set.imageFactorization, Subtype.ext_iff]

theorem dim_image_eq (hc : Continuous f) (hf : IsClosedMap f) (hd : ∀ y, _root_.IsDiscrete (f ⁻¹' {y})) {C : Set S}
    (hC : IsClosed C) : topologicalKrullDim (f '' C) = topologicalKrullDim C := by
  have := hC.isClosedEmbedding_subtypeVal.quasiSober
  have := (hf C hC).isClosedEmbedding_subtypeVal.quasiSober
  refine (dim_image_le hf hC).antisymm (dim_le_of_isDiscrete (f := Set.imageFactorization f C)
    ((hc.comp continuous_subtype_val).subtype_mk _) fun y => ?_)
  have := (hd y.1).preimage (f := (Subtype.val : C → S)) continuous_subtype_val.continuousOn
    Subtype.val_injective
  convert this using 1
  ext ⟨x, hx⟩
  simp [Set.imageFactorization, Subtype.ext_iff]

end Dim

section Nef

variable {k : Type} [Field k] {X Y : Scheme.{0}} [Algebra k Γ(X, ⊤)] {H H' L M : LB X}

theorem exists_hasNonzeroSec [IsProper (strHom k X)] (hH : IsAmpleLB H) (hM : M.IsLB) {Z : Closeds X}
    (hi : IsIrreducible (Z : Set X)) (hd : topologicalKrullDim (Z : Set X) ≤ 1)
    (hp : IsCompleteCurve k Z → 0 < interNumRed k Z ![M]) :
    ∃ r, 1 ≤ r ∧ HasNonzeroSec ((lbPow M r).pull (redι Z)) := by
  letI := algebraΓAlong k (redι Z)
  have := isIntegral_red hi
  have : IsProper (strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    rw [← comp_strHom (appTop_algebraMap_along k (redι Z))]
    infer_instance
  have hH' := hH.pull_of_isClosedImmersion (redι Z)
  have hproj := hH'.isProjOver (strHom k _)
  have := isNoetherian_of_isProjOver hproj
  have hr : ∀ r, ((lbPow M r).pull (redι Z)).IsLB := fun r => LB.isLB_pull (isLB_lbPow hM r) _
  rcases hd.eq_or_lt with hd' | hd'
  · have hZ : IsCompleteCurve k Z := (isCompleteCurve_iff (algebraMap_eq_strHom k X)).2 ⟨hi, hd'⟩
    have hpos := hp hZ
    set c := chi k (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) with hc
    let r := c.natAbs + 1
    refine ⟨r, by omega, lineBundleHasNonzeroSection_of_globalSectionsDim_pos (k := k) ?_⟩
    have hN := isLB_dual (isLB_lbPow hM r)
    have h₁ := interNumRed_one_eq (k := k) hN Z
    rw [hZ.interNumRed_dual hH (isLB_lbPow hM r), hZ.interNumRed_lbPow hH hM,
      interNum_one k _ (LB.isLB_pull hN _)] at h₁
    obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (structureModule _) (Twist.isLB_lbZPow (LB.isLB_pull hN (redι Z)) (-1))
      (hr r) (by rw [cls_lbZPow (LB.isLB_pull hN _), cls_pull hN, cls_pull (isLB_lbPow hM r),
        cls_dual (isLB_lbPow hM r), map_neg, neg_one_zsmul, neg_neg])
    have := Twist.isQuasicoherent_twist (F := structureModule _) (hr r)
    have h₂ := chi_eq_hdim_zero_sub_hdim_one k fun n hn => hH'.subsingleton_coh_of_dim_lt
      (twist (structureModule _) ((lbPow M r).pull (redι Z))) (n := n)
      (by rw [topologicalKrullDim_red, hd']; exact_mod_cast hn)
    have h₃ := (chi_congr k i).trans h₂
    erw [h₃, ← hc] at h₁
    rw [lineBundleGlobalSectionsDim_def]
    have : (r : ℤ) ≤ r * interNumRed k Z ![M] := le_mul_of_one_le_right (Nat.cast_nonneg r) hpos
    omega
  · have h0 : suppDim (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) ≤ 0 := by
      rw [suppDim_structureModule, topologicalKrullDim_red]
      exact (ENat.WithBot.lt_add_one_iff (m := 0)).1 (by simpa using hd')
    refine ⟨1, le_rfl, lineBundleHasNonzeroSection_of_globalSectionsDim_pos (k := k) ?_⟩
    rw [lineBundleGlobalSectionsDim_def, hdim_twist_of_suppDim_le_zero k h0 (hr 1), ← hdim_twist_of_suppDim_le_zero k h0 (LB.isLB_triv _)]
    exact (lineBundleGlobalSectionsDim_pos_iff (finite_coh_zero_twist_of_isProjOver (algebraMap_eq_strHom k _) hproj (LB.isLB_triv _))).2
      (isGenerated_triv _).hasNonzeroSec

theorem isNef_pull {E : Type} [Field E] [Algebra E Γ(Y, ⊤)] [IsProper (strHom k X)] (h : IsNef k L)
    (hH : IsAmpleLB H) {H' : LB Y} (hH' : IsAmpleLB H') (g : Y ⟶ X) (hg : IsClosedMap g) : IsNef E (L.pull g) := by
  have hL := LB.isLB_pull h.isLB g
  have hA := LB.isLB_pull hH.isLB g
  refine ⟨hL, fun C hC => ?_⟩
  let Z : Closeds X := Closeds.closure (g '' C)
  have hZ : (Z : Set X) = g '' C := (hg _ C.isClosed).closure_eq
  have hi : IsIrreducible (Z : Set X) := hZ ▸ hC.1.image g g.continuous.continuousOn
  have hd : topologicalKrullDim (Z : Set X) ≤ 1 := hZ ▸ (dim_image_le hg C.isClosed).trans hC.2.le
  obtain ⟨φ, hφ⟩ : ∃ φ, φ ≫ redι Z = redι C ≫ g := ⟨IsClosedImmersion.lift (redι Z) (redι C ≫ g) (by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.map_vanishingIdeal]), IsClosedImmersion.lift_fac _ _ _⟩
  have hs : Function.Surjective φ := fun z => by
    obtain ⟨y, hy, e⟩ := hZ.le ((range_redι Z).le ⟨z, rfl⟩)
    obtain ⟨y, rfl⟩ := (range_redι C).ge hy
    exact ⟨y, (redι Z).isClosedEmbedding.injective ((congrArg (fun q => q y) hφ).trans e)⟩
  have key : ∀ m : ℕ, 0 ≤ m * interNumRed E C ![L.pull g] + interNumRed E C ![H.pull g] := fun m => by
    have hm := isLB_lbPow h.isLB m
    have hT := isLB_tens hm hH.isLB
    obtain ⟨r, hr, s, hs0⟩ := exists_hasNonzeroSec (k := k) hH hT hi hd fun hZ' => by
      rw [hZ'.interNumRed_of_cls_eq_add hH hT hm hH.isLB rfl, hZ'.interNumRed_lbPow hH h.isLB]
      exact add_pos_of_nonneg_of_pos (mul_nonneg (Nat.cast_nonneg m) (h.2 Z hZ')) (hH.interNumRed_pos hZ')
    let := algebraΓAlong E (redι C)
    have := hC.isProper_strHom
    have := isIntegral_red hC.1
    have := isIntegral_red hi
    have hr' := isLB_lbPow hT r
    obtain ⟨x, hx⟩ := hs (genericPoint _)
    have hx' : x ∈ nonzeroLocus (secPull s φ) := (nonzeroLocus_secPull s φ).ge (by
      change φ x ∈ nonzeroLocus s
      rw [hx]; exact (sec_ne_zero_iff s).1 hs0)
    have h0 := (interNum_one_nonneg_of_sec (k := E) (hH'.pull_of_isClosedImmersion (redι C))
      ((topologicalKrullDim_red C).trans hC.2) (LB.isLB_pull (LB.isLB_pull hr' _) φ) (secPull s φ)
      ((sec_ne_zero_iff _).1 (sec_ne_zero_of_mem hx'))).1
    have hT' := isLB_tens (isLB_lbPow hL m) hA
    have h1 : interNumRed E C ![lbPow (tens (lbPow (L.pull g) m) (H.pull g)) r] =
        interNum E (structureModule _) ![((lbPow (tens (lbPow L m) H) r).pull (redι Z)).pull φ] := by
      rw [interNumRed_one_eq (isLB_lbPow hT' r)]
      refine interNum_congr_cls E _ (isLB_vecOne (LB.isLB_pull (isLB_lbPow hT' r) _))
        (isLB_vecOne (LB.isLB_pull (LB.isLB_pull hr' _) φ)) fun i => ?_
      fin_cases i
      change pull (redι C) (cls _ (isLB_lbPow hT' r)) = pull φ (pull (redι Z) (cls _ hr'))
      rw [← pull_comp, hφ, pull_comp, cls_lbPow_tens_lbPow hL hA, cls_lbPow_tens_lbPow h.isLB hH.isLB,
        cls_pull h.isLB, cls_pull hH.isLB, map_nsmul (pull g), map_add (pull g), map_nsmul (pull g)]
    rw [← h1, hC.interNumRed_lbPow hH' hT', hC.interNumRed_of_cls_eq_add hH' hT' (isLB_lbPow hL m) hA rfl,
      hC.interNumRed_lbPow hH' hL] at h0
    exact nonneg_of_mul_nonneg_right h0 (Nat.cast_pos.2 hr)
  by_contra! hneg
  have := key ((interNumRed E C ![H.pull g]).natAbs + 1)
  have h2 := le_abs_self (interNumRed E C ![H.pull g])
  have h3 := abs_nonneg (interNumRed E C ![H.pull g])
  push_cast at this
  nlinarith

end Nef

section Field

variable {k E : Type} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E] {X X' : Scheme.{0}} {f : X ⟶ Sp k}
  {f' : X' ⟶ Sp E} {π : X' ⟶ X} (H : IsPullback π f' f (spMap (algebraMap k E)))

include H

theorem isFinite_proj : IsFinite π :=
  MorphismProperty.of_isPullback H.flip ((IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance))

omit [FiniteDimensional k E] in

theorem surjective_proj : Function.Surjective π :=
  have : Surjective (spMap (algebraMap k E)) := ⟨Function.surjective_to_subsingleton _⟩
  have : Surjective π := MorphismProperty.of_isPullback H.flip this
  π.surjective

theorem dim_eq : topologicalKrullDim X' = topologicalKrullDim X :=
  have := isFinite_proj H
  le_antisymm (dim_le_of_isDiscrete π.continuous π.isDiscrete_preimage_singleton)
    (dim_le_of_isClosedMap π.isClosedMap (surjective_proj H))

omit [FiniteDimensional k E] in

theorem isProjOver_of_isPullback (hf : IsProjOver f) : IsProjOver f' := by
  obtain ⟨N, i, hi, e⟩ := ProjSpace.isProjOver_pullback_snd (algebraMap k E) hf
  exact ⟨N, H.isoPullback.hom ≫ i, inferInstance, by rw [Category.assoc, e, H.isoPullback_hom_snd]⟩

theorem isNef_baseChange (hf : IsProjOver f) {L : LB X} :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom f'
    IsNef k L → IsNef E (L.pull π) := by
  let := algebraΓOfHom f
  let := algebraΓOfHom f'
  intro h
  have := isFinite_proj H
  obtain ⟨hp, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB f).1 hf
  have : IsProper (strHom k X) := by rwa [strHom_eq (f := f) fun _ => rfl]
  exact isNef_pull h hA (hA.pull_of_isAffineHom π) π π.isClosedMap

theorem isBig_baseChange (hf : IsProjOver f) {L : LB X} :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom f'
    IsBig k L → IsBig E (L.pull π) := by
  let := algebraΓOfHom f
  let := algebraΓOfHom f'
  intro h
  have := ((isProjOver_iff_isProper_and_exists_isAmpleLB f).1 hf).1
  obtain ⟨D, hD, c, hc, hm⟩ := h.3
  have hL := LB.isLB_pull h.1 π
  refine (isBig_iff (f := f') (fun _ => rfl) (isProjOver_of_isPullback H hf) ((dim_eq H).trans hD)).2
    ⟨hL, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ ?_)⟩
  rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL m) (LB.isLB_pull (isLB_lbPow h.1 m) π)
    (by rw [cls_lbPow hL, cls_pull h.1, cls_pull (isLB_lbPow h.1 m), cls_lbPow h.1, map_nsmul])]
  exact (FieldChangeInter.hdim_pull H (isLB_lbPow h.1 m) 0).symm

end Field

end GlobalTheory.PosBaseChange

namespace GlobalTheory.Adelic

open PosBaseChange MvPolynomial

namespace LinSys

variable {k : Type} [Field k] {S : LinSys k} (E : Type) [Field E] [Algebra k E]

theorem baseHom_comp_bcFst {K : Type} [Field K] (x : Sp K ⟶ (S.baseChange E).Y) :
    S.baseHom (x ≫ S.bcFst E) = ((S.baseChange E).baseHom x).comp (algebraMap k E) := by
  refine baseHom_ptOver (S := S) ⟨x ≫ S.bcFst E, ?_⟩
  rw [Category.assoc, (S.isPullback_baseChange E).w, ← Category.assoc, (S.baseChange E).comp_str, ← Spec.map_comp]
  rfl

theorem mem_nonzeroLocus_form_map {d : ℕ} {g : MvPolynomial (Fin S.N) k} (hg : g.IsHomogeneous d)
    (y : (S.baseChange E).Y) : y ∈ nonzeroLocus ((S.baseChange E).form (hg.map (algebraMap k E))) ↔
      S.bcFst E y ∈ nonzeroLocus (S.form hg) := by
  obtain ⟨c, hc, h⟩ := S.exists_coords_baseChange E (resPt y)
  have e := Twist.eval₂Hom_unit_mul (S.baseHom (resPt y ≫ S.bcFst E)) (Units.mk0 c hc)
    (S.coords (resPt y ≫ S.bcFst E)) (mem_polyGrading_natCast.2 hg)
  conv_lhs => rw [← ptOf_resPt y]
  conv_rhs => rw [← ptOf_resPt y, ← ptOf_comp]
  rw [← powVal_ne_zero_iff, ← powVal_ne_zero_iff, S.powVal_form]
  erw [(S.baseChange E).powVal_form (resPt y) (hg.map (algebraMap k E)), h, eval₂_map]
  rw [← baseHom_comp_bcFst]
  exact not_congr ((Eq.congr_left e).trans (Units.mul_right_eq_zero (Units.mk0 c hc ^ (d : ℤ))))

theorem NoContract.baseChange [FiniteDimensional k E] {bd : Set S.Y} (h : S.NoContract bd) :
    (S.baseChange E).NoContract (S.bcFst E ⁻¹' bd) := fun C hC hi hd hb hc => by
  have := isFinite_proj (S.isPullback_baseChange E)
  have hm := (S.bcFst E).isClosedMap
  refine h (S.bcFst E '' C) (hm C hC) (hi.image _ (S.bcFst E).continuous.continuousOn)
    ((dim_image_eq (S.bcFst E).continuous hm (S.bcFst E).isDiscrete_preimage_singleton hC).trans hd)
    (Set.disjoint_image_left.2 hb) ?_
  rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ d g hg
  rw [← mem_nonzeroLocus_form_map, ← mem_nonzeroLocus_form_map]
  exact hc y hy y' hy' d _ _

theorem eq_top_of_factor {Y : Scheme.{0}} {y : Y} (K : Subfield (Y.residueField y)) (w : Sp K ⟶ Y)
    (h : spMap K.subtype ≫ w = resPt y) : K = ⊤ := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Y).symm.surjective w
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h
  obtain rfl : z = y := by
    have := congrArg ptOf h
    rw [ptOf_resPt, ← Category.assoc, ptOf_comp] at this
    exact (Scheme.fromSpecResidueField_apply _ _).symm.trans this
  have h' : Spec.map (φ ≫ CommRingCat.ofHom K.subtype) = Spec.map (𝟙 _) := by
    rw [← cancel_mono (Y.fromSpecResidueField z), Spec.map_comp, Spec.map_id, Category.assoc, Category.id_comp]
    exact h
  refine eq_top_iff.2 fun r _ => ?_
  have := ConcreteCategory.congr_hom (Spec.map_injective h') r
  exact (show ((φ r : K) : Y.residueField z) = r from this) ▸ (φ r).2

theorem Birational.baseChange [IrreducibleSpace (S.baseChange E).Y] (h : S.Birational) :
    (S.baseChange E).Birational := by
  obtain ⟨η, hη, hr⟩ := h
  refine ⟨genericPoint _, genericPoint_spec _, ?_⟩
  set η' := genericPoint (S.baseChange E).Y
  obtain rfl : S.bcFst E η' = η := by
    have := (genericPoint_spec (S.baseChange E).Y).image (S.bcFst E).continuous
    rw [Set.image_univ, (surjective_proj (S.isPullback_baseChange E)).range_eq, closure_univ] at this
    exact this.eq hη
  let τ := ((S.bcFst E).residueFieldMap η').hom
  have hτ : spMap τ ≫ resPt (S.bcFst E η') = resPt η' ≫ S.bcFst E :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ _
  set K := (S.baseChange E).ratioField (resPt η')
  have hE : ∀ a, (S.baseChange E).baseHom (resPt η') a ∈ K := fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  have hb : τ.comp (S.baseHom (resPt (S.bcFst E η'))) =
      ((S.baseChange E).baseHom (resPt η')).comp (algebraMap k E) := by
    rw [← baseHom_comp_bcFst, ← hτ]
    refine (baseHom_ptOver (S := S) ⟨spMap τ ≫ resPt (S.bcFst E η'), ?_⟩).symm
    rw [Category.assoc, S.comp_str, ← Spec.map_comp]
    rfl
  have hK : ∀ a, τ a ∈ K := fun a => by
    obtain ⟨c, hc, e⟩ := S.exists_coords_baseChange E (resPt η')
    refine (show S.ratioField (resPt (S.bcFst E η')) ≤ K.comap τ from Subfield.closure_le.2 ?_) (hr.ge trivial)
    rintro _ (⟨a, rfl⟩ | ⟨i, j, rfl⟩)
    · exact Subfield.mem_comap.2 (Set.mem_of_eq_of_mem (RingHom.congr_fun hb a) (hE _))
    · refine Subfield.subset_closure (Or.inr ⟨i, j, ?_⟩)
      rw [e, ← hτ, coords_spMap_comp, map_div₀]
      exact (mul_div_mul_left _ _ hc).symm
  refine eq_top_of_factor K ((S.isPullback_baseChange E).lift
    (spMap (τ.codRestrict K hK) ≫ resPt (S.bcFst E η'))
    (spMap (((S.baseChange E).baseHom (resPt η')).codRestrict K hE)) ?_) ((S.isPullback_baseChange E).hom_ext ?_ ?_)
  · rw [Category.assoc, S.comp_str, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => Subtype.ext (RingHom.congr_fun hb a)))
  · rw [Category.assoc, IsPullback.lift_fst, ← Category.assoc, ← Spec.map_comp, ← hτ]
    rfl
  · rw [Category.assoc, IsPullback.lift_snd, (S.baseChange E).comp_str, ← Spec.map_comp]
    rfl

end LinSys

theorem Tuple.IsBirationalOffBoundary.baseChange {F : Type} [Field F] [NumberField F] {T : Tuple F}
    (h : T.IsBirationalOffBoundary) (hv : T.IsVariety) (E : Type) [Field E] [NumberField E] [Algebra F E] :
    (T.baseChange E).IsBirationalOffBoundary := by
  have := hv.isIntegral
  have := (hv.baseChange E).isIntegral
  have hl : nonzeroLocus (T.baseChange E).th = T.bcFst E ⁻¹ᵁ nonzeroLocus T.th :=
    nonzeroLocus_chartSec _ T.th fun z _ _ => exists_chart (isLB_lbPow (LB.isLB_pull T.isLB _) _) z
  refine ⟨h.birational.baseChange E, h.noContract.baseChange E, h.one_le, ?_,
    fun y hy hy' => h.th_vanish _ hy (hl.le hy')⟩
  obtain ⟨y, hy⟩ := surjective_proj (T.isPullback_baseChange E) (genericPoint T.Y)
  exact sec_ne_zero_of_mem (x := y) (hl.ge (show T.bcFst E y ∈ _ from hy ▸ (sec_ne_zero_iff _).1 h.th_ne))

end GlobalTheory.Adelic

namespace GlobalTheory.HilbertSamuel.Geo

variable {F : Type} [Field F] [NumberField F] (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem isNef_baseChange (h : IsNef F G.LA) : IsNef E (G.baseChange E).LA :=
  PosBaseChange.isNef_baseChange (G.isPullback_fst E) G.geom.alg.variety.proj h

theorem isBig_baseChange (h : IsBig F G.LA) : IsBig E (G.baseChange E).LA :=
  PosBaseChange.isBig_baseChange (G.isPullback_fst E) G.geom.alg.variety.proj h

variable {G} in

theorem Positivity.baseChange (h : G.Positivity) : (G.baseChange E).Positivity :=
  ⟨h.bir.baseChange G.geom.alg.variety E, G.isNef_baseChange E h.nef, G.isBig_baseChange E h.big⟩

end GlobalTheory.HilbertSamuel.Geo
