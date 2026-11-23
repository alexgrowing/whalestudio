import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionCycleFormulaProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFibreProjectiveCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreeEqOrderSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.VdmRec

namespace GlobalTheory.DegRec

variable {k : Type} [CommRing k] {X Y : Scheme.{0}}

theorem topSelf_cxFibre (p : X ⟶ Sp k) [IsProper (p ≫ spMap (Int.castRingHom k))] {L : LB X} (hL : L.IsLB) (n : ℕ) :
    topSelfIntersection ℂ (L.pull (cxFibre.fst p)) n = topSelfIntersection ℚ (L.pull (ratFibre.fst p)) n := by
  have e : spMap (algebraMap ℚ ℂ) ≫ spMap (Int.castRingHom ℚ) = spMap (Int.castRingHom ℂ) := by
    rw [← Spec.map_comp]
    congr 1
  have H₀ : IsPullback (cxFibre.fst p) (cxFibre.snd p) (p ≫ spMap (Int.castRingHom k))
      (spMap (algebraMap ℚ ℂ) ≫ spMap (Int.castRingHom ℚ)) := by
    rw [e]
    exact IsPullback.of_hasPullback _ _
  let π := (ratFibre.isPullback p).lift (cxFibre.fst p) (cxFibre.snd p ≫ spMap (algebraMap ℚ ℂ))
    (by rw [Category.assoc]; exact H₀.w)
  have hπ : π ≫ ratFibre.fst p = cxFibre.fst p := IsPullback.lift_fst _ _ _ _
  have H : IsPullback π (cxFibre.snd p) (ratFibre.snd p) (spMap (algebraMap ℚ ℂ)) :=
    IsPullback.of_right (hπ ▸ H₀) (IsPullback.lift_snd _ _ _ _) (ratFibre.isPullback p)
  have : IsProper (ratFibre.snd p) := MorphismProperty.of_isPullback (P := @IsProper) (ratFibre.isPullback p) ‹_›
  have hR := pull_isLB hL (ratFibre.fst p)
  refine Eq.trans ?_ (FieldChangeInter.interNum_pull H (L := fun _ : Fin n => L.pull (ratFibre.fst p)) fun _ => hR)
  refine interNum_congr_cls ℂ _ (fun _ => pull_isLB hL _) (fun _ => pull_isLB hR _) fun _ => ?_
  rw [cls_pull hR, cls_pull hL, cls_pull hL, ← pull_comp, hπ]

theorem charZero_iff (g : Y ⟶ X) (y : Y) : CharZero (X.residueField (g y)) ↔ CharZero (Y.residueField y) :=
  (g.residueFieldMap y).hom.charZero_iff (g.residueFieldMap y).hom.injective

theorem charZero_ratFibre (p : X ⟶ Sp k) (y : ratFibre p) : CharZero ((ratFibre p).residueField y) :=
  ((((ratFibre p).Γevaluation y).hom.comp (algebraMap ℚ Γ(ratFibre p, ⊤))).charZero_iff (RingHom.injective _)).1
    inferInstance

theorem isIntegral_ratFibre (p : X ⟶ Sp k) [IsIntegral X] [Nonempty (ratFibre p)] : IsIntegral (ratFibre p) := by
  have h₁ : IsPreimmersion (spMap (Int.castRingHom ℚ)) :=
    IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  have : IsPreimmersion (ratFibre.fst p) := MorphismProperty.of_isPullback (ratFibre.isPullback p).flip h₁
  have := RatDegZeros.flat_fst p
  exact ratFibre.isIntegral_of_flat_preimmersion (ratFibre.fst p)

theorem redι_genericPoint (z : X) : redι (clo z) (genericPoint _) = z := by
  have hcl : closure ({redι (clo z) (genericPoint _)} : Set X) = closure {z} := by
    rw [← Set.image_singleton, (redι (clo z)).isClosedEmbedding.closure_image_eq,
      (genericPoint_spec _).def, Set.image_univ, range_redι]
    rfl
  exact (inseparable_iff_closure_eq.2 hcl).eq

theorem isEmpty_ratFibre (p : X ⟶ Sp k) {z : X} (hz : ¬ CharZero (X.residueField z)) :
    IsEmpty (ratFibre (redι (clo z) ≫ p)) := by
  by_contra hn
  have : Nonempty (ratFibre (redι (clo z) ≫ p)) := not_isEmpty_iff.1 hn
  have := isIntegral_ratFibre (redι (clo z) ≫ p)
  have h := (charZero_iff (ratFibre.fst (redι (clo z) ≫ p)) _).2 (charZero_ratFibre _ (genericPoint _))
  rw [RatDegZeros.fst_genericPoint, ← charZero_iff (redι (clo z)), redι_genericPoint] at h
  exact hz h

theorem degAt_eq (p : X ⟶ Sp k) [IsProper (p ≫ spMap (Int.castRingHom k))] {L : LB X} (hL : L.IsLB) (z : X) (n : ℕ) :
    degAt p L z n = topSelfIntersection ℚ ((L.pull (redι (clo z))).pull (ratFibre.fst (redι (clo z) ≫ p))) n :=
  haveI : IsProper ((redι (clo z) ≫ p) ≫ spMap (Int.castRingHom k)) := by
    rw [Category.assoc]; infer_instance
  topSelf_cxFibre _ (pull_isLB hL _) n

theorem degAt_eq_zero (p : X ⟶ Sp k) [IsProper (p ≫ spMap (Int.castRingHom k))] {L : LB X} (hL : L.IsLB) {z : X}
    (hz : ¬ CharZero (X.residueField z)) (n : ℕ) : degAt p L z n = 0 := by
  have := isEmpty_ratFibre p hz
  rw [degAt_eq p hL]
  exact interNum_eq_zero_of_isZero _ (InterModel.isZero_of_isEmpty _) fun _ => pull_isLB (pull_isLB hL _) _

theorem range_eq_closure (u : Y ⟶ X) [IsClosedImmersion u] [IsIntegral Y] :
    Set.range u = closure {u (genericPoint Y)} := by
  rw [← Set.image_singleton, u.isClosedEmbedding.closure_image_eq, (genericPoint_spec _).def, Set.image_univ]

theorem degAt_fst (p : X ⟶ Sp k) [IsProper (p ≫ spMap (Int.castRingHom k))] {L : LB X} (hL : L.IsLB) (x : ratFibre p)
    (n : ℕ) : degAt p L (ratFibre.fst p x) n = interNumRed ℚ (clo x) fun _ : Fin n => L.pull (ratFibre.fst p) := by
  set i := redι (clo (ratFibre.fst p x)) with hi
  have hg : i (genericPoint _) = ratFibre.fst p x := redι_genericPoint _
  have hc : CharZero ((Scheme.IdealSheafData.vanishingIdeal (clo (ratFibre.fst p x))).subscheme.residueField
      (genericPoint _)) := by
    rw [← charZero_iff i, hg, charZero_iff]
    exact charZero_ratFibre p x
  obtain ⟨y, -⟩ := RatDegZeros.mem_range_fst k _ (i ≫ p) _ hc
  have : Nonempty (ratFibre (i ≫ p)) := ⟨y⟩
  have := isIntegral_ratFibre (i ≫ p)
  have : IsClosedImmersion (ratFibre.map p i) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (ratFibre.isPullback_map p i) inferInstance
  have hux : ratFibre.map p i (genericPoint _) = x := by
    apply (RatDegZeros.isIso_stalkMap_and_injective k X p).2
    rw [← Scheme.Hom.comp_apply, ratFibre.map_fst, Scheme.Hom.comp_apply, RatDegZeros.fst_genericPoint, hg]
  have hr : Set.range (ratFibre.map p i) = clo x := by rw [range_eq_closure, hux]; rfl
  rw [degAt_eq p hL, InterModel.interNumRed_eq_interNumOn _ (ratFibre.map p i) _ hr,
    interNumOn_eq_interNum_pull (appTop_algebraΓOfHom _ _ (ratFibre.map_snd p i)) (fun _ => pull_isLB hL _)]
  refine interNum_congr_cls ℚ _ (fun _ => pull_isLB (pull_isLB hL _) _) (fun _ => pull_isLB (pull_isLB hL _) _)
    fun _ => ?_
  rw [cls_pull (pull_isLB hL _), cls_pull (pull_isLB hL _), cls_pull hL, cls_pull hL, ← pull_comp, ← pull_comp,
    ratFibre.map_fst]

theorem interNumRed_clo_pull {κ : Type} [Field κ] [Algebra κ Γ(X, ⊤)] [Algebra κ Γ(Y, ⊤)] (u : Y ⟶ X)
    [IsClosedImmersion u] (hu : ∀ r : κ, u.appTop (algebraMap κ Γ(X, ⊤) r) = algebraMap κ Γ(Y, ⊤) r) (y : Y)
    {ι : Type} [Fintype ι] {L : ι → LB X} (hL : ∀ a, (L a).IsLB) :
    interNumRed κ (clo (u y)) L = interNumRed κ (clo y) fun a => (L a).pull u := by
  have hr : Set.range (redι (clo y) ≫ u) = clo (u y) := by
    rw [range_eq_closure, Scheme.Hom.comp_apply, redι_genericPoint]; rfl
  rw [InterModel.interNumRed_eq_interNumOn _ (redι (clo y) ≫ u) _ hr, interNumOn_comp hu _ hL]
  rfl

theorem mul_topSelf_eq (q : Y ⟶ Sp k) [IsIntegral Y] [IsLocallyNoetherian Y] {n : ℕ} (hq : IsArithVar q (n + 1))
    {L M : LB Y} (hL : L.IsLB) (hM : M.IsLB) {m : ℕ} (hc : cls M hM = m • cls L hL) (s : M.Sec)
    (hs : genericPoint Y ∈ Out.nonzeroLocus s) :
    (m : ℤ) * topSelfIntersection ℚ (L.pull (ratFibre.fst q)) (n + 1) = ∑ᶠ y : ratFibre q,
      (divOfSec hM s hs).mult (ratFibre.fst q y) * interNumRed ℚ (clo y) fun _ : Fin n => L.pull (ratFibre.fst q) := by
  have := hq.finite
  have := hq.flat
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 hq.finite
  obtain ⟨_, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB q).1 hq.isProjOver
  have hP : IsProjOver (q ≫ spMap (Int.castRingHom k)) := hA.isProjOver _
  have H : IsPullback (ratFibre.fst q) (ratFibre.snd q) (q ≫ spMap (Int.castRingHom k)) (spMap (algebraMap ℤ ℚ)) :=
    ratFibre.isPullback q
  have hd : topologicalKrullDim (ratFibre q) = (n + 1 : ℕ) := ratFibre.dim_eq_of_isPullback _ H hq.dim_eq
  have : Nonempty (ratFibre q) := by
    by_contra hn
    have : IsEmpty (ratFibre q) := not_nonempty_iff.1 hn
    have : IsEmpty (IrreducibleCloseds (ratFibre q)) :=
      ⟨fun Z => Z.isIrreducible.nonempty.elim fun x _ => isEmptyElim x⟩
    rw [topologicalKrullDim, Order.krullDim_eq_bot] at hd
    exact WithBot.bot_ne_coe hd
  have := isIntegral_ratFibre q
  have hp : IsProjOver (strHom ℚ (ratFibre q)) := by
    rw [ratFibre.strHom_eq]
    exact ProjSpace.isProjOver_of_isPullback_spMap _ H hP
  have : AlgebraicGeometry.IsNoetherian (ratFibre q) := isNoetherian_of_isProjOver hp
  obtain ⟨r, hr, hmult⟩ := MultPull.exists_isRatSec_pull_mult _ _ (ratFibre.fst q) (RatDegZeros.fst_genericPoint k Y q)
    (RatDegZeros.isIso_stalkMap_and_injective k Y q).1 M hM _ (isRatSec_ratOfSec s hs)
  have hL' := pull_isLB hL (ratFibre.fst q)
  have hM' := LB.isLB_pull hM (ratFibre.fst q)
  have key := GlobalTheory.T.rational_section_cycle_formula_projective ℚ (ratFibre q) hp n hd.le _ hM' (fun _ : Fin n => L.pull (ratFibre.fst q)) (fun _ => hL') r hr
  simp only [hmult] at key
  rw [← key]
  have hv := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom ℚ (ratFibre q)) (structureModule (ratFibre q)) hp
    (d := n + 1) (by rw [QCoh.suppDim_structureModule]; exact hd.le)
  have e := hv.interNum_update_of_cls_eq_zsmul (L := fun _ : Fin (n + 1) => L.pull (ratFibre.fst q)) (by simp)
    (fun _ => hL') 0 hM' hL' m (by rw [cls_pull hM, cls_pull hL, hc, map_nsmul, natCast_zsmul])
  rw [Function.update_eq_self_iff.2 rfl] at e
  refine e.symm.trans (congrArg _ ?_)
  funext a
  refine Fin.cases ?_ (fun b => ?_) a
  · simp
  · rw [Function.update_of_ne (Fin.succ_ne_zero b)]; rfl

open NumberField MvPolynomial Filter Topology in
open scoped Classical in

theorem degAt_recursion : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (d : ℕ), IsArithVar p d → ∀ (N : HermLB p), (∀ (z : X) (n : ℕ), ¬ CharZero (X.residueField z) → degAt p N.B z n = 0) ∧ ∀ (m : ℕ) (s : (N.pow m).B.Sec) (z : X) (n : ℕ), topologicalKrullDim (closure ({z} : Set X)) = (n + 2 : ℕ) → z ∈ Out.nonzeroLocus s → (m : ℤ) * degAt p N.B z (n + 1) = ∑ᶠ w, cutMult (N.pow m).isLB s z w * degAt p N.B w n := by
  intro k _ X _ _ p d hX N
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 hX.finite
  have : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hX.isProjOver).1
  refine ⟨fun z n hz => degAt_eq_zero p N.isLB hz n, fun m s z n hdim hz => ?_⟩
  have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (redι (clo z))
  have hs : genericPoint _ ∈ Out.nonzeroLocus (GlobalTheory.ZM.RepBC.secPull _ (redι (clo z)) s) := by
    change _ ∈ Out.nonzeroLocus (Cartier.secPull s (redι (clo z)))
    rw [Cartier.nonzeroLocus_secPull]
    change redι (clo z) (genericPoint _) ∈ Out.nonzeroLocus s
    rwa [redι_genericPoint]
  set i := redι (clo z) with hi
  set j := ratFibre.fst (i ≫ p) with hj
  have hinj : Function.Injective (j ≫ i) := by
    rw [Scheme.Hom.comp_base]
    exact i.isClosedEmbedding.injective.comp (RatDegZeros.isIso_stalkMap_and_injective k _ (i ≫ p)).2
  set F : X → ℤ := fun w => cutMult (N.pow m).isLB s z w * degAt p N.B w n with hF
  have hmul (a) : cutMult (N.pow m).isLB s z (i a) = (divOfSec (LB.isLB_pull (N.pow m).isLB i) _ hs).mult a := by
    rw [cutMult, dif_pos hs]
    exact i.isClosedEmbedding.injective.extend_apply _ _ a
  have hsupp : Function.support F ⊆ Set.range (j ≫ i) := fun w hw => by
    have hw' : cutMult (N.pow m).isLB s z w * degAt p N.B w n ≠ 0 := hw
    obtain ⟨a, rfl⟩ : ∃ a, i a = w := by
      by_contra hn
      refine left_ne_zero_of_mul hw' ?_
      rw [cutMult, dif_pos hs]
      exact Function.extend_apply' _ _ _ hn
    have hc : CharZero (X.residueField (i a)) := by
      by_contra hc
      exact right_ne_zero_of_mul hw' (degAt_eq_zero p N.isLB hc n)
    obtain ⟨y, rfl⟩ := RatDegZeros.mem_range_fst k _ (i ≫ p) a ((charZero_iff i a).1 hc)
    exact ⟨y, Scheme.Hom.comp_apply _ _ _⟩
  have hre : ∑ᶠ y, F ((j ≫ i) y) = ∑ᶠ w, F w := by
    rw [← finsum_mem_range hinj, ← finsum_mem_inter_support, Set.inter_eq_right.2 hsupp, finsum_mem_support]
  rw [← hre]
  by_cases hc : CharZero (X.residueField z)
  swap
  · have := isEmpty_ratFibre p hc
    rw [degAt_eq_zero p N.isLB hc, mul_zero, finsum_of_isEmpty]
  have hc' : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme, ⊤) := by
    rw [← redι_genericPoint z, charZero_iff] at hc
    exact (Scheme.Γevaluation _ (genericPoint _)).hom.charZero
  have hq : IsArithVar (i ≫ p) (n + 1) := hX.of_isClosedImmersion i hc' ((topologicalKrullDim_red (clo z)).trans hdim)
  have : IsClosedImmersion (ratFibre.map p i) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (ratFibre.isPullback_map p i) inferInstance
  rw [degAt_eq p N.isLB, mul_topSelf_eq (i ≫ p) hq (pull_isLB N.isLB i) (LB.isLB_pull (N.pow m).isLB i) (m := m)
    (by rw [cls_pull (N.pow m).isLB, cls_pull N.isLB, ← map_nsmul]; exact congrArg _ (cls_lbPow N.isLB m _)) _ hs]
  refine finsum_congr fun y => ?_
  simp only [hF]
  rw [← ratFibre.map_fst, Scheme.Hom.comp_apply, degAt_fst p N.isLB, ← Scheme.Hom.comp_apply, ratFibre.map_fst,
    Scheme.Hom.comp_apply, hmul,
    interNumRed_clo_pull _ (appTop_algebraΓOfHom _ _ (ratFibre.map_snd p i)) y
      (L := fun _ : Fin n => N.B.pull (ratFibre.fst p)) (fun _ => pull_isLB N.isLB _)]
  congr 1
  refine interNum_congr_cls (ι := Fin n) ℚ _ (fun _ => pull_isLB (pull_isLB N.isLB _) _) (fun _ => pull_isLB (pull_isLB N.isLB _) _)
    fun _ => ?_
  rw [cls_pull (pull_isLB N.isLB _), cls_pull (pull_isLB N.isLB _), cls_pull N.isLB, cls_pull N.isLB, ← pull_comp,
    ← pull_comp, ratFibre.map_fst]

end GlobalTheory.DegRec
