import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.LocusEqTopOfDualPow
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsIsoGrCechMapPolyToGamma
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory

section Defs

variable (k : Type) [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]

variable (X) in

def strHom : X ⟶ Sp k := X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, ⊤)))

abbrev redι (Z : Closeds X) : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι

structure IsCompleteCurve (Z : Closeds X) : Prop where

  isIrreducible : IsIrreducible (Z : Set X)

  dim_eq : topologicalKrullDim (Z : Set X) = 1

  isProper : IsProper (redι Z ≫ strHom k X)

structure IsNef (L : LB X) : Prop where

  isLB : L.IsLB

  nonneg : ∀ Z : Closeds X, IsCompleteCurve k Z → 0 ≤ interNumRed k Z ![L]

def lbH0 (L : LB X) : ℕ := hdim k (twist (structureModule X) L) 0

structure IsBig (L : LB X) : Prop where

  isLB : L.IsLB

  finite : ∀ m : ℕ, Module.Finite k (coh (twist (structureModule X) (lbPow L m)) 0)

  growth : ∃ D : ℕ, topologicalKrullDim X = D ∧ ∃ c : ℝ, 0 < c ∧
    ∃ᶠ m : ℕ in atTop, c * (m : ℝ) ^ D ≤ lbH0 k (lbPow L m)

def HasNonzeroSec (L : LB X) : Prop := ∃ s : L.Sec, s ≠ 0

structure IsPsEff (N : LB X) : Prop where

  isLB : N.IsLB

  exists_ample : ∃ A : LB X, IsAmpleLB A ∧
    ∀ m, 1 ≤ m → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow (tens (lbPow N m) A) r)

end Defs

section Str

variable {k : Type} [Field k] {X Y : Scheme.{0}} [Algebra k Γ(X, ⊤)]

theorem strHom_eq {f : X ⟶ Sp k}
    (hf : ∀ r, algebraMap k Γ(X, ⊤) r = f.appTop ((Scheme.ΓSpecIso (.of k)).inv r)) :
    strHom k X = f := by
  have e : CommRingCat.ofHom (algebraMap k Γ(X, ⊤)) = (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop :=
    CommRingCat.hom_ext (RingHom.ext hf)
  rw [strHom, e, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

variable (k X) in

theorem algebraMap_eq_strHom (r : k) :
    algebraMap k Γ(X, ⊤) r = (strHom k X).appTop ((Scheme.ΓSpecIso (.of k)).inv r) := by
  have e : (Scheme.ΓSpecIso (.of k)).inv ≫ (strHom k X).appTop =
      CommRingCat.ofHom (algebraMap k Γ(X, ⊤)) := by
    rw [strHom, Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc,
      Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  exact (ConcreteCategory.congr_hom e r).symm

theorem comp_strHom [Algebra k Γ(Y, ⊤)] {g : Y ⟶ X}
    (hg : ∀ r : k, g.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(Y, ⊤) r) :
    g ≫ strHom k X = strHom k Y :=
  (strHom_eq fun r => by rw [← hg, algebraMap_eq_strHom k X r]; rfl).symm

theorem range_redι (Z : Closeds X) : Set.range (redι Z) = Z := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]

theorem isIntegral_red {Z : Closeds X} (h : IsIrreducible (Z : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  have := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  have he := (redι Z).isClosedEmbedding.isEmbedding
  have : IrreducibleSpace (Set.range (redι Z)) :=
    Subtype.irreducibleSpace ((range_redι Z).symm ▸ h)
  have : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    he.toHomeomorph.irreducibleSpace_iff.2 this
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem topologicalKrullDim_red (Z : Closeds X) :
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme =
      topologicalKrullDim (Z : Set X) :=
  (topologicalKrullDim_eq_of_isEmbedding (redι Z).isClosedEmbedding.isEmbedding
    (range_redι Z)).symm

theorem isCompleteCurve_iff {f : X ⟶ Sp k}
    (hf : ∀ r, algebraMap k Γ(X, ⊤) r = f.appTop ((Scheme.ΓSpecIso (.of k)).inv r)) [IsProper f]
    {Z : Closeds X} :
    IsCompleteCurve k Z ↔ IsIrreducible (Z : Set X) ∧ topologicalKrullDim (Z : Set X) = 1 :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2, by rw [strHom_eq hf]; infer_instance⟩⟩

theorem isNef_iff {f : X ⟶ Sp k}
    (hf : ∀ r, algebraMap k Γ(X, ⊤) r = f.appTop ((Scheme.ΓSpecIso (.of k)).inv r)) [IsProper f]
    {L : LB X} : IsNef k L ↔ L.IsLB ∧ ∀ Z : Closeds X, IsIrreducible (Z : Set X) →
      topologicalKrullDim (Z : Set X) = 1 → 0 ≤ interNumRed k Z ![L] :=
  ⟨fun h => ⟨h.1, fun Z h₁ h₂ => h.2 Z ((isCompleteCurve_iff hf).2 ⟨h₁, h₂⟩)⟩,
    fun h => ⟨h.1, fun Z hZ => h.2 Z hZ.1 hZ.2⟩⟩

theorem isCompleteCurve_range (i : Y ⟶ X) [IsClosedImmersion i] [IsIntegral Y]
    (hd : topologicalKrullDim Y = 1) [IsProper (i ≫ strHom k X)] :
    IsCompleteCurve k ⟨Set.range i, i.isClosedEmbedding.isClosed_range⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · have := (IrreducibleSpace.isIrreducible_univ Y).image i i.continuous.continuousOn
    rwa [Set.image_univ] at this
  · exact (topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding rfl).trans hd
  · have e : Scheme.IdealSheafData.vanishingIdeal
        (⟨Set.range i, i.isClosedEmbedding.isClosed_range⟩ : Closeds X) = i.ker := by
      rw [← InterModel.radical_ker i, ← Scheme.IdealSheafData.vanishingIdeal_support]
      congr 1
      ext1
      rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
      rfl
    change IsProper ((Scheme.IdealSheafData.vanishingIdeal _).subschemeι ≫ _)
    rw [e]
    have : IsIso i.toImage := inferInstance
    have e₂ : i.ker.subschemeι = inv i.toImage ≫ i := by
      rw [IsIso.eq_inv_comp]; exact i.toImage_imageι
    rw [e₂, Category.assoc]
    infer_instance

theorem isNef_iff_isClosedImmersion {L : LB X} : IsNef k L ↔ L.IsLB ∧
    ∀ (C : Scheme.{0}) (i : C ⟶ X), IsClosedImmersion i → IsIntegral C →
      topologicalKrullDim C = 1 → IsProper (i ≫ strHom k X) → 0 ≤ interNumOn k i ![L] := by
  refine ⟨fun h => ⟨h.1, fun C i _ _ hd _ => ?_⟩, fun h => ⟨h.1, fun Z hZ => ?_⟩⟩
  · have := h.2 _ (isCompleteCurve_range i hd)
    rwa [InterModel.interNumRed_eq_interNumOn k i _ rfl] at this
  · exact h.2 _ (redι Z) inferInstance (isIntegral_red hZ.1)
      ((topologicalKrullDim_red Z).trans hZ.2) hZ.3

end Str

section Sections

variable {X Y : Scheme.{0}} {L M N A B : LB X}

theorem exists_sec_of_cls_eq_add (hN : N.IsLB) (hA : A.IsLB) (hB : B.IsLB)
    (e : cls N hN = cls A hA + cls B hB) (s : A.Sec) (t : B.Sec) :
    ∃ u : N.Sec, nonzeroLocus u = nonzeroLocus s ⊓ nonzeroLocus t := by
  have hD := Semi.LB.isLB_div hN hA
  obtain ⟨t', ht'⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hD hB
    ((cls_eq_iff hD hB).1 (by rw [cls_div hN hA, e, add_sub_cancel_left])) t
  obtain ⟨u, hu⟩ := exists_sec_nonzeroLocus_eq_inf_div hA hN t' s
  exact ⟨u, by rw [hu, ht', inf_comm]⟩

theorem sec_ne_zero_of_mem {s : L.Sec} {x : X} (h : x ∈ nonzeroLocus s) : s ≠ 0 := by
  rintro rfl
  exact (nonzeroLocus_secZero (M := L)).le h

theorem sec_ne_zero_iff [IsIntegral X] (s : L.Sec) : s ≠ 0 ↔ genericPoint X ∈ nonzeroLocus s := by
  refine ⟨fun h => ?_, sec_ne_zero_of_mem⟩
  obtain ⟨i, hi⟩ : ∃ i, s.f i ≠ 0 := by
    by_contra! h'
    exact h (DVR.SecOps.sec_ext h')
  have hb : X.basicOpen (s.f i) ≠ ⊥ := fun hb => hi ((basicOpen_eq_bot_iff _).1 hb)
  exact basicOpen_le_nonzeroLocus s i (((genericPoint_spec X).mem_open_set_iff
    (X.basicOpen (s.f i)).isOpen).2 (by simpa using (Opens.ne_bot_iff_nonempty _).1 hb))

theorem hasNonzeroSec_iff [IsIntegral X] :
    HasNonzeroSec L ↔ ∃ s : L.Sec, genericPoint X ∈ nonzeroLocus s :=
  exists_congr sec_ne_zero_iff

def cohZeroTwistEquiv (L : LB X) : coh (twist (structureModule X) L) 0 ≃ₗ[Γ(X, ⊤)] L.Sec :=
  (cohOn.mapIso Γ(X, ⊤) ⊤ 0 (Twist.unitTwistIso L)).trans
    ((coh.zeroEquiv _).trans (LB.globalEquiv L))

theorem hasNonzeroSec_iff_nontrivial :
    HasNonzeroSec L ↔ Nontrivial (coh (twist (structureModule X) L) 0) :=
  (nontrivial_iff_exists_ne (0 : L.Sec)).symm.trans
    (cohZeroTwistEquiv L).toEquiv.nontrivial_congr.symm

theorem HasNonzeroSec.of_cls_eq (h : HasNonzeroSec M) (hL : L.IsLB) (hM : M.IsLB)
    (e : cls L hL = cls M hM) : HasNonzeroSec L := by
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (structureModule X) hL hM e
  rw [hasNonzeroSec_iff_nontrivial] at h ⊢
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ 0 i).toEquiv.nontrivial_congr.2 h

theorem HasNonzeroSec.of_cls_eq_add [IsIntegral X] (h₁ : HasNonzeroSec A) (h₂ : HasNonzeroSec B)
    (hN : N.IsLB) (hA : A.IsLB) (hB : B.IsLB) (e : cls N hN = cls A hA + cls B hB) :
    HasNonzeroSec N := by
  obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 h₁
  obtain ⟨t, ht⟩ := hasNonzeroSec_iff.1 h₂
  obtain ⟨u, hu⟩ := exists_sec_of_cls_eq_add hN hA hB e s t
  exact hasNonzeroSec_iff.2 ⟨u, hu.ge ⟨hs, ht⟩⟩

theorem HasNonzeroSec.tens [IsIntegral X] (h₁ : HasNonzeroSec A) (h₂ : HasNonzeroSec B)
    (hA : A.IsLB) (hB : B.IsLB) : HasNonzeroSec (tens A B) :=
  h₁.of_cls_eq_add h₂ (isLB_tens hA hB) hA hB rfl

theorem IsGenerated.hasNonzeroSec [Nonempty X] (h : IsGenerated L) : HasNonzeroSec L :=
  have ⟨s, hs⟩ := h.exists_mem (Classical.arbitrary X)
  ⟨s, sec_ne_zero_of_mem hs⟩

theorem HasNonzeroSec.pow [IsIntegral X] (h : HasNonzeroSec L) (hL : L.IsLB) (n : ℕ) :
    HasNonzeroSec (lbPow L n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact (isGenerated_triv X).hasNonzeroSec.of_cls_eq (isLB_lbPow hL 0) (LB.isLB_triv X)
      (by rw [cls_lbPow hL, zero_nsmul, cls_triv])
  · obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 h
    exact hasNonzeroSec_iff.2 ⟨secToPow s n, (nonzeroLocus_secToPow s hn).ge hs⟩

theorem EffCartierData.hasNonzeroSec [Nonempty X] (D : EffCartierData X) :
    HasNonzeroSec D.lb := by
  obtain ⟨x, hx⟩ := D.dense_nonzeroLocus_canonical.nonempty
  exact ⟨_, sec_ne_zero_of_mem hx⟩

end Sections

section Curve

variable {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] [IsIntegral C]
  [IsProper (strHom k C)] {H L : LB C}

theorem interNum_one_nonneg_of_sec (hH : IsAmpleLB H) (hd : topologicalKrullDim C = 1)
    (hL : L.IsLB) (s : L.Sec) (hs : genericPoint C ∈ nonzeroLocus s) :
    0 ≤ interNum k (structureModule C) ![L] ∧
      (nonzeroLocus s ≠ ⊤ → 0 < interNum k (structureModule C) ![L]) := by
  have hf := algebraMap_eq_strHom k C
  have := isNoetherian_of_isProjOver (hH.isProjOver (strHom k C))
  have := (mono_cutHom_structureModule_iff hL s).2 hs
  have hfin : FiniteCohTwists k (structureModule C) := hH.finiteCohTwists hf _
  have h0 : suppDim (cut (structureModule C) hL s) ≤ 0 :=
    suppDim_cut_le (d := 0) _ hL s (by rw [suppDim_structureModule, hd]; rfl)
  have e : interNum k (structureModule C) ![L] = hdim k (cut (structureModule C) hL s) 0 :=
    (interNum_cons_eq_interNum_cut hL s (P := ![]) isEmptyElim hfin).trans
      ((interNum_of_isEmpty k _ _).trans (chi_eq_hdim_zero_of_suppDim_le_zero k h0))
  refine ⟨e ▸ Nat.cast_nonneg _, fun ht => ?_⟩
  rw [e, Nat.cast_pos, Nat.pos_iff_ne_zero]
  have := (hfin.cut hL s).finiteCoh.finite 0
  intro hz
  rw [hdim_eq_zero_iff] at hz
  have hΓ : Subsingleton Γ(cut (structureModule C) hL s, ⊤) :=
    (coh.zeroEquiv _).toEquiv.subsingleton_congr.1 hz
  have hb := (germ_support_bijective (finite_support_of_suppDim_le_zero h0)
    fun x hx => isClosed_singleton_of_suppDim_le_zero h0 hx).2
  obtain ⟨x, hx⟩ : ∃ x, x ∉ nonzeroLocus s := by
    by_contra! h'
    exact ht (top_le_iff.1 fun x _ => h' x)
  have hx' : x ∈ support (cut (structureModule C) hL s) := by
    rw [support_cut, support_structureModule]
    exact ⟨trivial, hx⟩
  have hs' := hb.subsingleton
  have hn : Nontrivial ((cut (structureModule C) hL s).presheaf.stalk x :) := hx'
  classical
  obtain ⟨a, ha⟩ := exists_ne (0 : ((cut (structureModule C) hL s).presheaf.stalk x :))
  have := congrFun (hs'.elim (Pi.single (⟨x, hx'⟩ : support _) a) 0) ⟨x, hx'⟩
  rw [Pi.single_eq_same] at this
  exact ha this

omit [IsIntegral C] in

theorem interNum_one_of_cls_eq_add (hH : IsAmpleLB H) (hd : topologicalKrullDim C = 1)
    {A B : LB C} (hL : L.IsLB) (hA : A.IsLB) (hB : B.IsLB) (e : cls L hL = cls A hA + cls B hB) :
    interNum k (structureModule C) ![L] =
      interNum k (structureModule C) ![A] + interNum k (structureModule C) ![B] := by
  have := isNoetherian_of_isProjOver (hH.isProjOver (strHom k C))
  exact (hH.diffVanish_chiPic_of_isProper (algebraMap_eq_strHom k C) (structureModule C) (d := 1)
    (by rw [suppDim_structureModule, hd]; rfl)).interNum_cons_of_cls_eq_add le_rfl (P := ![])
      isEmptyElim hL hA hB e

end Curve

section Degree

variable {k : Type} [Field k] {X Y : Scheme.{0}} [Algebra k Γ(X, ⊤)] {H L M N A B : LB X}
  {Z : Closeds X}

theorem isLB_vecOne (hL : L.IsLB) : ∀ i, ((![L] : Fin 1 → LB X) i).IsLB :=
  isLB_cons hL isEmptyElim

theorem interNumRed_one_eq (hL : L.IsLB) (Z : Closeds X) :
    letI := algebraΓAlong k (redι Z)
    interNumRed k Z ![L] = interNum k (structureModule _) ![L.pull (redι Z)] := by
  letI := algebraΓAlong k (redι Z)
  refine (interNumOn_eq_interNum_pull (appTop_algebraMap_along k (redι Z))
    (isLB_vecOne hL)).trans (congrArg _ (funext fun i => ?_))
  fin_cases i
  rfl

theorem IsCompleteCurve.isProper_strHom (hZ : IsCompleteCurve k Z) :
    letI := algebraΓAlong k (redι Z)
    IsProper (strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
  letI := algebraΓAlong k (redι Z)
  rw [← comp_strHom (appTop_algebraMap_along k (redι Z))]
  exact hZ.3

theorem interNumRed_one_congr (hL : L.IsLB) (hM : M.IsLB) (e : cls L hL = cls M hM)
    (Z : Closeds X) : interNumRed k Z ![L] = interNumRed k Z ![M] :=
  interNum_congr_cls k _ (isLB_vecOne hL) (isLB_vecOne hM) fun i => by fin_cases i; exact e

theorem IsCompleteCurve.interNumRed_of_cls_eq_add (hZ : IsCompleteCurve k Z) (hH : IsAmpleLB H)
    (hN : N.IsLB) (hA : A.IsLB) (hB : B.IsLB) (e : cls N hN = cls A hA + cls B hB) :
    interNumRed k Z ![N] = interNumRed k Z ![A] + interNumRed k Z ![B] := by
  letI := algebraΓAlong k (redι Z)
  have := hZ.isProper_strHom
  rw [interNumRed_one_eq hN, interNumRed_one_eq hA, interNumRed_one_eq hB]
  exact interNum_one_of_cls_eq_add (hH.pull_of_isClosedImmersion (redι Z))
    ((topologicalKrullDim_red Z).trans hZ.2) (LB.isLB_pull hN _) (LB.isLB_pull hA _)
    (LB.isLB_pull hB _) (by rw [cls_pull hN, cls_pull hA, cls_pull hB, e, map_add])

theorem interNumRed_one_eq_zero (hL : L.IsLB) (e : cls L hL = 0) (Z : Closeds X) :
    interNumRed k Z ![L] = 0 :=
  interNum_eq_zero_of_cls_eq_zero k _ (isLB_vecOne hL) 0 e

theorem IsCompleteCurve.interNumRed_lbPow (hZ : IsCompleteCurve k Z) (hH : IsAmpleLB H)
    (hL : L.IsLB) (n : ℕ) : interNumRed k Z ![lbPow L n] = n * interNumRed k Z ![L] := by
  induction n with
  | zero => rw [interNumRed_one_eq_zero (isLB_lbPow hL 0) (by rw [cls_lbPow hL, zero_nsmul])]; simp
  | succ n ih =>
    rw [hZ.interNumRed_of_cls_eq_add hH (isLB_lbPow hL (n + 1)) (isLB_lbPow hL n) hL
      (by rw [cls_lbPow hL, cls_lbPow hL, succ_nsmul]), ih]
    push_cast
    ring

theorem IsCompleteCurve.interNumRed_dual (hZ : IsCompleteCurve k Z) (hH : IsAmpleLB H)
    (hL : L.IsLB) : interNumRed k Z ![dual L] = -interNumRed k Z ![L] := by
  have := hZ.interNumRed_of_cls_eq_add hH (LB.isLB_triv X) (isLB_dual hL) hL
    (cls_dual_add hL).symm
  rw [interNumRed_one_eq_zero (LB.isLB_triv X) rfl] at this
  omega

theorem IsCompleteCurve.interNumRed_nonneg_of_sec (hZ : IsCompleteCurve k Z) (hH : IsAmpleLB H)
    (hL : L.IsLB) (s : L.Sec) {x : X} (hx : x ∈ Z) (hs : x ∈ nonzeroLocus s) :
    0 ≤ interNumRed k Z ![L] ∧ ((∃ y ∈ Z, y ∉ nonzeroLocus s) → 0 < interNumRed k Z ![L]) := by
  letI := algebraΓAlong k (redι Z)
  have := hZ.isProper_strHom
  have := isIntegral_red hZ.1
  obtain ⟨x, rfl⟩ := (range_redι Z).ge hx
  have e := nonzeroLocus_secPull s (redι Z)
  have h := interNum_one_nonneg_of_sec (k := k) (hH.pull_of_isClosedImmersion (redι Z))
    ((topologicalKrullDim_red Z).trans hZ.2) (LB.isLB_pull hL _) (secPull s (redι Z))
    ((sec_ne_zero_iff _).1 (sec_ne_zero_of_mem (e.ge hs)))
  rw [interNumRed_one_eq hL]
  refine ⟨h.1, fun ⟨y, hy, hy'⟩ => h.2 fun ht => ?_⟩
  obtain ⟨y, rfl⟩ := (range_redι Z).ge hy
  exact hy' (e.le (ht.ge trivial))

theorem IsCompleteCurve.exists_open (hZ : IsCompleteCurve k Z) :
    ∃ x ∈ Z, ∃ y ∈ Z, ∃ U : X.Opens, x ∈ U ∧ y ∉ U := by
  by_contra! h
  have hs : (Z : Set X).Subsingleton := fun x hx y hy =>
    ((inseparable_iff_forall_isOpen).2 fun U hU =>
      ⟨h x hx y hy ⟨U, hU⟩, h y hy x hx ⟨U, hU⟩⟩).eq
  have := hs.coe_sort
  have h0 := topologicalKrullDim_zero_of_discreteTopology (Z : Set X)
  rw [hZ.2] at h0
  exact absurd h0 (by decide)

theorem IsAmpleLB.interNumRed_pos (hA : IsAmpleLB A) (hZ : IsCompleteCurve k Z) :
    0 < interNumRed k Z ![A] := by
  obtain ⟨x, hx, y, hy, U, hxU, hyU⟩ := hZ.exists_open
  obtain ⟨n, hn, s, hs, hle, -⟩ := hA.exists_affine_le hxU
  have h := (hZ.interNumRed_nonneg_of_sec hA (isLB_lbPow hA.isLB n) s hx hs).2
    ⟨y, hy, fun h => hyU (hle h)⟩
  rw [hZ.interNumRed_lbPow hA hA.isLB] at h
  exact (pos_iff_pos_of_mul_pos h).1 (Nat.cast_pos.2 hn)

end Degree

section Nef

variable {k : Type} [Field k] {X Y : Scheme.{0}} [Algebra k Γ(X, ⊤)] {H L M N A B : LB X}

theorem IsNef.of_cls_eq (h : IsNef k M) (hL : L.IsLB) (e : cls L hL = cls M h.isLB) : IsNef k L :=
  ⟨hL, fun Z hZ => (h.2 Z hZ).trans_eq (interNumRed_one_congr hL h.isLB e Z).symm⟩

theorem IsNef.of_lbIso (h : IsNef k M) (hL : L.IsLB) (e : LBIso L M) : IsNef k L :=
  h.of_cls_eq hL ((cls_eq_iff hL h.isLB).2 e)

variable (k X) in

theorem isNef_triv : IsNef k (LB.triv X) :=
  ⟨LB.isLB_triv X, fun Z _ => (interNumRed_one_eq_zero (LB.isLB_triv X) rfl Z).ge⟩

theorem IsGenerated.isNef (h : IsGenerated L) (hH : IsAmpleLB H) : IsNef k L :=
  ⟨h.isLB, fun _ hZ =>
    have ⟨x, hx⟩ := hZ.1.nonempty
    have ⟨s, hs⟩ := h.exists_mem x
    (hZ.interNumRed_nonneg_of_sec hH h.isLB s hx hs).1⟩

theorem IsAmpleLB.isNef (h : IsAmpleLB A) : IsNef k A :=
  ⟨h.isLB, fun _ hZ => (h.interNumRed_pos hZ).le⟩

theorem IsNef.of_cls_eq_add (hA : IsNef k A) (hB : IsNef k B) (hH : IsAmpleLB H) (hN : N.IsLB)
    (e : cls N hN = cls A hA.isLB + cls B hB.isLB) : IsNef k N :=
  ⟨hN, fun Z hZ => (add_nonneg (hA.2 Z hZ) (hB.2 Z hZ)).trans_eq
    (hZ.interNumRed_of_cls_eq_add hH hN hA.isLB hB.isLB e).symm⟩

theorem IsNef.tens (hA : IsNef k A) (hB : IsNef k B) (hH : IsAmpleLB H) : IsNef k (tens A B) :=
  hA.of_cls_eq_add hB hH (isLB_tens hA.isLB hB.isLB) rfl

theorem IsNef.pow (h : IsNef k L) (hH : IsAmpleLB H) (n : ℕ) : IsNef k (lbPow L n) :=
  ⟨isLB_lbPow h.isLB n, fun Z hZ => (mul_nonneg (Nat.cast_nonneg n) (h.2 Z hZ)).trans_eq
    (hZ.interNumRed_lbPow hH h.isLB n).symm⟩

theorem isNef_pow_iff (hH : IsAmpleLB H) (hL : L.IsLB) {n : ℕ} (hn : 1 ≤ n) :
    IsNef k (lbPow L n) ↔ IsNef k L :=
  ⟨fun h => ⟨hL, fun Z hZ => nonneg_of_mul_nonneg_right
      ((h.2 Z hZ).trans_eq (hZ.interNumRed_lbPow hH hL n)) (Nat.cast_pos.2 hn)⟩,
    fun h => h.pow hH n⟩

theorem IsNef.of_cls_eq_sum {ι : Type*} (s : Finset ι) {P : ι → LB X} (hP : ∀ i, IsNef k (P i))
    (n : ι → ℕ) (hH : IsAmpleLB H) (hN : N.IsLB)
    (e : cls N hN = ∑ i ∈ s, n i • cls (P i) (hP i).isLB) : IsNef k N := by
  classical
  induction s using Finset.induction_on generalizing N with
  | empty => exact (isNef_triv k X).of_cls_eq hN e
  | insert a s ha ih =>
    obtain ⟨M, hM, eM⟩ := cls_surj (∑ i ∈ s, n i • cls (P i) (hP i).isLB)
    exact ((hP a).pow hH (n a)).of_cls_eq_add (ih hM eM) hH hN
      (by rw [e, Finset.sum_insert ha, cls_lbPow (hP a).isLB, eM])

theorem IsGenerated.isNef_of_isProjOver (h : IsGenerated L) {f : X ⟶ Sp k} (hf : IsProjOver f) :
    IsNef k L :=
  have ⟨_, hH⟩ := exists_isAmpleLB_of_isProjOver hf
  h.isNef hH

theorem IsNef.tens_of_isProjOver (hA : IsNef k A) (hB : IsNef k B) {f : X ⟶ Sp k}
    (hf : IsProjOver f) : IsNef k (CechPic.tens A B) :=
  have ⟨_, hH⟩ := exists_isAmpleLB_of_isProjOver hf
  hA.tens hB hH

theorem IsNef.pull_of_isClosedImmersion [Algebra k Γ(Y, ⊤)] (h : IsNef k L) (g : Y ⟶ X)
    [IsClosedImmersion g]
    (hg : ∀ r : k, g.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(Y, ⊤) r) :
    IsNef k (L.pull g) := by
  refine isNef_iff_isClosedImmersion.2 ⟨LB.isLB_pull h.isLB g, fun C i _ _ hd hp => ?_⟩
  have := (isNef_iff_isClosedImmersion.1 h).2 C (i ≫ g) inferInstance inferInstance hd
    (by rwa [Category.assoc, comp_strHom hg])
  rw [interNumOn_comp hg i (isLB_vecOne h.isLB)] at this
  refine this.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j
  rfl

theorem IsAmpleLB.not_isNef_dual (h : IsAmpleLB A) {Z : Closeds X} (hZ : IsCompleteCurve k Z) :
    ¬ IsNef k (dual A) := fun h' => by
  have h₁ := h'.2 Z hZ
  have h₂ := h.interNumRed_pos hZ
  rw [hZ.interNumRed_dual h h.isLB] at h₁
  omega

end Nef

section PsEff

variable {X : Scheme.{0}} {H L M N A B : LB X}

theorem cls_lbPow_tens_lbPow (hN : N.IsLB) (hA : A.IsLB) (m r : ℕ)
    (h : (lbPow (tens (lbPow N m) A) r).IsLB) :
    cls _ h = r • (m • cls N hN + cls A hA) := by
  rw [cls_lbPow (isLB_tens (isLB_lbPow hN m) hA), cls_tens (isLB_lbPow hN m) hA, cls_lbPow hN]

theorem IsAmpleLB.exists_hasNonzeroSec [IsLocallyNoetherian X] [Nonempty X] (hA : IsAmpleLB A)
    (hM : M.IsLB) : ∃ q : ℕ, 1 ≤ q ∧ ∀ (P : LB X) (hP : P.IsLB),
      cls P hP = cls M hM + q • cls A hA.isLB → HasNonzeroSec P := by
  obtain ⟨n, hn, h⟩ := ((eventually_ge_atTop 1).and (hA.eventually_exists_mem_nonzeroLocus_le hM
    (x := Classical.arbitrary X) (U := ⊤) trivial)).exists
  lift n to ℕ using zero_le_one.trans hn
  refine ⟨n, by exact_mod_cast hn, fun P hP e => ?_⟩
  obtain ⟨t, ht, -⟩ := h P hP (by rw [e, natCast_zsmul])
  exact ⟨t, sec_ne_zero_of_mem ht⟩

variable [IsIntegral X]

theorem IsPsEff.exists_hasNonzeroSec [IsLocallyNoetherian X] (h : IsPsEff N) (hA : IsAmpleLB A)
    {m : ℕ} (hm : 1 ≤ m) : ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow (tens (lbPow N m) A) r) := by
  obtain ⟨B, hB, hs⟩ := h.2
  obtain ⟨q, hq, hq'⟩ := hA.exists_hasNonzeroSec (isLB_dual hB.isLB)
  obtain ⟨r, hr, hr'⟩ := hs (q * m) (Nat.mul_pos hq hm)
  have hP := isLB_tens (isLB_dual hB.isLB) (isLB_lbPow hA.isLB q)
  refine ⟨r * q, Nat.mul_pos hr hq, hr'.of_cls_eq_add
    ((hq' _ hP (by rw [cls_tens _ (isLB_lbPow hA.isLB q), cls_lbPow hA.isLB])).pow hP r)
    (isLB_lbPow (isLB_tens (isLB_lbPow h.1 m) hA.isLB) _)
    (isLB_lbPow (isLB_tens (isLB_lbPow h.1 _) hB.isLB) _) (isLB_lbPow hP r) ?_⟩
  rw [cls_lbPow_tens_lbPow h.1 hA.isLB, cls_lbPow_tens_lbPow h.1 hB.isLB, cls_lbPow hP,
    cls_tens (isLB_dual hB.isLB) (isLB_lbPow hA.isLB q), cls_dual hB.isLB, cls_lbPow hA.isLB]
  module

omit [IsIntegral X] in

theorem IsPsEff.of_cls_eq (h : IsPsEff M) (hL : L.IsLB) (e : cls L hL = cls M h.isLB) :
    IsPsEff L := by
  obtain ⟨A, hA, hs⟩ := h.2
  refine ⟨hL, A, hA, fun m hm => ?_⟩
  obtain ⟨r, hr, hr'⟩ := hs m hm
  exact ⟨r, hr, hr'.of_cls_eq (isLB_lbPow (isLB_tens (isLB_lbPow hL m) hA.isLB) r)
    (isLB_lbPow (isLB_tens (isLB_lbPow h.1 m) hA.isLB) r)
    (by rw [cls_lbPow_tens_lbPow hL hA.isLB, cls_lbPow_tens_lbPow h.1 hA.isLB, e])⟩

omit [IsIntegral X] in

theorem IsPsEff.of_lbIso (h : IsPsEff M) (hL : L.IsLB) (e : LBIso L M) : IsPsEff L :=
  h.of_cls_eq hL ((cls_eq_iff hL h.isLB).2 e)

theorem isPsEff_of_hasNonzeroSec_pow (hH : IsAmpleLB H) (hL : L.IsLB) {n : ℕ} (hn : 1 ≤ n)
    (h : HasNonzeroSec (lbPow L n)) : IsPsEff L := by
  obtain ⟨q, hq, hg⟩ := hH.exists_isGenerated_pow
  refine ⟨hL, H, hH, fun m _ => ⟨n * q, Nat.mul_pos hn hq,
    (h.pow (isLB_lbPow hL n) (m * q)).of_cls_eq_add (hg.hasNonzeroSec.pow hg.isLB n)
      (isLB_lbPow (isLB_tens (isLB_lbPow hL m) hH.isLB) _) (isLB_lbPow (isLB_lbPow hL n) _)
      (isLB_lbPow hg.isLB n) ?_⟩⟩
  rw [cls_lbPow_tens_lbPow hL hH.isLB, cls_lbPow (isLB_lbPow hL n), cls_lbPow hL,
    cls_lbPow hg.isLB, cls_lbPow hH.isLB]
  module

theorem HasNonzeroSec.isPsEff (h : HasNonzeroSec L) (hL : L.IsLB) (hH : IsAmpleLB H) :
    IsPsEff L :=
  isPsEff_of_hasNonzeroSec_pow hH hL le_rfl (h.pow hL 1)

theorem EffCartierData.isPsEff (D : EffCartierData X) (hH : IsAmpleLB H) : IsPsEff D.lb :=
  D.hasNonzeroSec.isPsEff D.isLB_lb hH

theorem IsGenerated.isPsEff (h : IsGenerated L) (hH : IsAmpleLB H) : IsPsEff L :=
  h.hasNonzeroSec.isPsEff h.isLB hH

theorem IsAmpleLB.isPsEff (h : IsAmpleLB A) : IsPsEff A :=
  have ⟨_, hn, hg⟩ := h.exists_isGenerated_pow
  isPsEff_of_hasNonzeroSec_pow h h.isLB hn hg.hasNonzeroSec

theorem IsPsEff.of_cls_eq_add (hL : IsPsEff L) (hM : IsPsEff M) (hN : N.IsLB)
    (e : cls N hN = cls L hL.isLB + cls M hM.isLB) : IsPsEff N := by
  obtain ⟨A, hA, hs⟩ := hL.2
  obtain ⟨B, hB, ht⟩ := hM.2
  have hAB := isLB_tens hA.isLB hB.isLB
  have hD := Semi.LB.isLB_div hAB hA.isLB
  refine ⟨hN, tens A B, hA.tensor hB hAB ((cls_eq_zero_iff (Semi.LB.isLB_div hD hB.isLB)).1 ?_),
    fun m hm => ?_⟩
  · rw [cls_div hD hB.isLB, cls_div hAB hA.isLB, cls_tens hA.isLB hB.isLB]
    abel
  obtain ⟨r, hr, hr'⟩ := hs m hm
  obtain ⟨q, hq, hq'⟩ := ht m hm
  have h₁ := isLB_lbPow (isLB_tens (isLB_lbPow hL.1 m) hA.isLB) r
  have h₂ := isLB_lbPow (isLB_tens (isLB_lbPow hM.1 m) hB.isLB) q
  refine ⟨r * q, Nat.mul_pos hr hq, (hr'.pow h₁ q).of_cls_eq_add (hq'.pow h₂ r)
    (isLB_lbPow (isLB_tens (isLB_lbPow hN m) hAB) _) (isLB_lbPow h₁ q) (isLB_lbPow h₂ r) ?_⟩
  rw [cls_lbPow_tens_lbPow hN hAB, cls_lbPow h₁, cls_lbPow h₂, cls_lbPow_tens_lbPow hL.1 hA.isLB,
    cls_lbPow_tens_lbPow hM.1 hB.isLB, cls_tens hA.isLB hB.isLB, e]
  module

theorem IsPsEff.tens (hL : IsPsEff L) (hM : IsPsEff M) : IsPsEff (tens L M) :=
  hL.of_cls_eq_add hM (isLB_tens hL.isLB hM.isLB) rfl

theorem IsPsEff.exists_of_dual [IsLocallyNoetherian X] (hA : IsAmpleLB A) (h : IsPsEff (dual A)) :
    ∃ r : ℕ, 1 ≤ r ∧ HasNonzeroSec (lbZPow A (-r)) := by
  obtain ⟨r, hr, hr'⟩ := h.exists_hasNonzeroSec hA (m := 2) one_le_two
  refine ⟨r, hr, hr'.of_cls_eq (Twist.isLB_lbZPow hA.isLB _)
    (isLB_lbPow (isLB_tens (isLB_lbPow h.1 2) hA.isLB) r) ?_⟩
  rw [cls_lbPow_tens_lbPow h.1 hA.isLB, cls_lbZPow hA.isLB, cls_dual hA.isLB]
  module

end PsEff

section Big

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {H L M N A B : LB X}

theorem lineBundleGlobalSectionsDim_def (L : LB X) : lbH0 k L = hdim k (twist (structureModule X) L) 0 := rfl

theorem lineBundleGlobalSectionsDim_eq_finrank (L : LB X) [Module k L.Sec] [IsScalarTower k Γ(X, ⊤) L.Sec] :
    lbH0 k L = Module.finrank k L.Sec :=
  ((cohZeroTwistEquiv L).restrictScalars k).finrank_eq

theorem lineBundleGlobalSectionsDim_congr_picardClass (hL : L.IsLB) (hM : M.IsLB) (e : cls L hL = cls M hM) : lbH0 k L = lbH0 k M :=
  (nonempty_twist_iso_of_cls_eq _ hL hM e).elim (hdim_congr k 0)

theorem finite_coh_zero_twist_congr (hL : L.IsLB) (hM : M.IsLB) (e : cls L hL = cls M hM)
    (h : Module.Finite k (coh (twist (structureModule X) M) 0)) :
    Module.Finite k (coh (twist (structureModule X) L) 0) :=
  (nonempty_twist_iso_of_cls_eq _ hL hM e).elim fun i => .equiv (cohOn.mapIso k ⊤ 0 i).symm

theorem finite_coh_zero_twist_of_isProjOver {f : X ⟶ Sp k}
    (hf : ∀ r, algebraMap k Γ(X, ⊤) r = f.appTop ((Scheme.ΓSpecIso (.of k)).inv r))
    (h : IsProjOver f) (hL : L.IsLB) : Module.Finite k (coh (twist (structureModule X) L) 0) :=
  finite_coh_twist_of_isProjOver hf _ h hL 0

theorem lineBundleHasNonzeroSection_of_globalSectionsDim_pos (h : 0 < lbH0 k L) : HasNonzeroSec L :=
  hasNonzeroSec_iff_nontrivial.2 (Module.nontrivial_of_finrank_pos h)

theorem lineBundleGlobalSectionsDim_pos_iff (h : Module.Finite k (coh (twist (structureModule X) L) 0)) :
    0 < lbH0 k L ↔ HasNonzeroSec L :=
  Module.finrank_pos_iff.trans hasNonzeroSec_iff_nontrivial.symm

theorem lineBundleGlobalSectionsDim_le_of_picardClass_add [IsIntegral X] [IsLocallyNoetherian X] (hN : N.IsLB) (hA : A.IsLB)
    (hB : B.IsLB) (e : cls N hN = cls A hA + cls B hB) (h : HasNonzeroSec B)
    (hfin : Module.Finite k (coh (twist (structureModule X) N) 0)) : lbH0 k A ≤ lbH0 k N := by
  obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 h
  obtain ⟨i⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule X) hA hB hN e
  have := Twist.isQuasicoherent_twist (F := structureModule X) hA
  have : Mono (Twist.secHom (twist (structureModule X) A) s) := by
    rw [mono_secHom_iff _ hB, Twist.assPoints_twist hA, ← mono_cutHom_iff _ hB]
    exact (mono_cutHom_structureModule_iff hB s).2 hs
  exact LinearMap.finrank_le_finrank_of_injective
    (cohOn.map_zero_injective_of_mono k ⊤ (Twist.secHom (twist (structureModule X) A) s ≫ i.hom))

theorem isBig_iff {f : X ⟶ Sp k}
    (hf : ∀ r, algebraMap k Γ(X, ⊤) r = f.appTop ((Scheme.ΓSpecIso (.of k)).inv r))
    (h : IsProjOver f) {D : ℕ} (hD : topologicalKrullDim X = D) :
    IsBig k L ↔ L.IsLB ∧ ∃ c : ℝ, 0 < c ∧
      ∃ᶠ m : ℕ in atTop, c * (m : ℝ) ^ D ≤ lbH0 k (lbPow L m) := by
  refine ⟨fun hL => ⟨hL.1, ?_⟩, fun hL => ⟨hL.1,
    fun m => finite_coh_zero_twist_of_isProjOver hf h (isLB_lbPow hL.1 m), D, hD, hL.2⟩⟩
  obtain ⟨D', hD', hc⟩ := hL.3
  obtain rfl : D' = D := by exact_mod_cast hD'.symm.trans hD
  exact hc

theorem IsBig.of_cls_eq (h : IsBig k M) (hL : L.IsLB) (e : cls L hL = cls M h.isLB) : IsBig k L := by
  have e' : ∀ m, cls _ (isLB_lbPow hL m) = cls _ (isLB_lbPow h.1 m) := fun m => by
    rw [cls_lbPow hL, cls_lbPow h.1, e]
  obtain ⟨D, hD, c, hc, hm⟩ := h.3
  exact ⟨hL, fun m => finite_coh_zero_twist_congr _ _ (e' m) (h.2 m), D, hD, c, hc,
    hm.mono fun m hm => by rwa [lineBundleGlobalSectionsDim_congr_picardClass _ _ (e' m)]⟩

theorem IsBig.of_lbIso (h : IsBig k M) (hL : L.IsLB) (e : LBIso L M) : IsBig k L :=
  h.of_cls_eq hL ((cls_eq_iff hL h.isLB).2 e)

theorem hasNonzeroSection_of_le_sectionBound {c : ℝ} (hc : 0 < c) {m D : ℕ} (hm : 1 ≤ m)
    (h : c * (m : ℝ) ^ D ≤ lbH0 k L) : HasNonzeroSec L :=
  lineBundleHasNonzeroSection_of_globalSectionsDim_pos (k := k) (Nat.cast_pos.1
    ((mul_pos hc (pow_pos (Nat.cast_pos.2 hm) D)).trans_le h))

theorem IsBig.frequently_hasNonzeroSec (h : IsBig k L) :
    ∃ᶠ m : ℕ in atTop, HasNonzeroSec (lbPow L m) :=
  have ⟨_, _, _, hc, hm⟩ := h.3
  (hm.and_eventually (eventually_ge_atTop 1)).mono fun _ hm =>
    hasNonzeroSection_of_le_sectionBound hc hm.2 hm.1

theorem IsBig.isPsEff [IsIntegral X] (h : IsBig k L) (hH : IsAmpleLB H) : IsPsEff L :=
  have ⟨_, hm, hm'⟩ := (h.frequently_hasNonzeroSec.and_eventually (eventually_ge_atTop 1)).exists
  isPsEff_of_hasNonzeroSec_pow hH h.1 hm' hm

theorem IsBig.of_pow {n : ℕ} (h : IsBig k (lbPow L n)) (hL : L.IsLB) (hn : 1 ≤ n)
    (hfin : ∀ m : ℕ, Module.Finite k (coh (twist (structureModule X) (lbPow L m)) 0)) :
    IsBig k L := by
  obtain ⟨D, hD, c, hc, hm⟩ := h.3
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  refine ⟨hL, hfin, D, hD, c / (n : ℝ) ^ D, by positivity, ?_⟩
  have ht : Tendsto (fun m : ℕ => n * m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hn) tendsto_id
  refine ht.frequently (hm.mono fun m hm => ?_)
  rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL (n * m)) (isLB_lbPow h.1 m)
    (by rw [cls_lbPow hL, cls_lbPow h.1, cls_lbPow hL, mul_nsmul])]
  refine le_of_eq_of_le ?_ hm
  rw [Nat.cast_mul, mul_pow]
  field_simp

section Proj

variable [IsIntegral X] {f : X ⟶ Sp k}
  (hf : ∀ r, algebraMap k Γ(X, ⊤) r = f.appTop ((Scheme.ΓSpecIso (.of k)).inv r))
  (hp : IsProjOver f)

include hf hp

theorem IsBig.of_cls_eq_add (hA : IsBig k A) (hB : B.IsLB) (h : HasNonzeroSec B) (hN : N.IsLB)
    (e : cls N hN = cls A hA.isLB + cls B hB) : IsBig k N := by
  have := isNoetherian_of_isProjOver hp
  have hfin := fun m => finite_coh_zero_twist_of_isProjOver hf hp (isLB_lbPow hN m)
  obtain ⟨D, hD, c, hc, hm⟩ := hA.3
  refine ⟨hN, hfin, D, hD, c, hc, hm.mono fun m hm => hm.trans (Nat.cast_le.2
    (lineBundleGlobalSectionsDim_le_of_picardClass_add (isLB_lbPow hN m) (isLB_lbPow hA.1 m) (isLB_lbPow hB m) ?_
      (h.pow hB m) (hfin m)))⟩
  rw [cls_lbPow hN, cls_lbPow hA.1, cls_lbPow hB, e, nsmul_add]

theorem IsBig.tens (hA : IsBig k A) (hB : B.IsLB) (h : HasNonzeroSec B) : IsBig k (tens A B) :=
  hA.of_cls_eq_add hf hp hB h (isLB_tens hA.isLB hB) rfl

theorem IsBig.pow (h : IsBig k L) {n : ℕ} (hn : 1 ≤ n) : IsBig k (lbPow L n) := by
  have := isNoetherian_of_isProjOver hp
  have hn' := isLB_lbPow h.1 n
  have hfin := fun m => finite_coh_zero_twist_of_isProjOver hf hp (isLB_lbPow hn' m)
  obtain ⟨D, hD, c, hc, hm⟩ := h.3
  refine ⟨hn', hfin, D, hD, c, hc, (hm.and_eventually (eventually_ge_atTop 1)).mono fun m hm =>
    hm.1.trans (Nat.cast_le.2 (lineBundleGlobalSectionsDim_le_of_picardClass_add (isLB_lbPow hn' m) (isLB_lbPow h.1 m)
      (isLB_lbPow (isLB_lbPow h.1 m) (n - 1)) ?_
      ((hasNonzeroSection_of_le_sectionBound hc hm.2 hm.1).pow (isLB_lbPow h.1 m) _) (hfin m)))⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [cls_lbPow hn', cls_lbPow (isLB_lbPow h.1 m), cls_lbPow h.1, cls_lbPow h.1,
    Nat.add_sub_cancel]
  module

theorem isBig_pow_iff (hL : L.IsLB) {n : ℕ} (hn : 1 ≤ n) : IsBig k (lbPow L n) ↔ IsBig k L :=
  ⟨fun h => h.of_pow hL hn fun m => finite_coh_zero_twist_of_isProjOver hf hp (isLB_lbPow hL m),
    fun h => h.pow hf hp hn⟩

end Proj

end Big

namespace ProjSpace

variable (k : Type) [Field k] (N : ℕ)

theorem topologicalKrullDim_eq : topologicalKrullDim (PSpace k N) = N := by
  have hc : ∀ i, topologicalKrullDim (chart k N i : Set (PSpace k N)) = N := fun i => by
    rw [topologicalKrullDim_eq_of_isEmbedding (chartι k N i).isOpenEmbedding.isEmbedding
      (congrArg SetLike.coe (opensRange_chartι k N i))]
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
      (R := MvPolynomial {j // j ≠ i} k)).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_)
    ((hc 0).ge.trans (topologicalKrullDim_subspace_le _ _))
  obtain ⟨i, hi⟩ := exists_mem_chart k N x
  exact ⟨_, (chart k N i).isOpen, hi, (hc i).le⟩

theorem algebraMap_top_eq (r : k) : algebraMap k Γ(PSpace k N, ⊤) r =
    (PSpace.str k N).appTop ((Scheme.ΓSpecIso (.of k)).inv r) := by
  rw [algebraMap_sections_eq, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem isProjOver_str : IsProjOver (PSpace.str k N) :=
  have := isProper_str k N
  (isAmple_projective_O_one k N).isProjOver _

theorem sectionDim_twistingSheaf_pow (m : ℕ) : lbH0 k (lbPow (O1 k N) m) = (m + N).choose N := by
  have h := (chi_eq_hdim_zero k fun _ hp => ProjCoh.subsingleton_coh_of_neg_le k N (n := m)
    (by omega) hp).symm.trans (ProjCoh.chi_sheafO k N m)
  rw [← Nat.cast_add, Ring.choose_natCast] at h
  exact Nat.cast_injective h

theorem isNef_twistingSheaf : IsNef k (O1 k N) := (isAmple_projective_O_one k N).isNef

theorem isBig_twistingSheaf : IsBig k (O1 k N) := by
  refine (isBig_iff (algebraMap_top_eq k N) (isProjOver_str k N) (topologicalKrullDim_eq k N)).2
    ⟨O1_isLB k N, (N.factorial : ℝ)⁻¹, by positivity, Frequently.of_forall fun m => ?_⟩
  rw [sectionDim_twistingSheaf_pow, ← div_eq_inv_mul]
  refine le_trans ?_ (Nat.pow_le_choose N (m + N))
  gcongr
  omega

theorem isPsEff_twistingSheaf : IsPsEff (O1 k N) := (isAmple_projective_O_one k N).isPsEff

theorem triv_nef_not_big : IsNef k (LB.triv (PSpace k (N + 1))) ∧
    IsPsEff (LB.triv (PSpace k (N + 1))) ∧ ¬ IsBig k (LB.triv (PSpace k (N + 1))) := by
  refine ⟨isNef_triv k _, (isGenerated_triv _).isPsEff (isAmple_projective_O_one k _), fun h => ?_⟩
  obtain ⟨-, c, hc, hm⟩ := (isBig_iff (algebraMap_top_eq k _) (isProjOver_str k _)
    (topologicalKrullDim_eq k _)).1 h
  have ht : Tendsto (fun m : ℕ => c * (m : ℝ) ^ (N + 1)) atTop atTop :=
    ((tendsto_pow_atTop N.succ_ne_zero).comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  obtain ⟨m, h₁, h₂⟩ := (hm.and_eventually (ht.eventually_gt_atTop 1)).exists
  rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow h.1 m) (isLB_lbPow (O1_isLB k _) 0)
    (by rw [cls_lbPow h.1, cls_lbPow (O1_isLB k _), cls_triv, zero_nsmul, nsmul_zero]),
    sectionDim_twistingSheaf_pow, zero_add, Nat.choose_self, Nat.cast_one] at h₁
  exact h₂.not_ge h₁

theorem not_isPsEff_dual_twistingSheaf :
    ¬ IsPsEff (dual (O1 k (N + 1))) ∧ ¬ IsBig k (dual (O1 k (N + 1))) := by
  have := isNoetherian_of_isProjOver (isProjOver_str k (N + 1))
  have h : ¬ IsPsEff (dual (O1 k (N + 1))) := fun h => by
    obtain ⟨r, hr, hs⟩ := h.exists_of_dual (isAmple_projective_O_one k _)
    have := ProjCoh.subsingleton_coh_zero k (N := N + 1) (by omega) (n := -r) (by omega)
    exact not_nontrivial _ (hasNonzeroSec_iff_nontrivial.1 hs)
  exact ⟨h, fun h' => h (h'.isPsEff (isAmple_projective_O_one k _))⟩

theorem isCompleteCurve_top : IsCompleteCurve k (⊤ : Closeds (PSpace k 1)) :=
  have := isProper_str k 1
  (isCompleteCurve_iff (algebraMap_top_eq k 1)).2 ⟨IrreducibleSpace.isIrreducible_univ _,
    (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id).trans
      (topologicalKrullDim_eq k 1)⟩

theorem not_isNef_dual_twistingSheaf : ¬ IsNef k (dual (O1 k 1)) :=
  (isAmple_projective_O_one k 1).not_isNef_dual (isCompleteCurve_top k)

example : lbH0 ℚ (lbPow (O1 ℚ 2) 2) = 6 := sectionDim_twistingSheaf_pow ℚ 2 2

example : 0 < interNumRed k (⊤ : Closeds (PSpace k 1)) ![O1 k 1] ∧
    interNumRed k (⊤ : Closeds (PSpace k 1)) ![dual (O1 k 1)] < 0 := by
  have h := (isAmple_projective_O_one k 1).interNumRed_pos (isCompleteCurve_top k)
  rw [(isCompleteCurve_top k).interNumRed_dual (isAmple_projective_O_one k 1) (O1_isLB k 1)]
  omega

example : IsNef k (lbPow (O1 k 2) 3) ∧ IsBig k (lbPow (O1 k 2) 3) ∧ IsPsEff (lbPow (O1 k 2) 3) :=
  have h := (isBig_twistingSheaf k 2).pow (algebraMap_top_eq k 2) (isProjOver_str k 2) (n := 3) (by norm_num)
  ⟨(isNef_twistingSheaf k 2).pow (isAmple_projective_O_one k 2) 3, h, h.isPsEff (isAmple_projective_O_one k 2)⟩

end ProjSpace

end GlobalTheory
