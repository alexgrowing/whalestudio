import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeImageBirationalLinearSystemEqSelfInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeBotOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedStr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsIdealSpMapClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsExtendVanishCompactifiedFlagSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalIntegralWeightSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefLineBundleWeightGapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongerPublishedHypothesesImplyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProportionalPositiveVolumesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPrincipalisationBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivLeSubMulDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRestrIsoTens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralBaseChangeRationalFunctionFieldFiniteVStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimFieldBaseChangeLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionNefLeCuspFormGrowthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOrIsEmptyGenericMemberLinearSystemStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open Limits

namespace GlobalTheory.JetRank

theorem isProjOver_along {k : Type} [Field k] {X Z : Scheme.{0}} [Algebra k Γ(X, ⊤)] (hp : IsProjOver (strHom k X))
    (i : Z ⟶ X) [IsClosedImmersion i] : letI := algebraΓAlong k i; IsProjOver (strHom k Z) := by
  letI := algebraΓAlong k i
  obtain ⟨n, e, he, hs⟩ := hp
  exact ⟨n, i ≫ e, inferInstance, by rw [Category.assoc, hs, comp_strHom (appTop_algebraMap_along k i)]⟩

section Nef

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]

theorem dim_zeroScheme_le [IsIntegral X] [IsLocallyNoetherian X] {L : LB X} (hL : L.IsLB) {t : L.Sec} (ht : t ≠ 0) {d : ℕ}
    (hd : topologicalKrullDim X ≤ (d + 1 : ℕ)) : topologicalKrullDim (secIdeal hL t).subscheme ≤ d := by
  have := (mono_cutHom_structureModule_iff hL t).2 ((sec_ne_zero_iff t).1 ht)
  refine le_of_eq_of_le ?_ (suppDim_cut_le (structureModule _) hL t (d := d) (by rwa [QCoh.suppDim_structureModule]))
  rw [QCoh.suppDim, support_cut_eq_inter, QCoh.support_structureModule, Set.univ_inter]
  exact (topologicalKrullDim_eq_of_isEmbedding (secIdeal hL t).subschemeι.isClosedEmbedding.isEmbedding
    (secIdeal hL t).range_subschemeι).symm

theorem globalSections_dim_le_div_add_restriction [IsIntegral X] (hp : IsProjOver (strHom k X)) {L B : LB X} (hL : L.IsLB) (hB : B.IsLB) {t : L.Sec}
    (ht : t ≠ 0) : letI := algebraΓAlong k (secIdeal hL t).subschemeι
    lbH0 k B ≤ lbH0 k (LB.div B L) + lbH0 k (B.pull (secIdeal hL t).subschemeι) := by
  letI := algebraΓAlong k (secIdeal hL t).subschemeι
  have := isNoetherian_of_isProjOver hp
  have := (mono_cutHom_structureModule_iff hL t).2 ((sec_ne_zero_iff t).1 ht)
  have hF := finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k X) (structureModule X) hp
  have h := hdim₂_le k (Twist.shortExact_map hB (shortExact_cutComplex (structureModule X) hL t)) 0
    ((hF.twist (Twist.isLB_lbZPow hL (-1)) _ hB).finite 0) ((hF.cut hL t _ hB).finite 0)
  obtain ⟨e₁⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule X) (Twist.isLB_lbZPow hL (-1)) hB
    (LB.isLB_div hB hL) (by rw [cls_div hB hL, cls_lbZPow hL]; abel)
  obtain ⟨e₂, -⟩ := exists_cut_structureModule_iso hL t
  have := Twist.isQuasicoherent_twist (F := structureModule _) (LB.isLB_pull hB (secIdeal hL t).subschemeι)
  refine h.trans_eq (congrArg₂ (· + ·) (hdim_congr k 0 e₁) ((hdim_congr k 0 ((twistFunctor B).mapIso e₂)).trans
    ((hdim_congr k 0 (Twist.projIso B _ _)).symm.trans ?_)))
  exact hdim_pushforward k (appTop_algebraMap_along k _) _ 0

theorem interNum_nonneg (hN : GlobalTheory.Published.NefNumerics) (hp : IsProjOver (strHom k X)) {d : ℕ}
    (hd : topologicalKrullDim X ≤ d) {P : Fin d → LB X} (hP : ∀ i, IsNef k (P i)) :
    0 ≤ interNum k (structureModule X) P := by
  rcases hd.eq_or_lt with h | h
  · exact hN.1.interNum_nonneg hp h hP
  · exact (interNum_eq_zero_of_isProjOver (algebraMap_eq_strHom k X) _ hp
      (by rwa [QCoh.suppDim_structureModule, Fintype.card_fin]) fun i => (hP i).isLB).ge

theorem interNum_cons_nonneg [IsIntegral X] (hN : GlobalTheory.Published.NefNumerics) (hp : IsProjOver (strHom k X)) {d : ℕ}
    (hd : topologicalKrullDim X ≤ (d + 1 : ℕ)) {B : LB X} {P : Fin d → LB X} (hB : B.IsLB) (hs : HasNonzeroSec B)
    (hP : ∀ i, IsNef k (P i)) : 0 ≤ interNum k (structureModule X) (Fin.cons B P : Fin (d + 1) → LB X) := by
  obtain ⟨t, ht⟩ := hs
  have := isNoetherian_of_isProjOver hp
  have := (mono_cutHom_structureModule_iff hB t).2 ((sec_ne_zero_iff t).1 ht)
  letI := algebraΓAlong k (secIdeal hB t).subschemeι
  have hi := appTop_algebraMap_along k (secIdeal hB t).subschemeι
  rw [interNum_cons_eq_interNumSub hB t (fun i => (hP i).isLB)
    (finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k X) _ hp), interNumSub_def,
    interNumOn_eq_interNum_pull hi fun i => (hP i).isLB]
  exact interNum_nonneg hN (isProjOver_along hp _) (dim_zeroScheme_le hB ht hd)
    fun i => (hP i).pull_of_isClosedImmersion _ hi

theorem interNum_mono [IsIntegral X] (hN : GlobalTheory.Published.NefNumerics) (hp : IsProjOver (strHom k X)) {d : ℕ}
    (hd : topologicalKrullDim X ≤ (d + 1 : ℕ)) {P Q R : Fin (d + 1) → LB X} (hP : ∀ i, IsNef k (P i))
    (hQ : ∀ i, IsNef k (Q i)) (hR : ∀ i, (R i).IsLB) (hR' : ∀ i, IsNef k (R i) ∨ HasNonzeroSec (R i))
    (e : ∀ i, cls (Q i) (hQ i).isLB = cls (P i) (hP i).isLB + cls (R i) (hR i)) :
    interNum k (structureModule X) P ≤ interNum k (structureModule X) Q := by
  have hV := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) (structureModule X) hp (d := d + 1)
    (by rwa [QCoh.suppDim_structureModule])
  have key : ∀ s : Finset (Fin (d + 1)),
      interNum k (structureModule X) P ≤ interNum k (structureModule X) (s.piecewise Q P) := fun s => by
    induction s using Finset.induction_on with
    | empty => rw [Finset.piecewise_empty]
    | insert i s hi ih =>
      have hn : ∀ j, IsNef k (s.piecewise Q P j) := fun j => by
        by_cases h : j ∈ s
        · rw [Finset.piecewise_eq_of_mem _ _ _ h]; exact hQ j
        · rw [Finset.piecewise_eq_of_notMem _ _ _ h]; exact hP j
      rw [Finset.piecewise_insert, hV.interNum_update_of_cls_eq_add (by simp) (fun j => (hn j).isLB) i (hQ i).isLB
        (hP i).isLB (hR i) (e i), ← Finset.piecewise_eq_of_notMem s Q P hi, Function.update_eq_self]
      refine ih.trans (le_add_of_nonneg_right ?_)
      rcases hR' i with h | h
      · refine interNum_nonneg hN hp hd fun j => ?_
        by_cases hj : j = i
        · subst hj; rwa [Function.update_self]
        · rw [Function.update_of_ne hj]; exact hn j
      · rw [← interNum_comp_perm k _ (isLB_update (fun j => (hn j).isLB) i (hR i)) i.cycleRange.symm]
        refine (interNum_cons_nonneg hN hp hd (hR i) h fun j => hn (i.succAbove j)).trans_eq
          (congrArg _ (funext fun j => Fin.cases ?_ (fun j => ?_) j))
        · simp
        · simp
  simpa using key Finset.univ

theorem cons_const {α : Type*} (a : α) (d : ℕ) : (Fin.cons a (fun _ : Fin d => a) : Fin (d + 1) → α) = fun _ => a :=
  funext fun i => Fin.cases rfl (fun _ => rfl) i

theorem interNum_cons_le [IsIntegral X] (hN : GlobalTheory.Published.NefNumerics) (hp : IsProjOver (strHom k X)) {d : ℕ}
    (hd : topologicalKrullDim X ≤ (d + 1 : ℕ)) {B L L' P Q : LB X} (hB : IsNef k B) (hL : IsNef k L) (hL' : IsNef k L')
    (hP : P.IsLB) (hQ : IsNef k Q) (n : ℕ) (hs : HasNonzeroSec P) (e₁ : cls L' hL'.isLB = cls L hL.isLB + cls P hP)
    (e₂ : n • cls L' hL'.isLB = cls B hB.isLB + cls Q hQ.isLB) :
    interNum k (structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) ≤ n * topSelfIntersection k L' (d + 1) := by
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hp
  have hV := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) (structureModule X) hp (d := d + 1)
    (by rwa [QCoh.suppDim_structureModule])
  refine (interNum_mono hN hp hd (Q := Fin.cons (lbPow L' n) fun _ => L') (R := Fin.cons Q fun _ => P)
    (Fin.cases hB fun _ => hL) (Fin.cases (hL'.pow hA n) fun _ => hL') (Fin.cases hQ.isLB fun _ => hP)
    (Fin.cases (Or.inl hQ) fun _ => Or.inr hs) (Fin.cases ((cls_lbPow hL'.isLB _ _).trans e₂) fun _ => e₁)).trans_eq ?_
  have h := hV.interNum_update_of_cls_eq_zsmul (L := fun _ : Fin (d + 1) => L') (by simp) (fun _ => hL'.isLB) 0
    (isLB_lbPow hL'.isLB n) hL'.isLB n (by rw [cls_lbPow hL'.isLB, natCast_zsmul])
  rw [Function.update_eq_self 0 fun _ : Fin (d + 1) => L'] at h
  exact (congrArg _ (funext fun i => Fin.cases (by simp) (fun _ => by simp) i)).trans h

end Nef

theorem exists_step {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [a : Algebra k Γ(X, ⊤)]
    (hp : IsProjOver (strHom k X)) {d : ℕ} (hd : topologicalKrullDim X ≤ (d + 1 : ℕ)) {L : LB X} (hL : IsGenerated L) :
    ∃ (K : Type) (_ : Field K) (H : Scheme.{0}) (_ : Algebra K Γ(H, ⊤)) (ρ : H ⟶ X),
      IsProjOver (strHom K H) ∧ topologicalKrullDim H ≤ d ∧ (IsIntegral H ∨ IsEmpty H) ∧
      (∀ B : LB X, B.IsLB → lbH0 k B ≤ lbH0 k (LB.div B L) + lbH0 K (B.pull ρ)) ∧
      ∀ (e : ℕ) (P : Fin e → LB X), (∀ i, (P i).IsLB) →
        interNum K (structureModule H) (fun i => (P i).pull ρ) =
          interNum k (structureModule X) (Fin.cons L P : Fin (e + 1) → LB X) := by
  obtain ⟨f, rfl⟩ : ∃ f : X ⟶ Sp k, a = algebraΓOfHom f :=
    ⟨strHom k X, Algebra.algebra_ext _ _ (algebraMap_eq_strHom k X)⟩
  letI := algebraΓOfHom f
  rw [strHom_eq (f := f) fun _ => rfl] at hp
  have hLB := hL.isLB
  obtain ⟨N, b, hb⟩ := hL
  let K := FractionRing (MvPolynomial (Fin N) k)
  have H := IsPullback.of_hasPullback f (spMap (algebraMap k K))
  set π := pullback.fst f (spMap (algebraMap k K))
  set f' := pullback.snd f (spMap (algebraMap k K))
  letI := algebraΓOfHom f'
  obtain ⟨hpr, -⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB f).1 hp
  have := GlobalTheory.T.isIntegral_baseChange_rationalFunctionField_finiteVars k N X _ f f' π H
  obtain ⟨t, ht, hH⟩ := GlobalTheory.T.isIntegral_or_isEmpty_generic_member_linearSystem k N X _ f f' π H L hLB b hb
  have hp' : IsProjOver (strHom K (pullback f (spMap (algebraMap k K)))) := by
    rw [strHom_eq (f := f') fun _ => rfl]
    exact PosBaseChange.isProjOver_of_isPullback H hp
  have hL' := LB.isLB_pull hLB π
  have := isNoetherian_of_isProjOver hp'
  have := (mono_cutHom_structureModule_iff hL' t).2 ((sec_ne_zero_iff t).1 ht)
  set ι := (secIdeal hL' t).subschemeι
  letI := algebraΓAlong K ι
  refine ⟨K, inferInstance, _, algebraΓAlong K ι, ι ≫ π, isProjOver_along hp' ι, ?_, hH, fun B hB => ?_, fun e P hP => ?_⟩
  · exact dim_zeroScheme_le hL' ht ((GlobalTheory.T.topologicalKrullDim_fieldBaseChange_le k K X _ f f' π H).trans hd)
  · have h1 := globalSections_dim_le_div_add_restriction hp' hL' (LB.isLB_pull hB π) ht
    have e1 : lbH0 K (B.pull π) = lbH0 k B := FieldChangeInter.hdim_pull H hB 0
    have e2 : lbH0 K ((LB.div B L).pull π) = lbH0 k (LB.div B L) := FieldChangeInter.hdim_pull H (LB.isLB_div hB hLB) 0
    rw [e1, lineBundleGlobalSectionsDim_congr_picardClass (LB.isLB_div (LB.isLB_pull hB π) hL') (LB.isLB_pull (LB.isLB_div hB hLB) π) (by
      rw [cls_div (LB.isLB_pull hB π) hL', cls_pull (LB.isLB_div hB hLB), cls_div hB hLB, map_sub, cls_pull hB, cls_pull hLB]), e2,
      lineBundleGlobalSectionsDim_congr_picardClass (LB.isLB_pull (LB.isLB_pull hB π) ι) (LB.isLB_pull hB (ι ≫ π)) (by
        rw [cls_pull (LB.isLB_pull hB π), cls_pull hB, cls_pull hB, pull_comp])] at h1
    exact h1
  · rw [← FieldChangeInter.interNum_pull H (isLB_cons hLB hP)]
    have h1 := interNum_cons_eq_interNumSub (k := K) hL' t (P := fun i => (P i).pull π) (fun i => LB.isLB_pull (hP i) π)
      (finiteCohTwists_of_isProjOver (algebraMap_eq_strHom K _) _ hp')
    rw [interNumSub_def, interNumOn_eq_interNum_pull (appTop_algebraMap_along K ι) (fun i => LB.isLB_pull (hP i) π)] at h1
    refine Eq.trans (interNum_congr_cls K _ (fun i => LB.isLB_pull (hP i) _)
      (fun i => LB.isLB_pull (LB.isLB_pull (hP i) π) ι) fun i => ?_) (h1.symm.trans (congrArg _ (funext fun i => ?_)))
    · rw [cls_pull (LB.isLB_pull (hP i) π), cls_pull (hP i), cls_pull (hP i), pull_comp]
    · exact Fin.cases rfl (fun _ => rfl) i

theorem globalSections_dim_le_of_intersection_bound (hN : GlobalTheory.Published.NefNumerics) (d : ℕ) : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X]
    [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → topologicalKrullDim X ≤ d → ∀ {L : LB X}, IsGenerated L →
    ∀ (a : ℕ) {B : LB X}, B.IsLB → (∀ e, d = e + 1 →
      interNum k (structureModule X) (Fin.cons B (fun _ : Fin e => L) : Fin (e + 1) → LB X) < (a + 1) * topSelfIntersection k L d) →
    (lbH0 k B : ℤ) ≤ (a + d).choose d * topSelfIntersection k L d := by
  induction d with
  | zero =>
    intro k _ X _ _ hp hd L hL a B hB _
    have := isNoetherian_of_isProjOver hp
    have h0 : QCoh.suppDim (structureModule X) ≤ 0 := by rw [QCoh.suppDim_structureModule]; exact hd
    rw [topSelf_def, interNum_of_isEmpty, chi_eq_hdim_zero_of_suppDim_le_zero k h0, lineBundleGlobalSectionsDim_def,
      hdim_twist_of_suppDim_le_zero k h0 hB]
    simp
  | succ d ih =>
    intro k _ X _ _ hp hd L hL
    have := isNoetherian_of_isProjOver hp
    have hf := algebraMap_eq_strHom k X
    have hnef : IsNef k L := hL.isNef_of_isProjOver hp
    obtain ⟨K, _, H, _, ρ, hp', hd', hH, h₁, h₂⟩ := exists_step hp hd hL
    have hδ : topSelfIntersection K (L.pull ρ) d = topSelfIntersection k L (d + 1) := by
      rw [topSelf_def, topSelf_def, ← cons_const]; exact h₂ d (fun _ => L) fun _ => hL.isLB
    have hδ₀ : 0 ≤ topSelfIntersection k L (d + 1) := by
      rw [topSelf_def, ← cons_const]
      exact interNum_cons_nonneg hN hp hd hL.isLB hL.hasNonzeroSec fun _ => hnef
    have key : ∀ (a : ℕ) {B : LB X}, B.IsLB →
        interNum k (structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < a * topSelfIntersection k L (d + 1) →
        (lbH0 k B : ℤ) ≤ (a + d).choose (d + 1) * topSelfIntersection k L (d + 1) := by
      intro a
      induction a with
      | zero =>
        intro B hB h
        have : lbH0 k B = 0 := by
          by_contra h0
          have := interNum_cons_nonneg (P := fun _ => L) hN hp hd hB (lineBundleHasNonzeroSection_of_globalSectionsDim_pos (Nat.pos_of_ne_zero h0)) fun _ => hnef
          simp only [Nat.cast_zero, zero_mul] at h
          omega
        rw [this]; positivity
      | succ a iha =>
        intro B hB h
        have hD := LB.isLB_div hB hL.isLB
        have e := (diffVanish_chiPic_of_isProjOver hf (structureModule X) hp (d := d + 1)
          (by rw [QCoh.suppDim_structureModule]; exact hd)).interNum_cons_of_cls_eq_add le_rfl (P := fun _ : Fin d => L)
          (fun _ => hL.isLB) hB hD hL.isLB (by rw [cls_div hB hL.isLB, sub_add_cancel])
        rw [cons_const, ← topSelf_def] at e
        have i₁ := iha hD (by push_cast at h; linarith)
        have i₂ : (lbH0 K (B.pull ρ) : ℤ) ≤ (a + d).choose d * topSelfIntersection k L (d + 1) := by
          rcases hH with hH | hH
          · rw [← hδ]
            refine ih K H hp' hd' (hL.pull ρ) a (LB.isLB_pull hB ρ) fun m he => ?_
            subst he
            have h₃ := h₂ (m + 1) (Fin.cons B fun _ => L) (isLB_cons hB fun _ => hL.isLB)
            rw [hδ]
            refine lt_of_eq_of_lt (Eq.trans (congrArg _ (funext fun i => Fin.cases rfl (fun _ => rfl) i)) (h₃.trans ?_))
              (by exact_mod_cast h)
            rw [← interNum_comp_perm k _ (isLB_cons hB fun _ => hL.isLB) (Equiv.swap 0 1)]
            refine congrArg _ (funext fun i => ?_)
            refine Fin.cases rfl (fun i => Fin.cases rfl (fun i => ?_) i) i
            rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _)]
            rfl
          · have : lbH0 K (B.pull ρ) = 0 := by
              by_contra h0
              obtain ⟨s, hs⟩ := lineBundleHasNonzeroSection_of_globalSectionsDim_pos (Nat.pos_of_ne_zero h0)
              exact hs ((Vanishing.H0.bijective_ofSec_top (p := strHom K H)).1
                (Vanishing.H0.ext_germ fun y _ => hH.elim y))
            rw [this]; positivity
        have i₃ : (lbH0 k B : ℤ) ≤ lbH0 k (LB.div B L) + lbH0 K (B.pull ρ) := by exact_mod_cast h₁ B hB
        rw [show a + 1 + d = (a + d) + 1 by ring, Nat.choose_succ_succ']
        push_cast
        linarith
    intro a B hB h
    rw [show a + (d + 1) = a + 1 + d by ring]
    exact key (a + 1) hB (by exact_mod_cast h d rfl)

section

open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)

theorem imageDeg_eq_del (hQ : GlobalTheory.HSCore.Quoted) {F : Type} [Field F] [NumberField F] (S : LinSys F) {V Ω : Type}
    [AddCommGroup V] [Module F V] [Field Ω] [Algebra F Ω] (ev : V →ₗ[F] Ω) (b : Module.Basis (Fin S.N) F V) (x : S.Pt Ω)
    {a : Ω} (hV : S.IsVariety) (hb : S.BasePointFree) (hx : IsGenericPoint (ptOf x.1) Set.univ) (ha : a ≠ 0)
    (hc : S.coords x.1 = a • fun j => ev (b j)) (hG : GlobalTheory.DegVal.GenRatios ev) :
    (GlobalTheory.CompHt.imageDeg ev S.D : ℤ) = S.del := by
  have : IsIntegral S.Y := hV.isIntegral
  have hB : S.Birational := by
    refine ⟨_, hx, ?_⟩
    obtain ⟨τ, hτ⟩ : ∃ τ : S.Y.residueField (ptOf x.1) →+* Ω, spMap τ ≫ resPt (ptOf x.1) = x.1 :=
      ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω S.Y x.1⟩
    have h₁ : S.ratioField x.1 ≤ (S.ratioField (resPt (ptOf x.1))).map τ := by
      have e₁ := S.coords_spMap_comp (resPt (ptOf x.1)) τ
      have e₂ : S.baseHom x.1 = τ.comp (S.baseHom (resPt (ptOf x.1))) :=
        LinSys.baseHom_ptOver (S := S) ⟨x.1, by
          rw [← congrArg (· ≫ S.str) hτ, Category.assoc, S.comp_str]; exact (Spec.map_comp _ _).symm⟩
      rw [hτ] at e₁
      refine Subfield.closure_le.2 ?_
      rintro _ (⟨r, rfl⟩ | ⟨i, j, rfl⟩)
      · exact ⟨_, Subfield.subset_closure (Or.inl ⟨r, rfl⟩), by rw [e₂]; rfl⟩
      · exact ⟨_, Subfield.subset_closure (Or.inr ⟨i, j, rfl⟩), by rw [e₁, map_div₀]⟩
    have h₂ : S.ratioField x.1 = ⊤ := by
      obtain ⟨j, hj⟩ := Function.ne_iff.1 (hb.coords_ne_zero x.1)
      have hF : ∀ r, algebraMap F Ω r ∈ S.ratioField x.1 := fun r =>
        Subfield.subset_closure (Or.inl ⟨r, by rw [LinSys.baseHom_ptOver]⟩)
      have h₃ : ∀ v, a * ev v / S.coords x.1 j ∈ S.ratioField x.1 := fun v => by
        rw [← b.sum_repr v, map_sum, Finset.mul_sum, Finset.sum_div]
        refine sum_mem fun i _ => ?_
        rw [map_smul, Algebra.smul_def, mul_left_comm, mul_div_assoc]
        exact mul_mem (hF _) (Subfield.subset_closure (Or.inr ⟨i, j, by rw [congrFun hc i]; rfl⟩))
      have h₄ : GlobalTheory.DegVal.ratioField ev ≤ (S.ratioField x.1).toIntermediateField hF := by
        refine IntermediateField.adjoin_le_iff.2 ?_
        rintro _ ⟨v, w, rfl⟩
        have := div_mem (h₃ v) (h₃ w)
        rwa [div_div_div_cancel_right₀ hj, mul_div_mul_left _ _ ha] at this
      exact top_le_iff.1 fun y _ => h₄ (hG.2.ge trivial)
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨z, hz, e⟩ := h₂.ge.trans h₁ (trivial : τ y ∈ ⊤)
    exact τ.injective e ▸ hz
  obtain ⟨-, hdeg, hdim⟩ := ImageDegree.degree_image_eq_topSelf hQ F S hV hb hB
  obtain ⟨f, hf, -⟩ := hQ.chowInt F S.N S.D S.imageIdeal S.isHomogeneous_imageIdeal
    (GlobalTheory.Adelic.HeightExists.isPrime_imageIdeal hV) hdim
  rw [GlobalTheory.CompHt.imageIdeal_eq_coneIdeal_of_generic F Ω S x hx a _ ha hc] at hf hdeg
  rw [GlobalTheory.CompHt.IsImageDeg.imageDeg_eq ⟨S.N, b, f, hf⟩]
  exact hdeg

theorem exists_basis_fin (F V : Type) [Field F] [AddCommGroup V] [Module F V] [Module.Finite F V] :
    ∃ N, Nonempty (Module.Basis (Fin N) F V) := ⟨_, ⟨Module.finBasis F V⟩⟩

section Moving

open GlobalTheory.Vanishing.H0 GlobalTheory.LB GlobalTheory.TangentOrigin
open GlobalTheory.AllWt (secZ exOf)
open GlobalTheory.CompHt (genVal)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem exists_chart_val (h : GenFrEx Xo c) {u : AllWt.Weight Dw} (R : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))
    (Δ : Cartier ((baseId X Z U u).comap R.σ)) (hfree : FreeOnOpen X Z U u)
    {z : Sp (Om Z) ⟶ R.X} (hz : z ≫ toFlag R = X.ptY (genFr h Z)) (hO : ⊤ ≤ z ⁻¹ᵁ R.off) :
    ∃ (i : Δ.moving.ι) (a : Om Z), ptOf z ∈ Δ.moving.U i ∧ a ≠ 0 ∧ ∀ (g : Cusp Z U u) (w : space X Z U u),
      restr le_top w.1 = cuspSec X Z U u g →
      valR z (Δ.moving.U i) ((toSec (Δ.lift w)).f i) = a * genVal Z g.1 := by
  classical
  have e₁ : (z ≫ R.σ) ≫ inc₀ X Z = X.pt (genFr h Z) ≫ X.inc := by
    rw [Category.assoc, X.pt_inc]; exact hz
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ (ptOf ((z ≫ R.σ) ≫ inc₀ X Z))))
  have hk₂ : ⊤ ≤ ((z ≫ R.σ) ≫ inc₀ X Z) ⁻¹ᵁ X.F.U k := (le_iff_ptOf_mem _ _).2 hk
  have hk₁ : ⊤ ≤ (X.pt (genFr h Z) ≫ X.inc) ⁻¹ᵁ X.F.U k := e₁ ▸ hk₂
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor (genFr h Z) k hk₁
  have hQ₂ : X.F.ChartFr k ((z ≫ R.σ) ≫ inc₀ X Z) hk₂ Q := chartFr_congr e₁.symm hQ
  have hU : ⊤ ≤ (z ≫ R.σ) ⁻¹ᵁ U₀ X Z := by
    intro s _
    have := hO (Set.mem_univ s)
    rw [R.off_eq] at this
    exact this
  have hO₂ : ⊤ ≤ ((z ≫ R.σ) ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hU
  obtain ⟨n, hn⟩ := exists_chart Δ.isLB (ptOf z)
  have hz' : ptOf z ∈ R.off := (le_iff_ptOf_mem _ _).1 hO
  have hm : ptOf z ∈ ((L₀ X Z u).pull R.σ).U (flagIdx R u k) := (((common₀ X Z).pull R.σ).mem _ _ _).2 hk
  have hi : ptOf z ∈ Δ.moving.U (flagIdx R u k, n) := ⟨hm, hn⟩
  have hτ : valR z _ (Δ.t.f n) ≠ 0 := (valR_ne_zero_iff z hn _).2
    ((mem_nonzeroLocus_iff_basicOpen Δ.t hn).1 ((Δ.mem_nonzeroLocus _).2 (R.notMem_support hfree _ hz')))
  obtain ⟨T, hT0, hT⟩ : ∃ T : Om Z, T ≠ 0 ∧ ∀ f : secZ Xo c (exOf Dw u 0),
      evR Xo c f.1 (genFr h Z) = T * H0.val (B := X.LL (exOf Dw u 0)) ((z ≫ R.σ) ≫ inc₀ X Z) k hO₂ hk₂ (secOf X _ f) :=
    ⟨_, Units.ne_zero _, fun f => evR_eq_val_secOf f hO₂ hQ₂ ht⟩
  refine ⟨(flagIdx R u k, n), (valR z _ (Δ.t.f n) * T)⁻¹, hi, inv_ne_zero (mul_ne_zero hτ hT0),
    fun g w hw => ?_⟩
  have hTop : ⊤ ≤ z ⁻¹ᵁ (⊤ : R.X.Opens) := fun _ _ => trivial
  have hTop' : ⊤ ≤ (z ≫ R.σ) ⁻¹ᵁ (⊤ : (Y₀ X Z).Opens) := fun _ _ => trivial
  have hi' := (le_iff_ptOf_mem z _).2 hi
  have hm' := (le_iff_ptOf_mem z _).2 hm
  have hn' := (le_iff_ptOf_mem z _).2 hn
  have hm'' : ⊤ ≤ (z ≫ R.σ) ⁻¹ᵁ (L₀ X Z u).U (flagIdx R u k PUnit.unit) := by
    have hm₀ : R.σ (ptOf z) ∈ (L₀ X Z u).U (flagIdx R u k PUnit.unit) := mem_pull.1 hm
    exact (le_iff_ptOf_mem _ _).2 hm₀
  have v₁ : valR z (Δ.moving.U (flagIdx R u k, n)) ((toSec (Δ.lift w)).f (flagIdx R u k, n)) =
      H0.val z _ hTop hi' (Δ.lift w) := by
    have := H0.val_ofSec (p := R.str) z (flagIdx R u k, n) hTop hi' (toSec (Δ.lift w))
    rw [ofSec_toSec] at this
    rw [this, valR_eq_evalPt z _ hi']
  have v₂ := (divChart (LB.isLB_pull (isLB_L₀ X Z u) R.σ) Δ.isLB).val_mul (ofSec R.str ⊤ Δ.t) (Δ.lift w)
    (flagIdx R u k, n) z hTop hn' hi' hm'
  have v₃ : H0.val z _ hTop hm' (H0.pull R.σ le_top w.1) = H0.val (z ≫ R.σ) _ hTop' hm'' w.1 :=
    H0.val_pull R.σ le_top z _ hTop hm' hTop' hm'' w.1
  have v₄ := val_restr' (p := str₀ X Z) (le_top : U₀ X Z ≤ ⊤) (z ≫ R.σ) _ hTop' hU hm'' w.1
  have v₅ : H0.val (z ≫ R.σ) _ hU hm'' (cuspSec X Z U u g) = H0.val (B := X.LL (exOf Dw u 0)) ((z ≫ R.σ) ≫ inc₀ X Z) k hO₂ hk₂
      (secOf X _ ⟨g.1, cusp_le_secZ Z U _ g.2⟩) :=
    H0.val_pull (inc₀ X Z) le_rfl (z ≫ R.σ) _ hU hm'' hO₂ hk₂ _
  have v₆ : genVal Z g.1 = evR Xo c g.1 (genFr h Z) := rfl
  have v₇ : H0.val z _ hTop hn' (ofSec R.str ⊤ Δ.t) = valR z _ (Δ.t.f n) := by
    rw [H0.val_ofSec, valR_eq_evalPt z _ hn']
  have v₈ := hT ⟨g.1, cusp_le_secZ Z U _ g.2⟩
  rw [v₁, v₆, v₈, ← v₅, ← hw, v₄, ← v₃, ← Δ.incl_lift w]
  have v₉ : H0.val z _ hTop hm' (Δ.incl ⊤ (Δ.lift w)) = valR z _ (Δ.t.f n) * H0.val z _ hTop hi' (Δ.lift w) :=
    v₂.trans (congrArg (· * _) v₇)
  rw [v₉]
  field_simp

theorem topSelf_moving (hQ : GlobalTheory.HSCore.Quoted) {u : AllWt.Weight Dw} (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))
    (Δ : Cartier ((baseId X Z U u).comap M.σ)) (hV : IsVariety₀ X Z) (hD : 1 ≤ dimFlag Dw) (hE : Extends X Z U u)
    (hF : FreeOnOpen X Z U u) (hB : GlobalTheory.DegVal.BirOn U Z (wtOf Dw u 0)) :
    letI := algebraΓOfHom M.str
    IsGenerated Δ.moving ∧ topSelfIntersection c.F Δ.moving (dimFlag Dw) = GlobalTheory.CompHt.compDeg U Z (wtOf Dw u 0) := by
  have hG : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  have := finite_top hV.2.1 (isLB_L₀ X Z u)
  have : Module.Finite c.F (Cusp Z U u) := .equiv hE.equiv.symm
  obtain ⟨N, ⟨b⟩⟩ := exists_basis_fin c.F (Cusp Z U u)
  let S : LinSys c.F := ⟨M.X, M.str, dimFlag Dw, Δ.moving, Δ.isLB_moving, _, fun j => toSec (Δ.lift (hE.equiv (b j)))⟩
  have hS : S.IsVariety := ⟨M.smooth, M.proj,
    GlobalTheory.CompHS.Modif.geometricallyConnected_str _ _ _ _ _ M hV.1 hV.2.2 (dense_U₀ _ _), hD⟩
  have hb : S.BasePointFree := Δ.iSup_nonzeroLocus (b.map hE.equiv).span_eq
  refine ⟨⟨_, S.b, hb⟩, ?_⟩
  obtain ⟨z, hz, hO⟩ := exists_lift_genFr M hG
  have hstr : z ≫ S.str = spMap (algebraMap c.F (Om Z)) := by
    show z ≫ (toFlag M ≫ flagStr X) = _
    rw [← Category.assoc, hz, ptY_str]
  obtain ⟨i, a, hi, ha, hv⟩ := exists_chart_val hG M Δ hF hz hO
  obtain ⟨a', ha', h', -⟩ := S.exists_frame_change z i hi
  have key := imageDeg_eq_del hQ S (GlobalTheory.CompHt.genPoint Z (Cusp Z U u)) b ⟨z, hstr⟩ (a := a'⁻¹ * a) hS hb
    (isGenericPoint_of_lift M hG hz hO) (mul_ne_zero (inv_ne_zero ha') ha) (funext fun j => by
      have e := (h' (S.b j)).symm.trans (hv (b j) (hE.equiv (b j)) (hE.restr_equiv _))
      show S.val z _ = (a'⁻¹ * a) * genVal Z (b j).1
      rw [mul_assoc, ← e, inv_mul_cancel_left₀ ha']) hB
  rw [GlobalTheory.CompHt.compDeg, dimFlag_eq]
  exact key.symm

end Moving

theorem topSelf_pull (hN : GlobalTheory.Published.NefNumerics) {k : Type} [Field k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}
    (hs : SmoothOfRelativeDimension D p) (hp : IsProjOver p) (hc : GeometricallyConnected p) (hD : 1 ≤ D)
    (M : Modif p U D) (hc' : GeometricallyConnected M.str) :
    letI := algebraΓOfHom p
    letI := algebraΓOfHom M.str
    IsIntegral M.X ∧ IsProjOver (strHom k M.X) ∧ topologicalKrullDim M.X = D ∧
      (∀ B : LB Y, B.IsLB → lbH0 k (B.pull M.σ) = lbH0 k B) ∧
      ∀ B : LB Y, IsNef k B → IsNef k (B.pull M.σ) ∧ topSelfIntersection k (B.pull M.σ) D = topSelfIntersection k B D := by
  letI := algebraΓOfHom p
  letI := algebraΓOfHom M.str
  have hV : LinSys.IsVariety ⟨Y, p, D, LB.triv Y, LB.isLB_triv Y, 0, Fin.elim0⟩ := ⟨hs, hp, hc, hD⟩
  have hV' : LinSys.IsVariety ⟨M.X, M.str, D, LB.triv _, LB.isLB_triv _, 0, Fin.elim0⟩ := ⟨M.smooth, M.proj, hc', hD⟩
  have : IsIntegral Y := hV.isIntegral
  have : IsIntegral M.X := hV'.isIntegral
  have hd : topologicalKrullDim Y = D := ImageDegree.topologicalKrullDim_eq _ hV
  have hd' : topologicalKrullDim M.X = D := ImageDegree.topologicalKrullDim_eq _ hV'
  have e : strHom k Y = p := strHom_eq fun _ => rfl
  have e' : strHom k M.X = M.str := strHom_eq fun _ => rfl
  obtain ⟨hpr, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  obtain ⟨hpr', A', hA'⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB M.str).1 M.proj
  have : IsProper M.σ := IsProper.of_comp M.σ p
  have : IsProper (strHom k Y) := e ▸ hpr
  have h0 := GlobalTheory.T.modification_globalSectionsDim_pull_eq k Y p U D hs hp M
  have hp₁ : IsProjOver (strHom k Y) := by rw [e]; exact hp
  have hp₂ : IsProjOver (strHom k M.X) := by rw [e']; exact M.proj
  refine ⟨inferInstance, hp₂, hd', h0, fun B hB => ?_⟩
  have hB' : IsNef k (B.pull M.σ) := PosBaseChange.isNef_pull hB hA hA' M.σ M.σ.isClosedMap
  refine ⟨hB', ?_⟩
  have t := hN.2.2.tendsto hp₁ hd hB
  have t' := hN.2.2.tendsto hp₂ hd' hB'
  have e₁ : ∀ m, lbH0 k (lbPow (B.pull M.σ) m) = lbH0 k (lbPow B m) := fun m => by
    rw [← h0 _ (isLB_lbPow hB.isLB m)]
    exact lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hB'.isLB m) (LB.isLB_pull (isLB_lbPow hB.isLB m) _)
      (by rw [cls_lbPow hB'.isLB, cls_pull hB.1, cls_pull (isLB_lbPow hB.1 m), cls_lbPow hB.1, map_nsmul])
  simp only [e₁] at t'
  have := tendsto_nhds_unique t' t
  have hf : (D.factorial : ℝ) ≠ 0 := by positivity
  exact_mod_cast (div_left_inj' hf).1 this

theorem cls_nsmul {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a : Λ) (n : ℕ) :
    cls (B (n • a)) (C.isLB _) = n • cls (B a) (C.isLB _) :=
  (AddMonoidHom.mk' (fun a => cls (B a) (C.isLB a)) (cls_common_add C)).map_nsmul n a

section Comp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem finrank_cusp_le (hQ : GlobalTheory.HSCore.Quoted) (hPr : GlobalTheory.Published.Principalisation) (hV : IsVariety₀ X Z) (hD : 1 ≤ dimFlag Dw)
    (hC : ∀ la, CuspIso X Z U la) {u la : AllWt.Weight Dw} (hF : FreeOnOpen X Z U u)
    (hB : GlobalTheory.DegVal.BirOn U Z (wtOf Dw u 0)) {n a : ℕ} {v : ℝ} (hv : 0 ≤ v)
    (hG : GlobalTheory.CompHt.growthOn U Z (wtOf Dw u 0) = ENNReal.ofReal v)
    (hn : letI := algebraΓOfHom (str₀ X Z)
      IsNef c.F (L₀ X Z u) ∧ IsNef c.F (L₀ X Z la) ∧ IsNef c.F (L₀ X Z (n • u - la)))
    (h : n * v < (a + 1) * (GlobalTheory.CompHt.compDeg U Z (wtOf Dw u 0) : ℝ)) :
    Module.finrank c.F (Cusp Z U la) ≤ (a + dimFlag Dw).choose (dimFlag Dw) * GlobalTheory.CompHt.compDeg U Z (wtOf Dw u 0) := by
  letI := algebraΓOfHom (str₀ X Z)
  obtain ⟨hs, hp, hc⟩ := id hV
  have : ConnectedSpace (Y₀ X Z) := GeometricallyConnected.connectedSpace_of_subsingleton (str₀ X Z)
  obtain ⟨R⟩ := nonempty_resol hPr hs hp hc (dense_U₀ X Z).nonempty (common₀ X Z) hF hF
  letI := algebraΓOfHom R.str
  have hc' := GlobalTheory.CompHS.Modif.geometricallyConnected_str _ _ _ _ _ R.toModif hs hc (dense_U₀ _ _)
  obtain ⟨_, hp', hd', h0, hpull⟩ := topSelf_pull hQ.nef hs hp hc hD R.toModif hc'
  obtain ⟨hgen, hdeg⟩ := topSelf_moving hQ R.toModif R.Δ₁ hV hD (hC u).1 hF hB
  have hne : ∃ f : Cusp Z U u, f ≠ 0 := by
    by_contra! h0
    exact hB.1 (LinearMap.ext fun f => by rw [h0 f, map_zero]; rfl)
  have htop := GlobalTheory.T.topSelfIntersection_nef_le_cuspFormGrowth hQ.nef E H Dw l Xo c Y X Z r U u hV hD hC hne hn.1
  rw [hG, ENNReal.ofReal_le_ofReal_iff hv, ← (hpull _ hn.1).2] at htop
  obtain ⟨d, hd⟩ : ∃ d, dimFlag Dw = d + 1 := ⟨dimFlag Dw - 1, by omega⟩
  have hP : HasNonzeroSec R.Δ₁.P := by
    obtain ⟨z, hz⟩ := R.dense.nonempty
    exact ⟨_, sec_ne_zero_of_mem ((R.Δ₁.mem_nonzeroLocus z).2 (R.notMem_support hF z (R.off_eq.ge hz)))⟩
  have hch := interNum_cons_le hQ.nef hp' (d := d) (hd ▸ hd'.le) (hpull _ hn.2.1).1 (hgen.isNef_of_isProjOver hp')
    (hpull _ hn.1).1 R.Δ₁.isLB (hpull _ hn.2.2).1 n hP
    (by rw [cls_div (hpull _ hn.1).1.isLB R.Δ₁.isLB, sub_add_cancel])
    ((cls_nsmul R.com u n).symm.trans ((congrArg (fun a => cls (R.pb a) (R.com.isLB a)) (add_sub_cancel la (n • u)).symm).trans
      (cls_common_add R.com _ _)))
  have key := globalSections_dim_le_of_intersection_bound hQ.nef (dimFlag Dw) c.F R.X hp' hd'.le hgen a (hpull _ hn.2.1).1.isLB fun e he => by
    obtain rfl : d = e := by omega
    rw [hdeg]
    rw [congrArg (topSelfIntersection c.F _) hd.symm] at hch
    have h₁ : ((interNum c.F (structureModule R.X) (Fin.cons (R.pb la) (fun _ : Fin d => R.Δ₁.moving) : Fin (d + 1) → LB R.X) : ℤ) : ℝ) ≤
      n * (topSelfIntersection c.F (R.pb u) (dimFlag Dw) : ℝ) := by exact_mod_cast hch
    have h₂ := h₁.trans_lt ((mul_le_mul_of_nonneg_left htop n.cast_nonneg).trans_lt h)
    exact_mod_cast h₂
  rw [hdeg, h0 _ (isLB_L₀ X Z la), ← H0.finrank_top] at key
  have := finite_top hp (isLB_L₀ X Z la)
  have h₃ := (hC la).1.equiv.finrank_eq.trans_le (space X Z U la).finrank_le
  exact h₃.trans (by exact_mod_cast key)

end Comp

theorem gapGe_zero_of_antitone {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {la : AllWt.Weight Dw} (h : ∀ τ, Antitone (la τ)) : GapGe 0 la := fun τ k hk => by
  rw [gap, dif_pos hk, sub_nonneg]
  exact h τ (Fin.mk_le_mk.2 k.le_succ)

end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem rkC_le : GlobalTheory.CovTop.HypothesesX → Hypotheses2 → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u la : AllWt.Weight (T.Q.Dw j)) (n a : ℕ), GapGe (((CompHt.dimFlag (T.Q.Dw j) + 3) * ((CompHt.dimFlag (T.Q.Dw j) + 1).choose 2 + 4 * ((T.Q.Dw j).p + (T.Q.Dw j).q) + CompHt.dimFlag (T.Q.Dw j) + 3) : ℕ) : ℤ) u → (∀ τ, Antitone (la τ)) → (∀ τ, Antitone ((n : ℤ) • u τ - la τ)) → (n : ℝ) * CompHt.topDeg Y.U Z u < (a + 1) * Y.dg u Z → Y.rkC la Z ≤ ((a + CompHt.dimFlag (T.Q.Dw j)).choose (CompHt.dimFlag (T.Q.Dw j)) : ℕ) * Y.dg u Z := by
  intro hX hP2 hSi hTo hGD hQ hSe D T hT j hp hq hf hj Y e o hY Z u la n a hu hla hnu hlt
  have hP := GlobalTheory.T.stronger_published_hypotheses_imply hP2
  have hDe := dimFlag_eq (T.Q.Dw j)
  have hD : 1 ≤ FlagTan.dimFlag (T.Q.Dw j) :=
    Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  obtain ⟨TF⟩ := GlobalTheory.T.toroidal_flag_nonempty hP _ _ _ _ Y.d.Xo₂ Y.d.c₂ hD
  have hV := GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ TF Z hY.geo
  have hC : ∀ la, CuspIso TF.X Z Y.U la := fun la =>
    ⟨GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace D T.toCore j Y e o hY hf Z TF la, GlobalTheory.HSApp.vanBd_le_space D T.toCore j Y e o hY hf Z TF la⟩
  have hC0 : (0 : ℤ) ≤ (((CompHt.dimFlag (T.Q.Dw j) + 1).choose 2 : ℕ) : ℤ) := Int.natCast_nonneg _
  have hD0 : (0 : ℤ) ≤ (CompHt.dimFlag (T.Q.Dw j) : ℤ) := Int.natCast_nonneg _
  have hp0 : (0 : ℤ) ≤ ((T.Q.Dw j).p : ℤ) := Int.natCast_nonneg _
  have hq0 : (0 : ℤ) ≤ ((T.Q.Dw j).q : ℤ) := Int.natCast_nonneg _
  have hF : FreeOnOpen TF.X Z Y.U u := by
    refine GlobalTheory.T.toroidal_integral_weight_section hP hGD hQ hP2.q15 hP2.q16 hSi hTo.toroidalChartsForFan hSe _ _ _ _ _ _ TF Z _ Y.U hY.geo hD _ (fun τ k hk => ?_) (hC _)
    have h₁ := hu τ k hk
    have h₂ := gap_kap_le (Dw := T.Q.Dw j) τ hk
    rw [Pi.sub_apply, gap_sub, ← hDe]
    push_cast at h₁ h₂ ⊢
    nlinarith
  have hB : BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) := by
    refine GlobalTheory.T.weight_principalisation_bound hX hGD hQ hSi hP hP2.q15 hP2.q16 D T hT j hp hq Y e o hY u (fun τ a b hab => ?_) Z
    have h₁ := hu τ a (hab ▸ b.2)
    rw [gap_eq _ hab] at h₁
    push_cast at h₁ ⊢
    nlinarith
  have hu1 : GapGe 1 u := hu.mono (by push_cast; nlinarith)
  have hsa : ∀ τ, StrictAnti (u τ) := fun τ => by
    have key : ∀ (m : ℕ) (w : Fin m → ℤ), (∀ k, k + 1 < m → 1 ≤ gap w k) → StrictAnti w := fun m w hw => by
      cases m with
      | zero => exact fun a => a.elim0
      | succ m =>
        refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
        have := hw i (by omega)
        rw [show (i : ℕ) = (i.castSucc : ℕ) from rfl, gap_eq w (j := i.succ) rfl] at this
        omega
    exact key _ _ (hu1 τ)
  obtain ⟨hPr, hv⟩ := GlobalTheory.T.proportional_positive_volumes hP2 hSi hTo hSe D T hT j hp hq hf hj Y e o hY
  have hnef := GlobalTheory.T.nef_line_bundle_weight_gap hP hQ.nef hSe _ _ _ _ _ _ TF Z hY.geo
  have key := finrank_cusp_le (n := n) (a := a) (la := la) hQ hP2.q16 hV hD hC hF hB
    (mul_nonneg (hv Z).le (Int.cast_pos.2 (CompHt.vdm_pos hsa)).le) (hPr Z u hsa)
    ⟨hnef _ (hu1.mono zero_le_one), hnef _ (gapGe_zero_of_antitone hla), hnef _ (gapGe_zero_of_antitone fun τ => by
      simpa using hnu τ)⟩ hlt
  rw [← hDe] at key
  have := Vanishing.finite_top hV.2.1 (isLB_L₀ TF.X Z la)
  have : Module.Finite Y.d.c₂.F (Cusp Z Y.U la) := .equiv (hC la).1.equiv.symm
  exact_mod_cast (Submodule.finrank_le _).trans key

end

end GlobalTheory.JetRank

end
