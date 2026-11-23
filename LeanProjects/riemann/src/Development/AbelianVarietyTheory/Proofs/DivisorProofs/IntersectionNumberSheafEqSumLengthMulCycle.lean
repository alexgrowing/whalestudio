import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubsetImageOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberEqGenericRankMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimAddOneLeOfSsubsetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthStalkNeTopOfNoGenerisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthStalkReducedClosedGenericPointEqRankStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SheafCycle

theorem dim_add_one_le {T : Type} [TopologicalSpace T] {A B : Set T} (hA : IsClosed A)
    (hAi : IsIrreducible A) (hBi : IsIrreducible B) (h : A ⊂ B) :
    topologicalKrullDim A + 1 ≤ topologicalKrullDim B :=
  GlobalTheory.T.topologicalKrullDim_add_one_le_of_irreducible_ssubset T A B hA hAi hBi h

theorem length_stalk_ne_top {X : Scheme.{0}} [IsLocallyNoetherian X] (F : X.Modules)
    [QCoh.IsFiniteQC F] (w : X) (h : ∀ y ∈ QCoh.support F, w ∈ closure {y} → y = w) :
    Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :) ≠ ⊤ :=
  GlobalTheory.T.length_stalk_ne_infty_of_no_generization X F w h

theorem length_stalk_pushforward_generic {X : Scheme.{0}} (Z : Closeds X)
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme]
    (G : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules) [QCoh.IsFiniteQC G] :
    Module.length (X.presheaf.stalk (redι Z (genericPoint _)))
      (((Scheme.Modules.pushforward (redι Z)).obj G).presheaf.stalk (redι Z (genericPoint _)) :) =
      (GlobalTheory.VB.genRank G : ℕ∞) :=
  GlobalTheory.T.length_stalk_reducedClosed_genericPoint_eq_rank X Z G

theorem lt_of_add_one_le_natCast {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ n) : a < n := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have e : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) := rfl
      rw [e, top_add] at h
      have : ((⊤ : ℕ∞)) ≤ (n : ℕ∞) := by exact_mod_cast h
      exact ENat.natCast_ne_top n (top_le_iff.1 this)
    | coe m =>
      have : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ n := by exact_mod_cast h
      have : m + 1 ≤ n := by exact_mod_cast this
      exact_mod_cast (by omega : m < n)

open QCoh

variable {κ : Type} [Field κ] {X : Scheme.{0}} [Algebra κ Γ(X, ⊤)]

theorem length_stalk_eq_zero_of_notMem {F : X.Modules} {w : X} (h : w ∉ support F) :
    Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :) = 0 := by
  haveI := notMem_support_iff.1 h
  exact Module.length_eq_zero

theorem dim_closure_le_suppDim {F : X.Modules} [IsFiniteQC F] {w : X} (h : w ∈ support F) :
    topologicalKrullDim (closure {w} : Set X) ≤ suppDim F := by
  rw [suppDim_eq_iSup_closure F]
  exact le_iSup₂ (f := fun x (_ : x ∈ support F) ↦ topologicalKrullDim (closure {x} : Set X)) w h

theorem eq_of_mem_closure {F : X.Modules} [IsFiniteQC F] {n : ℕ} (hd : suppDim F ≤ n) {w : X}
    (hw : topologicalKrullDim (closure {w} : Set X) = n) :
    ∀ y ∈ support F, w ∈ closure {y} → y = w := by
  intro y hy hwy
  have hsub : closure {w} ⊆ closure {y} :=
    isClosed_closure.closure_subset_iff.2 (Set.singleton_subset_iff.2 hwy)
  by_cases he : closure ({w} : Set X) = closure {y}
  · exact (inseparable_iff_closure_eq.2 he.symm).eq
  · have h1 := dim_add_one_le isClosed_closure isIrreducible_singleton.closure
      isIrreducible_singleton.closure (ssubset_of_subset_of_ne hsub he)
    have h2 := (dim_closure_le_suppDim hy).trans hd
    rw [hw] at h1
    have h3 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ n := by push_cast; exact h1.trans h2
    exact absurd (by exact_mod_cast h3 : n + 1 ≤ n) (by omega)

variable (κ) in

theorem interNumRed_eq_zero (hp : IsProjOver (strHom κ X)) {ι : Type} [Fintype ι]
    {P : ι → LB X} (hP : ∀ i, (P i).IsLB) (C : Closeds X)
    (hC : topologicalKrullDim (C : Set X) < (Fintype.card ι : ℕ)) : interNumRed κ C P = 0 := by
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  have : IsLocallyNoetherian X := (isNoetherian_of_isProjOver hp).toIsLocallyNoetherian
  have hAV : IsAmpleLB (A.pull (redι C)) := hA.pull_of_isClosedImmersion _
  haveI : IsFiniteQC ((Scheme.Modules.pushforward (redι C)).obj (structureModule _)) :=
    ProperFinite.isFiniteQC_pushforward (redι C) hAV _
  refine interNum_eq_zero_of_isProjOver (algebraMap_eq_strHom κ X) _ hp ?_ hP
  refine lt_of_le_of_lt (topologicalKrullDim_mono ?_) hC
  exact (support_pushforward_subset_image_of_isClosedImmersion (redι C) _).trans
    ((Set.image_subset_range _ _).trans (range_redι C).le)

theorem interNum_eq_sum_length_mul_interNumRed : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ X) → ∀ (ι : Type) [Fintype ι] (P : ι → LB X), (∀ i, (P i).IsLB) → ∀ (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F], GlobalTheory.QCoh.suppDim F ≤ (Fintype.card ι : ℕ) → ∀ S : Finset X, (∀ w ∈ GlobalTheory.QCoh.support F, topologicalKrullDim (closure ({w} : Set X)) = (Fintype.card ι : ℕ) → w ∈ S) → interNum κ F P = ∑ w ∈ S, ((Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :)).toNat : ℤ) * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  intro κ _ X _ hp ι _ P hP F hF
  have hf := algebraMap_eq_strHom κ X
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  set n := Fintype.card ι with hn
  let term : X.Modules → X → ℤ := fun E w ↦
    ((Module.length (X.presheaf.stalk w) (E.presheaf.stalk w :)).toNat : ℤ) *
      interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P

  have hsmall : ∀ (E : X.Modules) (w : X), topologicalKrullDim (closure ({w} : Set X)) < n →
      term E w = 0 := fun E w h ↦ by
    simp only [term, interNumRed_eq_zero κ hp hP ⟨closure {w}, isClosed_closure⟩ h, mul_zero]
  have hout : ∀ (E : X.Modules) (w : X), w ∉ support E → term E w = 0 := fun E w h ↦ by
    simp only [term, length_stalk_eq_zero_of_notMem h, ENat.toNat_zero, Nat.cast_zero, zero_mul]
  let Q : X.Modules → Prop := fun E ↦ suppDim E ≤ n → ∀ S : Finset X,
    (∀ w ∈ support E, topologicalKrullDim (closure ({w} : Set X)) = n → w ∈ S) →
      interNum κ E P = ∑ w ∈ S, term E w
  suffices H : Q F from H
  refine GlobalTheory.QCoh.devissage X Q ?_ ?_ ?_ F hF
  · intro E hE _ S _
    rw [interNum_eq_zero_of_isZero κ hE hP]
    refine (Finset.sum_eq_zero fun w _ ↦ hout E w ?_).symm
    rw [support_eq_empty_iff.2 hE]
    exact Set.notMem_empty w
  · intro C hC h₁ h₃ Q₁ Q₃ hd S hS
    haveI := h₁
    haveI := h₃
    haveI := hC.mono_f
    haveI := hC.epi_g
    have hd₁ : suppDim C.X₁ ≤ n := (suppDim_le_of_mono C.f).trans hd
    have hd₃ : suppDim C.X₃ ≤ n := (suppDim_le_of_epi C.g).trans hd
    rw [interNum_shortExact hC hP (finiteCohTwists_of_isProjOver hf _ hp)
        (finiteCohTwists_of_isProjOver hf _ hp),
      Q₁ hd₁ S (fun w hw ↦ hS w (support_subset_of_mono C.f hw)),
      Q₃ hd₃ S (fun w hw ↦ hS w (support_subset_of_epi C.g hw)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    by_cases hw : topologicalKrullDim (closure ({w} : Set X)) < n
    · rw [hsmall _ _ hw, hsmall _ _ hw, hsmall _ _ hw, add_zero]
    have hfin : ∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ n →
        Module.length (X.presheaf.stalk w) (E.presheaf.stalk w :) ≠ ⊤ := fun E _ hE ↦ by
      by_cases hm : w ∈ support E
      · have he : topologicalKrullDim (closure ({w} : Set X)) = n :=
          le_antisymm ((dim_closure_le_suppDim hm).trans hE) (not_lt.1 hw)
        exact length_stalk_ne_top E w (eq_of_mem_closure hE he)
      · rw [length_stalk_eq_zero_of_notMem hm]; exact ENat.zero_ne_top
    have hex := Module.length_eq_add_of_exact (stalkLinear C.f w) (stalkLinear C.g w)
      (stalkLinear_injective C.f w) (stalkLinear_surjective C.g w)
      ((exact_iff_stalkLinear C).1 hC.exact w)
    simp only [term]
    rw [hex, ENat.toNat_add (hfin C.X₁ hd₁) (hfin C.X₃ hd₃)]
    push_cast
    ring
  · intro Z hZ hsm G hG hd S hS
    haveI := hG
    haveI := isIntegral_red hZ
    have hAV : IsAmpleLB (A.pull (redι Z)) := hA.pull_of_isClosedImmersion _
    haveI hFq : IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj G) :=
      ProperFinite.isFiniteQC_pushforward (redι Z) hAV G
    have hsupp : support ((Scheme.Modules.pushforward (redι Z)).obj G) ⊆ (Z : Set X) :=
      (support_pushforward_subset_image_of_isClosedImmersion (redι Z) G).trans
        ((Set.image_subset_range _ _).trans (range_redι Z).le)
    by_cases hss : support ((Scheme.Modules.pushforward (redι Z)).obj G) = (Z : Set X)
    swap
    · exact hsm _ hFq (ssubset_of_subset_of_ne hsupp hss) hd S hS
    have hdZ : topologicalKrullDim (Z : Set X) ≤ n := by
      rw [← hss]; exact hd

    have hlt : ∀ w ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G),
        closure ({w} : Set X) ≠ Z → topologicalKrullDim (closure ({w} : Set X)) < n := by
      intro w hw hne
      have hwZ : closure ({w} : Set X) ⊆ Z :=
        Z.isClosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 (hsupp hw))
      have h1 := dim_add_one_le isClosed_closure isIrreducible_singleton.closure hZ
        (ssubset_of_subset_of_ne hwZ hne)
      exact lt_of_add_one_le_natCast (h1.trans hdZ)
    rcases lt_or_eq_of_le hdZ with hZlt | hZeq
    · rw [interNum_eq_zero_of_isProjOver hf _ hp (by rw [suppDim, hss]; exact hZlt) hP]
      refine (Finset.sum_eq_zero fun w _ ↦ ?_).symm
      by_cases hw : w ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G)
      · refine hsmall _ _ (lt_of_le_of_lt (topologicalKrullDim_mono ?_) hZlt)
        exact Z.isClosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 (hsupp hw))
      · exact hout _ _ hw
    set η := redι Z (genericPoint (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) with hη
    have hcl : closure ({η} : Set X) = Z := by
      rw [hη, ← Set.image_singleton, (redι Z).isClosedEmbedding.closure_image_eq,
        (genericPoint_spec _).def, Set.image_univ, range_redι]
    have hηs : η ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G) := by
      rw [hss]; exact (range_redι Z).le ⟨_, rfl⟩
    rw [Finset.sum_eq_single_of_mem η (hS η hηs (by rw [hcl]; exact hZeq)) fun w _ hne ↦ ?_]
    swap
    · by_cases hw : w ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G)
      · refine hsmall _ _ (hlt w hw fun e ↦ hne ?_)
        exact (inseparable_iff_closure_eq.2 (e.trans hcl.symm)).eq
      · exact hout _ _ hw
    simp only [term]
    rw [length_stalk_pushforward_generic Z G, ENat.toNat_natCast]
    have hC : (⟨closure {η}, isClosed_closure⟩ : Closeds X) = Z := Closeds.ext hcl
    rw [hC]
    letI : Algebra κ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) :=
      algebraΓOfHom (redι Z ≫ strHom κ X)
    have hfZ : ∀ r : κ, (redι Z).appTop (algebraMap κ Γ(X, ⊤) r) =
        algebraMap κ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r := fun r ↦ by
      rw [hf r]; rfl
    have hstr : strHom κ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = redι Z ≫ strHom κ X :=
      strHom_eq fun _ ↦ rfl
    have hpZ : IsProjOver (strHom κ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
      rw [hstr]; exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
    have hdimZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤
        (Fintype.card ι : ℕ) := by
      rw [topologicalKrullDim_red]; exact hdZ
    rw [interNum_pushforward_of_isClosedImmersion hfZ G hP,
      GlobalTheory.T.lineBundleIntersectionNumber_eq_genericRank_mul κ _ hpZ ι hdimZ G _ (fun i ↦ pull_isLB (hP i) _), interNumRed_def, interNumSub_def,
      interNumOn_def, interNum_pushforward_of_isClosedImmersion hfZ _ hP]

end GlobalTheory.SheafCycle
