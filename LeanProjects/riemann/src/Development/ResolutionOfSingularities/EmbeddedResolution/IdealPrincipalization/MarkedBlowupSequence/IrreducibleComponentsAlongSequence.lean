import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.CartierDivisorComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def EffectiveCartierSupportContainsNoComponent : Prop :=
  ∀ (X : Scheme.{u}) (D : X.IdealSheafData), Blowup.IsLocallyGeneratedByNonZeroDivisor D →
    ∀ C ∈ irreducibleComponents (X : Type u), ¬ C ⊆ (D.support : Set (X : Type u))

theorem effectiveCartierSupportContainsNoComponent : EffectiveCartierSupportContainsNoComponent.{u} :=
  fun _ _ hD _ hC => hD.not_irreducibleComponent_subset_support hC

theorem nonzeroOnComponents_comap_iso_hom {X Y : Scheme.{u}} (f : X ≅ Y) (I : Y.IdealSheafData)
    (h : NonzeroOnComponents I) : NonzeroOnComponents (I.comap f.hom) :=
  PrincipalizationIsoTransport.nonzeroOnComponents_comap_iso f I h

private theorem isPreirreducible_inter_of_isOpen {α : Type u} [TopologicalSpace α] {T U : Set α}
    (hT : IsPreirreducible T) (hU : IsOpen U) : IsPreirreducible (T ∩ U) := by
  intro V W hV hW hVne hWne
  obtain ⟨a, haTU, haV⟩ := hVne
  obtain ⟨b, hbTU, hbW⟩ := hWne
  obtain ⟨x, hxT, hx1, hx2⟩ :=
    hT (V ∩ U) (W ∩ U) (hV.inter hU) (hW.inter hU)
      ⟨a, haTU.1, haV, haTU.2⟩ ⟨b, hbTU.1, hbW, hbTU.2⟩
  exact ⟨x, ⟨hxT, hx1.2⟩, hx1.1, hx2.1⟩

private theorem isPreirreducible_preimage_val {α : Type u} [TopologicalSpace α] {U V : Set α}
    (hVU : V ⊆ U) (hV : IsPreirreducible V) :
    IsPreirreducible ((Subtype.val : U → α) ⁻¹' V) := by
  intro O₁ O₂ hO₁ hO₂ h₁ h₂
  obtain ⟨G₁, hG₁, rfl⟩ := isOpen_induced_iff.mp hO₁
  obtain ⟨G₂, hG₂, rfl⟩ := isOpen_induced_iff.mp hO₂
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  obtain ⟨x, hxV, hx1, hx2⟩ := hV G₁ G₂ hG₁ hG₂ ⟨a.1, ha.1, ha.2⟩ ⟨b.1, hb.1, hb.2⟩
  exact ⟨⟨x, hVU hxV⟩, hxV, hx1, hx2⟩

private theorem exists_irreducibleComponent_subset_of_section {α : Type u} {β : Type u}
    [TopologicalSpace α] [TopologicalSpace β]
    (f : α → β) (hf : Continuous f) (Uc : Set β) (hUc : IsOpen Uc)
    (g : ↥Uc → α) (hgc : Continuous g) (hgf : ∀ y, f (g y) = (y : β))
    (hgs : ∀ x, f x ∈ Uc → ∃ y, g y = x)
    (C : Set α) (hC : C ∈ irreducibleComponents α) (x₀ : α) (hx₀ : x₀ ∈ C) (hx₀U : f x₀ ∈ Uc)
    (K : Set β) (hK : IsClosed K) (hCK : C ⊆ f ⁻¹' K) :
    ∃ T ∈ irreducibleComponents β, T ⊆ K := by
  have hCirr : IsIrreducible C := hC.1
  have hVcOpen : IsOpen (f ⁻¹' Uc) := hUc.preimage hf
  have hWne : (C ∩ f ⁻¹' Uc).Nonempty := ⟨x₀, hx₀, hx₀U⟩
  have hWirr : IsIrreducible (C ∩ f ⁻¹' Uc) :=
    ⟨hWne, isPreirreducible_inter_of_isOpen hCirr.2 hVcOpen⟩
  have hImIrr : IsIrreducible (f '' (C ∩ f ⁻¹' Uc)) := hWirr.image f hf.continuousOn
  obtain ⟨T, hT, hTsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hImIrr
  have hTirr : IsIrreducible T := hT.1
  have hy₀T : f x₀ ∈ T := hTsub ⟨x₀, ⟨hx₀, hx₀U⟩, rfl⟩
  have hSne : (T ∩ Uc).Nonempty := ⟨f x₀, hy₀T, hx₀U⟩
  have hSirr : IsIrreducible (T ∩ Uc) := ⟨hSne, isPreirreducible_inter_of_isOpen hTirr.2 hUc⟩
  have hpre : IsIrreducible ((Subtype.val : ↥Uc → β) ⁻¹' (T ∩ Uc)) :=
    ⟨⟨⟨f x₀, hx₀U⟩, hy₀T, hx₀U⟩, isPreirreducible_preimage_val (fun y hy => hy.2) hSirr.2⟩
  have hVeq : f ⁻¹' (T ∩ Uc) = g '' ((Subtype.val : ↥Uc → β) ⁻¹' (T ∩ Uc)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hgs x hx.2
      refine ⟨y, ?_, hy⟩
      have h3 : f (g y) = (y : β) := hgf y
      rw [hy] at h3
      show (y : β) ∈ T ∩ Uc
      rw [← h3]
      exact hx
    · rintro ⟨y, hy, rfl⟩
      show f (g y) ∈ T ∩ Uc
      rw [hgf y]
      exact hy
  have hVirr : IsIrreducible (f ⁻¹' (T ∩ Uc)) := by
    rw [hVeq]
    exact hpre.image g hgc.continuousOn
  have hWV : C ∩ f ⁻¹' Uc ⊆ f ⁻¹' (T ∩ Uc) := fun x hx => ⟨hTsub ⟨x, hx, rfl⟩, hx.2⟩
  have hCcl : C ⊆ closure (C ∩ f ⁻¹' Uc) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen hCirr.2 hVcOpen hWne
  have hVC : f ⁻¹' (T ∩ Uc) ⊆ C :=
    subset_closure.trans (hC.2 hVirr.closure (hCcl.trans (closure_mono hWV)))
  have hVW : f ⁻¹' (T ∩ Uc) ⊆ C ∩ f ⁻¹' Uc := fun x hx => ⟨hVC hx, hx.2⟩
  have hTUK : T ∩ Uc ⊆ K := by
    intro y hy
    have hx : g ⟨y, hy.2⟩ ∈ C ∩ f ⁻¹' Uc := by
      refine hVW ?_
      show f (g ⟨y, hy.2⟩) ∈ T ∩ Uc
      rw [hgf ⟨y, hy.2⟩]
      exact hy
    have h5 : f (g ⟨y, hy.2⟩) ∈ K := hCK hx.1
    rw [hgf ⟨y, hy.2⟩] at h5
    exact h5
  refine ⟨T, hT, ?_⟩
  have hd : T ⊆ closure (T ∩ Uc) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen hTirr.2 hUc hSne
  exact hd.trans (closure_minimal hTUK hK)

private theorem coe_support_comap_eq_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData) :
    ((I.comap f).support : Set ↥X) = ⇑f.base ⁻¹' (I.support : Set ↥Y) := by
  ext x
  simp [Scheme.IdealSheafData.support_comap]

private theorem exists_section_off_center {X X' : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    ∃ g : ↥(((Z.support : Set ↥X))ᶜ) → ↥X', Continuous g ∧
      (∀ y, ⇑π.base (g y) = (y : ↥X)) ∧
      (∀ x : ↥X', ⇑π.base x ∈ ((Z.support : Set ↥X))ᶜ → ∃ y, g y = x) := by
  have := Blowup.blowupIsIsoOffCenter X X' π Z hπ
  have hinvhom : ∀ (A B : Scheme.{u}) (f : A ≅ B) (z : ↥B), f.hom.base (f.inv.base z) = z := by
    intro A B f z
    simp
  have hhominv : ∀ (A B : Scheme.{u}) (f : A ≅ B) (z : ↥A), f.inv.base (f.hom.base z) = z := by
    intro A B f z
    simp
  let e := asIso (π ∣_ Z.support.compl)
  have hmem : ∀ y : ↥(((Z.support : Set ↥X))ᶜ), (y : ↥X) ∈ Z.support.compl := fun y => y.2
  have hcont : Continuous (⇑e.inv.base) := e.inv.continuous
  refine ⟨fun y => (e.inv.base ⟨(y : ↥X), hmem y⟩).1, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp
      (hcont.comp (continuous_subtype_val.subtype_mk hmem))
  · intro y
    have h1 : e.hom.base (e.inv.base ⟨(y : ↥X), hmem y⟩) = ⟨(y : ↥X), hmem y⟩ :=
      hinvhom _ _ e _
    have h2 := morphismRestrict_base_coe π Z.support.compl (e.inv.base ⟨(y : ↥X), hmem y⟩)
    show ⇑π.base (e.inv.base ⟨(y : ↥X), hmem y⟩).1 = (y : ↥X)
    rw [← h2]
    exact congrArg Subtype.val h1
  · intro x hx
    have hx' : x ∈ π ⁻¹ᵁ Z.support.compl := hx
    refine ⟨⟨⇑π.base x, hx⟩, ?_⟩
    have hb : e.hom.base (⟨x, hx'⟩ : ↥(π ⁻¹ᵁ Z.support.compl).toScheme)
        = ⟨⇑π.base x, hmem ⟨⇑π.base x, hx⟩⟩ :=
      Subtype.ext (morphismRestrict_base_coe π Z.support.compl ⟨x, hx'⟩)
    have hc : e.inv.base (e.hom.base (⟨x, hx'⟩ : ↥(π ⁻¹ᵁ Z.support.compl).toScheme))
        = ⟨x, hx'⟩ := hhominv _ _ e _
    rw [hb] at hc
    exact congrArg Subtype.val hc

theorem nonzeroOnComponents_of_pow_mul_eq_comap (hcart : EffectiveCartierSupportContainsNoComponent.{u})
    {X X' : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (m : ℕ)
    (I : X.IdealSheafData) (I' : X'.IdealSheafData)
    (htr : (Z.comap π) ^ m * I' = I.comap π)
    (hI : NonzeroOnComponents I) : NonzeroOnComponents I' := by
  rw [nonzeroOnComponents_iff] at hI ⊢
  intro C hC hsub
  have hsub2 : C ⊆ ((I.comap π).support : Set ↥X') := by
    intro x hx
    have h1 : stalkIdeal I' x ≠ ⊤ := (mem_support_iff_stalkIdeal_ne_top I' x).mp (hsub hx)
    refine (mem_support_iff_stalkIdeal_ne_top (I.comap π) x).mpr ?_
    rw [← htr, stalkIdeal_mul]
    intro hcon
    have hle : stalkIdeal ((Z.comap π) ^ m) x * stalkIdeal I' x ≤ stalkIdeal I' x :=
      le_trans Ideal.mul_le_inf inf_le_right
    rw [hcon] at hle
    exact h1 (top_le_iff.mp hle)
  obtain ⟨x₀, hx₀C, hx₀E⟩ := Set.not_subset.mp (hcart X' (Z.comap π) hπ.1 C hC)
  have hx₀U : ⇑π.base x₀ ∈ ((Z.support : Set ↥X))ᶜ := by
    intro hmem
    refine hx₀E ?_
    rw [coe_support_comap_eq_preimage π Z]
    exact hmem
  have hCK : C ⊆ ⇑π.base ⁻¹' ((I.support : Set ↥X)) := by
    rw [← coe_support_comap_eq_preimage π I]
    exact hsub2
  obtain ⟨g, hgc, hgf, hgs⟩ := exists_section_off_center π Z hπ
  obtain ⟨T, hTcomp, hTK⟩ :=
    exists_irreducibleComponent_subset_of_section (⇑π.base) π.continuous (((Z.support : Set ↥X))ᶜ)
      (Z.support.2.isOpen_compl) g hgc hgf hgs C hC x₀ hx₀C hx₀U
      ((I.support : Set ↥X)) I.support.2 hCK
  exact hI T hTcomp hTK

namespace MarkedSequenceOfBlowups

theorem nonzeroOnComponents_ideal_of_isAdmissible (hcart : EffectiveCartierSupportContainsNoComponent.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) :
    ∀ t : ℕ, t ≤ s.toSequenceOfBlowups.length → NonzeroOnComponents (s.ideal t) := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [s.ideal_zero]
    exact nonzeroOnComponents_comap_iso_hom s.toSequenceOfBlowups.isoZero T.ideal hT.nonzeroOnComponents
  | succ n ih =>
    intro hn
    have hlt : n < s.toSequenceOfBlowups.length := hn
    refine nonzeroOnComponents_of_pow_mul_eq_comap hcart (s.toSequenceOfBlowups.transitionMapSucc n)
      (s.toSequenceOfBlowups.center n) (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt) T.mult
      (s.ideal n) (s.ideal (n + 1)) ?_ (ih (Nat.le_of_lt hlt))
    have he : Blowup.exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc n) (s.toSequenceOfBlowups.center n)
        = (s.toSequenceOfBlowups.center n).comap (s.toSequenceOfBlowups.transitionMapSucc n) := s.exceptionalDivisor_eq n
    rw [← he]
    exact s.ideal_succ n hlt

theorem centersContainNoComponent_ofMarkedSequence (hcart : EffectiveCartierSupportContainsNoComponent.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) :
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent := by
  intro i hi W hW hsub
  have hlt : i < s.toSequenceOfBlowups.length := hi
  have hnz := nonzeroOnComponents_ideal_of_isAdmissible hcart hT s i (Nat.le_of_lt hlt)
  rw [nonzeroOnComponents_iff] at hnz
  refine hnz W hW (hsub.trans ?_)
  intro x hx
  have h2 : x ∈ orderAtLeastLocus (s.ideal i) T.mult := s.center_order i hlt hx
  exact (mem_orderAtLeastLocus_one_iff (s.ideal i) x).mp
    (orderAtLeastLocus_subset_of_le (s.ideal i) hT.one_le_mult h2)

end MarkedSequenceOfBlowups

end FunctorialResolution.EmbeddedResolution

end
