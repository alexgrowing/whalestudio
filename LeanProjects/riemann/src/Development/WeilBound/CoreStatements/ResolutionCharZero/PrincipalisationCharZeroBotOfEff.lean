import Mathlib
import Development.ResolutionOfSingularities.Statements
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NotSubsetOfDenseCompl
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.WeilBound.CoreStatements.ResolutionCharZero.SupportStrictTransformUnion
import Development.ResolutionOfSingularities.HasSimpleNormalCrossingsOfInStrictNormalCrossing
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PrincipalisationOfCharZero
import Development.WeilBound.CoreStatements.ResolutionCharZero.ExistsFinsetComapProdIdealEqSpanProdCoord
import Development.WeilBound.CoreStatements.ResolutionCharZero.FromResIso
import Development.WeilBound.CoreStatements.ResolutionCharZero.FromResSnc

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup FunctorialResolution

abbrev FPrinc : Prop := FunctorialResolution.FunctorialPrincipalizationCharZero.{0}

def GBoundary : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    [LocallyOfFiniteType p] [QuasiCompact p] (E : Closeds X),
    (∀ x ∈ E, FinalTheorems.SncAt (Scheme.IdealSheafData.vanishingIdeal E) x) →
    ∃ L : List X.IdealSheafData, HasSimpleNormalCrossings p L ∧ (⋃ D ∈ L, (D.support : Set X)) = E

def GCentre : Prop :=
  ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of k)) [Smooth q] (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) (F : Closeds X),
    HasSimpleNormalCrossings q L → HasSimpleNormalCrossingsWith q Z L → (⋃ D ∈ L, (D.support : Set X)) = F →
    IsSncCentre F Z

def GEnd : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    [LocallyOfFiniteType p] [QuasiCompact p] (I : X.IdealSheafData) (L : List X.IdealSheafData)
    (s : BlowupSequence X), IsNonzeroOnComponents I → HasSimpleNormalCrossings p L →
    IsPrincipalizingSequence p I L s →
    FinalTheorems.EffCartier (I.comap s.topMap) ∧
      FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (I.comap s.topMap).support) ∧
      IsIso (s.topMap ∣_ I.support.compl)

end PositivityTheory.ResPlug.WeightsCompactStabilizer

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup FunctorialResolution

example (k : Type) [Field k] : Sp k = Spec (CommRingCat.of k) := rfl

theorem isIso_structMap_zero {X : Scheme.{0}} (s : BlowupSequence X) : IsIso (s.structMap 0) := by
  have : IsIso (s.down (le_refl 0)) := by
    unfold BlowupSequence.down
    have : (homOfLE (le_refl 0)).op = 𝟙 (Opposite.op 0) := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id]; infer_instance
  unfold BlowupSequence.structMap
  infer_instance

theorem blowup_top_of_isIso {X X' : Scheme.{0}} (f : X' ⟶ X) [IsIso f] : FinalTheorems.Blowup f ⊤ :=
  FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.of_isIso f

theorem biUnion_union_congr {α β : Type*} (L : List α) (A B : α → Set β) (C : Set β)
    (h : ∀ D, A D ∪ C = B D ∪ C) : (⋃ D ∈ L, A D) ∪ C = (⋃ D ∈ L, B D) ∪ C := by
  ext x
  simp only [Set.mem_union, Set.mem_iUnion, exists_prop]
  constructor
  · rintro (⟨D, hD, hx⟩ | hx)
    · have := (Set.ext_iff.1 (h D) x).1 (Or.inl hx)
      rcases this with hx | hx
      · exact Or.inl ⟨D, hD, hx⟩
      · exact Or.inr hx
    · exact Or.inr hx
  · rintro (⟨D, hD, hx⟩ | hx)
    · have := (Set.ext_iff.1 (h D) x).2 (Or.inl hx)
      rcases this with hx | hx
      · exact Or.inl ⟨D, hD, hx⟩
      · exact Or.inr hx
    · exact Or.inr hx

end PositivityTheory.ResPlug.WeightsCompactStabilizer

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup FunctorialResolution

theorem isSncBlowupSeq_of_principalizing (hC : GCentre) (hT : GTransform) {k : Type} [Field k] [CharZero k]
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of k)) [Smooth g] (E : Closeds X) (I : X.IdealSheafData)
    (L : List X.IdealSheafData) (hL : (⋃ D ∈ L, (D.support : Set X)) = E) (s : BlowupSequence X)
    (hs : IsPrincipalizingSequence g I L s) :
    ∃ E' : Closeds s.top, IsSncBlowupSeq g E s.topMap E' := by
  obtain ⟨ideal, boundary, h0, hb0, hZsm, hZsnc, -, -, hbsucc, -, -, hsm, hbsnc⟩ := hs
  have key : ∀ i, i ≤ s.length → ∃ Ei : Closeds (s.obj i), IsSncBlowupSeq g E (s.structMap i) Ei ∧
      (Ei : Set (s.obj i)) = ⋃ D ∈ boundary i, (D.support : Set (s.obj i)) := by
    intro i
    induction i with
    | zero =>
      intro _
      have := isIso_structMap_zero s
      have h := IsSncBlowupSeq.step (g := g) (E := E) (⊤ : X.IdealSheafData) (s.structMap 0) .id (by simpa using ‹Smooth g›)
        (by infer_instance) (fun x hx => by rw [Scheme.IdealSheafData.support_top] at hx; exact absurd (SetLike.mem_coe.2 hx) (by simp)) (blowup_top_of_isIso (s.structMap 0))
      rw [Category.comp_id] at h
      refine ⟨_, h, ?_⟩
      rw [hb0]
      ext x
      simp [totalTransform, ← hL, Scheme.IdealSheafData.support_comap]
    | succ i ih =>
      intro hi
      have hlt : i < s.length := hi
      obtain ⟨Ei, hseq, hEi⟩ := ih hlt.le
      have : Smooth (s.structMap i ≫ g) := hsm i hlt.le
      have hZ : IsSncCentre Ei (s.center i) :=
        hC k (s.obj i) (s.structMap i ≫ g) (s.center i) (boundary i) Ei (hbsnc i hlt.le) (hZsnc i hlt) hEi.symm
      have h := IsSncBlowupSeq.step (s.center i) (s.blowupMap i) hseq (hsm i hlt.le) (hZsm i hlt) hZ
        (s.isBlowup i hlt)
      have e : s.blowupMap i ≫ s.structMap i = s.structMap (i + 1) := s.structMap_down (Nat.le_succ i)
      rw [e] at h
      refine ⟨_, h, ?_⟩
      have : IsLocallyNoetherian (s.obj i) := LocallyOfFiniteType.isLocallyNoetherian (s.structMap i ≫ g)
      have : Smooth (s.structMap (i + 1) ≫ g) := hsm (i + 1) hi
      have : IsLocallyNoetherian (s.obj (i + 1)) := LocallyOfFiniteType.isLocallyNoetherian (s.structMap (i + 1) ≫ g)
      have hT' := fun D => hT (s.obj i) (s.obj (i + 1)) (s.blowupMap i) (s.center i) D inferInstance inferInstance
        (s.isBlowup i hlt)
      rw [hbsucc i hlt]
      have hU := biUnion_union_congr (boundary i) (fun D => ((strictTransform (s.blowupMap i) (s.center i) D).support : Set _))
        (fun D => (s.blowupMap i).base ⁻¹' (D.support : Set _)) ((s.blowupMap i).base ⁻¹' ((s.center i).support : Set _)) hT'
      ext x
      have hx := Set.ext_iff.1 hU x
      simp only [totalTransform, Closeds.coe_preimage, Closeds.coe_sup, Set.preimage_union, hEi, Set.preimage_iUnion,
        List.mem_append, List.mem_map, List.mem_singleton, Set.mem_iUnion, Set.mem_union, Set.mem_preimage,
        exists_prop] at hx ⊢
      rw [← hx]
      constructor
      · rintro (⟨a, ha, hxa⟩ | hx')
        · exact ⟨_, Or.inl ⟨a, ha, rfl⟩, hxa⟩
        · exact ⟨_, Or.inr rfl, by simpa [Scheme.IdealSheafData.support_comap] using hx'⟩
      · rintro ⟨D, (⟨a, ha, rfl⟩ | rfl), hxD⟩
        · exact Or.inl ⟨a, ha, hxD⟩
        · right; simpa [Scheme.IdealSheafData.support_comap] using hxD
  obtain ⟨E', h, -⟩ := key s.length le_rfl
  exact ⟨E', h⟩

end PositivityTheory.ResPlug.WeightsCompactStabilizer

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup FunctorialResolution

theorem principalisationCharZero_of (H : FPrinc) (hB : GBoundary) (hC : GCentre) (hE : GEnd) :
    PrincipalisationCharZero := by
  intro k _ _ d X g hd hqc hsep I E hI hEsnc
  have : SmoothOfRelativeDimension d g := hd
  have : Smooth g := SmoothOfRelativeDimension.smooth d g
  have : QuasiCompact g := hqc
  obtain ⟨L, hL, hLE⟩ := hB k X g E hEsnc
  obtain ⟨R, hR, -, -⟩ := H
  have hs := hR k X g I hI L hL
  obtain ⟨E', hseq⟩ := isSncBlowupSeq_of_principalizing hC gTransform g E I L hLE _ hs
  obtain ⟨h1, h2, h3⟩ := hE k X g I L _ hI hL hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsm, -⟩ := hs
  exact ⟨_, _, E', hseq, hsm _ le_rfl, h1, h2, h3⟩

end PositivityTheory.ResPlug.WeightsCompactStabilizer

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup FunctorialResolution

theorem fPrinc : FPrinc := FunctorialResolution.functorialPrincipalizationCharZero.{0}

theorem principalisationCharZero (hB : GBoundary) (hC : GCentre) (hE : GEnd) : PrincipalisationCharZero :=
  principalisationCharZero_of fPrinc hB hC hE

theorem principalisationCharZero_bot (hC : GCentre) (hE : GEnd) :
    ∀ (k : Type) [Field k] [CharZero k] (d : ℕ) (X : Scheme.{0}) (g : X ⟶ Sp k),
      SmoothOfRelativeDimension d g → QuasiCompact g → IsSeparated g →
      ∀ (I : X.IdealSheafData), (∀ C ∈ irreducibleComponents X, ¬ C ⊆ (I.support : Set X)) →
        ∃ (X' : Scheme.{0}) (s : X' ⟶ X) (E' : Closeds X'),
          IsSncBlowupSeq g ⊥ s E' ∧ Smooth (s ≫ g) ∧
          FinalTheorems.EffCartier (I.comap s) ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (I.comap s).support) ∧
          IsIso (s ∣_ I.support.compl) := by
  intro k _ _ d X g hd hqc hsep I hI
  have : SmoothOfRelativeDimension d g := hd
  have : Smooth g := SmoothOfRelativeDimension.smooth d g
  have : QuasiCompact g := hqc
  have hL : HasSimpleNormalCrossings g [] := ⟨fun D hD => by simp at hD, fun x => by
    obtain ⟨U, hx, m, c, h1, h2, a, h3, h4, h5⟩ :=
      (FunctorialResolution.hasSimpleNormalCrossings_of_inStrictNormalCrossingPosition
        (EmbeddedResolution.inStrictNormalCrossingPosition_nil g)).2 x
    exact ⟨U, hx, m, c, h1, h2, a, h3, h4, h5⟩⟩
  obtain ⟨R, hR, -, -⟩ := fPrinc
  have hs := hR k X g I hI [] hL
  obtain ⟨E', hseq⟩ := isSncBlowupSeq_of_principalizing hC gTransform g ⊥ I [] (by simp) _ hs
  obtain ⟨h1, h2, h3⟩ := hE k X g I [] _ hI hL hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsm, -⟩ := hs
  exact ⟨_, _, E', hseq, hsm _ le_rfl, h1, h2, h3⟩

end PositivityTheory.ResPlug.WeightsCompactStabilizer

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

end PositivityTheory.ResPlug.WeightsCompactStabilizer

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup FunctorialResolution

theorem gCentre : GCentre := PositivityTheory.ResPlug.BlowupCentre.gCentre

theorem principalisationCharZero' (hB : GBoundary) (hE : GEnd) : PrincipalisationCharZero :=
  principalisationCharZero hB gCentre hE

end PositivityTheory.ResPlug.WeightsCompactStabilizer

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup FunctorialResolution

def GIso : Prop :=
  ∀ (k : Type) [Field k] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (L : List X.IdealSheafData) (s : BlowupSequence X), IsPrincipalizingSequence p I L s →
    IsIso (s.topMap ∣_ I.support.compl)

def GSnc : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    [LocallyOfFiniteType p] [QuasiCompact p] (I : X.IdealSheafData) (L : List X.IdealSheafData)
    (s : BlowupSequence X), HasSimpleNormalCrossings p L → IsPrincipalizingSequence p I L s →
    IsStrictNormalCrossings (reducedPreimage s.topMap I.support)

def GEff : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    [LocallyOfFiniteType p] [QuasiCompact p] (I : X.IdealSheafData) (L : List X.IdealSheafData)
    (s : BlowupSequence X), IsNonzeroOnComponents I → HasSimpleNormalCrossings p L →
    IsPrincipalizingSequence p I L s → FinalTheorems.EffCartier (I.comap s.topMap)

theorem gEnd_of (ha : GIso) (hb : GSnc) (hc : GEff) : GEnd := by
  intro k _ _ X p _ _ _ I L s hI hL hs
  refine ⟨hc k X p I L s hI hL hs, ?_, ha k X p I L s hs⟩
  have h := hb k X p I L s hL hs
  have e : Scheme.IdealSheafData.vanishingIdeal (I.comap s.topMap).support = reducedPreimage s.topMap I.support := by
    unfold reducedPreimage
    congr 1
    ext x
    simp [Scheme.IdealSheafData.support_comap]
  rw [e]
  exact h

theorem principalisationCharZero'' (hB : GBoundary) (ha : GIso) (hb : GSnc) (hc : GEff) : PrincipalisationCharZero :=
  principalisationCharZero' hB (gEnd_of ha hb hc)

end PositivityTheory.ResPlug.WeightsCompactStabilizer

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup FunctorialResolution

theorem gIso : GIso := fun _ _ _ _ _ _ _ hs =>
  PositivityTheory.ResPlug.FromRes.isIso_topMap_restrict_of_isPrincipalizingSequence hs

theorem gSnc : GSnc := fun _ _ _ _ _ _ _ _ _ _ _ hL hs =>
  PositivityTheory.ResPlug.FromRes.isStrictNormalCrossings_of_isPrincipalizingSequence hL hs

theorem principalisationCharZero_of_eff (hB : GBoundary) (hc : GEff) : PrincipalisationCharZero :=
  principalisationCharZero'' hB gIso gSnc hc

end PositivityTheory.ResPlug.WeightsCompactStabilizer

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup FunctorialResolution

theorem principalisationCharZero_bot_of_eff (hc : GEff) :
    ∀ (k : Type) [Field k] [CharZero k] (d : ℕ) (X : Scheme.{0}) (g : X ⟶ Sp k),
      SmoothOfRelativeDimension d g → QuasiCompact g → IsSeparated g →
      ∀ (I : X.IdealSheafData), (∀ C ∈ irreducibleComponents X, ¬ C ⊆ (I.support : Set X)) →
        ∃ (X' : Scheme.{0}) (s : X' ⟶ X) (E' : Closeds X'),
          IsSncBlowupSeq g ⊥ s E' ∧ Smooth (s ≫ g) ∧
          FinalTheorems.EffCartier (I.comap s) ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (I.comap s).support) ∧
          IsIso (s ∣_ I.support.compl) :=
  principalisationCharZero_bot gCentre (gEnd_of gIso gSnc hc)

end PositivityTheory.ResPlug.WeightsCompactStabilizer
