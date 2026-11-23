import Mathlib
import Development.ResolutionOfSingularities.Statements
import Development.WeilBound.CoreStatements.ResolutionCharZero.WeakPair
import Development.WeilBound.CoreStatements.ResolutionCharZero.FromResIso
import Development.WeilBound.CoreStatements.ResolutionCharZero.FromResSnc
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsNil

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.ResK ReciprocityTheory.AnForm.R

namespace PositivityTheory.ResPlug.FromRes

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide FunctorialResolution

theorem isEffectiveCartier_top {X : Scheme.{0}} : IsEffectiveCartier (⊤ : X.IdealSheafData) := by
  intro x
  obtain ⟨U, hU, hx, -⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
  refine ⟨⟨U, hU⟩, 1, hx, Submonoid.one_mem _, ?_⟩
  simp [Ideal.span_singleton_one]

theorem isBlowup_iso_top {X Y : Scheme.{0}} (e : Y ≅ X) : IsBlowup e.hom (⊤ : X.IdealSheafData) := by
  refine ⟨by simpa using (isEffectiveCartier_top (X := Y)), fun T g _ => ⟨g ≫ e.inv, by simp, fun h hh => ?_⟩⟩
  rw [← hh]; simp

theorem isBlowupSeq_structMap {X : Scheme.{0}} (s : BlowupSequence X) :
    ∀ i, i ≤ s.length → Resolution.IsBlowupSeq (s.structMap i)
  | 0, _ => by
    have h0 : s.structMap 0 = s.isoZero.hom := by
      simp only [BlowupSequence.structMap, BlowupSequence.down]
      have : (homOfLE (Nat.zero_le 0)).op = 𝟙 (op (0 : ℕ)) := Subsingleton.elim _ _
      rw [this, CategoryTheory.Functor.map_id, Category.id_comp]
    rw [h0]
    simpa using Resolution.IsBlowupSeq.step ⊤ s.isoZero.hom .id (isBlowup_iso_top s.isoZero)
  | i + 1, hi => by
    have ih := isBlowupSeq_structMap s i (Nat.le_of_succ_le hi)
    rw [← s.structMap_down (Nat.le_succ i)]
    exact .step (s.center i) (s.down (Nat.le_succ i)) ih (s.isBlowup i hi)

theorem isBlowupSeq_topMap {X : Scheme.{0}} (s : BlowupSequence X) : Resolution.IsBlowupSeq s.topMap :=
  isBlowupSeq_structMap s s.length le_rfl

theorem resW_of_functorialResolution (H : FunctorialResolutionCharZero.{0}) : ResW := by
  intro K _ _ M D X i U ⟨hi, hred, hdense, hU⟩
  obtain ⟨R, hR, -, -⟩ := H
  have : IsProper (PSpace.str K M) := isProper_str K M
  let f : X ⟶ Spec (CommRingCat.of K) := i ≫ PSpace.str K M
  have : LocallyOfFiniteType f := by dsimp [f]; infer_instance
  have : QuasiCompact f := by dsimp [f]; infer_instance
  obtain ⟨hsm, -, hiso, hd, -, -⟩ := hR K X f
  have hproj : IsProjOver f := ⟨M, i, hi, rfl⟩
  refine ⟨_, (R K X f).topMap, (isBlowupSeq_topMap (R K X f)).isProjOver hproj, hsm, ?_, ?_⟩
  · have : Smooth (U.ι ≫ f) := hU.smooth D _
    exact isIso_morphismRestrict_of_le _ (le_smoothLocus f U)
  · exact dense_preimage (R K X f).topMap (V := f.smoothLocus) hd hdense

theorem hasSimpleNormalCrossings_nil {X : Scheme.{0}} {k : Type} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] : HasSimpleNormalCrossings p ([] : List X.IdealSheafData) := by
  have h := EmbeddedResolution.inStrictNormalCrossingPosition_nil p
  refine ⟨by simp, fun x => ?_⟩
  obtain ⟨U, hx, m, c, a, h1, h2, h3⟩ := h.2 x
  exact ⟨U, hx, m, c.map, c.comp_struct, c.isEtale, a, h1, h2, h3⟩

theorem princW_of_functorialPrincipalization (H : FunctorialPrincipalizationCharZero.{0}) : PrincW := by
  intro K _ _ d X g hd hp U hU
  obtain ⟨R, hR, -, -⟩ := H
  have hP : IsProper g := isProper_of_isProjOver hp
  have : Smooth g := hd.smooth d _
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNoetherian X := by first | infer_instance | exact ⟨⟩
  have : NoetherianSpace X := inferInstance
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
  have hsupp : I.support = ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ :=
    SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  have hdense : Dense (I.support : Set X)ᶜ := by rw [hsupp]; simpa using hU
  have hI : IsNonzeroOnComponents I := SncBlowup.not_subset_of_dense_compl hdense
  have hs := hR K X g I hI [] (hasSimpleNormalCrossings_nil g)
  set s := R K X g I hI [] (hasSimpleNormalCrossings_nil g) with hsdef
  have hsm : Smooth (s.topMap ≫ g) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hs
    exact h s.length le_rfl
  have hUc : I.support.compl = U := by
    ext x; simp [hsupp]
  have hiso := isIso_topMap_restrict_of_isPrincipalizingSequence hs
  rw [hUc] at hiso
  have hsnc := isStrictNormalCrossings_of_isPrincipalizingSequence_nil hs
  rw [hsupp] at hsnc
  exact ⟨_, s.topMap, (isBlowupSeq_topMap s).isProjOver hp, hsm, hiso, hsnc⟩

end PositivityTheory.ResPlug.FromRes
