import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupClosedSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StalkKrullDimension
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FiniteKrullDim
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

theorem ringKrullDim_stalk_eq_of_isOpenImmersion {Y W : Scheme.{u}} (g : Y ⟶ W)
    [AlgebraicGeometry.IsOpenImmersion g] (y : Y) :
    ringKrullDim (Y.presheaf.stalk y) = ringKrullDim (W.presheaf.stalk (g.base y)) := by
  have : IsIso (g.stalkMap y) := inferInstance
  have e : (W.presheaf.stalk (g.base y)) ≅ (Y.presheaf.stalk y) := asIso (g.stalkMap y)
  exact (ringKrullDim_eq_of_ringEquiv e.commRingCatIsoToRingEquiv).symm

theorem isNoetherianRing_stalk_of_isOpenImmersion {Y W : Scheme.{u}} (g : Y ⟶ W)
    [AlgebraicGeometry.IsOpenImmersion g] (y : Y)
    [IsNoetherianRing (W.presheaf.stalk (g.base y))] :
    IsNoetherianRing (Y.presheaf.stalk y) := by
  have : IsIso (g.stalkMap y) := inferInstance
  exact isNoetherianRing_of_ringEquiv _
    (CategoryTheory.asIso (g.stalkMap y)).commRingCatIsoToRingEquiv

theorem ringKrullDim_stalk_le_of_etaleChart {k : Type u} [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.IsLocallyNoetherian Y]
    {U : Y.Opens} {m : ℕ} (c : EtaleChart p U m) (y : Y) (hy : y ∈ U) :
    ringKrullDim (Y.presheaf.stalk y) ≤ ((m : ℕ∞) : WithBot ℕ∞) := by
  have := c.isEtale
  have hbase : U.ι.base (⟨y, hy⟩ : ↥U) = y := rfl
  have h0 : IsNoetherianRing (Y.presheaf.stalk (U.ι.base (⟨y, hy⟩ : ↥U))) := by
    rw [hbase]
    exact inferInstance
  have h1 : IsNoetherianRing (U.toScheme.presheaf.stalk (⟨y, hy⟩ : ↥U)) :=
    isNoetherianRing_stalk_of_isOpenImmersion U.ι (⟨y, hy⟩ : ↥U)
  have h2 := ringKrullDim_stalk_le_of_etale_affineSpace c.map (⟨y, hy⟩ : ↥U)
  have h3 := ringKrullDim_stalk_eq_of_isOpenImmersion U.ι (⟨y, hy⟩ : ↥U)
  rw [hbase] at h3
  rw [← h3]
  exact h2

theorem le_topologicalKrullDim_of_etaleChart {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (hU : (U : Set X).Nonempty) :
    ((m : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim ↥X := by
  have : AlgebraicGeometry.Etale c.map := c.isEtale
  have : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨x0, hx0⟩ := hU
  obtain ⟨V, hVaff, hxv, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := U.toScheme) (x := ⟨x0, hx0⟩) (U := ⊤) trivial
  obtain ⟨y, hy⟩ := exists_isClosed_singleton_of_isAffineOpen V hVaff ⟨_, hxv⟩
  have he1 : AlgebraicGeometry.Etale (Scheme.Opens.ι V) := inferInstance
  have he2 : AlgebraicGeometry.Etale (V.ι ≫ c.map) := inferInstance
  have : IsNoetherianRing (X.presheaf.stalk ((V.ι ≫ U.ι).base y)) := inferInstance
  have : IsNoetherianRing (V.toScheme.presheaf.stalk y) :=
    isNoetherianRing_stalk_of_isOpenImmersion (V.ι ≫ U.ι) y
  calc ((m : ℕ∞) : WithBot ℕ∞)
      = ringKrullDim (V.toScheme.presheaf.stalk y) :=
        (ringKrullDim_stalk_eq_of_etale_affineSpace (V.ι ≫ c.map) y hy).symm
    _ = ringKrullDim (X.presheaf.stalk ((V.ι ≫ U.ι).base y)) :=
        ringKrullDim_stalk_eq_of_isOpenImmersion (V.ι ≫ U.ι) y
    _ ≤ topologicalKrullDim ↥X :=
        ringKrullDim_stalk_le_topologicalKrullDim X ((V.ι ≫ U.ι).base y)

theorem ringKrullDim_stalk_eq_of_isBlowupAlongIdealSheaf_of_notMem {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (x₁ : X₁) (hx₁ : π.base x₁ ∉ Z.support) :
    ringKrullDim (X₁.presheaf.stalk x₁) = ringKrullDim (X.presheaf.stalk (π.base x₁)) := by
  obtain ⟨W, hWeq⟩ : ∃ W : X.Opens, (W : Set X) = (Z.support : Set X)ᶜ :=
    ⟨⟨(Z.support : Set X)ᶜ, Z.support.2.isOpen_compl⟩, rfl⟩
  have hW : ∀ x : X, x ∈ W → x ∉ Z.support := by
    intro x hxm
    have h2 : x ∈ (W : Set X) := hxm
    rw [hWeq] at h2
    exact h2
  have hxW : π.base x₁ ∈ W := by
    have h2 : π.base x₁ ∈ (Z.support : Set X)ᶜ := hx₁
    rw [← hWeq] at h2
    exact h2
  have hx : x₁ ∈ π ⁻¹ᵁ W := hxW
  have hiso : IsIso (π ∣_ W) := isIso_morphismRestrict_of_isBlowupAlongIdealSheaf hπ W hW
  have hoi : AlgebraicGeometry.IsOpenImmersion (π ∣_ W) := inferInstance
  have e1 := ringKrullDim_stalk_eq_of_isOpenImmersion (Scheme.Opens.ι (π ⁻¹ᵁ W))
    (⟨x₁, hx⟩ : ↥(π ⁻¹ᵁ W))
  have e2 := ringKrullDim_stalk_eq_of_isOpenImmersion ((π ∣_ W) ≫ Scheme.Opens.ι W)
    (⟨x₁, hx⟩ : ↥(π ⁻¹ᵁ W))
  rw [morphismRestrict_ι] at e2
  exact e1.symm.trans e2

theorem topologicalKrullDim_le_of_blowup_strictNormalCrossings {k : Type u} [Field k] {X X₁ : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    (π : X₁ ⟶ X) (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hZE : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    topologicalKrullDim ↥X₁ ≤ topologicalKrullDim ↥X := by
  have hXN : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian p
  have hX₁N : AlgebraicGeometry.IsLocallyNoetherian X₁ :=
    isLocallyNoetherian_of_isBlowupAlongIdealSheaf π Z hπ
  refine topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le X₁ _ ?_
  intro x₁
  by_cases hx : π.base x₁ ∈ Z.support
  · obtain ⟨U, hU, m, c, a, S, h1, h2, h3, h4⟩ := hZE.exists_etaleChart hx
    have hxU : x₁ ∈ π ⁻¹ᵁ U := hU
    obtain ⟨s, hs, hmem⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ h4 x₁ hxU
    have hle := ringKrullDim_stalk_le_of_etaleChart (π ≫ p)
      (blowupChartOfIsBlowup π c S hπ h4 s hs).chart x₁ hmem
    exact hle.trans (le_topologicalKrullDim_of_etaleChart p c ⟨π.base x₁, hU⟩)
  · rw [ringKrullDim_stalk_eq_of_isBlowupAlongIdealSheaf_of_notMem π Z hπ x₁ hx]
    exact ringKrullDim_stalk_le_topologicalKrullDim X (π.base x₁)

private theorem withBotSuccToNat_mono_of_lt_top {a b : WithBot ℕ∞} (hab : a ≤ b) (hb : b < ⊤) :
    withBotSuccToNat a ≤ withBotSuccToNat b := by
  revert hab hb
  induction a using WithBot.recBotCoe with
  | bot =>
      intro _ _
      rw [withBotSuccToNat_bot]
      exact Nat.zero_le _
  | coe x =>
      induction b using WithBot.recBotCoe with
      | bot =>
          intro hab _
          exact absurd (le_bot_iff.mp hab) (by simp)
      | coe y =>
          intro hab hb
          have hy : y ≠ ⊤ := fun h => hb.ne (by simp [h])
          obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hy
          have hxy : x ≤ ((n : ℕ) : ℕ∞) := WithBot.coe_le_coe.mp hab
          have hx : x ≠ ⊤ := by
            intro h
            rw [h, top_le_iff] at hxy
            exact absurd hxy (by simp)
          obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hx
          have hmn : m ≤ n := by exact_mod_cast hxy
          rw [withBotSuccToNat_coe, withBotSuccToNat_coe]
          have h1 : ((m : ℕ) : ℕ∞).toNat = m := by simp
          have h2 : ((n : ℕ) : ℕ∞).toNat = n := by simp
          omega

theorem krullDimSucc_le_of_blowup_strictNormalCrossings {k : Type u} [Field k] {X X₁ : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (π : X₁ ⟶ X) (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hZE : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    krullDimSucc X₁ ≤ krullDimSucc X := by
  have h1 : topologicalKrullDim ↥X₁ ≤ topologicalKrullDim ↥X :=
    topologicalKrullDim_le_of_blowup_strictNormalCrossings p π Z E hZE hπ
  have h2 : topologicalKrullDim ↥X < ⊤ :=
    topologicalKrullDim_lt_top_of_finiteType p inferInstance inferInstance
  simp only [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]
  exact withBotSuccToNat_mono_of_lt_top h1 h2

end FunctorialResolution.EmbeddedResolution
