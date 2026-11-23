import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.CartierDivisorComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDivisorBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.MaximalContactCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem mem_support_restrictIdeal_iff {Y : Scheme.{u}} (K : Y.IdealSheafData) (V : Y.Opens)
    (v : ↥V.toScheme) :
    v ∈ (restrictIdeal K V).support ↔ V.ι v ∈ K.support := by
  rw [restrictIdeal_eq_comap_ι]
  have h : (↑(K.comap V.ι).support : Set ↥V.toScheme) = ⇑V.ι ⁻¹' (↑K.support : Set ↥Y) :=
    support_comap_eq V.ι K
  exact Set.ext_iff.mp h v

theorem exists_opens_totalTransform_eq_of_notMem_support {X X₁ : Scheme.{u}}
    [IsLocallyNoetherian X₁] (π : X₁ ⟶ X) (Z D : X.IdealSheafData) (x₁ : ↥X₁)
    (hx₁ : π x₁ ∉ Z.support) :
    ∃ V : X₁.Opens, x₁ ∈ V ∧
      restrictIdeal (D.comap π) V =
        restrictIdeal (Blowup.strictTransform π Z D) V * restrictIdeal (Blowup.exceptionalIdeal π Z) V ^ 1 := by
  refine ⟨π ⁻¹ᵁ Z.support.compl, hx₁, ?_⟩
  rw [restrictIdeal_strictTransform_eq_comap_of_le_compl π Z D _ le_rfl,
    restrictIdeal_exceptionalIdeal_eq_top_of_le_compl π Z _ le_rfl, pow_one,
    Scheme.IdealSheafData.mul_top]

theorem inter_support_subset_support_of_mem_coordIdeal {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (Z D : X.IdealSheafData) (S : Finset (Fin m)) (j : Fin m) (hj : j ∈ S)
    (hZ : restrictIdeal Z U = c.coordIdeal S)
    (hD : restrictIdeal D U = c.coordIdeal {j}) :
    (↑Z.support : Set ↥X) ∩ (U : Set ↥X) ⊆ (↑D.support : Set ↥X) := by
  have hle : restrictIdeal D U ≤ restrictIdeal Z U := by
    rw [hD, hZ]
    exact c.coordIdeal_mono (Finset.singleton_subset_iff.mpr hj)
  intro x hx
  obtain ⟨v, hv⟩ : ∃ v : ↥U.toScheme, U.ι v = x := ⟨⟨x, hx.2⟩, rfl⟩
  have h1 : v ∈ (restrictIdeal Z U).support := by
    rw [mem_support_restrictIdeal_iff, hv]
    exact hx.1
  have h2 : v ∈ (restrictIdeal D U).support := Scheme.IdealSheafData.support_antitone hle h1
  rw [mem_support_restrictIdeal_iff, hv] at h2
  exact h2

theorem not_inter_support_subset_support_of_notMem_coordIdeal {X : Scheme.{u}} {k : Type u}
    [Field k] [NoetherianSpace ↥X] (p : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens}
    (hU : IsAffineOpen U) {m : ℕ} (c : EtaleChart p U m) (Z D : X.IdealSheafData)
    (S : Finset (Fin m)) (j : Fin m) (hj : j ∉ S)
    (hZ : restrictIdeal Z U = c.coordIdeal S)
    (hD : restrictIdeal D U = c.coordIdeal {j})
    (x : ↥X) (hxU : x ∈ U) (hxZ : x ∈ Z.support) :
    ¬ ((↑Z.support : Set ↥X) ∩ (U : Set ↥X) ⊆ (↑D.support : Set ↥X)) := by
  intro hsub
  obtain ⟨i, hi⟩ := exists_complOrderEmb_eq m S hj
  have hD' : restrictIdeal D U = c.coordIdeal {complOrderEmb m S i} := by
    rw [hi]; exact hD
  have hG : restrictIdeal (D.comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U)
      = (c.restrictToSubscheme hU Z S hZ).coordIdeal {i} :=
    c.restrictToSubscheme_coordIdeal_singleton hU Z S hZ i D hD'
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (restrictIdeal (D.comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U)) := by
    refine isLocallyGeneratedByNonZeroDivisor_of_locally_coordIdeal
      (p := (Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p)) _ ?_
    intro y
    refine ⟨⊤, trivial, m - S.card, (c.restrictToSubscheme hU Z S hZ).restrictOpens ⊤,
      Or.inr ⟨i, ?_⟩⟩
    rw [hG]
    exact (c.restrictToSubscheme hU Z S hZ).restrictIdeal_coordIdeal ⊤ {i}
  have hall : ∀ y : ↥(Z.subschemeι ⁻¹ᵁ U).toScheme,
      y ∈ (restrictIdeal (D.comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U)).support := by
    intro y
    rw [mem_support_restrictIdeal_iff]
    have hyU : Z.subschemeι ((Z.subschemeι ⁻¹ᵁ U).ι y) ∈ (U : Set ↥X) := y.2
    have hyZ : Z.subschemeι ((Z.subschemeι ⁻¹ᵁ U).ι y) ∈ (↑Z.support : Set ↥X) := by
      rw [← Scheme.IdealSheafData.range_subschemeι Z]
      exact Set.mem_range_self _
    have hmem : Z.subschemeι ((Z.subschemeι ⁻¹ᵁ U).ι y) ∈ (↑D.support : Set ↥X) :=
      hsub ⟨hyZ, hyU⟩
    have h2 : ((Z.subschemeι ⁻¹ᵁ U).ι y) ∈
        (↑(D.comap Z.subschemeι).support : Set ↥Z.subscheme) := by
      rw [support_comap_eq Z.subschemeι D]
      exact hmem
    exact h2
  obtain ⟨z, hz⟩ : ∃ z : ↥Z.subscheme, Z.subschemeι z = x := by
    have hxr : x ∈ Set.range (⇑Z.subschemeι) := by
      rw [Scheme.IdealSheafData.range_subschemeι Z]
      exact hxZ
    exact hxr
  have hzU : z ∈ Z.subschemeι ⁻¹ᵁ U := by
    show Z.subschemeι z ∈ U
    rw [hz]
    exact hxU
  obtain ⟨y₀, -⟩ : ∃ y₀ : ↥(Z.subschemeι ⁻¹ᵁ U).toScheme, (Z.subschemeι ⁻¹ᵁ U).ι y₀ = z :=
    ⟨⟨z, hzU⟩, rfl⟩
  exact hcart.not_irreducibleComponent_subset_support
    (irreducibleComponent_mem_irreducibleComponents y₀) (fun w _ => hall w)

theorem comap_eq_strictTransform_mul_exceptionalIdeal_pow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ Z : T.scheme.IdealSheafData,
      AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
      HasStrictNormalCrossingsWith T.structMap Z T.boundary →
      ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
      ∀ D ∈ T.boundary, ∀ x' : ↥X',
        ∃ (U' : X'.Opens) (ε : ℕ), x' ∈ U' ∧ (ε = 0 ∨ ε = 1) ∧
          (ε = 1 ↔ ∃ V : T.scheme.Opens, π x' ∈ V ∧
            ((↑Z.support : Set ↥T.scheme) ∩ (V : Set ↥T.scheme)) ⊆ (↑D.support : Set ↥T.scheme)) ∧
          (D.comap π).comap U'.ι =
            (Blowup.strictTransform π Z D).comap U'.ι * ((Blowup.exceptionalIdeal π Z).comap U'.ι) ^ ε := by
  intro T hV Z _hZsm hsnc X' π hπ D hD x'
  have : AlgebraicGeometry.IsNoetherian T.scheme := hV.isNoetherian
  have : NoetherianSpace ↥T.scheme := inferInstance
  have : AlgebraicGeometry.IsNoetherian X' := isNoetherian_of_isBlowupAlongIdealSheaf hπ
  have : AlgebraicGeometry.IsLocallyNoetherian X' := inferInstance
  by_cases hx : π x' ∈ Z.support
  · obtain ⟨U, hxU, m, c, a, S, _hinj, hnone, hsome, hZU⟩ := hsnc.exists_etaleChart hx
    obtain ⟨i, hi, hDi⟩ := List.mem_iff_getElem.mp hD
    have hx'U : x' ∈ π ⁻¹ᵁ U := hxU
    obtain ⟨s, hs, B, hx'B⟩ :
        ∃ (s : Fin m) (_ : s ∈ S) (B : BlowupChart π c S s), x' ∈ B.domain := by
      obtain ⟨s, hs, hmem⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZU x' hx'U
      exact ⟨s, hs, _, hmem⟩
    cases hai : a i with
    | none =>
      have hDtop : restrictIdeal D U = ⊤ := by
        have h1 := hnone i hi hai
        rwa [hDi] at h1
      refine ⟨B.domain, 0, hx'B, Or.inl rfl, ?_, ?_⟩
      · refine ⟨fun h0 => absurd h0 (by omega), fun hV' => ?_⟩
        obtain ⟨V, hxV, hsubV⟩ := hV'
        exact absurd (hsubV ⟨hx, hxV⟩)
          (notMem_support_of_restrictIdeal_eq_top D U _ hxU hDtop)
      · show restrictIdeal (D.comap π) B.domain =
          restrictIdeal (Blowup.strictTransform π Z D) B.domain *
            restrictIdeal (Blowup.exceptionalIdeal π Z) B.domain ^ 0
        rw [B.restrictIdeal_comap_top D hDtop, B.restrictIdeal_strictTransform_of_eq_top Z D hDtop,
          pow_zero, mul_one]
    | some t =>
      have hDU : restrictIdeal D U = c.coordIdeal {t} := by
        have h1 := hsome i hi t hai
        rwa [hDi] at h1
      by_cases htS : t ∈ S
      · have hcrit : ∃ V : T.scheme.Opens, π x' ∈ V ∧
            ((↑Z.support : Set ↥T.scheme) ∩ (V : Set ↥T.scheme)) ⊆
              (↑D.support : Set ↥T.scheme) :=
          ⟨U, hxU,
            inter_support_subset_support_of_mem_coordIdeal T.structMap c Z D S t htS hZU hDU⟩
        refine ⟨B.domain, 1, hx'B, Or.inr rfl, ⟨fun _ => hcrit, fun _ => rfl⟩, ?_⟩
        show restrictIdeal (D.comap π) B.domain =
          restrictIdeal (Blowup.strictTransform π Z D) B.domain *
            restrictIdeal (Blowup.exceptionalIdeal π Z) B.domain ^ 1
        by_cases hts : t = s
        · rw [hts] at hDU
          rw [B.restrictIdeal_comap_coordIdeal_self D hDU,
            B.restrictIdeal_strictTransform_coordIdeal_self Z D hs hZU hDU,
            B.restrictIdeal_exceptionalIdeal Z hs hZU, pow_one,
            Scheme.IdealSheafData.top_mul]
        · rw [B.restrictIdeal_comap_coordIdeal_of_mem D t htS hts hDU,
            B.restrictIdeal_strictTransform_of_mem_of_ne Z D hs hZU t htS hts hDU,
            B.restrictIdeal_exceptionalIdeal Z hs hZU, pow_one]
      · refine ⟨B.domain, 0, hx'B, Or.inl rfl, ?_, ?_⟩
        · refine ⟨fun h0 => absurd h0 (by omega), fun hV' => ?_⟩
          exfalso
          obtain ⟨V, hxV, hsubV⟩ := hV'
          obtain ⟨W, hxW, hWle⟩ :
              ∃ W : T.scheme.affineOpens, π x' ∈ W.1 ∧ W.1 ≤ U ⊓ V := by
            apply Scheme.exists_affineOpens_mem_le
            exact (⟨hxU, hxV⟩ : π x' ∈ U ⊓ V)
          have hWU : W.1 ≤ U := hWle.trans inf_le_left
          have hWV : W.1 ≤ V := hWle.trans inf_le_right
          have hZW := restrictIdeal_eq_restrict_coordIdeal_of_le hWU c Z S hZU
          have hDW := restrictIdeal_eq_restrict_coordIdeal_of_le hWU c D {t} hDU
          refine not_inter_support_subset_support_of_notMem_coordIdeal T.structMap W.2
            (c.restrict hWU) Z D S t htS hZW hDW (π x') hxW hx ?_
          intro w hw
          exact hsubV ⟨hw.1, SetLike.coe_subset_coe.mpr hWV hw.2⟩
        · show restrictIdeal (D.comap π) B.domain =
            restrictIdeal (Blowup.strictTransform π Z D) B.domain *
              restrictIdeal (Blowup.exceptionalIdeal π Z) B.domain ^ 0
          rw [B.restrictIdeal_comap_coordIdeal_of_not_mem D t htS hDU,
            B.restrictIdeal_strictTransform_coordIdeal_of_notMem Z D hs hZU t htS hDU, pow_zero, mul_one]
  · obtain ⟨V, hxV, hVeq⟩ := exists_opens_totalTransform_eq_of_notMem_support π Z D x' hx
    refine ⟨V, 1, hxV, Or.inr rfl, ?_, hVeq⟩
    refine ⟨fun _ => ⟨Z.support.compl, hx, ?_⟩, fun _ => rfl⟩
    intro y hy
    exact absurd hy.1 hy.2

end FunctorialResolution.EmbeddedResolution

end
