import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.AffineSpaceCoordinateBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDivisorBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.BlowupDerivativeIdealBound
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativesInBlowupCharts
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealSheafOpenImmersion
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private theorem ideal_mul_apply {Y : Scheme.{u}} (A B : Y.IdealSheafData) (V : Y.affineOpens) :
    (A * B).ideal V = A.ideal V * B.ideal V := rfl

private theorem ideal_pow_apply {Y : Scheme.{u}} (A : Y.IdealSheafData) (n : ℕ)
    (V : Y.affineOpens) : (A ^ n).ideal V = A.ideal V ^ n :=
  congrFun (Scheme.IdealSheafData.ideal_pow A n) V

private theorem ideal_top_eq_top {Y : Scheme.{u}} (V : Y.affineOpens) :
    (⊤ : Y.IdealSheafData).ideal V = ⊤ := by simp

private theorem restrictIdeal_top_eq_top {Y : Scheme.{u}} (V : Y.Opens) :
    restrictIdeal (⊤ : Y.IdealSheafData) V = ⊤ := Scheme.IdealSheafData.comap_top _

private theorem ideal_le_ideal_of_le {Y : Scheme.{u}} {A B : Y.IdealSheafData} (h : A ≤ B)
    (V : Y.affineOpens) : A.ideal V ≤ B.ideal V := h V

private theorem ideal_map_congr {R S : Type u} [CommRing R] [CommRing S] {F G : Type u}
    [FunLike F R S] [RingHomClass F R S] [FunLike G R S] [RingHomClass G R S]
    (f : F) (g : G) (h : ∀ x, f x = g x) (I : Ideal R) :
    Ideal.map f I = Ideal.map g I := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, h x]
    exact Ideal.mem_map_of_mem _ hx
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← h x]
    exact Ideal.mem_map_of_mem _ hx

private theorem logDerivIdealSheafIterate_congr_hom (k : Type u) [CommRing k]
    [IsNoetherianRing k] {Y : Scheme.{u}} {q q' : Y ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (h : q = q') (P : Y.IdealSheafData) (r : ℕ)
    (I : Y.IdealSheafData) :
    logDerivIdealSheafIterate k q P r I = logDerivIdealSheafIterate k q' P r I := by
  subst h
  rfl

theorem exists_affineOpen_comap_logDerivIdealSheafIterate_eq (k : Type u) [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [AlgebraicGeometry.Smooth (π ≫ p)] (W : X.Opens)
    [IsIso (AlgebraicGeometry.morphismRestrict π W)] (x₁ : ↥X₁) (hx₁ : x₁ ∈ π ⁻¹ᵁ W)
    (a : ℕ) (P K : X.IdealSheafData) :
    ∃ V : X₁.affineOpens, x₁ ∈ V.1 ∧ V.1 ≤ π ⁻¹ᵁ W ∧
      ((logDerivIdealSheafIterate k p P a K).comap π).ideal V =
        (logDerivIdealSheafIterate k (π ≫ p) (P.comap π) a (K.comap π)).ideal V := by
  obtain ⟨⟨V, hVaff⟩, hxV, hVU⟩ :
      ∃ V : X₁.affineOpens, x₁ ∈ V.1 ∧ V.1 ≤ π ⁻¹ᵁ W := by
    apply AlgebraicGeometry.Scheme.exists_affineOpens_mem_le
    exact hx₁
  refine ⟨⟨V, hVaff⟩, hxV, hVU, ?_⟩
  have : IsOpenImmersion (π ∣_ W) := inferInstance
  have : LocallyOfFiniteType (W.ι ≫ p) := inferInstance
  have : LocallyOfFiniteType ((π ∣_ W) ≫ (W.ι ≫ p)) := inferInstance
  have : LocallyOfFiniteType ((π ⁻¹ᵁ W).ι ≫ (π ≫ p)) := inferInstance
  have hq : (π ∣_ W) ≫ (W.ι ≫ p) = (π ⁻¹ᵁ W).ι ≫ (π ≫ p) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  have hP : (P.comap W.ι).comap (π ∣_ W) = (P.comap π).comap (π ⁻¹ᵁ W).ι := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  have hKc : (K.comap W.ι).comap (π ∣_ W) = (K.comap π).comap (π ⁻¹ᵁ W).ι := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  have e1 : ((logDerivIdealSheafIterate k p P a K).comap π).comap (π ⁻¹ᵁ W).ι
      = ((logDerivIdealSheafIterate k p P a K).comap W.ι).comap (π ∣_ W) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  have e2 : ((logDerivIdealSheafIterate k p P a K).comap W.ι).comap (π ∣_ W)
      = (logDerivIdealSheafIterate k (W.ι ≫ p) (P.comap W.ι) a (K.comap W.ι)).comap (π ∣_ W) := by
    rw [logDerivIdealSheafIterate_comap_of_isOpenImmersion k p W.ι P K a]
  have e3 : (logDerivIdealSheafIterate k (W.ι ≫ p) (P.comap W.ι) a (K.comap W.ι)).comap (π ∣_ W)
      = logDerivIdealSheafIterate k ((π ∣_ W) ≫ (W.ι ≫ p)) ((P.comap W.ι).comap (π ∣_ W)) a
          ((K.comap W.ι).comap (π ∣_ W)) :=
    logDerivIdealSheafIterate_comap_of_isOpenImmersion k (W.ι ≫ p) (π ∣_ W) (P.comap W.ι)
      (K.comap W.ι) a
  have e4 : logDerivIdealSheafIterate k ((π ∣_ W) ≫ (W.ι ≫ p)) ((P.comap W.ι).comap (π ∣_ W)) a
        ((K.comap W.ι).comap (π ∣_ W))
      = logDerivIdealSheafIterate k ((π ⁻¹ᵁ W).ι ≫ (π ≫ p)) ((P.comap π).comap (π ⁻¹ᵁ W).ι) a
          ((K.comap π).comap (π ⁻¹ᵁ W).ι) := by
    rw [hP, hKc]
    exact logDerivIdealSheafIterate_congr_hom k hq _ _ _
  have e5 : (logDerivIdealSheafIterate k (π ≫ p) (P.comap π) a (K.comap π)).comap (π ⁻¹ᵁ W).ι
      = logDerivIdealSheafIterate k ((π ⁻¹ᵁ W).ι ≫ (π ≫ p)) ((P.comap π).comap (π ⁻¹ᵁ W).ι) a
          ((K.comap π).comap (π ⁻¹ᵁ W).ι) :=
    logDerivIdealSheafIterate_comap_of_isOpenImmersion k (π ≫ p) (π ⁻¹ᵁ W).ι (P.comap π) (K.comap π) a
  have hmain : restrictIdeal ((logDerivIdealSheafIterate k p P a K).comap π) (π ⁻¹ᵁ W)
      = restrictIdeal (logDerivIdealSheafIterate k (π ≫ p) (P.comap π) a (K.comap π)) (π ⁻¹ᵁ W) :=
    e1.trans (e2.trans (e3.trans (e4.trans e5.symm)))
  exact ideal_eq_of_restrictIdeal_eq _ _ ⟨V, hVaff⟩ (FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_of_le_of_eq hVU hmain)

theorem exists_affineOpen_comap_logDerivIdealSheafIterate_le (k : Type u) [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [IsLocallyNoetherian X₁] (Z H : X.IdealSheafData) (E : List X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (hHZ : H ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (K : X.IdealSheafData) (c : ℕ) (hK : K ≤ Z ^ c) (a : ℕ) (ha : a ≤ c)
    (x₁ : ↥X₁) (hx₁ : π.base x₁ ∈ Z.support) :
    haveI : AlgebraicGeometry.Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
    ∃ V : X₁.affineOpens, x₁ ∈ V.1 ∧
      ((logDerivIdealSheafIterate k p H a K).comap π).ideal V ≤
        (Blowup.exceptionalIdeal π Z ^ (c - a) *
            logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) a
              (controlledTransform π Z K c hπ hK)).ideal V := by
  have hsm : AlgebraicGeometry.Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
  obtain ⟨U0, hxU0, m, c0, S, aH, aE, hZ0, hHnone, hHsome, -, -, -, -⟩ :=
    hsnc.exists_etaleChart_of_cons hx₁
  obtain ⟨⟨U, hUaff⟩, hxU, hUU0⟩ :
      ∃ V : X.affineOpens, π.base x₁ ∈ V.1 ∧ V.1 ≤ U0 := by
    apply AlgebraicGeometry.Scheme.exists_affineOpens_mem_le
    exact hxU0
  let c1 : EtaleChart p U m := c0.restrict hUU0
  have hZ1 : restrictIdeal Z U = c1.coordIdeal S :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hUU0 c0 Z S hZ0
  have hx₁U : x₁ ∈ π ⁻¹ᵁ U := hxU
  obtain ⟨s, hsS, hx₁B0⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c1 S hπ hZ1 x₁ hx₁U
  let B0 : BlowupChart π c1 S s := blowupChartOfIsBlowup π c1 S hπ hZ1 s hsS
  have hx₁B0' : x₁ ∈ B0.domain := hx₁B0
  obtain ⟨Vsub, hVsubDomain, hV0aff, hx₁V0⟩ := B0.exists_isAffineOpen_mem_le_domain x₁ hx₁B0'
  let B : BlowupChart π c1 S s := B0.restrict Vsub hVsubDomain
  have hdom : B.domain = Vsub := BlowupChart.restrict_domain B0 Vsub hVsubDomain
  have hBaff : IsAffineOpen B.domain := by rw [hdom]; exact hV0aff
  have hx₁B : x₁ ∈ B.domain := by rw [hdom]; exact hx₁V0
  have hEW : restrictIdeal (Blowup.exceptionalIdeal π Z) B.domain = B.chart.coordIdeal {s} :=
    B.restrictIdeal_exceptionalIdeal Z hsS hZ1
  have hEideal : (Blowup.exceptionalIdeal π Z).ideal ⟨B.domain, hBaff⟩
      = Ideal.span {B.chart.coord s} := by
    have h := EtaleChart.ideal_eq_span_coord B.chart hBaff (Blowup.exceptionalIdeal π Z) {s} hEW
    simpa using h
  refine ⟨⟨B.domain, hBaff⟩, hx₁B, ?_⟩
  have hofEqTop : restrictIdeal (Blowup.strictTransform π Z H) B.domain = ⊤ →
      ((logDerivIdealSheafIterate k p H a K).comap π).ideal ⟨B.domain, hBaff⟩ ≤
        (Blowup.exceptionalIdeal π Z ^ (c - a) *
            logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) a
              (controlledTransform π Z K c hπ hK)).ideal ⟨B.domain, hBaff⟩ := by
    intro hST
    have hST2 : restrictIdeal (Blowup.strictTransform π Z H) B.domain
        = restrictIdeal (⊤ : X₁.IdealSheafData) B.domain := by
      rw [hST, restrictIdeal_top_eq_top]
    have hST' : (Blowup.strictTransform π Z H).ideal ⟨B.domain, hBaff⟩ = ⊤ :=
      (ideal_eq_of_restrictIdeal_eq _ _ ⟨B.domain, hBaff⟩ hST2).trans (ideal_top_eq_top _)
    have h1 : (logDerivIdealSheafIterate k p H a K).ideal ⟨U, hUaff⟩ ≤
        (derivIdealSheafIterate k p a K).ideal ⟨U, hUaff⟩ :=
      ideal_le_ideal_of_le (logDerivIdealSheafIterate_le_derivIdealSheafIterate k p H a K) _
    have h2 : ((logDerivIdealSheafIterate k p H a K).comap π).ideal ⟨B.domain, hBaff⟩ ≤
        ((derivIdealSheafIterate k p a K).comap π).ideal ⟨B.domain, hBaff⟩ := by
      rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (logDerivIdealSheafIterate k p H a K) π
          ⟨U, hUaff⟩ ⟨B.domain, hBaff⟩ B.domain_le,
        Scheme.IdealSheafData.comap_ideal_eq_map_appLE (derivIdealSheafIterate k p a K) π
          ⟨U, hUaff⟩ ⟨B.domain, hBaff⟩ B.domain_le]
      exact Ideal.map_mono h1
    have h3 := comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p π Z (H :: E) hsnc hπ
      K c hK a ha
    refine le_trans h2 (le_trans (ideal_le_ideal_of_le h3 ⟨B.domain, hBaff⟩) (le_of_eq ?_))
    rw [ideal_mul_apply, ideal_mul_apply, logDerivIdealSheafIterate_ideal, derivIdealSheafIterate_ideal,
      hST', logDerivIdealIterate_top_eq_derivIdealIterate]
  cases haH : aH with
  | none =>
      have hHU : restrictIdeal H U = ⊤ := restrictIdeal_eq_top_of_le H hUU0 (hHnone haH)
      exact hofEqTop (B.restrictIdeal_strictTransform_of_eq_top Z H hHU)
  | some t =>
      have hHU : restrictIdeal H U = c1.coordIdeal {t} :=
        restrictIdeal_eq_restrict_coordIdeal_of_le hUU0 c0 H {t} (hHsome t haH)
      by_cases hts : t = s
      · subst hts
        exact hofEqTop (B.restrictIdeal_strictTransform_coordIdeal_self Z H hsS hZ1 hHU)
      · have htS : t ∈ S :=
          mem_of_restrictIdeal_eq_coordIdeal_of_le hUaff c1 Z H S t hHZ hHU hZ1 (π.base x₁) hxU hx₁
        have hSTW : restrictIdeal (Blowup.strictTransform π Z H) B.domain = B.chart.coordIdeal {t} :=
          B.restrictIdeal_strictTransform_of_mem_of_ne Z H hsS hZ1 t htS hts hHU
        have hHideal : H.ideal ⟨U, hUaff⟩ = Ideal.span {c1.coord t} := by
          have h := EtaleChart.ideal_eq_span_coord c1 hUaff H {t} hHU
          simpa using h
        have hSTideal : (Blowup.strictTransform π Z H).ideal ⟨B.domain, hBaff⟩
            = Ideal.span {B.chart.coord t} := by
          have h := EtaleChart.ideal_eq_span_coord B.chart hBaff (Blowup.strictTransform π Z H) {t} hSTW
          simpa using h
        let algU : Algebra k Γ(X, U) := sectionsAlgebra k p U
        let algB : Algebra k Γ(X₁, B.domain) := sectionsAlgebra k (π ≫ p) B.domain
        have hcomm : ∀ r : k,
            (π.appLE U B.domain B.domain_le).hom (sectionsAlgebraMap k p U r)
              = sectionsAlgebraMap k (π ≫ p) B.domain r :=
          sectionsAlgebraMap_appLE_apply k p π U B.domain B.domain_le
        let φ : Γ(X, U) →ₐ[k] Γ(X₁, B.domain) :=
          { toRingHom := (π.appLE U B.domain B.domain_le).hom
            commutes' := hcomm }
        have hφ : ∀ x, φ x = (π.appLE U B.domain B.domain_le).hom x := fun _ => rfl
        have hmapRestrict : ∀ I : Ideal Γ(X, U),
            Ideal.map φ I = Ideal.map (π.appLE U B.domain B.domain_le).hom I :=
          fun I => ideal_map_congr φ (π.appLE U B.domain B.domain_le).hom hφ I
        have hcoordU : ∀ i : ULift.{u} (Fin m),
            @EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X, U) _ c1.algebra i
              = c1.coord i.down :=
          fun i => EtaleChart.etaleCoordinates_coord c1 i.down
        have hcoordW : ∀ i : ULift.{u} (Fin m),
            @EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X₁, B.domain) _ B.chart.algebra i
              = B.chart.coord i.down :=
          fun i => EtaleChart.etaleCoordinates_coord B.chart i.down
        have hcoordUt : @EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X, U) _ c1.algebra
            (ULift.up t) = c1.coord t := EtaleChart.etaleCoordinates_coord c1 t
        have hcoordWt : @EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X₁, B.domain) _
            B.chart.algebra (ULift.up t) = B.chart.coord t :=
          EtaleChart.etaleCoordinates_coord B.chart t
        have hcoordWs : @EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X₁, B.domain) _
            B.chart.algebra (ULift.up s) = B.chart.coord s :=
          EtaleChart.etaleCoordinates_coord B.chart s
        have hin : ∀ i ∈ uliftFinset m S, i ≠ (ULift.up s : ULift.{u} (Fin m)) →
            φ (@EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X, U) _ c1.algebra i) =
              (@EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X₁, B.domain) _
                  B.chart.algebra i) *
                (@EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X₁, B.domain) _
                  B.chart.algebra (ULift.up s)) := by
          intro i hi hne
          rw [hcoordU i, hcoordW i, hcoordW (ULift.up s), hφ]
          exact B.appLE_coord_of_mem i.down (down_mem_of_mem_uliftFinset hi)
            (fun h => hne (congrArg ULift.up h))
        have hself : φ (@EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X, U) _ c1.algebra
              (ULift.up s))
            = @EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X₁, B.domain) _ B.chart.algebra
              (ULift.up s) := by
          rw [hcoordU (ULift.up s), hcoordW (ULift.up s), hφ]
          exact B.appLE_coord_self
        have hout : ∀ i ∉ uliftFinset m S,
            φ (@EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X, U) _ c1.algebra i) =
              @EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X₁, B.domain) _
                B.chart.algebra i := by
          intro i hi
          rw [hcoordU i, hcoordW i, hφ]
          exact B.appLE_coord_of_not_mem i.down (fun h => hi (up_mem_uliftFinset h))
        have hnzd : (@EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X₁, B.domain) _
            B.chart.algebra (ULift.up s)) ∈ nonZeroDivisors Γ(X₁, B.domain) := by
          rw [hcoordWs]
          exact coord_mem_nonZeroDivisors hBaff B.chart s
        have hJ : Ideal.map φ (K.ideal ⟨U, hUaff⟩) ≤
            Ideal.span {(@EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X₁, B.domain) _
                B.chart.algebra (ULift.up s)) ^ c} *
              (controlledTransform π Z K c hπ hK).ideal ⟨B.domain, hBaff⟩ := by
          rw [hcoordWs, hmapRestrict]
          refine le_of_eq ?_
          rw [← Ideal.span_singleton_pow, ← hEideal, ← ideal_pow_apply, ← ideal_mul_apply,
            exceptionalIdeal_pow_mul_controlledTransform π Z K c hπ hK]
          exact (Scheme.IdealSheafData.comap_ideal_eq_map_appLE K π ⟨U, hUaff⟩
            ⟨B.domain, hBaff⟩ B.domain_le).symm
        have key := @EtaleCoordinates.map_logDerivIdealIterate_le_span_pow_mul k _ (ULift.{u} (Fin m))
          (Classical.decEq (ULift.{u} (Fin m)))
          Γ(X, U) _ (sectionsAlgebra k p U) c1.algebra c1.isScalarTower
          (c1.algebra_formallyEtale hUaff)
          Γ(X₁, B.domain) _ (sectionsAlgebra k (π ≫ p) B.domain) B.chart.algebra
          B.chart.isScalarTower (B.chart.algebra_formallyEtale hBaff)
          φ (uliftFinset m S) (ULift.up s) _
          hin hself hout (up_mem_uliftFinset hsS) hnzd (ULift.up t) (up_mem_uliftFinset htS)
          (fun h => hts (congrArg ULift.down h))
          (K.ideal ⟨U, hUaff⟩) ((controlledTransform π Z K c hπ hK).ideal ⟨B.domain, hBaff⟩)
          c hJ a ha
        rw [hcoordUt, hcoordWs, hcoordWt, hmapRestrict] at key
        rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (logDerivIdealSheafIterate k p H a K) π
            ⟨U, hUaff⟩ ⟨B.domain, hBaff⟩ B.domain_le,
          logDerivIdealSheafIterate_ideal, hHideal, ideal_mul_apply, ideal_pow_apply, hEideal,
          logDerivIdealSheafIterate_ideal, hSTideal, Ideal.span_singleton_pow]
        exact key

theorem comap_logDerivIdealSheafIterate_le_exceptionalIdeal_pow_mul (k : Type u) [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [IsLocallyNoetherian X₁] (Z H : X.IdealSheafData) (E : List X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (hHZ : H ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (K : X.IdealSheafData) (c : ℕ) (hK : K ≤ Z ^ c) (a : ℕ) (ha : a ≤ c) :
    haveI : AlgebraicGeometry.Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
    (logDerivIdealSheafIterate k p H a K).comap π ≤
      Blowup.exceptionalIdeal π Z ^ (c - a) *
        logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) a
          (controlledTransform π Z K c hπ hK) := by
  have hsm : AlgebraicGeometry.Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
  refine le_of_forall_exists_affineOpen ?_
  intro y
  by_cases hy : π.base y ∈ Z.support
  · exact exists_affineOpen_comap_logDerivIdealSheafIterate_le k p π Z H E hsnc hHZ hπ K c hK a ha
      y hy
  · have : IsIso (π ∣_ Z.support.compl) :=
      isIso_morphismRestrict_of_isBlowupAlongIdealSheaf hπ Z.support.compl (fun x hx => hx)
    have hyW : y ∈ π ⁻¹ᵁ Z.support.compl := hy
    obtain ⟨V, hyV, hVW, heq⟩ :=
      exists_affineOpen_comap_logDerivIdealSheafIterate_eq k p π Z.support.compl y hyW a H K
    have hEV2 : restrictIdeal (Blowup.exceptionalIdeal π Z) V.1
        = restrictIdeal (⊤ : X₁.IdealSheafData) V.1 := by
      rw [restrictIdeal_exceptionalIdeal_eq_top_of_le_compl π Z V.1 hVW, restrictIdeal_top_eq_top]
    have hEV : (Blowup.exceptionalIdeal π Z).ideal V = ⊤ :=
      (ideal_eq_of_restrictIdeal_eq _ _ V hEV2).trans (ideal_top_eq_top _)
    have hSTV : (Blowup.strictTransform π Z H).ideal V = (H.comap π).ideal V :=
      ideal_eq_of_restrictIdeal_eq _ _ V
        (restrictIdeal_strictTransform_eq_comap_of_le_compl π Z H V.1 hVW)
    have hCTV : (controlledTransform π Z K c hπ hK).ideal V = (K.comap π).ideal V := by
      have h := congrArg (fun A : X₁.IdealSheafData => A.ideal V)
        (exceptionalIdeal_pow_mul_controlledTransform π Z K c hπ hK)
      simp only [ideal_mul_apply, ideal_pow_apply, hEV] at h
      rw [← Ideal.one_eq_top, one_pow, one_mul] at h
      exact h
    have hexcPow : (Blowup.exceptionalIdeal π Z ^ (c - a) *
          logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) a
            (controlledTransform π Z K c hπ hK)).ideal V
        = (logDerivIdealSheafIterate k (π ≫ p) (H.comap π) a (K.comap π)).ideal V := by
      rw [ideal_mul_apply, ideal_pow_apply, hEV, ← Ideal.one_eq_top, one_pow, one_mul,
        logDerivIdealSheafIterate_ideal, logDerivIdealSheafIterate_ideal, hSTV, hCTV]
    exact ⟨V, hyV, le_of_eq (heq.trans hexcPow.symm)⟩

end FunctorialResolution.EmbeddedResolution
