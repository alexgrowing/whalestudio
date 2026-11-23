import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDivisorBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.BlowupDerivativeIdealBound
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.ControlledTransformLogDerivativesInCharts
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
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

private theorem top_ideal_eq_top {Y : Scheme.{u}} (U : Y.affineOpens) :
    (⊤ : Y.IdealSheafData).ideal U = ⊤ := by
  simp [Scheme.IdealSheafData.ideal_top]

private theorem pow_ideal_eq_ideal_pow {Y : Scheme.{u}} (A : Y.IdealSheafData)
    (U : Y.affineOpens) : ∀ j : ℕ, (A ^ j).ideal U = A.ideal U ^ j :=
  fun j => congrFun (Scheme.IdealSheafData.ideal_pow A j) U

private theorem restrictIdeal_top {Y : Scheme.{u}} (U : Y.Opens) :
    restrictIdeal (⊤ : Y.IdealSheafData) U = ⊤ := by
  simp [restrictIdeal_eq_comap_ι]

private theorem ideal_affineOpen_eq_top_of_restrictIdeal_eq_top {Y : Scheme.{u}} (D : Y.IdealSheafData)
    {V : Y.Opens} (hV : IsAffineOpen V) (h : restrictIdeal D V = ⊤) :
    D.ideal ⟨V, hV⟩ = ⊤ := by
  have h2 : restrictIdeal D V = restrictIdeal (⊤ : Y.IdealSheafData) V := by
    rw [restrictIdeal_top]
    exact h
  rw [ideal_eq_of_restrictIdeal_eq D ⊤ ⟨V, hV⟩ h2, top_ideal_eq_top]

theorem exists_affineOpen_derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate
    (k : Type u) [Field k] [CharZero k] {X X₁ : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [IsLocallyNoetherian X₁]
    (Z H : X.IdealSheafData) (E : List X.IdealSheafData)
    (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (hHZ : H ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    [QuasiCompact (strictTransformι π Z H)]
    (A : X.IdealSheafData) (m : ℕ) (L : ℕ → X₁.IdealSheafData)
    (hL : ∀ l ≤ m,
      Blowup.exceptionalIdeal π Z ^ (m - l) * L l = (derivIdealSheafIterate k p l A).comap π)
    (n : ℕ) (hn : n ≤ m) (x₁ : ↥X₁) (hx₁ : π.base x₁ ∈ Z.support) :
    haveI : AlgebraicGeometry.Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
    ∃ V : X₁.affineOpens, x₁ ∈ V.1 ∧
      (derivIdealSheafIterate k (π ≫ p) n (L 0)).ideal V ≤
        (⨆ l, ⨆ _ : l ≤ n,
            logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (L l)).ideal V := by
  let hsmooth : AlgebraicGeometry.Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
  show ∃ V : X₁.affineOpens, x₁ ∈ V.1 ∧
      (derivIdealSheafIterate k (π ≫ p) n (L 0)).ideal V ≤
        (⨆ l, ⨆ _ : l ≤ n,
            logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (L l)).ideal V
  obtain ⟨U, hxU, mm, c, S, aH, a, hZU, hHtop, hHcoord, -, -, -, -⟩ :=
    hsnc.exists_etaleChart_of_cons hx₁
  obtain ⟨U', _mm2, hxU', hU'U, hU'aff, -⟩ := exists_etaleChart_le p (π.base x₁) U hxU
  obtain ⟨cU, hZU', hHU'⟩ : ∃ cU : EtaleChart p U' mm, restrictIdeal Z U' = cU.coordIdeal S ∧
      (restrictIdeal H U' = ⊤ ∨ ∃ t : Fin mm, restrictIdeal H U' = cU.coordIdeal {t}) := by
    refine ⟨c.restrict hU'U, restrictIdeal_eq_restrict_coordIdeal_of_le hU'U c Z S hZU, ?_⟩
    cases haH : aH with
    | none => exact Or.inl (FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_top_of_le H hU'U (hHtop haH))
    | some t =>
        exact Or.inr ⟨t, restrictIdeal_eq_restrict_coordIdeal_of_le hU'U c H {t} (hHcoord t haH)⟩
  have hx₁U' : x₁ ∈ π ⁻¹ᵁ U' := hxU'
  obtain ⟨s, hs, hx₁dom⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π cU S hπ hZU' x₁ hx₁U'
  obtain ⟨B, hBaff, hx₁B⟩ : ∃ B : BlowupChart π cU S s, IsAffineOpen B.domain ∧ x₁ ∈ B.domain := by
    obtain ⟨V, hVle, hVaff, hxV⟩ :=
      (blowupChartOfIsBlowup π cU S hπ hZU' s hs).exists_isAffineOpen_mem_le_domain x₁ hx₁dom
    refine ⟨(blowupChartOfIsBlowup π cU S hπ hZU' s hs).restrict V hVle, ?_, ?_⟩
    · rw [BlowupChart.restrict_domain]
      exact hVaff
    · rw [BlowupChart.restrict_domain]
      exact hxV
  have hcase : (Blowup.strictTransform π Z H).ideal ⟨B.domain, hBaff⟩ = ⊤ ∨
      ∃ t : Fin mm, (Blowup.strictTransform π Z H).ideal ⟨B.domain, hBaff⟩
          = Ideal.span {B.chart.coord t} ∧ t ≠ s ∧ t ∈ S := by
    rcases hHU' with hHtopU | ⟨t, hHt⟩
    · exact Or.inl (ideal_affineOpen_eq_top_of_restrictIdeal_eq_top _ hBaff
        (B.restrictIdeal_strictTransform_of_eq_top Z H hHtopU))
    · by_cases hts : t = s
      · subst hts
        exact Or.inl (ideal_affineOpen_eq_top_of_restrictIdeal_eq_top _ hBaff
          (B.restrictIdeal_strictTransform_coordIdeal_self Z H hs hZU' hHt))
      · have htS : t ∈ S :=
          mem_of_restrictIdeal_eq_coordIdeal_of_le hU'aff cU Z H S t hHZ hHt hZU'
            (π.base x₁) hxU' hx₁
        refine Or.inr ⟨t, ?_, hts, htS⟩
        rw [B.chart.ideal_eq_span_coord hBaff _ {t}
          (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZU' t htS hts hHt)]
        simp
  rcases hcase with hP | ⟨t, hP, hts, htS⟩
  · refine ⟨⟨B.domain, hBaff⟩, hx₁B, ?_⟩
    refine le_trans ?_ (Scheme.IdealSheafData.le_def.mp (le_iSup₂ (f := fun l (_ : l ≤ n) =>
      logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (L l)) 0
      (Nat.zero_le n)) _)
    rw [derivIdealSheafIterate_ideal, logDerivIdealSheafIterate_ideal, hP,
      logDerivIdealIterate_top_eq_derivIdealIterate, Nat.sub_zero]
  · refine ⟨⟨B.domain, hBaff⟩, hx₁B, ?_⟩
    let instS : Algebra k Γ(X, U') := sectionsAlgebra k p U'
    let instS₁ : Algebra k Γ(X₁, B.domain) := sectionsAlgebra k (π ≫ p) B.domain
    let instPS : Algebra (MvPolynomial (ULift.{u, 0} (Fin mm)) k) Γ(X, U') := cU.algebra
    let instPS₁ : Algebra (MvPolynomial (ULift.{u, 0} (Fin mm)) k) Γ(X₁, B.domain) :=
      B.chart.algebra
    have instST : IsScalarTower k (MvPolynomial (ULift.{u, 0} (Fin mm)) k) Γ(X, U') :=
      cU.isScalarTower
    have instST₁ : IsScalarTower k (MvPolynomial (ULift.{u, 0} (Fin mm)) k) Γ(X₁, B.domain) :=
      B.chart.isScalarTower
    have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u, 0} (Fin mm)) k) Γ(X, U') :=
      cU.algebra_formallyEtale hU'aff
    have instFE₁ :
        Algebra.FormallyEtale (MvPolynomial (ULift.{u, 0} (Fin mm)) k) Γ(X₁, B.domain) :=
      B.chart.algebra_formallyEtale hBaff
    let instDecEq : DecidableEq (ULift.{u, 0} (Fin mm)) := Classical.decEq _
    have hcoordU : ∀ j : Fin mm,
        EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X, U') ⟨j⟩ = cU.coord j :=
      fun j => cU.etaleCoordinates_coord j
    have hcoordV : ∀ j : Fin mm,
        EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X₁, B.domain) ⟨j⟩ = B.chart.coord j :=
      fun j => B.chart.etaleCoordinates_coord j
    have hBle : B.domain ≤ π ⁻¹ᵁ U' := B.domain_le
    let φ : Γ(X, U') →ₐ[k] Γ(X₁, B.domain) :=
      { ((π.appLE U' B.domain hBle).hom) with
        commutes' := fun x => sectionsAlgebraMap_appLE_apply k p π U' B.domain hBle x }
    obtain ⟨T, hmemT⟩ : ∃ T : Finset (ULift.{u, 0} (Fin mm)),
        ∀ i : ULift.{u, 0} (Fin mm), i ∈ T ↔ i.down ∈ S := by
      refine ⟨S.map ⟨ULift.up, fun x y hxy => by simpa using hxy⟩, fun i => ?_⟩
      constructor
      · intro hi
        obtain ⟨j, hj, hji⟩ := Finset.mem_map.1 hi
        rw [← hji]
        exact hj
      · intro hi
        exact Finset.mem_map.2 ⟨i.down, hi, rfl⟩
    have hsT : (⟨s⟩ : ULift.{u, 0} (Fin mm)) ∈ T := (hmemT ⟨s⟩).2 hs
    have hhT : (⟨t⟩ : ULift.{u, 0} (Fin mm)) ∈ T := (hmemT ⟨t⟩).2 htS
    have hhs : (⟨t⟩ : ULift.{u, 0} (Fin mm)) ≠ ⟨s⟩ := fun hh => hts (congrArg ULift.down hh)
    have hin : ∀ i ∈ T, i ≠ (⟨s⟩ : ULift.{u, 0} (Fin mm)) →
        φ (EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X, U') i) =
          EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X₁, B.domain) i *
            EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X₁, B.domain) ⟨s⟩ := by
      rintro ⟨i⟩ hiT hine
      rw [hcoordU, hcoordV, hcoordV]
      exact B.appLE_coord_of_mem i ((hmemT ⟨i⟩).1 hiT) (fun hh => hine (congrArg ULift.up hh))
    have hsc : φ (EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X, U')
          (⟨s⟩ : ULift.{u, 0} (Fin mm))) =
        EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X₁, B.domain) ⟨s⟩ := by
      rw [hcoordU, hcoordV]
      exact B.appLE_coord_self
    have hout : ∀ i ∉ T,
        φ (EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X, U') i) =
          EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X₁, B.domain) i := by
      rintro ⟨i⟩ hiT
      rw [hcoordU, hcoordV]
      exact B.appLE_coord_of_not_mem i (fun hh => hiT ((hmemT ⟨i⟩).2 hh))
    have hnzd : EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X₁, B.domain)
        (⟨s⟩ : ULift.{u, 0} (Fin mm)) ∈ nonZeroDivisors Γ(X₁, B.domain) := by
      rw [hcoordV]
      exact coord_mem_nonZeroDivisors hBaff B.chart s
    have hE : (Blowup.exceptionalIdeal π Z).ideal ⟨B.domain, hBaff⟩
        = Ideal.span {B.chart.coord s} := by
      rw [B.chart.ideal_eq_span_coord hBaff _ {s} (B.restrictIdeal_exceptionalIdeal Z hs hZU')]
      simp
    have hL' : ∀ i ≤ m,
        Ideal.span {EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X₁, B.domain)
            (⟨s⟩ : ULift.{u, 0} (Fin mm)) ^ (m - i)} * (L i).ideal ⟨B.domain, hBaff⟩ =
          Ideal.map φ (derivIdealIterate k i (A.ideal ⟨U', hU'aff⟩)) := by
      intro i hi
      have hmul : (Blowup.exceptionalIdeal π Z ^ (m - i) * L i).ideal ⟨B.domain, hBaff⟩ =
          (Blowup.exceptionalIdeal π Z ^ (m - i)).ideal ⟨B.domain, hBaff⟩ *
            (L i).ideal ⟨B.domain, hBaff⟩ := by
        simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
      rw [hcoordV, ← Ideal.span_singleton_pow, ← hE, ← pow_ideal_eq_ideal_pow, ← hmul,
        hL i hi,
        Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ π ⟨U', hU'aff⟩ ⟨B.domain, hBaff⟩ hBle,
        derivIdealSheafIterate_ideal]
      rfl
    have key : derivIdealIterate k n ((L 0).ideal ⟨B.domain, hBaff⟩) ≤
        ⨆ i, ⨆ _ : i ≤ n, logDerivIdealIterate k
          (Ideal.span {EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X₁, B.domain)
            (⟨t⟩ : ULift.{u, 0} (Fin mm))}) (n - i) ((L i).ideal ⟨B.domain, hBaff⟩) :=
      EtaleCoordinates.derivIdealIterate_le_iSup_logDerivIdealIterate_controlledTransform
        k (ULift.{u, 0} (Fin mm)) Γ(X, U') Γ(X₁, B.domain) φ T ⟨s⟩ ⟨t⟩
        hsT hin hsc hout hnzd hhT hhs (A.ideal ⟨U', hU'aff⟩)
        (fun i => (L i).ideal ⟨B.domain, hBaff⟩) m hL' n hn
    rw [hcoordV] at key
    rw [derivIdealSheafIterate_ideal]
    refine le_trans key ?_
    refine iSup_le fun i => ?_
    refine iSup_le fun hi => ?_
    have hre : logDerivIdealIterate k (Ideal.span {B.chart.coord t}) (n - i)
          ((L i).ideal ⟨B.domain, hBaff⟩) =
        (logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - i) (L i)).ideal
          ⟨B.domain, hBaff⟩ := by
      rw [logDerivIdealSheafIterate_ideal, hP]
    rw [hre]
    exact Scheme.IdealSheafData.le_def.mp (le_iSup₂ (f := fun l (_ : l ≤ n) =>
      logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (L l)) i hi) _

theorem derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_strictTransform
    (k : Type u) [Field k] [CharZero k] {X X₁ : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [IsLocallyNoetherian X₁]
    (Z H : X.IdealSheafData) (E : List X.IdealSheafData)
    (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (hHZ : H ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    [QuasiCompact (strictTransformι π Z H)]
    (A : X.IdealSheafData) (m : ℕ) (L : ℕ → X₁.IdealSheafData)
    (hL : ∀ l ≤ m,
      Blowup.exceptionalIdeal π Z ^ (m - l) * L l = (derivIdealSheafIterate k p l A).comap π)
    (n : ℕ) (hn : n ≤ m) :
    haveI : AlgebraicGeometry.Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
    derivIdealSheafIterate k (π ≫ p) n (L 0) ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (L l) := by
  let hsmooth : AlgebraicGeometry.Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
  show derivIdealSheafIterate k (π ≫ p) n (L 0) ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (L l)
  have main : ∀ y : ↥X₁, ∃ V : X₁.affineOpens, y ∈ V.1 ∧
      (derivIdealSheafIterate k (π ≫ p) n (L 0)).ideal V ≤
        (⨆ l, ⨆ _ : l ≤ n,
            logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (L l)).ideal V := by
    intro y
    by_cases hy : π.base y ∈ Z.support
    · exact exists_affineOpen_derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate
        k p π Z H E hsnc hHZ hπ A m L hL n hn y hy
    · have hyW : y ∈ π ⁻¹ᵁ (Z.support.compl) := hy
      have : IsIso (π ∣_ (Z.support.compl)) :=
        isIso_morphismRestrict_of_isBlowupAlongIdealSheaf hπ (Z.support.compl) (fun x hx => hx)
      obtain ⟨V, hyV, hVW, heq⟩ :=
        exists_affineOpen_comap_derivIdealSheafIterate_eq k p π (Z.support.compl) y hyW n A
      refine ⟨V, hyV, ?_⟩
      have hEV : (Blowup.exceptionalIdeal π Z).ideal V = ⊤ :=
        ideal_affineOpen_eq_top_of_restrictIdeal_eq_top _ V.2
          (restrictIdeal_exceptionalIdeal_eq_top_of_le_compl π Z (V : X₁.Opens) hVW)
      have hiterate : ∀ l, l ≤ m →
          (L l).ideal V = ((derivIdealSheafIterate k p l A).comap π).ideal V := by
        intro l hl
        have hx : (Blowup.exceptionalIdeal π Z ^ (m - l) * L l).ideal V
            = ((derivIdealSheafIterate k p l A).comap π).ideal V := by rw [hL l hl]
        have hmul : (Blowup.exceptionalIdeal π Z ^ (m - l) * L l).ideal V
            = (Blowup.exceptionalIdeal π Z ^ (m - l)).ideal V * (L l).ideal V := by
          simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
        rw [hmul, pow_ideal_eq_ideal_pow, hEV, Ideal.top_pow, Ideal.top_mul] at hx
        exact hx
      have h0 : (L 0).ideal V = (A.comap π).ideal V := by
        have h00 := hiterate 0 (Nat.zero_le m)
        rwa [derivIdealSheafIterate_zero] at h00
      have hstep : (derivIdealSheafIterate k (π ≫ p) n (L 0)).ideal V = (L n).ideal V := by
        rw [derivIdealSheafIterate_ideal, h0,
          ← derivIdealSheafIterate_ideal k (π ≫ p) n (A.comap π) V, ← heq, ← hiterate n hn]
      rw [hstep]
      have hmono := Scheme.IdealSheafData.le_def.mp (le_iSup₂ (f := fun l (_ : l ≤ n) =>
        logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (L l)) n
        (le_refl n)) V
      rwa [Nat.sub_self, logDerivIdealSheafIterate_zero] at hmono
  exact le_of_forall_exists_affineOpen main

end FunctorialResolution.EmbeddedResolution
