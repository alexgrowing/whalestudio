import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.AffineSpaceCoordinateBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativesInBlowupCharts
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private theorem presheaf_map_eq {X : Scheme.{u}} {A B : (X.Opens)ᵒᵖ} (f g : A ⟶ B) :
    X.presheaf.map f = X.presheaf.map g := by
  have h : f = g := Quiver.Hom.unop_inj (Subsingleton.elim f.unop g.unop)
  rw [h]

private theorem idealSheafData_mul_le_mul {Y : Scheme.{u}} {A B C D : Y.IdealSheafData}
    (h1 : A ≤ B) (h2 : C ≤ D) : A * C ≤ B * D := by
  refine Scheme.IdealSheafData.le_def.mpr fun U => ?_
  rw [Scheme.IdealSheafData.ideal_mul, Scheme.IdealSheafData.ideal_mul]
  exact Ideal.mul_mono (Scheme.IdealSheafData.le_def.mp h1 U)
    (Scheme.IdealSheafData.le_def.mp h2 U)

private theorem idealSheafData_mul_le_left {Y : Scheme.{u}} (A B : Y.IdealSheafData) :
    A * B ≤ A := by
  refine Scheme.IdealSheafData.le_def.mpr fun U => ?_
  rw [Scheme.IdealSheafData.ideal_mul]
  exact Ideal.mul_le.mpr fun r hr s _ => Ideal.mul_mem_right _ _ hr

private theorem idealSheafData_pow_le_pow_of_le {Y : Scheme.{u}} (A : Y.IdealSheafData) {i j : ℕ}
    (h : j ≤ i) : A ^ i ≤ A ^ j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  calc A ^ (j + d) = A ^ j * A ^ d := by rw [pow_add]
    _ ≤ A ^ j := idealSheafData_mul_le_left _ _

private theorem appLE_ι_bijective {Y : Scheme.{u}} (V : Y.Opens)
    (e : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V) :
    Function.Bijective (V.ι.appLE V ⊤ e).hom := by
  have h : V.ι.appLE V ⊤ e = V.topIso.inv := by
    simp
    exact presheaf_map_eq _ _
  rw [h]
  exact ConcreteCategory.bijective_of_isIso _

private theorem ideal_eq_of_comap_ι_eq {Y : Scheme.{u}} {A B : Y.IdealSheafData}
    (V : Y.affineOpens) (h : A.comap (V : Y.Opens).ι = B.comap (V : Y.Opens).ι) :
    A.ideal V = B.ideal V := by
  have : IsAffine (V : Y.Opens).toScheme := V.2
  have e : (⊤ : (V : Y.Opens).toScheme.Opens) ≤ (V : Y.Opens).ι ⁻¹ᵁ (V : Y.Opens) := by simp
  have h1 := A.comap_ideal_eq_map_appLE (V : Y.Opens).ι V ⟨⊤, isAffineOpen_top _⟩ e
  have h2 := B.comap_ideal_eq_map_appLE (V : Y.Opens).ι V ⟨⊤, isAffineOpen_top _⟩ e
  rw [h, h2] at h1
  have hbij := appLE_ι_bijective (V : Y.Opens) e
  have hbot : Ideal.comap ((V : Y.Opens).ι.appLE (V : Y.Opens) ⊤ e).hom
      (⊥ : Ideal Γ((V : Y.Opens).toScheme, ⊤)) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hbij.1
  have h3 := congrArg (Ideal.comap ((V : Y.Opens).ι.appLE (V : Y.Opens) ⊤ e).hom) h1
  rw [Ideal.comap_map_of_surjective _ hbij.2, Ideal.comap_map_of_surjective _ hbij.2, hbot,
    sup_bot_eq, sup_bot_eq] at h3
  exact h3.symm

private theorem exists_affineOpen_le {X : Scheme.{u}} (x : ↥X) (W : X.Opens)
    (hx : x ∈ W) : ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ W := by
  obtain ⟨U, hU, hxU, hUW⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hx
  exact ⟨⟨U, hU⟩, hxU, hUW⟩

private theorem exists_pow_mul_mem_of_map_mem_basicOpen {Y : Scheme.{u}} (U : Y.affineOpens)
    (f : Γ(Y, U.1)) (J : Ideal Γ(Y, U.1)) (x : Γ(Y, U.1))
    (hx : (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom x ∈
      J.map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom) :
    ∃ n : ℕ, f ^ n * x ∈ J := by
  have := U.2.isLocalization_basicOpen f
  have halg : (algebraMap Γ(Y, U.1) Γ(Y, Y.basicOpen f)) =
      (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom := rfl
  rw [← halg] at hx
  obtain ⟨⟨⟨y, hy⟩, ⟨m, hm⟩⟩, hxy⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) Γ(Y, Y.basicOpen f)).mp hx
  simp only at hxy
  rw [← map_mul] at hxy
  obtain ⟨⟨c, hc⟩, hcc⟩ :=
    (IsLocalization.eq_iff_exists (Submonoid.powers f) Γ(Y, Y.basicOpen f)).mp hxy
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hc
  refine ⟨b + a, ?_⟩
  simp only at hcc
  have h2 : f ^ (b + a) * x = f ^ b * y := by rw [← hcc]; ring
  rw [h2]
  exact J.mul_mem_left _ hy

theorem le_of_forall_exists_affineOpen {Y : Scheme.{u}} {A B : Y.IdealSheafData}
    (h : ∀ y : ↥Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧ A.ideal U ≤ B.ideal U) :
    A ≤ B := by
  refine Scheme.IdealSheafData.le_def.mpr fun U => ?_
  refine of_affine_open_cover (P := fun W : Y.affineOpens => A.ideal W ≤ B.ideal W)
    (fun y : ↥Y => (h y).choose) ?_ U ?_ ?_ ?_
  · rw [eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, (h y).choose_spec.1⟩
  · intro W f hW
    rw [← A.map_ideal_basicOpen W f, ← B.map_ideal_basicOpen W f]
    exact Ideal.map_mono hW
  · intro W s hspan hs x hxA
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (B.ideal W) (s : Set Γ(Y, W.1)) hspan x ?_
    rintro ⟨f, hf⟩
    have hmem : (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom x ∈
        (B.ideal W).map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom := by
      rw [B.map_ideal_basicOpen W f]
      refine hs ⟨f, Finset.mem_coe.mp hf⟩ ?_
      rw [← A.map_ideal_basicOpen W f]
      exact Ideal.mem_map_of_mem _ hxA
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_of_map_mem_basicOpen W f (B.ideal W) x hmem
    exact ⟨n, by simpa [smul_eq_mul] using hn⟩
  · intro y
    exact (h y).choose_spec.2

theorem derivIdealSheaf_pow_succ_mul_le (k : Type u) [Field k] [CharZero k] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth q]
    (F J : Y.IdealSheafData) (n : ℕ) :
    derivIdealSheaf k q (F ^ (n + 1) * J) ≤ F ^ n * derivIdealSheaf k q J := by
  refine le_trans (derivIdealSheaf_mul_le k q (F ^ (n + 1)) J) (sup_le ?_ ?_)
  · exact idealSheafData_mul_le_mul (idealSheafData_pow_le_pow_of_le F (Nat.le_succ n)) le_rfl
  · calc J * derivIdealSheaf k q (F ^ (n + 1))
        ≤ J * (F ^ n * derivIdealSheaf k q F) :=
          idealSheafData_mul_le_mul le_rfl (derivIdealSheaf_pow_succ_le k q F n)
      _ = F ^ n * (J * derivIdealSheaf k q F) := mul_left_comm _ _ _
      _ ≤ F ^ n * derivIdealSheaf k q J :=
          idealSheafData_mul_le_mul le_rfl
            (le_trans (idealSheafData_mul_le_left J (derivIdealSheaf k q F))
              (le_derivIdealSheaf k q J))

theorem derivIdealSheafIterate_pow_mul_le (k : Type u) [Field k] [CharZero k] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth q]
    (F J : Y.IdealSheafData) (m j : ℕ) (hj : j ≤ m) :
    derivIdealSheafIterate k q j (F ^ m * J) ≤ F ^ (m - j) * derivIdealSheafIterate k q j J := by
  revert hj
  induction j with
  | zero =>
    intro _
    rw [derivIdealSheafIterate_zero, derivIdealSheafIterate_zero, Nat.sub_zero]
  | succ j ih =>
    intro hj
    have hj' : j ≤ m := Nat.le_of_succ_le hj
    have h1 : m - j = (m - (j + 1)) + 1 := by omega
    rw [derivIdealSheafIterate_succ, derivIdealSheafIterate_succ]
    refine le_trans (derivIdealSheaf_mono k q (ih hj')) ?_
    rw [h1]
    exact derivIdealSheaf_pow_succ_mul_le k q F (derivIdealSheafIterate k q j J) (m - (j + 1))

private theorem derivIdealSheafIterate_congr_hom (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (q q' : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q]
    [LocallyOfFiniteType q'] (hq : q = q') (r : ℕ) (I : X.IdealSheafData) :
    derivIdealSheafIterate k q r I = derivIdealSheafIterate k q' r I := by
  subst hq
  rfl

theorem exists_affineOpen_comap_derivIdealSheafIterate_eq (k : Type u) [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [AlgebraicGeometry.Smooth (π ≫ p)] (W : X.Opens)
    [IsIso (AlgebraicGeometry.morphismRestrict π W)] (x : ↥X₁) (hx : x ∈ π ⁻¹ᵁ W)
    (j : ℕ) (I : X.IdealSheafData) :
    ∃ V : X₁.affineOpens, x ∈ V.1 ∧ V.1 ≤ π ⁻¹ᵁ W ∧
      ((derivIdealSheafIterate k p j I).comap π).ideal V =
        (derivIdealSheafIterate k (π ≫ p) j (I.comap π)).ideal V := by
  obtain ⟨V, hxV, hVW⟩ := exists_affineOpen_le x (π ⁻¹ᵁ W) hx
  refine ⟨V, hxV, hVW, ?_⟩
  have hfac : (V : X₁.Opens).ι ≫ π
      = X₁.homOfLE hVW ≫ (AlgebraicGeometry.morphismRestrict π W ≫ W.ι) := by
    rw [morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have : IsOpenImmersion ((V : X₁.Opens).ι ≫ π) := by rw [hfac]; infer_instance
  have : AlgebraicGeometry.Smooth ((V : X₁.Opens).ι ≫ π) := inferInstance
  have hcomp : ∀ A : X.IdealSheafData,
      A.comap ((V : X₁.Opens).ι ≫ π) = (A.comap π).comap (V : X₁.Opens).ι := by
    intro A
    simp [Scheme.IdealSheafData.comap_comp]
  have hassoc : ((V : X₁.Opens).ι ≫ π) ≫ p = (V : X₁.Opens).ι ≫ (π ≫ p) := Category.assoc _ _ _
  have h1 := derivIdealSheafIterate_comap k p ((V : X₁.Opens).ι ≫ π) j I
  have h2 := derivIdealSheafIterate_comap k (π ≫ p) (V : X₁.Opens).ι j (I.comap π)
  rw [hcomp I] at h1
  rw [derivIdealSheafIterate_congr_hom k (((V : X₁.Opens).ι ≫ π) ≫ p)
      ((V : X₁.Opens).ι ≫ (π ≫ p)) hassoc j ((I.comap π).comap (V : X₁.Opens).ι)] at h1
  have key : ((derivIdealSheafIterate k p j I).comap π).comap (V : X₁.Opens).ι
      = (derivIdealSheafIterate k (π ≫ p) j (I.comap π)).comap (V : X₁.Opens).ι := by
    rw [← hcomp (derivIdealSheafIterate k p j I), ← h1]
    exact h2
  exact ideal_eq_of_comap_ι_eq V key

theorem comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul (k : Type u) [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [IsLocallyNoetherian X₁] (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (I : X.IdealSheafData) (m : ℕ)
    (hI : I ≤ Z ^ m) (j : ℕ) (hj : j ≤ m) :
    haveI : AlgebraicGeometry.Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hZ hπ
    (derivIdealSheafIterate k p j I).comap π ≤
      Blowup.exceptionalIdeal π Z ^ (m - j) *
        derivIdealSheafIterate k (π ≫ p) j (controlledTransform π Z I m hπ hI) := by
  have : AlgebraicGeometry.Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hZ hπ
  refine le_of_forall_exists_affineOpen ?_
  intro x
  by_cases hxs : π.base x ∈ Z.support
  · obtain ⟨U, hxU, n, c, a, S, -, -, -, hZU⟩ := hZ.exists_etaleChart hxs
    obtain ⟨U₀, hxU0, hU0U⟩ := exists_affineOpen_le (π.base x) U hxU
    have hle : (U₀ : X.Opens) ≤ U := hU0U
    set c₀ := c.restrict hle with hc₀
    have hZU₀ : restrictIdeal Z (U₀ : X.Opens) = c₀.coordIdeal S := by
      rw [hc₀]
      exact restrictIdeal_eq_restrict_coordIdeal_of_le hle c Z S hZU
    have hx' : x ∈ π ⁻¹ᵁ (U₀ : X.Opens) := hxU0
    obtain ⟨s, hs, hxB⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c₀ S hπ hZU₀ x hx'
    set Bc := blowupChartOfIsBlowup π c₀ S hπ hZU₀ s hs with hBc
    obtain ⟨V, hxV, hVle⟩ := exists_affineOpen_le x Bc.domain hxB
    refine ⟨V, hxV, ?_⟩
    have hVdom : (V : X₁.Opens) ≤ Bc.domain := hVle
    have hVU : (V : X₁.Opens) ≤ π ⁻¹ᵁ (U₀ : X.Opens) := le_trans hVdom Bc.domain_le
    set cV := Bc.chart.restrict hVdom with hcV
    have hcoordres : ∀ i : Fin n,
        cV.coord i = (X₁.presheaf.map (homOfLE hVdom).op).hom (Bc.chart.coord i) := by
      intro i
      rw [hcV]
      exact EtaleChart.coord_restrict Bc.chart hVdom i
    have hE : (Blowup.exceptionalIdeal π Z).ideal V = Ideal.span {cV.coord s} := by
      have h1 : restrictIdeal (Blowup.exceptionalIdeal π Z) (V : X₁.Opens) = cV.coordIdeal {s} := by
        rw [hcV]
        exact restrictIdeal_eq_restrict_coordIdeal_of_le hVdom Bc.chart (Blowup.exceptionalIdeal π Z) {s}
          (Bc.restrictIdeal_exceptionalIdeal Z hs hZU₀)
      have h2 := EtaleChart.ideal_eq_span_coord cV V.2 (Blowup.exceptionalIdeal π Z) {s} h1
      simpa using h2
    have hEpow : ∀ (t : ℕ) (C : X₁.IdealSheafData),
        (Blowup.exceptionalIdeal π Z ^ t * C).ideal V = Ideal.span {cV.coord s ^ t} * C.ideal V := by
      intro t C
      rw [Scheme.IdealSheafData.ideal_mul, Scheme.IdealSheafData.ideal_pow]
      show (Blowup.exceptionalIdeal π Z).ideal V ^ t * C.ideal V
        = Ideal.span {cV.coord s ^ t} * C.ideal V
      rw [hE, Ideal.span_singleton_pow]
    let algU : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, (U₀ : X.Opens)) := c₀.algebra
    let algV : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X₁, (V : X₁.Opens)) := cV.algebra
    let kU : Algebra k Γ(X, (U₀ : X.Opens)) := sectionsAlgebra k p (U₀ : X.Opens)
    let kV : Algebra k Γ(X₁, (V : X₁.Opens)) := sectionsAlgebra k (π ≫ p) (V : X₁.Opens)
    have towerU := c₀.isScalarTower
    have towerV := cV.isScalarTower
    have feU := c₀.algebra_formallyEtale U₀.2
    have feV := cV.algebra_formallyEtale V.2
    let φA : Γ(X, (U₀ : X.Opens)) →ₐ[k] Γ(X₁, (V : X₁.Opens)) :=
      { (π.appLE (U₀ : X.Opens) (V : X₁.Opens) hVU).hom with
        commutes' := fun a => sectionsAlgebraMap_appLE_apply k p π _ _ hVU a }
    have hφ : ∀ y : Γ(X, (U₀ : X.Opens)), φA y
        = (X₁.presheaf.map (homOfLE hVdom).op).hom
            ((π.appLE (U₀ : X.Opens) Bc.domain Bc.domain_le).hom y) := by
      intro y
      show (π.appLE (U₀ : X.Opens) (V : X₁.Opens) hVU).hom y = _
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    have hmap : ∀ J : Ideal Γ(X, (U₀ : X.Opens)),
        Ideal.map φA J
          = Ideal.map (π.appLE (U₀ : X.Opens) (V : X₁.Opens) hVU).hom J := fun J => rfl
    have hcoordU : ∀ i : ULift.{u} (Fin n),
        @EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X, (U₀ : X.Opens)) _ algU i
          = c₀.coord i.down := by
      rintro ⟨i⟩
      exact c₀.etaleCoordinates_coord i
    have hcoordV : ∀ i : ULift.{u} (Fin n),
        @EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X₁, (V : X₁.Opens)) _ algV i
          = cV.coord i.down := by
      rintro ⟨i⟩
      exact cV.etaleCoordinates_coord i
    have hcoordVs :
        @EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X₁, (V : X₁.Opens)) _ algV
          (ULift.up s) = cV.coord s := cV.etaleCoordinates_coord s
    have hin : ∀ i ∈ uliftFinset n S, i ≠ (ULift.up s : ULift.{u} (Fin n)) →
        φA (@EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X, (U₀ : X.Opens)) _ algU i)
          = @EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X₁, (V : X₁.Opens)) _ algV i *
            @EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X₁, (V : X₁.Opens)) _ algV
              (ULift.up s) := by
      intro i hi his
      have hids : i.down ≠ s := fun hh => his (ULift.ext i (ULift.up s) hh)
      have hmem : i.down ∈ S := down_mem_of_mem_uliftFinset hi
      rw [hcoordU i, hcoordV i, hcoordVs]
      rw [hφ, Bc.appLE_coord_of_mem i.down hmem hids, map_mul, hcoordres, hcoordres]
    have hsc : φA (@EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X, (U₀ : X.Opens)) _ algU
          (ULift.up s))
        = @EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X₁, (V : X₁.Opens)) _ algV
            (ULift.up s) := by
      rw [hcoordU (ULift.up s), hcoordVs]
      rw [hφ, Bc.appLE_coord_self, hcoordres]
    have hout : ∀ i ∉ uliftFinset n S,
        φA (@EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X, (U₀ : X.Opens)) _ algU i)
          = @EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X₁, (V : X₁.Opens)) _ algV i := by
      intro i hi
      have hid : i.down ∉ S := fun hh => hi ((mem_uliftFinset S i).mpr hh)
      rw [hcoordU i, hcoordV i]
      rw [hφ, Bc.appLE_coord_of_not_mem i.down hid, hcoordres]
    have hsT : (ULift.up s : ULift.{u} (Fin n)) ∈ uliftFinset n S := up_mem_uliftFinset hs
    have hnzd : @EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X₁, (V : X₁.Opens)) _ algV
        (ULift.up s) ∈ nonZeroDivisors Γ(X₁, (V : X₁.Opens)) := by
      rw [hcoordVs]
      exact coord_mem_nonZeroDivisors V.2 cV s
    have hJ : Ideal.map φA (I.ideal U₀) ≤
        Ideal.span {(@EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X₁, (V : X₁.Opens)) _ algV
          (ULift.up s)) ^ m} * (controlledTransform π Z I m hπ hI).ideal V := by
      have h1 : Ideal.map (π.appLE (U₀ : X.Opens) (V : X₁.Opens) hVU).hom (I.ideal U₀)
          ≤ (I.comap π).ideal V :=
        I.map_appLE_le_comap_ideal π U₀ V hVU
      rw [← exceptionalIdeal_pow_mul_controlledTransform π Z I m hπ hI,
        hEpow m (controlledTransform π Z I m hπ hI)] at h1
      rw [hcoordVs, hmap]
      exact h1
    have hring := EtaleCoordinates.map_derivIdealIterate_le_span_pow_mul k (ULift.{u} (Fin n))
      Γ(X, (U₀ : X.Opens)) Γ(X₁, (V : X₁.Opens)) φA (uliftFinset n S) (ULift.up s)
      hin hsc hout hsT hnzd (I.ideal U₀) ((controlledTransform π Z I m hπ hI).ideal V) m hJ j hj
    rw [hcoordVs] at hring
    rw [(derivIdealSheafIterate k p j I).comap_ideal_eq_map_appLE π U₀ V hVU,
      derivIdealSheafIterate_ideal,
      hEpow (m - j) (derivIdealSheafIterate k (π ≫ p) j (controlledTransform π Z I m hπ hI)),
      derivIdealSheafIterate_ideal, ← hmap]
    exact hring
  · have : IsIso (AlgebraicGeometry.morphismRestrict π Z.support.compl) :=
      Blowup.blowupIsIsoOffCenter X X₁ π Z hπ
    have hx : x ∈ π ⁻¹ᵁ Z.support.compl := by exact hxs
    obtain ⟨V, hxV, hVW, heq⟩ :=
      exists_affineOpen_comap_derivIdealSheafIterate_eq k p π Z.support.compl x hx j I
    refine ⟨V, hxV, ?_⟩
    rw [heq]
    have h2 := derivIdealSheafIterate_pow_mul_le k (π ≫ p) (Blowup.exceptionalIdeal π Z)
      (controlledTransform π Z I m hπ hI) m j hj
    rw [exceptionalIdeal_pow_mul_controlledTransform π Z I m hπ hI] at h2
    exact Scheme.IdealSheafData.le_def.mp h2 V

theorem derivIdealSheafIterate_le_pow_of_hasStrictNormalCrossingsWith (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (Z I : X.IdealSheafData) (E : List X.IdealSheafData) (hZ : HasStrictNormalCrossingsWith p Z E) (m : ℕ)
    (hI : I ≤ Z ^ m) (j : ℕ) :
    derivIdealSheafIterate k p j I ≤ Z ^ (m - j) :=
  le_pow_of_hasStrictNormalCrossingsWith p Z (derivIdealSheafIterate k p j I) E hZ (m - j)
    (Set.Subset.trans (support_subset_orderAtLeastLocus_of_le_pow Z I m hI)
      (orderAtLeastLocus_subset_orderAtLeastLocus_derivIdealSheafIterate k p I j m))

end FunctorialResolution.EmbeddedResolution
