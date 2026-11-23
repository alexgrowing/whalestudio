import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDivisorBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsChartNormalization
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsAddHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.BlowupDerivativeIdealBound
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.ControlledTransformOrderBound
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactCoordinate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

section

variable (k : Type u) [Field k] {P₁ : Scheme.{u}} (q : P₁ ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType q]

def IsMaxContactHypersurfaceAt (A₁ : P₁.IdealSheafData) (m : ℕ) (H₁ : P₁.IdealSheafData) (x : P₁) : Prop :=
  ∃ U : P₁.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ((Disjoint (orderAtLeastLocus A₁ m) (U : Set ↥P₁) ∧ restrictIdeal H₁ U = ⊤) ∨
      (∃ (n : ℕ) (c : EtaleChart q U n) (j : Fin n),
        restrictIdeal H₁ U = c.coordIdeal {j} ∧ IsMaxContactCoord k q A₁ m c j))

end

section

private theorem idealSheafData_eq_of_forall_ideal_eq {Y : Scheme.{u}} {A B : Y.IdealSheafData}
    (h : ∀ V : Y.affineOpens, A.ideal V = B.ideal V) : A = B :=
  Scheme.IdealSheafData.ext (funext h)

private theorem mul_le_right_idealSheafData {X : Scheme.{u}} (I J : X.IdealSheafData) :
    I * J ≤ J := by
  rw [le_iff_forall_stalkIdeal_le]
  intro x
  rw [stalkIdeal_mul]
  exact Ideal.mul_le.2 fun r _ s hs => Ideal.mul_mem_left _ _ hs

private theorem mul_le_left_idealSheafData {X : Scheme.{u}} (I J : X.IdealSheafData) :
    I * J ≤ I := by
  rw [le_iff_forall_stalkIdeal_le]
  intro x
  rw [stalkIdeal_mul]
  exact Ideal.mul_le.2 fun r hr s _ => Ideal.mul_mem_right _ _ hr

private theorem restrictIdeal_le_of_le_opens {X : Scheme.{u}} {I J : X.IdealSheafData}
    {U V : X.Opens} (hVU : V ≤ U) (h : restrictIdeal I U ≤ restrictIdeal J U) :
    restrictIdeal I V ≤ restrictIdeal J V := by
  have hI : ∀ K : X.IdealSheafData,
      restrictIdeal K V = (restrictIdeal K U).comap (X.homOfLE hVU) := by
    intro K
    rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
      Scheme.homOfLE_ι]
  rw [hI I, hI J]
  exact Scheme.IdealSheafData.comap_mono _ h

private theorem saturation_of_eq_top {Y : Scheme.{u}} (F T : Y.IdealSheafData)
    (hqc : QuasiCompact (saturationι F T)) (hF : F = ⊤) :
    saturation F T = T := by
  have := hqc
  refine idealSheafData_eq_of_forall_ideal_eq (fun V => ?_)
  refine saturation_ideal_eq_of_isUnit F T V 1 ?_ isUnit_one
  rw [hF]
  simp

private theorem restrictIdeal_strictTransform_eq_of_comap_eq_top {P P₁ : Scheme.{u}} (π : P₁ ⟶ P)
    (Z H : P.IdealSheafData) [QuasiCompact (strictTransformι π Z H)] (V : P.Opens)
    (hZtop : Z.comap ((π ⁻¹ᵁ V).ι ≫ π) = ⊤) :
    restrictIdeal (Blowup.strictTransform π Z H) (π ⁻¹ᵁ V) = restrictIdeal (H.comap π) (π ⁻¹ᵁ V) := by
  have hqc : QuasiCompact (saturationι (Z.comap ((π ⁻¹ᵁ V).ι ≫ π))
      (H.comap ((π ⁻¹ᵁ V).ι ≫ π))) := by
    rw [← strictTransformι_eq_saturationι]
    exact quasiCompact_strictTransformι_comp_ι π Z H (π ⁻¹ᵁ V)
  have hsat : Blowup.strictTransform ((π ⁻¹ᵁ V).ι ≫ π) Z H = H.comap ((π ⁻¹ᵁ V).ι ≫ π) := by
    rw [strictTransform_eq_saturation]
    exact saturation_of_eq_top _ _ hqc hZtop
  rw [restrictIdeal_strictTransform π Z H (π ⁻¹ᵁ V), hsat, restrictIdeal_eq_comap_ι,
    Scheme.IdealSheafData.comap_comp]

private noncomputable def etaleChartPullbackOfIsIso {P P₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : P ⟶ Spec (CommRingCat.of k)} (π : P₁ ⟶ P) {V : P.Opens} {n : ℕ}
    (c : EtaleChart p V n) [IsIso (π ∣_ V)] : EtaleChart (π ≫ p) (π ⁻¹ᵁ V) n where
  map := (π ∣_ V) ≫ c.map
  comp_struct := by
    rw [Category.assoc, c.comp_struct, ← Category.assoc, morphismRestrict_ι, Category.assoc]
  isEtale := by
    have := c.isEtale
    infer_instance

private theorem pullbackChartIso_coordIdeal {P P₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : P ⟶ Spec (CommRingCat.of k)} (π : P₁ ⟶ P) {V : P.Opens} {n : ℕ}
    (c : EtaleChart p V n) [IsIso (π ∣_ V)] (T : Finset (Fin n)) :
    (etaleChartPullbackOfIsIso π c).coordIdeal T = (c.coordIdeal T).comap (π ∣_ V) := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  show (coordSubspaceIdeal k n T).comap ((π ∣_ V) ≫ c.map) = _
  rw [Scheme.IdealSheafData.comap_comp]

private theorem exists_etaleChart_of_isMaxContactHypersurface {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    [AlgebraicGeometry.Smooth p] (A : X.IdealSheafData) (μ : ℕ) (H : X.IdealSheafData)
    (hH : IsMaxContactHypersurface k p A μ H) (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal H U = ⊤ ∨ ∃ j, restrictIdeal H U = c.coordIdeal {j} := by
  obtain ⟨U, hU, hxU, hcase⟩ := hH x
  rcases hcase with ⟨-, htop⟩ | ⟨n, c, j, hHU, -⟩
  · obtain ⟨V, nV, hxV, hVU, hVaff, ⟨cV⟩⟩ := exists_etaleChart_le p x U hxU
    exact ⟨V, hxV, nV, cV, Or.inl (restrictIdeal_eq_top_of_le H hVU htop)⟩
  · exact ⟨U, hxU, n, c, Or.inr ⟨j, hHU⟩⟩

private theorem inStrictNormalCrossingPosition_singleton_of_isMaxContactHypersurface {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [AlgebraicGeometry.Smooth p]
    (A : X.IdealSheafData) (μ : ℕ) (H : X.IdealSheafData)
    (hH : IsMaxContactHypersurface k p A μ H) :
    InStrictNormalCrossingPosition p [H] := by
  rw [inStrictNormalCrossingPosition_iff]
  constructor
  · intro D hD
    simp only [List.mem_singleton] at hD
    subst hD
    exact isSmoothDivisor_of_locally_coordIdeal D
      (fun x => exists_etaleChart_of_isMaxContactHypersurface p A μ D hH x)
  · intro x
    refine inStrictNormalCrossingPositionAt_of_exists_etaleChart ?_
    obtain ⟨U, hxU, n, c, hcase⟩ := exists_etaleChart_of_isMaxContactHypersurface p A μ H hH x
    rcases hcase with htop | ⟨j, hj⟩
    · refine ⟨U, hxU, n, c, (fun _ => none), ?_, ?_, ?_⟩
      · intro i _ i' _ t h1 _
        simp at h1
      · intro i hi _
        have hi0 : i = 0 := Nat.lt_one_iff.mp hi
        subst hi0
        simpa using htop
      · intro i _ t h
        simp at h
    · refine ⟨U, hxU, n, c, (fun i => match i with | 0 => some j | _ => none), ?_, ?_, ?_⟩
      · intro i hi i' hi' t _ _
        have e1 : i = 0 := Nat.lt_one_iff.mp hi
        have e2 : i' = 0 := Nat.lt_one_iff.mp hi'
        omega
      · intro i hi h
        have hi0 : i = 0 := Nat.lt_one_iff.mp hi
        subst hi0
        exact absurd (show (some j : Option (Fin n)) = none from h) (by simp)
      · intro i hi t h
        have hi0 : i = 0 := Nat.lt_one_iff.mp hi
        subst hi0
        have hjt : j = t := Option.some.inj (show (some j : Option (Fin n)) = some t from h)
        subst hjt
        simpa using hj

theorem comap_maxContactIdeal_le_exceptionalIdeal_mul (k : Type u) [Field k] [CharZero k] {P P₁ : Scheme.{u}}
    (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (π : P₁ ⟶ P) [IsLocallyNoetherian P₁] [AlgebraicGeometry.Smooth (π ≫ p)]
    [LocallyOfFiniteType (π ≫ p)] (Z : P.IdealSheafData) (E : List P.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (A : P.IdealSheafData) (A₁ : P₁.IdealSheafData)
    (μ : ℕ) (hμ : 1 ≤ μ) (hA : A ≤ Z ^ μ)
    (htr : Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π) :
    (maxContactIdeal k p A μ).comap π ≤
      Blowup.exceptionalIdeal π Z * maxContactIdeal k (π ≫ p) A₁ μ := by
  have hA1 : controlledTransform π Z A μ hπ hA = A₁ :=
    (eq_controlledTransform_of_mul_eq_comap π Z A μ hπ hA A₁ htr).symm
  have h : (derivIdealSheafIterate k p (μ - 1) A).comap π ≤
      Blowup.exceptionalIdeal π Z ^ (μ - (μ - 1)) *
        derivIdealSheafIterate k (π ≫ p) (μ - 1) (controlledTransform π Z A μ hπ hA) :=
    comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p π Z E hZ hπ A μ hA (μ - 1)
      (Nat.sub_le μ 1)
  rw [hA1] at h
  have hμ1 : μ - (μ - 1) = 1 := by omega
  rw [hμ1, pow_one] at h
  rw [maxContactIdeal_eq_derivIdealSheafIterate, maxContactIdeal_eq_derivIdealSheafIterate]
  exact h

theorem mem_orderAtLeastLocus_base_of_mem_orderAtLeastLocus_transform (k : Type u) [Field k] [CharZero k]
    {P P₁ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [LocallyOfFiniteType p] (π : P₁ ⟶ P) [IsLocallyNoetherian P₁]
    [AlgebraicGeometry.Smooth (π ≫ p)] [LocallyOfFiniteType (π ≫ p)] (Z : P.IdealSheafData)
    (E : List P.IdealSheafData) (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (A : P.IdealSheafData) (A₁ : P₁.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ) (hA : A ≤ Z ^ μ)
    (htr : Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π) (y : P₁) (hy : y ∈ orderAtLeastLocus A₁ μ) :
    π.base y ∈ orderAtLeastLocus A μ := by
  by_contra hcon
  have hsucc : μ - 1 + 1 = μ := by omega
  have hz : orderAt A (π.base y) ≤ ((μ - 1 : ℕ) : ℕ∞) := by
    rw [orderAt_le_iff_notMem_orderAtLeastLocus, hsucc]
    exact hcon
  have hA' : A ≤ Z ^ (μ - 1) := by
    refine le_trans hA ?_
    have hpow : Z ^ μ = Z ^ (μ - 1) * Z := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow]
    exact mul_le_left_idealSheafData _ _
  have hEA : Blowup.exceptionalIdeal π Z * A₁ = controlledTransform π Z A (μ - 1) hπ hA' := by
    refine eq_controlledTransform_of_mul_eq_comap π Z A (μ - 1) hπ hA' _ ?_
    calc Blowup.exceptionalIdeal π Z ^ (μ - 1) * (Blowup.exceptionalIdeal π Z * A₁)
        = Blowup.exceptionalIdeal π Z ^ (μ - 1 + 1) * A₁ := by rw [pow_succ, mul_assoc]
      _ = A.comap π := by rw [hsucc]; exact htr
  have h1 := orderAt_controlledTransform_le k p π Z E hZ hπ A (μ - 1) hA' (π.base y) hz y rfl
  rw [← hEA] at h1
  have hle : Blowup.exceptionalIdeal π Z * A₁ ≤ A₁ := mul_le_right_idealSheafData _ _
  have h2 : orderAt A₁ y ≤ ((μ - 1 : ℕ) : ℕ∞) := le_trans (orderAt_le_of_le hle y) h1
  rw [orderAt_le_iff_notMem_orderAtLeastLocus, hsucc] at h2
  exact h2 hy

theorem le_center_of_isMaxContactHypersurface (k : Type u) [Field k] [CharZero k]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [LocallyOfFiniteType p] (Z : P.IdealSheafData) (E : List P.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith p Z E) (A : P.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ)
    (hsupp : (Z.support : Set ↥P) ⊆ orderAtLeastLocus A μ) (H : P.IdealSheafData)
    (hH : IsMaxContactHypersurface k p A μ H) :
    H ≤ Z := by
  have h1 : (Z.support : Set ↥P) ⊆ (H.support : Set ↥P) :=
    hsupp.trans (hH.orderAtLeastLocus_subset_support hμ)
  have h2 : (Z.support : Set ↥P) ⊆ orderAtLeastLocus H 1 := by
    intro x hx
    rw [mem_orderAtLeastLocus_one_iff]
    exact h1 hx
  have h3 := le_pow_of_hasStrictNormalCrossingsWith p Z H E hZ 1 h2
  rwa [pow_one] at h3

theorem isMaxContactHypersurfaceAt_strictTransform_of_etaleChart (k : Type u) [Field k] [CharZero k]
    {P P₁ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [LocallyOfFiniteType p] (π : P₁ ⟶ P) [IsLocallyNoetherian P₁]
    [AlgebraicGeometry.Smooth (π ≫ p)] [LocallyOfFiniteType (π ≫ p)] (Z : P.IdealSheafData)
    (E : List P.IdealSheafData) (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (A : P.IdealSheafData) (A₁ : P₁.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ) (hA : A ≤ Z ^ μ)
    (htr : Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π) (H : P.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)] {U' : P.Opens} (hU' : IsAffineOpen U')
    {m : ℕ} (c : EtaleChart p U' m) (S : Finset (Fin m)) (j₀ : Fin m) (hj₀ : j₀ ∈ S)
    (hZU : restrictIdeal Z U' = c.coordIdeal S)
    (hHU : restrictIdeal H U' = c.coordIdeal {j₀})
    (hcoord : c.coord j₀ ∈ (maxContactIdeal k p A μ).ideal ⟨U', hU'⟩)
    (x₁ : P₁) (hx₁ : x₁ ∈ π ⁻¹ᵁ U') :
    IsMaxContactHypersurfaceAt k (π ≫ p) A₁ μ (Blowup.strictTransform π Z H) x₁ := by
  classical
  obtain ⟨s, hs, hx₁D⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZU x₁ hx₁
  set B := blowupChartOfIsBlowup π c S hπ hZU s hs with hBdef
  obtain ⟨V, _, hxV, hVD, hVaff, -⟩ :=
    exists_etaleChart_le (π ≫ p) x₁ B.domain hx₁D
  have hE : restrictIdeal (Blowup.exceptionalIdeal π Z) B.domain = B.chart.coordIdeal {s} :=
    B.restrictIdeal_exceptionalIdeal Z hs hZU
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (B.chart.coordIdeal {s}) := by
    refine isLocallyGeneratedByNonZeroDivisor_of_locally_coordIdeal (p := B.domain.ι ≫ (π ≫ p)) _ (fun x => ?_)
    exact ⟨⊤, trivial, m, B.chart.restrictOpens ⊤,
      Or.inr ⟨s, B.chart.restrictIdeal_coordIdeal ⊤ {s}⟩⟩
  have key : restrictIdeal (H.comap π) B.domain ≤
      B.chart.coordIdeal {s} * restrictIdeal (maxContactIdeal k (π ≫ p) A₁ μ) B.domain := by
    have h1 : restrictIdeal (H.comap π) B.domain
        ≤ restrictIdeal ((maxContactIdeal k p A μ).comap π) B.domain := by
      rw [B.restrictIdeal_comap H, B.restrictIdeal_comap (maxContactIdeal k p A μ)]
      refine Scheme.IdealSheafData.comap_mono _ ?_
      rw [hHU]
      exact (coordIdeal_singleton_le_restrictIdeal_iff k p hU' c j₀
        (maxContactIdeal k p A μ)).2 hcoord
    have h2 : restrictIdeal ((maxContactIdeal k p A μ).comap π) B.domain ≤
        restrictIdeal (Blowup.exceptionalIdeal π Z * maxContactIdeal k (π ≫ p) A₁ μ) B.domain :=
      Scheme.IdealSheafData.comap_mono _
        (comap_maxContactIdeal_le_exceptionalIdeal_mul k p π Z E hZ hπ A A₁ μ hμ hA htr)
    have hmul : restrictIdeal (Blowup.exceptionalIdeal π Z * maxContactIdeal k (π ≫ p) A₁ μ) B.domain =
        restrictIdeal (Blowup.exceptionalIdeal π Z) B.domain *
          restrictIdeal (maxContactIdeal k (π ≫ p) A₁ μ) B.domain :=
      Scheme.IdealSheafData.comap_mul _ _ _
    rw [hmul, hE] at h2
    exact h1.trans h2
  by_cases hj : j₀ = s
  · have hHU' : restrictIdeal H U' = c.coordIdeal {s} := by rw [hHU, hj]
    have hcomap : restrictIdeal (H.comap π) B.domain = B.chart.coordIdeal {s} :=
      B.restrictIdeal_comap_coordIdeal_self H hHU'
    have hST : restrictIdeal (Blowup.strictTransform π Z H) B.domain = ⊤ :=
      B.restrictIdeal_strictTransform_coordIdeal_self Z H hs hZU hHU'
    have htop : restrictIdeal (maxContactIdeal k (π ≫ p) A₁ μ) B.domain = ⊤ := by
      refine top_le_iff.1 (hcart.le_of_mul_le_mul ?_)
      rw [Scheme.IdealSheafData.mul_top]
      exact le_trans (le_of_eq hcomap.symm) key
    have hdisj : Disjoint (orderAtLeastLocus A₁ μ) ((V : Set ↥P₁)) := by
      rw [Set.disjoint_left]
      intro x hxc hxV
      have hx1 : x ∈ (maxContactIdeal k (π ≫ p) A₁ μ).support :=
        mem_support_maxContactIdeal_of_mem_orderAtLeastLocus k (π ≫ p) A₁ hμ hxc
      exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top _ B.domain htop x (hVD hxV) hx1
    exact ⟨V, hVaff, hxV, Or.inl ⟨hdisj, restrictIdeal_eq_top_of_le _ hVD hST⟩⟩
  · have hcomap : restrictIdeal (H.comap π) B.domain =
        B.chart.coordIdeal {j₀} * B.chart.coordIdeal {s} :=
      B.restrictIdeal_comap_coordIdeal_of_mem H j₀ hj₀ hj hHU
    have hST : restrictIdeal (Blowup.strictTransform π Z H) B.domain = B.chart.coordIdeal {j₀} :=
      B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZU j₀ hj₀ hj hHU
    have hmc : B.chart.coordIdeal {j₀} ≤
        restrictIdeal (maxContactIdeal k (π ≫ p) A₁ μ) B.domain := by
      refine hcart.le_of_mul_le_mul ?_
      rw [mul_comm (B.chart.coordIdeal {s}) (B.chart.coordIdeal {j₀})]
      exact le_trans (le_of_eq hcomap.symm) key
    have hSTV : restrictIdeal (Blowup.strictTransform π Z H) V =
        (B.chart.restrict hVD).coordIdeal {j₀} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hVD B.chart (Blowup.strictTransform π Z H) {j₀} hST
    refine ⟨V, hVaff, hxV, Or.inr ⟨m, B.chart.restrict hVD, j₀, hSTV, ?_⟩⟩
    show (B.chart.restrict hVD).coordIdeal {j₀} ≤
      restrictIdeal (maxContactIdeal k (π ≫ p) A₁ μ) V
    have h4 : restrictIdeal (Blowup.strictTransform π Z H) B.domain ≤
        restrictIdeal (maxContactIdeal k (π ≫ p) A₁ μ) B.domain := by
      rw [hST]; exact hmc
    have h5 := restrictIdeal_le_of_le_opens hVD h4
    rw [← hSTV]
    exact h5

theorem isMaxContactHypersurfaceAt_strictTransform_of_mem_support (k : Type u) [Field k] [CharZero k]
    {P P₁ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [LocallyOfFiniteType p] (π : P₁ ⟶ P) [IsLocallyNoetherian P₁]
    [AlgebraicGeometry.Smooth (π ≫ p)] [LocallyOfFiniteType (π ≫ p)] (Z : P.IdealSheafData)
    (E : List P.IdealSheafData) (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (A : P.IdealSheafData) (A₁ : P₁.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ)
    (hsupp : (Z.support : Set ↥P) ⊆ orderAtLeastLocus A μ) (hA : A ≤ Z ^ μ)
    (htr : Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π) (H : P.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hH : IsMaxContactHypersurface k p A μ H) (x₁ : P₁) (hx₁ : π.base x₁ ∈ Z.support) :
    IsMaxContactHypersurfaceAt k (π ≫ p) A₁ μ (Blowup.strictTransform π Z H) x₁ := by
  classical
  have hzA : π.base x₁ ∈ orderAtLeastLocus A μ := hsupp hx₁
  have hsm : AlgebraicGeometry.Smooth (Z.subschemeι ≫ p) :=
    smooth_subschemeι_comp_of_hasStrictNormalCrossingsWith Z E hZ
  have hZnil : HasStrictNormalCrossingsWith p Z ([] : List P.IdealSheafData) := hasStrictNormalCrossingsWith_nil_of_smooth p Z
  have hHZ : H ≤ Z := le_center_of_isMaxContactHypersurface k p Z E hZ A μ hμ hsupp H hH
  have hsnc : InStrictNormalCrossingPosition p (H :: ([] : List P.IdealSheafData)) :=
    inStrictNormalCrossingPosition_singleton_of_isMaxContactHypersurface p A μ H hH
  obtain ⟨U, hU, hzU, m, c, lab, S, m', c', j0, lab', hZU, hHU, hlab, _, hlab', hj0⟩ :=
    exists_etaleCharts_of_inStrictNormalCrossingPosition_cons p Z H [] hsnc hZnil hHZ (π.base x₁) hx₁
  have hSprime : ∀ i ∈ S, c.coord i ∈ (hU.primeIdealOf ⟨π.base x₁, hzU⟩).asIdeal := by
    intro i hi
    have h1 : Z.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m))) :=
      c.ideal_eq_span_coord hU Z S hZU
    have h2 : c.coord i ∈ Z.ideal ⟨U, hU⟩ := by
      rw [h1]
      exact Ideal.subset_span ⟨i, hi, rfl⟩
    exact ideal_le_primeIdealOf Z hU hzU hx₁ h2
  obtain ⟨a, hcoeff, j, hjS, haj, -⟩ :=
    exists_coord_eq_sum_coeff_not_mem_of_le p hU hzU c lab S c' j0 lab' Z H [] hx₁ hlab hZU hHU hlab'
      hj0 hHZ
  obtain ⟨V, hV, hVU, hzV, cV, hcne, hcj, huj⟩ :=
    exists_etaleChart_update_coord p hU c hzU S a j hjS hSprime haj
  have hZV : restrictIdeal Z V = cV.coordIdeal S := by
    refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV cV Z S ?_
    have h1 : Z.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m))) :=
      c.ideal_eq_span_coord hU Z S hZU
    have h2 := ideal_eq_span_image_map_of_le Z hU hV hVU (c.coord '' (S : Set (Fin m))) h1
    rw [h2, Set.image_image]
    rw [← span_image_update_sum_eq
      (fun i => (P.presheaf.map (homOfLE hVU).op).hom (c.coord i)) S
      (fun i => (P.presheaf.map (homOfLE hVU).op).hom (a i)) j hjS huj]
    congr 1
    refine Set.image_congr ?_
    intro i hi
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self, hcj, map_sum]
      exact Finset.sum_congr rfl (fun t _ => (map_mul _ _ _).symm)
    · rw [Function.update_of_ne hij, hcne i hij]
  have hHV : restrictIdeal H V = cV.coordIdeal {j} := by
    refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV cV H {j} ?_
    have h1 : H.ideal ⟨U, hU⟩ =
        Ideal.span (c'.coord '' ((({j0} : Finset (Fin m')) : Set (Fin m')))) :=
      c'.ideal_eq_span_coord hU H {j0} hHU
    have h2 := ideal_eq_span_image_map_of_le H hU hV hVU _ h1
    have hone : (P.presheaf.map (homOfLE hVU).op).hom (c'.coord j0) = cV.coord j := by
      rw [hcoeff, hcj]
    rw [h2]
    simp only [Finset.coe_singleton, Set.image_singleton, hone]
  obtain ⟨W, hW, hzW, hcase⟩ := hH (π.base x₁)
  have hHmc : restrictIdeal H W ≤ restrictIdeal (maxContactIdeal k p A μ) W := by
    rcases hcase with ⟨hdisj, -⟩ | ⟨nW, cW, jW, hHW, hmcW⟩
    · exact absurd hzW (Set.disjoint_left.mp hdisj hzA)
    · rw [hHW]
      exact hmcW
  obtain ⟨V', _, hzV', hV'le, hV'aff, -⟩ :=
    exists_etaleChart_le p (π.base x₁) (V ⊓ W) ⟨hzV, hzW⟩
  have hV'V : V' ≤ V := fun y hy => (hV'le hy).1
  have hV'W : V' ≤ W := fun y hy => (hV'le hy).2
  have hZV' : restrictIdeal Z V' = (cV.restrict hV'V).coordIdeal S :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hV'V cV Z S hZV
  have hHV' : restrictIdeal H V' = (cV.restrict hV'V).coordIdeal {j} :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hV'V cV H {j} hHV
  have hcoordmem : (cV.restrict hV'V).coord j ∈ (maxContactIdeal k p A μ).ideal ⟨V', hV'aff⟩ := by
    refine (coordIdeal_singleton_le_restrictIdeal_iff k p hV'aff (cV.restrict hV'V) j
      (maxContactIdeal k p A μ)).1 ?_
    rw [← hHV']
    exact restrictIdeal_le_of_le_opens hV'W hHmc
  exact isMaxContactHypersurfaceAt_strictTransform_of_etaleChart k p π Z E hZ hπ A A₁ μ hμ hA htr H
    hV'aff (cV.restrict hV'V) S j hjS hZV' hHV' hcoordmem x₁ hzV'

theorem isMaxContactHypersurfaceAt_strictTransform_of_notMem_support (k : Type u) [Field k] [CharZero k]
    {P P₁ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [LocallyOfFiniteType p] (π : P₁ ⟶ P) [IsLocallyNoetherian P₁]
    [AlgebraicGeometry.Smooth (π ≫ p)] [LocallyOfFiniteType (π ≫ p)] (Z : P.IdealSheafData)
    (E : List P.IdealSheafData) (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (A : P.IdealSheafData) (A₁ : P₁.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ) (hA : A ≤ Z ^ μ)
    (htr : Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π) (H : P.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hH : IsMaxContactHypersurface k p A μ H) (x₁ : P₁) (hx₁ : π.base x₁ ∉ Z.support) :
    IsMaxContactHypersurfaceAt k (π ≫ p) A₁ μ (Blowup.strictTransform π Z H) x₁ := by
  classical
  obtain ⟨U, hU, hxU, hcase⟩ := hH (π.base x₁)
  have hxc : π.base x₁ ∈ Z.support.compl := hx₁
  obtain ⟨V, _, hxV, hVle, hVaff, -⟩ :=
    exists_etaleChart_le p (π.base x₁) (U ⊓ Z.support.compl) ⟨hxU, hxc⟩
  have hVU : V ≤ U := fun y hy => (hVle hy).1
  have hx₁V : x₁ ∈ π ⁻¹ᵁ V := hxV
  have hrestrict : ∀ K : P.IdealSheafData,
      restrictIdeal (K.comap π) (π ⁻¹ᵁ V) = (restrictIdeal K V).comap (π ∣_ V) := by
    intro K
    rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι]
  have hZtop : Z.comap ((π ⁻¹ᵁ V).ι ≫ π) = ⊤ := by
    rw [Scheme.IdealSheafData.comap_comp]
    refine Blowup.comap_eq_top_of_notMem_support _ (Z.comap π) (fun y => ?_)
    show (y.1 : ↥P₁) ∉ (Z.comap π).support
    have hy : π.base y.1 ∈ V := y.2
    rw [Scheme.IdealSheafData.support_comap]
    exact (hVle hy).2
  have hST : restrictIdeal (Blowup.strictTransform π Z H) (π ⁻¹ᵁ V) =
      restrictIdeal (H.comap π) (π ⁻¹ᵁ V) :=
    restrictIdeal_strictTransform_eq_of_comap_eq_top π Z H V hZtop
  rcases hcase with ⟨hdisj, hHtop⟩ | ⟨n, c, j₀, hHU, hmc⟩
  · obtain ⟨V₁, _, hx₁V₁, hV₁le, hV₁aff, -⟩ :=
      exists_etaleChart_le (π ≫ p) x₁ (π ⁻¹ᵁ V) hx₁V
    refine ⟨V₁, hV₁aff, hx₁V₁, Or.inl ⟨?_, ?_⟩⟩
    · rw [Set.disjoint_left]
      intro y hy hyV
      have h1 : π.base y ∈ orderAtLeastLocus A μ :=
        mem_orderAtLeastLocus_base_of_mem_orderAtLeastLocus_transform k p π Z E hZ hπ A A₁ μ hμ hA htr y hy
      have h2 : π.base y ∈ V := hV₁le hyV
      exact (Set.disjoint_left.mp hdisj h1) (hVU h2)
    · have h3 : restrictIdeal (H.comap π) (π ⁻¹ᵁ V) = ⊤ :=
        restrictIdeal_comap_preimage_eq_top π V H (restrictIdeal_eq_top_of_le H hVU hHtop)
      have h4 : restrictIdeal (Blowup.strictTransform π Z H) (π ⁻¹ᵁ V) = ⊤ := by rw [hST, h3]
      exact restrictIdeal_eq_top_of_le _ hV₁le h4
  · have hHV : restrictIdeal H V = (c.restrict hVU).coordIdeal {j₀} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hVU c H {j₀} hHU
    have hZV : Z.comap V.ι = ⊤ := by
      refine Blowup.comap_eq_top_of_notMem_support V.ι Z (fun y => ?_)
      show (y.1 : ↥P) ∉ Z.support
      exact (hVle y.2).2
    have hbiso : IsIso (π ∣_ V) := by
      have hb := hπ.restrict V
      rw [hZV] at hb
      exact hb.isIso_of_top
    have hSTV : restrictIdeal (Blowup.strictTransform π Z H) (π ⁻¹ᵁ V) =
        (etaleChartPullbackOfIsIso π (c.restrict hVU)).coordIdeal {j₀} := by
      rw [hST, hrestrict H, hHV, pullbackChartIso_coordIdeal]
    have hmcV : (etaleChartPullbackOfIsIso π (c.restrict hVU)).coordIdeal {j₀} ≤
        restrictIdeal (maxContactIdeal k (π ≫ p) A₁ μ) (π ⁻¹ᵁ V) := by
      have h1 : restrictIdeal H V ≤ restrictIdeal (maxContactIdeal k p A μ) V := by
        refine restrictIdeal_le_of_le_opens hVU ?_
        rw [hHU]
        exact hmc
      have h2 : (etaleChartPullbackOfIsIso π (c.restrict hVU)).coordIdeal {j₀} ≤
          restrictIdeal ((maxContactIdeal k p A μ).comap π) (π ⁻¹ᵁ V) := by
        rw [pullbackChartIso_coordIdeal, hrestrict (maxContactIdeal k p A μ), ← hHV]
        exact Scheme.IdealSheafData.comap_mono _ h1
      refine h2.trans ?_
      refine Scheme.IdealSheafData.comap_mono _ ?_
      refine le_trans (comap_maxContactIdeal_le_exceptionalIdeal_mul k p π Z E hZ hπ A A₁ μ hμ hA htr) ?_
      exact mul_le_right_idealSheafData _ _
    obtain ⟨V₁, _, hx₁V₁, hV₁le, hV₁aff, -⟩ :=
      exists_etaleChart_le (π ≫ p) x₁ (π ⁻¹ᵁ V) hx₁V
    have hSTV₁ : restrictIdeal (Blowup.strictTransform π Z H) V₁ =
        ((etaleChartPullbackOfIsIso π (c.restrict hVU)).restrict hV₁le).coordIdeal {j₀} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hV₁le (etaleChartPullbackOfIsIso π (c.restrict hVU))
        (Blowup.strictTransform π Z H) {j₀} hSTV
    refine ⟨V₁, hV₁aff, hx₁V₁,
      Or.inr ⟨n, (etaleChartPullbackOfIsIso π (c.restrict hVU)).restrict hV₁le, j₀, hSTV₁, ?_⟩⟩
    show ((etaleChartPullbackOfIsIso π (c.restrict hVU)).restrict hV₁le).coordIdeal {j₀} ≤
      restrictIdeal (maxContactIdeal k (π ≫ p) A₁ μ) V₁
    have h4 : restrictIdeal (Blowup.strictTransform π Z H) (π ⁻¹ᵁ V) ≤
        restrictIdeal (maxContactIdeal k (π ≫ p) A₁ μ) (π ⁻¹ᵁ V) := by
      rw [hSTV]
      exact hmcV
    have h5 := restrictIdeal_le_of_le_opens hV₁le h4
    rw [← hSTV₁]
    exact h5

theorem isMaxContactHypersurface_strictTransform_of_quasiCompact (k : Type u) [Field k]
    [CharZero k] {P P₁ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p] (π : P₁ ⟶ P) [IsLocallyNoetherian P₁]
    [LocallyOfFiniteType (π ≫ p)] (Z : P.IdealSheafData) (E : List P.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (A : P.IdealSheafData)
    (A₁ : P₁.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ)
    (hsupp : (Z.support : Set ↥P) ⊆ orderAtLeastLocus A μ)
    (htr : Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π) (H : P.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hH : IsMaxContactHypersurface k p A μ H) :
    IsMaxContactHypersurface k (π ≫ p) A₁ μ (Blowup.strictTransform π Z H) := by
  have : AlgebraicGeometry.Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hZ hπ
  have hA : A ≤ Z ^ μ := le_pow_of_hasStrictNormalCrossingsWith p Z A E hZ μ hsupp
  intro x₁
  by_cases hx : π.base x₁ ∈ Z.support
  · exact isMaxContactHypersurfaceAt_strictTransform_of_mem_support k p π Z E hZ hπ A A₁ μ hμ hsupp hA
      htr H hH x₁ hx
  · exact isMaxContactHypersurfaceAt_strictTransform_of_notMem_support k p π Z E hZ hπ A A₁ μ hμ hA
      htr H hH x₁ hx

theorem isMaxContactHypersurface_strictTransform_of_orderAt_le (k : Type u) [Field k] [CharZero k]
    {P P₁ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [LocallyOfFiniteType p] (π : P₁ ⟶ P) [IsLocallyNoetherian P₁] [LocallyOfFiniteType (π ≫ p)]
    (Z : P.IdealSheafData) (E : List P.IdealSheafData) (hZ : HasStrictNormalCrossingsWith p Z E)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (A : P.IdealSheafData) (A₁ : P₁.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ)
    (_hord : ∀ x : P, orderAt A x ≤ (μ : ℕ∞))
    (hsupp : (Z.support : Set ↥P) ⊆ orderAtLeastLocus A μ)
    (htr : Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π) (H : P.IdealSheafData) :
    IsMaxContactHypersurface k p A μ H →
      IsMaxContactHypersurface k (π ≫ p) A₁ μ (Blowup.strictTransform π Z H) := by
  intro hH
  exact isMaxContactHypersurface_strictTransform_of_quasiCompact k p π Z E hZ hπ A A₁ μ hμ
    hsupp htr H hH

end

end FunctorialResolution.EmbeddedResolution
