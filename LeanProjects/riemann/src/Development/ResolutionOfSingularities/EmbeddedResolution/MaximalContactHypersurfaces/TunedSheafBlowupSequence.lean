import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafLcm
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem exists_affineOpen_mem {X : Scheme.{u}} (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1.1 := by
  have hx : x ∈ (⨆ U : X.affineOpens, (U : X.Opens)) := by
    rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
    trivial
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨U, hU⟩

private theorem stalkIdeal_iSup_le_of_forall {X : Scheme.{u}} {ι : Type}
    (F : ι → X.IdealSheafData) (x : X) (Jd : Ideal (X.presheaf.stalk x))
    (h : ∀ i, stalkIdeal (F i) x ≤ Jd) : stalkIdeal (iSup F) x ≤ Jd := by
  obtain ⟨U, hxU0⟩ := exists_affineOpen_mem x
  have hxU : x ∈ U.1 := hxU0
  have hUeq : (iSup F).ideal U = ⨆ i, (F i).ideal U := by
    simp only [Scheme.IdealSheafData.ideal_iSup, iSup_apply]
  rw [stalkIdeal_eq_map_germ _ x U hxU, hUeq, (Ideal.gc_map_comap _).l_iSup]
  refine iSup_le fun i => ?_
  rw [← stalkIdeal_eq_map_germ (F i) x U hxU]
  exact h i

private theorem sum_map_range_eq_sum_range (w : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map w).sum = ∑ j ∈ Finset.range n, w j := by
  induction n with
  | zero => simp
  | succ t ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp

private theorem prod_map_range_pow_ite_eq {X : Scheme.{u}} (f : ℕ → X.IdealSheafData) (s n : ℕ) :
    ((List.range (n + 1)).map (fun j => f j ^ (if j = 0 then s else 0))).prod = f 0 ^ s := by
  induction n with
  | zero => simp
  | succ t ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih]
      simp

private theorem mem_orderAtLeastLocus_prod_map_of_forall {X : Scheme.{u}} (x : X)
    (g : ℕ → X.IdealSheafData) (w : ℕ → ℕ) (h : ∀ j, x ∈ orderAtLeastLocus (g j) (w j)) (l : List ℕ) :
    x ∈ orderAtLeastLocus ((l.map g).prod) ((l.map w).sum) := by
  induction l with
  | nil =>
      simp only [List.map_nil, List.prod_nil, List.sum_nil]
      rw [orderAtLeastLocus_zero]
      exact Set.mem_univ x
  | cons a t ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact inter_orderAtLeastLocus_subset_orderAtLeastLocus_mul _ _ _ _ ⟨h a, ih⟩

theorem orderAtLeastLocus_subset_orderAtLeastLocus_tunedSheaf (k : Type u) [Field k] [IsNoetherianRing k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (A : Y.IdealSheafData) (m n : ℕ) :
    orderAtLeastLocus A m ⊆ orderAtLeastLocus (tunedSheaf k p A m n) n := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff_stalkIdeal_le_maximalIdeal_pow, tunedSheaf_eq_iSup]
  refine stalkIdeal_iSup_le_of_forall _ x _ ?_
  rintro ⟨c, hc⟩
  refine (mem_orderAtLeastLocus_iff_stalkIdeal_le_maximalIdeal_pow _ n x).mp ?_
  have key := mem_orderAtLeastLocus_prod_map_of_forall x (fun j => derivIdealSheafIterate k p j A ^ c j)
      (fun j => c j * (m - j))
      (fun j => orderAtLeastLocus_subset_orderAtLeastLocus_pow _ _ _
        (orderAtLeastLocus_subset_orderAtLeastLocus_derivIdealSheafIterate k p A j m hx)) (List.range m)
  have hn : n ≤ ((List.range m).map (fun j => c j * (m - j))).sum := by
    rw [sum_map_range_eq_sum_range]
    refine le_trans hc (le_of_eq ?_)
    exact Finset.sum_congr rfl fun j _ => Nat.mul_comm _ _
  exact orderAtLeastLocus_subset_of_le _ hn key

theorem orderAtLeastLocus_pow_mul_eq_orderAtLeastLocus (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (A : X.IdealSheafData)
    (m : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    orderAtLeastLocus (A ^ s) (m * s) = orderAtLeastLocus A m := by
  rw [mul_comm]
  exact orderAtLeastLocus_pow_mul k p A hs m

theorem orderAtLeastLocus_eq_of_pow_le_of_le_tunedSheaf (k : Type u) [Field k] [CharZero k]
    [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p] (I J : X.IdealSheafData) (m : ℕ)
    {s : ℕ} (hs : 1 ≤ s) (h1 : I ^ s ≤ J) (h2 : J ≤ tunedSheaf k p I m (m * s)) :
    orderAtLeastLocus J (m * s) = orderAtLeastLocus I m := by
  refine Set.Subset.antisymm ?_ ?_
  · rw [← orderAtLeastLocus_pow_mul_eq_orderAtLeastLocus k p I m hs]
    exact orderAtLeastLocus_subset_of_le_ideal h1 (m * s)
  · exact fun x hx => orderAtLeastLocus_subset_of_le_ideal h2 (m * s)
      (orderAtLeastLocus_subset_orderAtLeastLocus_tunedSheaf k p I m (m * s) hx)

theorem pow_le_tunedSheaf (k : Type u) [Field k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData)
    {m : ℕ} (hm : 1 ≤ m) (s : ℕ) :
    I ^ s ≤ tunedSheaf k p I m (m * s) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hsum : (m' + 1) * s ≤
      ∑ j ∈ Finset.range (m' + 1), (m' + 1 - j) * (if j = 0 then s else 0) := by
    have h := Finset.sum_eq_single_of_mem (s := Finset.range (m' + 1))
      (f := fun j => (m' + 1 - j) * (if j = 0 then s else 0)) 0
      (Finset.mem_range.mpr (Nat.succ_pos m'))
      (fun b _ hb => by simp [hb])
    rw [h]
    simp
  have hle := le_iSup
    (fun c : {c : ℕ → ℕ // (m' + 1) * s ≤ ∑ j ∈ Finset.range (m' + 1), (m' + 1 - j) * c j} =>
      ((List.range (m' + 1)).map (fun j => derivIdealSheafIterate k p j I ^ (c.1 j))).prod)
    ⟨fun j => if j = 0 then s else 0, hsum⟩
  rw [tunedSheaf_eq_iSup]
  refine le_trans (le_of_eq ?_) hle
  have := prod_map_range_pow_ite_eq (fun j => derivIdealSheafIterate k p j I) s m'
  rw [this]
  simp

theorem exists_tuningExponent_eq {m : ℕ} (hm : 1 ≤ m) :
    ∃ r s : ℕ, m - 1 ≤ r ∧ tuningExponent m = r * lcmUpTo m ∧ 1 ≤ s ∧ tuningExponent m = m * s := by
  rcases Nat.lt_or_ge m 2 with h | h
  · have hm1 : m = 1 := by omega
    subst hm1
    refine ⟨1, 1, by omega, ?_, le_rfl, ?_⟩
    · rw [tuningExponent_one, lcmUpTo_one]
    · rw [tuningExponent_one]
  · obtain ⟨t, ht⟩ := dvd_lcmUpTo m m (by omega) le_rfl
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0, Nat.mul_zero] at ht
        have hpos := lcmUpTo_pos m
        omega
      · exact h0
    refine ⟨m - 1, (m - 1) * t, le_rfl, tuningExponent_of_two_le h, ?_, ?_⟩
    · have : 0 < (m - 1) * t := Nat.mul_pos (by omega) htpos
      omega
    · rw [tuningExponent_of_two_le h, ht]
      ring

private theorem smooth_projectionToBase_comp_of_snc (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (E : List X.IdealSheafData) (d : BlowupSequenceData X)
    (hiso : AlgebraicGeometry.Smooth d.isoZero.hom)
    (hsnc : ∀ i, i < d.length → HasStrictNormalCrossingsWith (d.projectionToBase i ≫ p) (d.center i) (d.boundaryFrom E i)) :
    ∀ i, i ≤ d.length → AlgebraicGeometry.Smooth (d.projectionToBase i ≫ p) := by
  intro i
  induction i with
  | zero =>
      intro _
      have := hiso
      rw [BlowupSequenceData.projectionToBase_zero]
      infer_instance
  | succ j ih =>
      intro hj
      have := ih (Nat.le_of_succ_le hj)
      have hb := smooth_comp_of_isBlowupAlongIdealSheaf (hsnc j hj) (d.isBlowup j hj)
      rw [BlowupSequenceData.projectionToBase_succ, Category.assoc]
      exact hb

private theorem locallyOfFiniteType_projectionToBase_comp_of_snc (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (E : List X.IdealSheafData) (d : BlowupSequenceData X)
    (hiso : AlgebraicGeometry.Smooth d.isoZero.hom)
    (hsnc : ∀ i, i < d.length → HasStrictNormalCrossingsWith (d.projectionToBase i ≫ p) (d.center i) (d.boundaryFrom E i)) :
    ∀ i, i ≤ d.length → LocallyOfFiniteType (d.projectionToBase i ≫ p) := by
  intro i hi
  have := smooth_projectionToBase_comp_of_snc k p E d hiso hsnc i hi
  infer_instance

private theorem pow_le_and_le_tunedSheaf_of_isBlowupAlongIdealSheaf (k : Type u) [Field k] [CharZero k]
    [IsNoetherianRing k] {P P₁ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p] (π : P₁ ⟶ P)
    (p₁ : P₁ ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p₁] (hp₁ : p₁ = π ≫ p)
    (Z : P.IdealSheafData) (E : List P.IdealSheafData) (hZ : HasStrictNormalCrossingsWith p Z E)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (m s : ℕ) (A B : P.IdealSheafData) (A' B' : P₁.IdealSheafData)
    (hA : A ≤ Z ^ m)
    (hA' : Blowup.exceptionalIdeal π Z ^ m * A' = A.comap π)
    (hB' : Blowup.exceptionalIdeal π Z ^ (m * s) * B' = B.comap π)
    (h1 : A ^ s ≤ B) (h2 : B ≤ tunedSheaf k p A m (m * s)) :
    A' ^ s ≤ B' ∧ B' ≤ tunedSheaf k p₁ A' m (m * s) := by
  have : IsLocallyNoetherian P₁ := LocallyOfFiniteType.isLocallyNoetherian p₁
  have : LocallyOfFiniteType (π ≫ p) := by
    rw [← hp₁]
    infer_instance
  have hF : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hπ
  constructor
  · refine hF.le_of_pow_mul_le_pow_mul (m * s) ?_
    have hcm : (A.comap π) ^ s ≤ B.comap π := by
      rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_pow]
      exact Scheme.IdealSheafData.comap_mono π h1
    calc Blowup.exceptionalIdeal π Z ^ (m * s) * A' ^ s
        = (Blowup.exceptionalIdeal π Z ^ m * A') ^ s := by rw [mul_pow, ← pow_mul]
      _ = (A.comap π) ^ s := by rw [hA']
      _ ≤ B.comap π := hcm
      _ = Blowup.exceptionalIdeal π Z ^ (m * s) * B' := hB'.symm
  · refine hF.le_of_pow_mul_le_pow_mul (m * s) ?_
    have hct : A' = controlledTransform π Z A m hπ hA :=
      eq_controlledTransform_of_mul_eq_comap π Z A m hπ hA A' hA'
    calc Blowup.exceptionalIdeal π Z ^ (m * s) * B' = B.comap π := hB'
      _ ≤ (tunedSheaf k p A m (m * s)).comap π := Scheme.IdealSheafData.comap_mono π h2
      _ ≤ Blowup.exceptionalIdeal π Z ^ (m * s) *
            tunedSheaf k p₁ (controlledTransform π Z A m hπ hA) m (m * s) :=
          comap_tunedSheaf_le_exceptionalIdeal_pow_mul k p π p₁ hp₁ Z E hZ hπ A m hA (m * s)
      _ = Blowup.exceptionalIdeal π Z ^ (m * s) * tunedSheaf k p₁ A' m (m * s) := by rw [hct]

private theorem orderAtLeastLocus_eq_and_exceptionalIdeal_dvd_of_blowupSequence (k : Type u) [Field k] [CharZero k]
    [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p] (I J : X.IdealSheafData) (m s : ℕ)
    (hs : 1 ≤ s) (h1 : I ^ s ≤ J) (h2 : J ≤ tunedSheaf k p I m (m * s))
    (E : List X.IdealSheafData) (d : BlowupSequenceData X)
    (hiso : AlgebraicGeometry.Smooth d.isoZero.hom)
    (hft : ∀ i, i ≤ d.length → LocallyOfFiniteType (d.projectionToBase i ≫ p))
    (hsnc : ∀ i, i < d.length → HasStrictNormalCrossingsWith (d.projectionToBase i ≫ p) (d.center i) (d.boundaryFrom E i))
    (hord : ∀ i, i < d.length →
      orderAtLeastLocus (d.controlledTransform J (m * s) i) (m * s) = orderAtLeastLocus (d.controlledTransform I m i) m →
      ((d.center i).support : Set ↥(d.obj i)) ⊆ orderAtLeastLocus (d.controlledTransform I m i) m) :
    (∀ i, i ≤ d.length →
        orderAtLeastLocus (d.controlledTransform J (m * s) i) (m * s) = orderAtLeastLocus (d.controlledTransform I m i) m) ∧
    (∀ i, i < d.length → ∃ B : (d.obj (i + 1)).IdealSheafData,
        Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * B = (d.controlledTransform I m i).comap (d.map i)) ∧
    (∀ i, i < d.length → ∃ B : (d.obj (i + 1)).IdealSheafData,
        Blowup.exceptionalIdeal (d.map i) (d.center i) ^ (m * s) * B =
          (d.controlledTransform J (m * s) i).comap (d.map i)) := by
  have hsm : ∀ i, i ≤ d.length → AlgebraicGeometry.Smooth (d.projectionToBase i ≫ p) :=
    smooth_projectionToBase_comp_of_snc k p E d hiso hsnc
  have key : ∀ i, i ≤ d.length →
      (d.controlledTransform I m i) ^ s ≤ d.controlledTransform J (m * s) i ∧
      ∀ [_hq : LocallyOfFiniteType (d.projectionToBase i ≫ p)],
        d.controlledTransform J (m * s) i ≤
          tunedSheaf k (d.projectionToBase i ≫ p) (d.controlledTransform I m i) m (m * s) := by
    intro i
    induction i with
    | zero =>
        intro _
        constructor
        · simp only [BlowupSequenceData.controlledTransform_zero]
          rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_pow]
          exact Scheme.IdealSheafData.comap_mono _ h1
        · intro hq0
          have := hq0
          have := hiso
          simp only [BlowupSequenceData.controlledTransform_zero]
          have heq : (tunedSheaf k p I m (m * s)).comap d.isoZero.hom
              = tunedSheaf k (d.projectionToBase 0 ≫ p) (I.comap d.isoZero.hom) m (m * s) :=
            comap_tunedSheaf_of_smooth k p d.isoZero.hom (d.projectionToBase 0 ≫ p) rfl I m (m * s)
          rw [← heq]
          exact Scheme.IdealSheafData.comap_mono _ h2
    | succ j ih =>
        intro hj
        have hj' : j < d.length := hj
        have hjle : j ≤ d.length := Nat.le_of_succ_le hj
        obtain ⟨ih1, ih2⟩ := ih hjle
        have := hsm j hjle
        have := hft j hjle
        have := hft (j + 1) hj
        have hcosj : orderAtLeastLocus (d.controlledTransform J (m * s) j) (m * s)
            = orderAtLeastLocus (d.controlledTransform I m j) m :=
          orderAtLeastLocus_eq_of_pow_le_of_le_tunedSheaf k (d.projectionToBase j ≫ p) _ _ m hs ih1 ih2
        have hordj := hord j hj' hcosj
        have hAZ : d.controlledTransform I m j ≤ d.center j ^ m :=
          le_pow_of_hasStrictNormalCrossingsWith (d.projectionToBase j ≫ p) (d.center j) _ (d.boundaryFrom E j) (hsnc j hj') m hordj
        have hBZ : d.controlledTransform J (m * s) j ≤ d.center j ^ (m * s) := by
          refine le_pow_of_hasStrictNormalCrossingsWith (d.projectionToBase j ≫ p) (d.center j) _ (d.boundaryFrom E j)
            (hsnc j hj') (m * s) ?_
          rw [hcosj]
          exact hordj
        have : IsLocallyNoetherian (d.obj (j + 1)) :=
          LocallyOfFiniteType.isLocallyNoetherian (d.projectionToBase (j + 1) ≫ p)
        obtain ⟨A1, hA1, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map j) (d.center j)
          (d.controlledTransform I m j) m (d.isBlowup j hj') hAZ
        obtain ⟨B1, hB1, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map j) (d.center j)
          (d.controlledTransform J (m * s) j) (m * s) (d.isBlowup j hj') hBZ
        have hA1' : Blowup.exceptionalIdeal (d.map j) (d.center j) ^ m * d.controlledTransform I m (j + 1)
            = (d.controlledTransform I m j).comap (d.map j) :=
          d.pow_exceptionalIdeal_mul_controlledTransform_succ I m j ⟨A1, hA1⟩
        have hB1' : Blowup.exceptionalIdeal (d.map j) (d.center j) ^ (m * s) *
              d.controlledTransform J (m * s) (j + 1)
            = (d.controlledTransform J (m * s) j).comap (d.map j) :=
          d.pow_exceptionalIdeal_mul_controlledTransform_succ J (m * s) j ⟨B1, hB1⟩
        have hp1 : d.projectionToBase (j + 1) ≫ p = d.map j ≫ (d.projectionToBase j ≫ p) := by
          rw [BlowupSequenceData.projectionToBase_succ, Category.assoc]
        obtain ⟨r1, r2⟩ := pow_le_and_le_tunedSheaf_of_isBlowupAlongIdealSheaf k (d.projectionToBase j ≫ p) (d.map j)
          (d.projectionToBase (j + 1) ≫ p) hp1
          (d.center j) (d.boundaryFrom E j) (hsnc j hj') (d.isBlowup j hj') m s
          (d.controlledTransform I m j) (d.controlledTransform J (m * s) j) (d.controlledTransform I m (j + 1))
          (d.controlledTransform J (m * s) (j + 1)) hAZ hA1' hB1' ih1 ih2
        refine ⟨r1, ?_⟩
        intro _
        exact r2
  have hcos : ∀ i, i ≤ d.length →
      orderAtLeastLocus (d.controlledTransform J (m * s) i) (m * s) = orderAtLeastLocus (d.controlledTransform I m i) m := by
    intro i hi
    have := hsm i hi
    have := hft i hi
    exact orderAtLeastLocus_eq_of_pow_le_of_le_tunedSheaf k (d.projectionToBase i ≫ p) _ _ m hs
      (key i hi).1 (key i hi).2
  have hdiv : ∀ i, i < d.length →
      (d.controlledTransform I m i ≤ d.center i ^ m) ∧
        (d.controlledTransform J (m * s) i ≤ d.center i ^ (m * s)) := by
    intro i hi
    have := hsm i (Nat.le_of_succ_le hi)
    have hordi := hord i hi (hcos i (Nat.le_of_succ_le hi))
    constructor
    · exact le_pow_of_hasStrictNormalCrossingsWith (d.projectionToBase i ≫ p) (d.center i) _ (d.boundaryFrom E i) (hsnc i hi) m hordi
    · refine le_pow_of_hasStrictNormalCrossingsWith (d.projectionToBase i ≫ p) (d.center i) _ (d.boundaryFrom E i)
        (hsnc i hi) (m * s) ?_
      rw [hcos i (Nat.le_of_succ_le hi)]
      exact hordi
  refine ⟨hcos, ?_, ?_⟩
  · intro i hi
    have := hft (i + 1) hi
    have : IsLocallyNoetherian (d.obj (i + 1)) :=
      LocallyOfFiniteType.isLocallyNoetherian (d.projectionToBase (i + 1) ≫ p)
    obtain ⟨B, hB, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map i) (d.center i)
      (d.controlledTransform I m i) m (d.isBlowup i hi) (hdiv i hi).1
    exact ⟨B, hB⟩
  · intro i hi
    have := hft (i + 1) hi
    have : IsLocallyNoetherian (d.obj (i + 1)) :=
      LocallyOfFiniteType.isLocallyNoetherian (d.projectionToBase (i + 1) ≫ p)
    obtain ⟨B, hB, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map i) (d.center i)
      (d.controlledTransform J (m * s) i) (m * s) (d.isBlowup i hi) (hdiv i hi).2
    exact ⟨B, hB⟩

theorem isMarked_iff_of_pow_le_of_le_tunedSheaf : IsMarkedIffOfPowLeOfLeTunedSheaf.{u} := by
  intro k hk1 hk2 hk3 X p hp1 hp2 I m _hm _hmax s hs J h1 h2 E d
  have hiso : AlgebraicGeometry.Smooth d.isoZero.hom := inferInstance
  constructor
  · constructor
    · intro hI
      have hft := locallyOfFiniteType_projectionToBase_comp_of_snc k p E d hiso hI.center_snc
      obtain ⟨hc, -, hdivJ⟩ := orderAtLeastLocus_eq_and_exceptionalIdeal_dvd_of_blowupSequence k p I J m s hs h1 h2 E d
        hiso hft hI.center_snc (fun i hi _ => hI.center_order i hi)
      exact { divisible := hdivJ
              center_order := fun i hi => by
                rw [hc i (Nat.le_of_succ_le hi)]
                exact hI.center_order i hi
              center_smooth := hI.center_smooth
              center_snc := hI.center_snc }
    · intro hJ
      have hft := locallyOfFiniteType_projectionToBase_comp_of_snc k p E d hiso hJ.center_snc
      obtain ⟨hc, hdivI, -⟩ := orderAtLeastLocus_eq_and_exceptionalIdeal_dvd_of_blowupSequence k p I J m s hs h1 h2 E d
        hiso hft hJ.center_snc
        (fun i hi heq => by
          rw [← heq]
          exact hJ.center_order i hi)
      exact { divisible := hdivI
              center_order := fun i hi => by
                rw [← hc i (Nat.le_of_succ_le hi)]
                exact hJ.center_order i hi
              center_smooth := hJ.center_smooth
              center_snc := hJ.center_snc }
  · intro hI i hi
    have hft := locallyOfFiniteType_projectionToBase_comp_of_snc k p E d hiso hI.center_snc
    obtain ⟨hc, -, -⟩ := orderAtLeastLocus_eq_and_exceptionalIdeal_dvd_of_blowupSequence k p I J m s hs h1 h2 E d
      hiso hft hI.center_snc (fun i hi _ => hI.center_order i hi)
    exact hc i hi

theorem isMarked_iff_balanced_tunedSheaf : IsMarkedIffBalancedTunedSheaf.{u} := by
  intro k hk1 hk2 hk3 X p hp1 hp2 I m hm hmax E d
  obtain ⟨r, s, hr, hre, hs, hms⟩ := exists_tuningExponent_eq hm
  have hWe : balancedTunedSheaf k p I m = tunedSheaf k p I m (m * s) := by rw [balancedTunedSheaf_eq, hms]
  have h1 : I ^ s ≤ balancedTunedSheaf k p I m := by
    rw [hWe]
    exact pow_le_tunedSheaf k p I hm s
  have h2 : balancedTunedSheaf k p I m ≤ tunedSheaf k p I m (m * s) := le_of_eq hWe
  have hmarked := isMarked_iff_of_pow_le_of_le_tunedSheaf.{u} k X p I m hm hmax s hs
    (balancedTunedSheaf k p I m) h1 h2 E d
  rw [← hms] at hmarked
  have he1 : 1 ≤ tuningExponent m := by
    rw [hms]
    exact Nat.mul_pos hm hs
  refine ⟨hmarked.1, hmarked.2, ?_, ?_⟩
  · have h5 := isMaxContactInvariantTunedSheaf.{u} k X p I m hm hmax
      (tuningExponent m) he1
    rw [balancedTunedSheaf_eq]
    exact h5
  · have h8 := isDerivBalanced_tunedSheaf_mul_lcmUpTo.{u} k X p I m hm hmax r hr
    rw [← hre] at h8
    rw [balancedTunedSheaf_eq]
    exact h8

theorem tunedSheafProperties_of_succ_le_of_mul_le (h1 : TunedSheafSuccLe.{u}) (h2 : TunedSheafMulLeAdd.{u}) :
    TunedSheafProperties.{u} where
  isMarked_tuned_iff := isMarked_iff_balanced_tunedSheaf.{u}
  tunedSheaf_succ_le := h1
  tunedSheaf_mul_le := h2
  derivIdealSheaf_tunedSheaf_succ := derivIdealSheaf_tunedSheaf_succ.{u}
  derivIdealSheafIter_pred_tunedSheaf := maxContactIdealTunedSheafEq.{u}
  derivIdealSheafIter_mul_derivIdealSheaf_le_tunedSheaf :=
    isMaxContactInvariantTunedSheaf.{u}
  tunedSheaf_mul_eq := tunedSheaf_mul_eq_add.{u}
  tunedSheaf_pow := tunedSheaf_pow_eq_mul.{u}
  derivIdealSheafIter_tunedSheaf_pow_le := isDerivBalanced_tunedSheaf_mul_lcmUpTo.{u}
  coSupport_tunedSheaf_eq_and_orderLE := orderAtLeastLocus_tunedSheaf_eq_and_order_le.{u}
  isMarked_iff_of_pow_le_of_le_tunedSheaf := isMarked_iff_of_pow_le_of_le_tunedSheaf.{u}

end FunctorialResolution.EmbeddedResolution
