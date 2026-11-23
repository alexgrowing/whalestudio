import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ChartRingLocalizationMembership
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalization
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.LatticeChartPoints

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type}

theorem int_le (O : Type) [CommRing O] [Algebra O Ω] (S : Set Ω) {a : Ω} (ha : a ∈ Algebra.adjoin ℤ S) :
    a ∈ Algebra.adjoin O S := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact Algebra.subset_adjoin ha
  | algebraMap n =>
    have : algebraMap ℤ Ω n = algebraMap O Ω (n : O) := by simp
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem unitAt_mul_iff {q : Cpt ξ} {a s : Ω} (ha : unitAt ξ q a) : unitAt ξ q (a * s) ↔ unitAt ξ q s := by
  obtain ⟨h0, h1, h2⟩ := ha
  constructor
  · rintro ⟨k0, k1, k2⟩
    have hs : s ≠ 0 := right_ne_zero_of_mul k0
    refine ⟨hs, ?_, ?_⟩
    · have : s = a⁻¹ * (a * s) := by field_simp
      rw [this]; exact mul_mem h2 k1
    · have : s⁻¹ = a * (a * s)⁻¹ := by field_simp
      rw [this]; exact mul_mem h1 k2
  · rintro ⟨k0, k1, k2⟩
    refine ⟨mul_ne_zero h0 k0, mul_mem h1 k1, ?_⟩
    rw [mul_inv]; exact mul_mem h2 k2

theorem reg (O : Type) [CommRing O] [Algebra O Ω] (x : κ → Ω) (c : κ) (a : Ω)
    (ha : a ∈ Algebra.adjoin O (Set.range fun j => x j / x c)) (q : Cpt ξ) (hq : InChart ξ x c q)
    (hO : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q) : a ∈ regAt ξ q := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha => obtain ⟨j, rfl⟩ := ha; exact hq.2 j
  | algebraMap o => exact hO o
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem exists_incl {O : Type} [CommRing O] [Algebra O Ω] (B : Subalgebra ℤ Ω) (R : Subalgebra O Ω)
    (h : ∀ a ∈ B, a ∈ R) : ∃ φ : B →+* R, ∀ t : B, ((φ t : R) : Ω) = t :=
  ⟨{ toFun := fun t => ⟨t.1, h _ t.2⟩
     map_one' := Subtype.ext rfl
     map_mul' := fun _ _ => Subtype.ext rfl
     map_zero' := Subtype.ext rfl
     map_add' := fun _ _ => Subtype.ext rfl }, fun _ => rfl⟩

theorem point_of_prime (C : Cpt ξ → Prop)
    (A : Type) [CommRing A] [Algebra A Ω] (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O]
    [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω]
    (B : Subalgebra ℤ Ω) (R : Subalgebra O Ω) (hle : ∀ a ∈ B, a ∈ R)
    (hpt : ∀ I : Ideal B, I.IsPrime → ∃ q, C q ∧ ∀ s : B, s ∉ I ↔ unitAt ξ q (s : Ω))
    (hreg : ∀ a ∈ B, ∀ q, C q → a ∈ regAt ξ q)
    (hconst : ∀ a : A, algebraMap A Ω a ∈ B)
    (hloc : ∀ t ∈ R, ∃ s : A, s ∉ m ∧ algebraMap A Ω s * t ∈ B)
    (P : Ideal R) (hP : P.IsPrime) :
    ∃ q : Cpt ξ, C q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) ∧
      ∀ s : R, s ∉ P ↔ unitAt ξ q (s : Ω) := by
  obtain ⟨φ, hφ⟩ := exists_incl B R hle
  obtain ⟨q, hq, hI⟩ := hpt (P.comap φ) (Ideal.comap_isPrime φ P)
  have hAO : ∀ a : A, algebraMap A Ω a = algebraMap O Ω (algebraMap A O a) := fun a =>
    IsScalarTower.algebraMap_apply A O Ω a
  have hnot : ∀ a : A, a ∉ m → φ ⟨_, hconst a⟩ ∉ P := by
    intro a ha hmem
    have hu : IsUnit (algebraMap A O a) := IsLocalization.map_units O (⟨a, ha⟩ : m.primeCompl)
    have he : φ ⟨_, hconst a⟩ = algebraMap O R (algebraMap A O a) :=
      Subtype.ext ((hφ _).trans (hAO a))
    rw [he] at hmem
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (hu.map _))
  have hunit : ∀ a : A, a ∉ m → unitAt ξ q (algebraMap A Ω a) := fun a ha =>
    (hI ⟨_, hconst a⟩).1 (fun h => hnot a ha (Ideal.mem_comap.1 h))
  refine ⟨q, hq, fun o => ?_, fun s => ?_⟩
  · obtain ⟨a, ha, hb⟩ := hloc _ (R.algebraMap_mem o)
    obtain ⟨h0, -, h2⟩ := hunit a ha
    have : algebraMap O Ω o = (algebraMap A Ω a)⁻¹ * (algebraMap A Ω a * algebraMap O Ω o) := by
      rw [← _root_.mul_assoc, inv_mul_cancel₀ h0, _root_.one_mul]
    rw [this]
    exact mul_mem h2 (hreg _ hb q hq)
  · obtain ⟨a, ha, hb⟩ := hloc s s.2
    refine Iff.trans ?_ ((hI ⟨_, hb⟩).trans (unitAt_mul_iff (hunit a ha)))
    have he : φ ⟨_, hb⟩ = φ ⟨_, hconst a⟩ * s := Subtype.ext (by
      rw [hφ, MulMemClass.coe_mul, hφ])
    rw [Ideal.mem_comap, he, hP.mul_mem_iff_mem_or_mem]
    exact ⟨fun h h' => h'.elim (hnot a ha) h, fun h h' => h (Or.inr h')⟩

open GlobalTheory.CompanionTheory.Ar.ChartPrimes in
theorem basic_nbhd (x : κ → Ω) (T : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0) (q : Cpt ξ) (hq : InChart ξ x c q)
    (U : X.Opens) (hU : q.1 ∈ U) : ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), unitAt ξ q g ∧
      ∀ q' : Cpt ξ, InChart ξ x c q' → unitAt ξ q' g → q'.1 ∈ U := by
  obtain ⟨V, hV, hmem⟩ := T.affine c hc
  have hqV : q.1 ∈ V := (hmem _).2 ⟨q.2, hq⟩
  have hg : genPt ξ ∈ V := q.2.mem_open V.2 hqV
  obtain ⟨f, hfU, hqf⟩ := hV.exists_basicOpen_le ⟨q.1, hU⟩ hqV
  have key : ∀ (p : Cpt ξ), p.1 ∈ V → (p.1 ∈ X.basicOpen f ↔ unitAt ξ p (secVal ξ V hg f)) := fun p hp => by
    rw [X.mem_basicOpen f _ hp, ← genMap_germ_eq V hg p hp f]
    exact isUnit_iff_unitAt p (T.gen.inj _) _
  refine ⟨secVal ξ V hg f, (T.ring c hc _).2 fun p hp => ⟨_, genMap_germ_eq V hg p ((hmem _).2 ⟨p.2, hp⟩) f⟩,
    (key q hqV).1 hqf, fun q' hq' hu => hfU ((key q' ((hmem _).2 ⟨q'.2, hq'⟩)).2 hu)⟩

end PositivityTheory.Xgn.LatticeChartPoints

open PositivityTheory.Xgn.LatticeChartPoints in
theorem PositivityTheory.Xgn.lattice_chart_points : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (mseg y) → ∀ (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c : ∀ k, J k), mseg y c ≠ 0 → (∀ a ∈ chartRing O (mseg y) c, ∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → a ∈ regAt ξ q) ∧ (∀ P : Ideal (chartRing O (mseg y) c), P.IsPrime → ∃ q : Cpt ξ, InChart ξ (mseg y) c q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) ∧ ∀ s : chartRing O (mseg y) c, s ∉ P ↔ unitAt ξ q (s : Ω)) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ a ∈ regAt ξ q, ∃ s ∈ chartRing O (mseg y) c, unitAt ξ q s ∧ s * a ∈ chartRing O (mseg y) c) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ U : X.Opens, q.1 ∈ U → ∃ g ∈ chartRing O (mseg y) c, unitAt ξ q g ∧ ∀ q' : Cpt ξ, InChart ξ (mseg y) c q' → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q') → unitAt ξ q' g → q'.1 ∈ U) := by
  intro X Ω _ ξ K _ _ J _ y T A _ _ hA m _ O _ _ _ _ _ _ _ c hc
  refine ⟨fun a ha q hq hO => reg O (mseg y) c a ha q hq hO, fun P hP => ?_, fun q hq _ a ha => ?_,
    fun q hq _ U hU => ?_⟩
  · exact point_of_prime (InChart ξ (mseg y) c) A m O (Algebra.adjoin ℤ (Set.range fun j => mseg y j / mseg y c)) _
      (fun a ha => int_le O _ ha)
      (fun I hI => (chart_point_of_prime X Ω ξ ℤ _ (mseg y) T c hc I hI).exists)
      (fun a ha => (T.ring c hc a).1 ha) (hA c hc)
      (fun t ht => (mem_chartRing_atPrime_iff K J Ω y A hA m O c hc t).1 ht) P hP
  · obtain ⟨s, hs, hu, hsa⟩ := (regAt_iff_exists_chart_fraction X Ω ξ ℤ _ (mseg y) T c q hq a).1 ha
    exact ⟨s, int_le O _ hs, hu, int_le O _ hsa⟩
  · obtain ⟨g, hg, hu, h⟩ := basic_nbhd (mseg y) T c hc q hq U hU
    exact ⟨g, int_le O _ hg, hu, fun q' hq' _ hu' => h q' hq' hu'⟩
