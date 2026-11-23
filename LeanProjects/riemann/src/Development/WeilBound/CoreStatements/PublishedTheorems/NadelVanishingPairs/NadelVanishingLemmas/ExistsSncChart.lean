import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RegularSequenceExtendCoords
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RegularSequencePrimeDivisors
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem not_mem_basicOpen_prod {Y : Scheme.{0}} {U : Y.Opens} {v : Y} (hv : v ∈ U) {c : ℕ}
    (f : Fin c → Γ(Y, U)) (s : Finset (Fin c)) :
    v ∉ Y.basicOpen (∏ i ∈ s, f i) ↔ ∃ i ∈ s, v ∉ Y.basicOpen (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.notMem_empty, false_and, exists_false, iff_false, not_not]
    rw [Scheme.basicOpen_of_isUnit Y isUnit_one]
    exact hv
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul]
    simp only [TopologicalSpace.Opens.mem_inf, not_and_or, ih, Finset.mem_insert,
      exists_eq_or_imp]

theorem exists_isSncChart (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y]
    [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y)
    (hB : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)) (y : Y) :
    ∃ (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y)
      (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u := by
  classical
  obtain ⟨hreg, U, hyU, c, f, J₀, hrsp, hid⟩ := hB y
  obtain ⟨V, hV, hyV, z, e, hz, hframe⟩ := GlobalTheory.T.regular_sequence_extend_coords k Y q n y U hyU c f hrsp
  obtain ⟨w₀, u₀, hinj, hw⟩ := GlobalTheory.T.regular_sequence_prime_divisors Y y U.1 hyU c f hreg hrsp
  have hwe : ∀ i, Function.extend e w₀ (fun _ => y) (e i) = w₀ i :=
    fun i => e.injective.extend_apply _ _ i
  have hue : ∀ i, Function.extend e u₀ (fun _ => 1) (e i) = u₀ i :=
    fun i => e.injective.extend_apply _ _ i

  have hB' : ∀ v, v ∈ U.1 → (v ∈ B ↔ ∃ i ∈ J₀, v ∉ Y.basicOpen (f i)) := by
    intro v hv
    have h1 : v ∈ B ↔ v ∈ (Scheme.IdealSheafData.vanishingIdeal B).support := Iff.rfl
    rw [h1, Scheme.IdealSheafData.mem_support_iff_of_mem (U := U) hv, hid, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton]
    exact not_mem_basicOpen_prod hv f J₀
  refine ⟨V, hyV, z, J₀.map e, Function.extend e w₀ (fun _ => y),
    Function.extend e u₀ (fun _ => 1), ⟨hframe, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    rw [hue, (hw i).1, hz, fnOf_resG]
  · intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    rw [hwe]; exact (hw i).2.1
  · intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    rw [hwe]; exact (hw i).2.2.1
  · intro a ha b hb hab
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 ha)
    obtain ⟨i', -, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hb)
    rw [hwe, hwe] at hab
    rw [hinj hab]
  · intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    rw [hwe, hue]; exact (hw i).2.2.2.2.1
  · intro j hj v hvy hne
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    rw [hwe] at hne
    rw [hue]
    by_cases hc : Order.coheight v = 1
    · have hvU : v ∈ U.1 := hvy.mem_open U.1.isOpen hyU
      have hb : v ∈ Y.basicOpen (f i) := (hw i).2.2.2.2.2 v hvy hc hne
      rw [(hw i).1]
      exact UnitAt.ord_eq_zero ((unitAt_fnOf_iff hvU _ _).2 hb)
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hc _
  · intro v hvy hc
    have hvU : v ∈ U.1 := hvy.mem_open U.1.isOpen hyU
    rw [hB' v hvU]
    constructor
    · rintro ⟨i, hi, hnot⟩
      refine ⟨e i, Finset.mem_map_of_mem e hi, ?_⟩
      rw [hwe]
      by_contra hne
      exact hnot ((hw i).2.2.2.2.2 v hvy hc hne)
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hj
      rw [hwe]
      exact ⟨i, hi, (hw i).2.2.2.1⟩

end GlobalTheory.Discrepancy
