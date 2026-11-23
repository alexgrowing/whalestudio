import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution

namespace GlobalTheory.LogResInt
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions

noncomputable section

variable {d : ℕ} {X : Type} [TopologicalSpace X]

def HasHoloImm (A : FinHolAtlas d X) (T : Set X) (k : ℕ) : Prop :=
  ∃ (U : Set (Fin k → ℂ)) (g : (Fin k → ℂ) → X) (j : Fin A.n),
    IsOpen U ∧ U.Nonempty ∧ Set.MapsTo g U (T ∩ (A.chart j).source) ∧
    AnalyticOnNhd ℂ (A.chart j ∘ g) U ∧
    ∀ z ∈ U, Function.Injective (fderiv ℂ (A.chart j ∘ g) z)

theorem HasHoloImm.mono {A : FinHolAtlas d X} {T T' : Set X} {k : ℕ} (h : HasHoloImm A T k)
    (hT : T ⊆ T') : HasHoloImm A T' k := by
  obtain ⟨U, g, j, hU, hne, hmaps, han, hinj⟩ := h
  exact ⟨U, g, j, hU, hne, fun z hz => ⟨hT (hmaps hz).1, (hmaps hz).2⟩, han, hinj⟩

theorem holoOn_continuousAt {A : FinHolAtlas d X} {W : Set X} {f : X → ℂ} (hf : A.HoloOn W f)
    {x : X} (hx : x ∈ W) : ContinuousAt f x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
    (hf j (A.chart j x) ⟨(A.chart j).map_source hj, by
      simpa [Set.mem_preimage, (A.chart j).left_inv hj] using hx⟩).continuousAt
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x :=
    h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem isClosed_of_isAnalyticSubset {A : FinHolAtlas d X} {S : Set X}
    (hS : A.IsAnalyticSubset S) : IsClosed S := by
  refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun x hx => ?_)
  obtain ⟨W, hW, hxW, r, f, hf, hSW⟩ := hS x
  have : ¬ ∀ i, f i x = 0 := fun h => hx (hSW.ge ⟨hxW, h⟩).1
  push_neg at this
  obtain ⟨i, hi⟩ := this
  have hev : ∀ᶠ y in nhds x, f i y ≠ 0 := (holoOn_continuousAt (hf i) hxW).eventually_ne hi
  filter_upwards [hev, hW.mem_nhds hxW] with y hy hyW hyS
  exact hy ((hSW.le ⟨hyS, hyW⟩).2 i)

theorem isAnalyticSubset_inter {A : FinHolAtlas d X} {S T : Set X} (hS : A.IsAnalyticSubset S)
    (hT : A.IsAnalyticSubset T) : A.IsAnalyticSubset (S ∩ T) := by
  intro x
  obtain ⟨W, hW, hxW, r, f, hf, hSW⟩ := hS x
  obtain ⟨W', hW', hxW', r', f', hf', hTW⟩ := hT x
  refine ⟨W ∩ W', hW.inter hW', ⟨hxW, hxW'⟩, r + r', Fin.append f f', fun i => ?_, ?_⟩
  · induction i using Fin.addCases with
    | left i =>
      simp only [Fin.append_left]
      exact fun j => (hf i j).mono fun z hz => ⟨hz.1, hz.2.1⟩
    | right i =>
      simp only [Fin.append_right]
      exact fun j => (hf' i j).mono fun z hz => ⟨hz.1, hz.2.2⟩
  · ext y
    constructor
    · rintro ⟨⟨hyS, hyT⟩, hyW, hyW'⟩
      refine ⟨⟨hyW, hyW'⟩, fun i => ?_⟩
      induction i using Fin.addCases with
      | left i => simpa using (hSW.le ⟨hyS, hyW⟩).2 i
      | right i => simpa using (hTW.le ⟨hyT, hyW'⟩).2 i
    · rintro ⟨⟨hyW, hyW'⟩, h⟩
      exact ⟨⟨(hSW.ge ⟨hyW, fun i => by simpa using h (Fin.castAdd r' i)⟩).1,
        (hTW.ge ⟨hyW', fun i => by simpa using h (Fin.natAdd r i)⟩).1⟩, hyW, hyW'⟩

theorem isSection_zero_iff {A : FinHolAtlas d X} {L : LocPot X} {s : X → X → ℂ}
    (hs : IsSection A L s) {x y : X} (hy : y ∈ L.U x) : s x y = 0 ↔ s y y = 0 := by
  have h := hs.2 x y y ⟨hy, L.mem_U y⟩
  constructor
  · intro h0
    rw [h0, norm_zero, zero_mul] at h
    exact norm_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_right (Real.exp_pos _).ne')
  · intro h0
    rw [h0, norm_zero, zero_mul] at h
    exact norm_eq_zero.1 ((mul_eq_zero.1 h).resolve_right (Real.exp_pos _).ne')

theorem isAnalyticSubset_zero {A : FinHolAtlas d X} {L : LocPot X} {s : X → X → ℂ}
    (hs : IsSection A L s) : A.IsAnalyticSubset {y | s y y = 0} := by
  intro x
  refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hs.1 x, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hy, hyU⟩
    exact ⟨hyU, fun _ => (isSection_zero_iff hs hyU).2 hy⟩
  · rintro ⟨hyU, h⟩
    exact ⟨(isSection_zero_iff hs hyU).1 (h 0), hyU⟩

theorem isAnalyticSubset_boundary {A : FinHolAtlas d X} {m : ℕ} {Λ : Fin m → LocPot X}
    {σ : Fin m → X → X → ℂ} (hσ : ∀ i, IsSection A (Λ i) (σ i)) :
    A.IsAnalyticSubset (boundary σ) := by
  intro x
  refine ⟨⋂ i, (Λ i).U x, isOpen_iInter_of_finite fun i => (Λ i).isOpen_U x,
    Set.mem_iInter.2 fun i => (Λ i).mem_U x, 1, fun _ y => ∏ i, σ i x y, fun _ j => ?_, ?_⟩
  · have h : ∀ i, AnalyticOnNhd ℂ (σ i x ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ⋂ i, (Λ i).U x) :=
      fun i => ((hσ i).1 x j).mono fun z hz => ⟨hz.1, Set.mem_iInter.1 hz.2 i⟩
    exact Finset.univ.analyticOnNhd_fun_prod (fun i _ => h i)
  · ext y
    simp only [boundary, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter,
      Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, hi⟩, hU⟩
      exact ⟨hU, fun _ => ⟨i, (isSection_zero_iff (hσ i) (hU i)).2 hi⟩⟩
    · rintro ⟨hU, h⟩
      obtain ⟨i, hi⟩ := h 0
      exact ⟨⟨i, (isSection_zero_iff (hσ i) (hU i)).1 hi⟩, hU⟩

end

end GlobalTheory.LogResInt
