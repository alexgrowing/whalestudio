import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

open Filter Topology
open ReciprocityTheory.AnForm.M

noncomputable section

namespace GlobalTheory.SectionZero

variable {D : ℕ} {Y : Type} [TopologicalSpace Y]

theorem continuousAt_of_holoOn (A : FinHolAtlas D Y) {U : Set Y} {f : Y → ℂ}
    (hf : A.HoloOn U f) {y₀ : Y} (hy₀ : y₀ ∈ U) : ContinuousAt f y₀ := by
  obtain ⟨j, hj⟩ := A.cover y₀
  have hz : A.chart j y₀ ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hy₀⟩
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j y₀) :=
    (hf j _ hz).continuousAt
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) y₀ :=
    h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem ne_zero_iff (A : FinHolAtlas D Y) {L : LocPot Y} {s : Y → Y → ℂ} (hs : IsSection A L s)
    {y₀ y : Y} (hy : y ∈ L.U y₀) : s y y ≠ 0 ↔ s y₀ y ≠ 0 := by
  have h := hs.2 y₀ y y ⟨hy, L.mem_U y⟩
  constructor <;> intro hne h0
  · rw [h0, norm_zero, zero_mul] at h
    exact hne (norm_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_right (Real.exp_pos _).ne'))
  · rw [h0, norm_zero, zero_mul] at h
    exact hne (norm_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (Real.exp_pos _).ne'))

theorem dense_coord_ne_zero : Dense {z : Fin D → ℂ | ∀ i, z i ≠ 0} := by
  have h := dense_pi (α := fun _ : Fin D => ℂ) (s := fun _ => ({0}ᶜ : Set ℂ)) Set.univ
    (fun _ _ => dense_compl_singleton 0)
  convert h using 1
  ext z
  simp

theorem isOpen_and_dense_opn : ∀ (D : ℕ) (Y : Type) [TopologicalSpace Y]
    (A : ReciprocityTheory.AnForm.M.FinHolAtlas D Y) (L : ReciprocityTheory.AnForm.M.LocPot Y) (s : Y → Y → ℂ)
    (m : ℕ) (W : Fin m → Set Y), GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.IsBoundary A L s W →
    IsOpen (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s) ∧ Dense (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s) := by
  intro D Y _ A L s m W hB
  have hs : IsSection A L s := hB.2.1
  refine ⟨?_, ?_⟩
  · rw [isOpen_iff_mem_nhds]
    intro y₀ hy₀
    have hy₀' : s y₀ y₀ ≠ 0 := hy₀
    have hc := continuousAt_of_holoOn A (hs.1 y₀) (L.mem_U y₀)
    filter_upwards [(L.isOpen_U y₀).mem_nhds (L.mem_U y₀), hc.eventually_ne hy₀'] with y hyU hy
    exact (ne_zero_iff A hs hyU).mpr hy
  · rw [dense_iff_inter_open]
    rintro O hO ⟨y₁, hy₁⟩
    obtain ⟨ψ, -, hψ₁, hψU, σ, -, -, u, -, hu, hprod⟩ := hB.2.2.1 y₁
    have hOpen : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (O ∩ ψ.source)) :=
      ψ.isOpen_inter_preimage_symm (hO.inter ψ.open_source)
    have hmem : ψ y₁ ∈ ψ.target ∩ ψ.symm ⁻¹' (O ∩ ψ.source) :=
      ⟨ψ.map_source hψ₁, by simpa [ψ.left_inv hψ₁] using And.intro hy₁ hψ₁⟩
    obtain ⟨z, ⟨hzt, hzO, hzs⟩, hz⟩ := dense_coord_ne_zero.inter_open_nonempty _ hOpen ⟨_, hmem⟩
    refine ⟨ψ.symm z, hzO, ?_⟩
    show s (ψ.symm z) (ψ.symm z) ≠ 0
    rw [ne_zero_iff A hs (hψU hzs), hprod _ hzs]
    refine mul_ne_zero (hu _ hzs) (Finset.prod_ne_zero_iff.mpr fun k _ => ?_)
    rcases σ k with _ | i
    · exact one_ne_zero
    · simpa [ψ.right_inv hzt] using pow_ne_zero 1 (hz i)

end GlobalTheory.SectionZero
