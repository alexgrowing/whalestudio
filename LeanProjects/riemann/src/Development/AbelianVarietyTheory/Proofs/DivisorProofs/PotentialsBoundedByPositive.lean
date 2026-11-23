import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositivePotentialMinusSmallMultiplePsh
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BoundaryPolynomialFunctions

namespace GlobalTheory.PosDom

open Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem contDiffAt_two_of_isPotential {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hx : (A.chart j).symm y ∈ P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y :=
  ((hP.1 x j).of_le two_le_top).contDiffAt
    (((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds ⟨hy, hx⟩)

theorem isPotential_rsmul_real {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P) (c : ℝ) :
    IsPotential A (P.rsmul c) := by
  refine ⟨fun x j => contDiffOn_const.mul (hP.1 x j), fun x x' y hy => ?_⟩
  obtain ⟨W, hW, hyW, G, hG, hGeq⟩ := hP.2 x x' y hy
  refine ⟨W, hW, hyW, fun z => (c : ℂ) * G z, fun j => analyticOnNhd_const.mul (hG j), fun z hz => ?_⟩
  have := hGeq z hz
  simp only [LocPot.rsmul, Complex.re_ofReal_mul]
  rw [← this]; ring

theorem exists_forall_isPsh_rsmul_add [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (P L : LocPot X)
    (hP : IsPotential A P) (hpos : IsPosPot A P) (hL : IsPotential A L) :
    ∃ K₀ : ℝ, ∀ K, K₀ ≤ K → IsPsh A (P.rsmul K + L) := by
  obtain ⟨k, hk, h⟩ := exists_pos_sub_isPsh A P (L.rsmul (-1)) hP hpos (isPotential_rsmul_real hL (-1))
  refine ⟨k⁻¹, fun K hK x j y hy w => ?_⟩
  have hPy := contDiffAt_two_of_isPotential hP x j hy.1 hy.2.1
  have hLy := contDiffAt_two_of_isPotential hL x j hy.1 hy.2.2
  have h1 := h x j y hy w
  have e1 : (P + (L.rsmul (-1)).rsmul (-k)).φ x ∘ (A.chart j).symm =
      fun v => (P.φ x ∘ (A.chart j).symm) v + k * (L.φ x ∘ (A.chart j).symm) v := by
    funext v
    change P.φ x _ + -k * (-1 * L.φ x _) = P.φ x _ + k * L.φ x _
    ring
  have e2 : (P.rsmul K + L).φ x ∘ (A.chart j).symm =
      fun v => (L.φ x ∘ (A.chart j).symm) v + K * (P.φ x ∘ (A.chart j).symm) v := by
    funext v
    exact add_comm _ _
  rw [e1, levi_add_smul k hPy hLy] at h1
  rw [e2, levi_add_smul K hLy hPy]
  have h0 : 0 ≤ levi (P.φ x ∘ (A.chart j).symm) y w := by
    rcases eq_or_ne w 0 with h0 | h0
    · rw [h0, levi_zero]
    · exact (hpos x j y ⟨hy.1, hy.2.1⟩ w h0).le
  have h2 := mul_nonneg (inv_pos.2 hk).le h1
  rw [mul_add, inv_mul_cancel_left₀ hk.ne'] at h2
  have h3 := mul_le_mul_of_nonneg_right hK h0
  linarith

theorem exists_formBoundedBy (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (At : FinHolAtlas e X) (α : LocPot X) (m : ℕ) (Λ : Fin m → LocPot X) (hα : IsPotential At α)
    (hpos : IsPosPot At α) (hΛ : ∀ i, IsPotential At (Λ i)) :
    ∃ K : Fin m → ℝ, ∀ i, 0 ≤ K i ∧ GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions.FormBoundedBy At α (Λ i) (K i) := by
  choose a ha using fun i => exists_forall_isPsh_rsmul_add At α (Λ i) hα hpos (hΛ i)
  choose b hb using fun i =>
    exists_forall_isPsh_rsmul_add At α ((Λ i).rsmul (-1)) hα hpos (isPotential_rsmul_real (hΛ i) (-1))
  exact ⟨fun i => max 0 (max (a i) (b i)), fun i => ⟨le_max_left _ _,
    ha i _ ((le_max_left _ _).trans (le_max_right _ _)), hb i _ ((le_max_right _ _).trans (le_max_right _ _))⟩⟩

end GlobalTheory.PosDom
