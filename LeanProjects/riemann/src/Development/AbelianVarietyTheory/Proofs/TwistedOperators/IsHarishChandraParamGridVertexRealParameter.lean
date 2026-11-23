import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Grid

open GlobalTheory.SignedHC

theorem parD_entry_int (D : D7) (τ : D.what₂.Tau) (i j : ℕ) {x : ℚ × Bool} (hx : x ∈ (grid D τ).parD i j) :
    ∃ z : ℤ, x.1 = z := by
  obtain ⟨c, hc⟩ := D.R.t_odd
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have hk := D.R.m_add_three_le_k
  have hs : ∃ d : ℕ, sLen D = 2 * d + 1 := ⟨a + b + 2, by unfold sLen Formalism.BasicNotions.Ranks.r; omega⟩
  obtain ⟨d, hd⟩ := hs
  rcases GridData.mem_parD.1 hx with ⟨h1, -⟩ | ⟨l, -, -, rfl⟩ | ⟨l, -, -, h3, -⟩ | ⟨l, -, -, h4, -⟩
  · obtain ⟨i', -, -, h⟩ := GridData.mem_cloud.1 h1
    exact ⟨_, h⟩
  · exact ⟨-(grid D τ).b l, by push_cast; rfl⟩
  · simp only [GridData.blockM, TPar.block, Finset.mem_image, Finset.mem_range] at h3
    obtain ⟨a', -, h⟩ := h3
    refine ⟨-((grid D τ).e l) + c - a', ?_⟩
    rw [← h]
    have ht : ((grid D τ).t : ℚ) = 2 * c + 1 := by exact_mod_cast hc
    rw [ht]; push_cast; ring
  · simp only [GridData.blockC, TPar.block, Finset.mem_image, Finset.mem_range] at h4
    obtain ⟨a', -, h⟩ := h4
    refine ⟨(grid D τ).cen l + d - a', ?_⟩
    rw [← h]
    have ht : ((grid D τ).s : ℚ) = 2 * d + 1 := by exact_mod_cast hd
    rw [ht]; push_cast; ring

theorem even_rkV_iff (D : D7) (i j : ℕ) : Even (rkV D i j) ↔ Odd (i + j) := by
  obtain ⟨c, hc⟩ := D.R.t_odd
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have hk := D.R.m_add_three_le_k
  obtain ⟨u, hu⟩ : ∃ u, a + b = u + 1 := ⟨a + b - 1, by omega⟩
  have hr : D.R.r = 2 * u + 1 := by unfold Formalism.BasicNotions.Ranks.r; omega
  have e : rkV D i j = 2 * (u + j * c + i * (u + 3)) + (1 + j + i) := by
    unfold rkV sLen; rw [hr, hc]; ring
  rw [e, Nat.even_add, Nat.odd_add]
  simp only [even_two, Even.mul_right, true_iff, Nat.even_add, Nat.odd_add]
  simp only [Nat.odd_iff, Nat.even_iff]; omega

theorem isHCParam_parV : ∀ (D : D7), HostHyp D → ∀ (i j : ℕ), 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool), n = GlobalTheory.Grid.rkV D i j → IsEnum (GlobalTheory.Grid.parV D i j τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  intro D _ i j _ _ _ τ n lam ε hn hE
  refine ⟨hE.1, fun a' => ?_⟩
  obtain ⟨-, q, hq, hS⟩ := hE
  have hmem : (q a', ε a') ∈ parV D i j τ := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  simp only [parV, dualPar, GlobalTheory.SignedHC.shift, Finset.mem_image, Prod.mk.injEq] at hmem
  obtain ⟨y, ⟨x, hx, rfl⟩, hy1, -⟩ := hmem
  obtain ⟨z, hz⟩ := parD_entry_int D τ i j hx
  have hpar := even_rkV_iff D i j
  rw [hq a', ← hy1]
  by_cases ho : Odd (i + j)
  · obtain ⟨N, hN⟩ := hpar.2 ho
    rw [if_pos ho] at *
    refine ⟨-z + 1 - N, ?_⟩
    have : (n : ℝ) = N + N := by rw [hn, hN]; push_cast; ring
    simp only [hz, this]; push_cast; ring
  · have hne : ¬ Even (rkV D i j) := fun h => ho (hpar.1 h)
    obtain ⟨N, hN⟩ := Nat.not_even_iff_odd.1 hne
    rw [if_neg ho] at *
    refine ⟨-z - N, ?_⟩
    have : (n : ℝ) = 2 * N + 1 := by rw [hn, hN]; push_cast; ring
    simp only [hz, this]; push_cast; ring

end GlobalTheory.Grid
