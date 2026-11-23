import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPermOfCardFalse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridParameterRegularCardEqRankFormula
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHarishChandraParamGridVertexRealParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiscreteSeriesModelOfOrthonormalBasisCartaStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodParParBLast
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepRows

open Matrix

theorem exists_model_of_enum {D : D7} (hDS : GlobalTheory.Published.DiscreteSeriesUpqExists) {V : HSp D} (hV : V.SigOK)
    {S : D.what₂.Tau → SPar} (O C : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hS : ∀ τ, ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε ∧ Formalism.QuantumDeterminants.IsHCParam lam ∧
      (Finset.univ.filter fun a => ε a = false).card = (V.sig (tauE D τ)).2)
    (hO : ∀ τ, ∃ ε : Fin V.rank → Bool, (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε ∧ C τ * O τ = O τ * Formalism.REAL.Jm ε) :
    ∃ M : DSModel V S, cart M = C := by
  classical
  have key : ∀ τ, ∃ σ : Equiv.Perm (Fin V.rank), ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε ∧
      Formalism.QuantumDeterminants.IsHCParam lam ∧ ((O τ).submatrix id σ)ᴴ * gramAt D V τ * (O τ).submatrix id σ = Formalism.REAL.Jm ε ∧
      C τ * (O τ).submatrix id σ = (O τ).submatrix id σ * Formalism.REAL.Jm ε := by
    intro τ
    obtain ⟨lam, ε', hE, hH, hc⟩ := hS τ
    obtain ⟨ε, h1, h2⟩ := hO τ
    obtain ⟨σ, hσ⟩ := GlobalTheory.GridJoin.exists_perm_of_card_false ε ε' (by rw [GlobalTheory.GridJoin.card_false_of_gram hV τ h1, hc])
    have e : ε ∘ σ = ε' := funext hσ
    refine ⟨σ, lam, ε', hE, hH, ?_, ?_⟩
    · rw [GlobalTheory.GridJoin.gram_submatrix, h1, GlobalTheory.GridJoin.jm_submatrix, e]
    · rw [GlobalTheory.GridJoin.mul_submatrix_cols, h2, GlobalTheory.GridJoin.submatrix_mul_jm, e]
  choose σ lam ε hE hH h1 h2 using key
  obtain ⟨M, hM, -⟩ := GlobalTheory.T.exists_discreteSeriesModel_of_orthonormalBasis_cartan D hDS V S (fun τ => (O τ).submatrix id (σ τ)) C
    (fun τ => ⟨lam τ, ε τ, hE τ, hH τ, h1 τ⟩) (fun τ => ⟨ε τ, h1 τ, h2 τ⟩)
  exact ⟨M, hM⟩

theorem isHCParam_dual_parV (D : D7) (i j : ℕ) (τ : D.what₂.Tau) {n : ℕ} (lam : Fin n → ℝ) (ε : Fin n → Bool)
    (hn : n = rankV D i j) (hE : IsEnum (dualPar (parV D 1 i j τ)) lam ε) : Formalism.QuantumDeterminants.IsHCParam lam := by
  refine ⟨hE.1, fun a' => ?_⟩
  obtain ⟨-, q, hq, hS⟩ := hE
  have hmem : (q a', ε a') ∈ dualPar (parV D 1 i j τ) := by
    rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  simp only [parV, dualPar, GlobalTheory.SignedHC.shift, Finset.mem_image, Prod.mk.injEq] at hmem
  obtain ⟨y, ⟨x, hx, rfl⟩, hy1, -⟩ := hmem
  rw [← GlobalTheory.GridParDCount.grid_eq_num] at hx
  obtain ⟨z, hz⟩ := GlobalTheory.Grid.parD_entry_int D τ i j hx
  have hpar : Even (rankV D i j) ↔ Odd (i + j) := GlobalTheory.Grid.even_rkV_iff D i j
  rw [hq a', ← hy1]
  by_cases ho : Odd (i + j)
  · obtain ⟨N, hN⟩ := hpar.2 ho
    rw [if_pos ho]
    refine ⟨-z + 1 - N, ?_⟩
    have : (n : ℝ) = N + N := by rw [hn, hN]; push_cast; ring
    simp only [hz, this]; push_cast; ring
  · have hne : ¬ Even (rankV D i j) := fun h => ho (hpar.1 h)
    obtain ⟨N, hN⟩ := Nat.not_even_iff_odd.1 hne
    rw [if_neg ho]
    refine ⟨-z - N, ?_⟩
    have : (n : ℝ) = 2 * N + 1 := by rw [hn, hN]; push_cast; ring
    simp only [hz, this]; push_cast; ring

theorem rowModels_of_functoriality : GlobalTheory.FunPr.Hypotheses₂ → RowModels := by
  intro hP D _ _ T L μ0 _ sc hsc G W M _ i hi
  have hDS := hP.discreteSeriesUpqExists
  classical
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  ·
    rw [parRow_zero]
    have hV : (G.V (.grid 0 0)).SigOK := D.sp.Y_sig (min 0 D.R.m)
    refine exists_model_of_enum hDS hV (W.onb (.grid 0 0)) (W.cart (.grid 0 0)) (fun τ => ?_)
      (W.onb_is (.grid 0 0) ⟨Nat.zero_le _, Nat.zero_le _⟩)
    obtain ⟨lam, ε, hE, hH, -, hq⟩ := GlobalTheory.ChainModels.goodPar_parB D (min 0 D.R.m) (min_le_right _ _) τ
    have e : parB (Ptw D) (min 0 D.R.m) τ = parB (Ptw D) 0 τ := by rw [Nat.zero_min]
    rw [e] at hE
    exact ⟨lam, ε, hE, hH, hq⟩
  · rw [hsc]
    have hX : (Node.grid i 0).InRange D.R.m := ⟨hi, Nat.zero_le _⟩
    have hv := G.isV hX (fun j e => by cases e; omega)
    refine exists_model_of_enum hDS hv.sigOK (W.onb (.grid i 0)) (W.cart (.grid i 0)) (fun τ => ?_) (W.onb_is _ hX)
    obtain ⟨hr, hc, hm⟩ := GlobalTheory.GridJoin.dualPar_shift_counts (if Odd (i + 0) then -(1 / 2) else 0)
      (GlobalTheory.GridParDCount.isRegular_parD D 1 τ hi (Nat.zero_le D.R.m))
    have hc' : (parRow D 1 i τ).card = (G.V (.grid i 0)).rank :=
      hc.trans ((GlobalTheory.GridParDCount.card_parD D 1 τ hi (Nat.zero_le _)).trans hv.rank.symm)
    obtain ⟨lam, ε, hE, hcount⟩ := GlobalTheory.GridJoin.exists_isEnum_of_regular hr hc'
    refine ⟨lam, ε, hE, isHCParam_dual_parV D i 0 τ lam ε hv.rank hE, ?_⟩
    rw [hcount, hv.sig]
    exact hm.trans (GlobalTheory.SignedHC.Model.nMinus_parD _ i 0)

end GlobalTheory.SepRows
