import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSummableBoundSchwartzMajorantRationalTrans
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.StatementOfTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactFiniteComponentsOfAnnihilatorOpenSuStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormDerivCharacterSymplecticPairingRealLineStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBoundMatrixBySymplecticFormHomAtRealPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.LatticeTranslateSum

theorem sum_pow_le {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (N : ℕ) :
    (∑ i, f i) ^ N ≤ (Fintype.card ι : ℝ) ^ N * ∑ i, f i ^ N := by
  set k : ℝ := (Fintype.card ι : ℝ) with hk_def
  have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr Fintype.card_pos
  have hk : (0 : ℝ) < k := by linarith
  have hw : ∑ _i : ι, (1 / k) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hk_def]
    field_simp
  have h := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun _ => 1 / k) f
    (fun _ _ => by positivity) hw (fun i _ => hf i) N
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_pow] at h
  have hs : 0 ≤ ∑ i, f i ^ N := Finset.sum_nonneg fun i _ => pow_nonneg (hf i) _
  calc (∑ i, f i) ^ N = k ^ N * ((1 / k) ^ N * (∑ i, f i) ^ N) := by
        rw [← mul_assoc, ← mul_pow, mul_one_div_cancel hk.ne', one_pow, one_mul]
    _ ≤ k ^ N * (1 / k * ∑ i, f i ^ N) := mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ k ^ N * ∑ i, f i ^ N := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : 1 / k ≤ 1 := by rw [div_le_one hk]; exact hk1
        nlinarith

theorem decay (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (hθ : IsInfFam θ)
    (S T : HSp D) (c : WO S T → ℂ)
    (hder : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (k : ℕ), ∃ C : ℝ, ∀ w : WO S T,
      ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ ^ k * ‖c w‖ ≤ C) (N : ℕ) :
    ∃ C : ℝ, ∀ w : WO S T, (1 + GlobalTheory.Unf.realSize θ w) ^ N * ‖c w‖ ≤ C := by
  classical
  choose n zs κ hκ using fun τ => GlobalTheory.T.exists_bound_matrix_by_symplecticFormHomAtRealPlace D S T τ
  choose Cf hCf using hder
  obtain ⟨τ₀⟩ := (GlobalTheory.DataRowsCounterexample.places_nonempty D).1
  let dv : (Σ τ : D.what₂.Tau, Fin (n τ)) → WO S T → ℝ := fun p w =>
    ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ p.1 (zs p.1 p.2) t) w)) 0‖
  let r : (Σ τ : D.what₂.Tau, Fin (n τ)) → ℝ := fun p => |κ p.1| / (2 * Real.pi)
  let f : WO S T → Option (Σ τ : D.what₂.Tau, Fin (n τ)) → ℝ := fun w o =>
    match o with
    | none => 1
    | some p => r p * dv p w
  have hf0 : ∀ w o, 0 ≤ f w o := by
    intro w o
    cases o with
    | none => simp [f]
    | some p => exact mul_nonneg (div_nonneg (abs_nonneg _) (by positivity)) (norm_nonneg _)
  have hdv : ∀ p w, r p * dv p w = |κ p.1| * |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T p.1 (zs p.1 p.2) (compAt θ p.1 w)| := by
    intro p w
    simp only [r, dv]
    rw [GlobalTheory.T.norm_deriv_character_symplecticPairing_realLine D ψ hψ θ hθ S T p.1 (zs p.1 p.2) w]
    field_simp
  have hsize : ∀ w, 1 + GlobalTheory.Unf.realSize θ w ≤ ∑ o, f w o := by
    intro w
    rw [Fintype.sum_option]
    simp only [f]
    refine add_le_add le_rfl ?_
    rw [Fintype.sum_sigma]
    unfold GlobalTheory.Unf.realSize
    refine Finset.sum_le_sum fun τ _ => ?_
    simp only [hdv]
    rw [← Finset.mul_sum]
    have hs : 0 ≤ ∑ l, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ (zs τ l) (compAt θ τ w)| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    exact (hκ τ (compAt θ τ w)).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hs)
  refine ⟨(Fintype.card (Option (Σ τ : D.what₂.Tau, Fin (n τ))) : ℝ) ^ N *
    (Cf τ₀ 0 0 + ∑ p, r p ^ N * Cf p.1 (zs p.1 p.2) N), fun w => ?_⟩
  have hrs : 0 ≤ GlobalTheory.Unf.realSize θ w := by
    unfold GlobalTheory.Unf.realSize
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h1 : (1 + GlobalTheory.Unf.realSize θ w) ^ N ≤ (∑ o, f w o) ^ N := pow_le_pow_left₀ (by positivity) (hsize w) N
  have h2 := sum_pow_le (f w) (hf0 w) N
  calc (1 + GlobalTheory.Unf.realSize θ w) ^ N * ‖c w‖ ≤ (∑ o, f w o) ^ N * ‖c w‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ (Fintype.card (Option (Σ τ : D.what₂.Tau, Fin (n τ))) : ℝ) ^ N * (∑ o, f w o ^ N) * ‖c w‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ ≤ _ := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Fintype.sum_option, add_mul, Finset.sum_mul]
        refine add_le_add ?_ (Finset.sum_le_sum fun p _ => ?_)
        · simp only [f, one_pow, one_mul]
          simpa using hCf τ₀ 0 0 w
        · simp only [f]
          rw [mul_pow, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hCf p.1 (zs p.1 p.2) N w)
            (pow_nonneg (div_nonneg (abs_nonneg _) (by positivity)) _)

end GlobalTheory.LatticeTranslateSum

open GlobalTheory.LatticeTranslateSum in

theorem GlobalTheory.LatticeTranslateSum.sum_translates_bounded : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (c : WO S T → ℂ), (∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ w : WO S T, c w ≠ 0 → ∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO S T w u) = 1) → (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (k : ℕ), ∃ C : ℝ, ∀ w : WO S T, ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ ^ k * ‖c w‖ ≤ C) → ∃ C : ℝ, ∀ w : WO S T, Summable (fun γ : ratL T S => ‖c ((γ : WO S T) + w)‖) ∧ ∑' γ : ratL T S, ‖c ((γ : WO S T) + w)‖ ≤ C := by
  intro D ψ hψ θ hθ S T c ⟨U, hU, hUc⟩ hder
  obtain ⟨Q, hQ, hQc⟩ := GlobalTheory.T.exists_compact_finiteComponents_of_annihilator_openSubgroup D ψ hψ S T U hU
  have hbox : ∀ x, c x ≠ 0 → GlobalTheory.Unf.InBox Q x := fun x hx => hQc x (hUc x hx)
  obtain ⟨-, -, -, -, -, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨N, hN⟩ := GlobalTheory.Unf.MajLoc.summable_bound D θ hθ T.rank S.rank
  obtain ⟨b, hb, hbb⟩ := hN Q K hQ hK
  obtain ⟨C, hC⟩ := decay D ψ hψ θ hθ S T c hder N
  have hmaj : ∀ x : WO S T, ‖c x‖ ≤ max C 0 * GlobalTheory.Unf.maj θ Q N x := by
    intro x
    by_cases hx : c x = 0
    · rw [hx, norm_zero]
      refine mul_nonneg (le_max_right _ _) ?_
      unfold GlobalTheory.Unf.maj
      split_ifs
      · have hrs : 0 ≤ GlobalTheory.Unf.realSize θ x := by
          unfold GlobalTheory.Unf.realSize
          exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
        positivity
      · exact le_rfl
    · have hrs : 0 ≤ GlobalTheory.Unf.realSize θ x := by
        unfold GlobalTheory.Unf.realSize
        exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hp : 0 < (1 + GlobalTheory.Unf.realSize θ x) ^ N := by positivity
      unfold GlobalTheory.Unf.maj
      rw [if_pos (hbox x hx), ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
      exact (hC x).trans (le_max_left _ _)
  have hinj : Function.Injective (incA D) := GlobalTheory.MixModel.incA_injective
  let e0 : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ratL T S := fun ξ => ⟨rat ξ, ⟨ξ, rfl⟩⟩
  have he0 : Function.Bijective e0 := by
    refine ⟨fun ξ ξ' h => ?_, fun γ => ?_⟩
    · have h' : rat ξ = rat ξ' := congrArg Subtype.val h
      exact Matrix.map_injective hinj h'
    · obtain ⟨x, ξ, hξ⟩ := γ
      exact ⟨ξ, Subtype.ext hξ⟩
  refine ⟨max C 0 * ∑' ξ, b ξ, fun w => ?_⟩
  obtain ⟨g0, hg0, hg0K⟩ := hcov w
  let e : Matrix (Fin T.rank) (Fin S.rank) D.host.E ≃ ratL T S :=
    (Equiv.ofBijective e0 he0).trans (Equiv.addRight ⟨g0, hg0⟩)
  have hterm : ∀ ξ, ‖c (((e ξ : ratL T S) : WO S T) + w)‖ ≤ max C 0 * b ξ := by
    intro ξ
    have he : ((e ξ : ratL T S) : WO S T) + w = (g0 + w) + rat ξ := by
      show rat ξ + g0 + w = (g0 + w) + rat ξ
      abel
    rw [he]
    exact (hmaj _).trans (mul_le_mul_of_nonneg_left (hbb _ hg0K ξ) (le_max_right _ _))
  have hs : Summable (fun ξ => ‖c (((e ξ : ratL T S) : WO S T) + w)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hb.mul_left _)
  refine ⟨e.summable_iff.mp hs, ?_⟩
  rw [← e.tsum_eq, ← tsum_mul_left]
  exact hs.tsum_le_tsum hterm (hb.mul_left _)
