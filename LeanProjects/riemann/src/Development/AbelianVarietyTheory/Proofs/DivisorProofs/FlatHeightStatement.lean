import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedBasePt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothExtensionOfPhaseFunctionStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightIndicatorBoundedStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts GlobalTheory.ShFam.Pad

set_option autoImplicit false

noncomputable section

open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts
open scoped Classical

namespace GlobalTheory.HeightParts

theorem chg_neg {D : D7} (O : Setup D) (c : O.s.Comp) (R : Option ℝ) (u : D.what₂.Tau → Fin O.N → ℝ)
    (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ) : O.chg c R (fun τ i => -u τ i) σ z = -O.chg c R u σ z := by
  simp only [Setup.chg, neg_mul, Finset.sum_neg_distrib]

theorem exists_bound_of_smooth {e : ℕ} {M : Man e} {g : M.Fun} (hg : M.Smooth g) : ∃ B : ℝ, ∀ σ x, |g σ x| ≤ B := by
  have hb : ∀ σ, ∃ B : ℝ, ∀ x, |g σ x| ≤ B := fun σ => by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
      (ReciprocityTheory.AnForm.M.PLAux.smooth_continuous (hg σ)).continuousOn
    exact ⟨B, fun x => by simpa [Real.norm_eq_abs] using hB x (Set.mem_univ x)⟩
  choose B hB using hb
  exact ⟨∑ σ, |B σ|, fun σ x => (hB σ x).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun σ => |B σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)))⟩

theorem height_difference_reference_bounded (p2 : Hypotheses2) (pH : HypothesesH) : OnObj fun D O _ _ H _ => ∃ C : ℝ, ∀ (τ : D.what₂.Tau) (y : Pt O.s),
    y ∈ H.int → |H.hH (fun τ' _ => if τ' = τ then 1 else 0) y - H.h0 (fun τ' _ => if τ' = τ then 1 else 0) y| ≤ C := by
  intro D O hC hN A T H h
  obtain ⟨-, -, hint, hH, -⟩ := htTie_of_reads D O A T H h hC.mbIs
  choose g hgs hgeq using GlobalTheory.T.smooth_extension_of_phase_function p2 pH D O hC hN A T H h
  have hb : ∀ (τ : D.what₂.Tau) (c : O.s.Comp), ∃ B : ℝ, ∀ σ x, |g τ c σ x| ≤ B :=
    fun τ c => exists_bound_of_smooth (hgs τ c)
  choose B hB using hb
  obtain ⟨C, hC'⟩ := (Set.finite_range fun q : D.what₂.Tau × O.s.Comp => B q.1 q.2).bddAbove
  refine ⟨C, fun τ y hy => ?_⟩
  have hval : ∀ σ i, |(T.F (O.Y.compPt y)).ph (fun τ' _ => if τ' = τ then 1 else 0) σ (h.pts.conj (O.Y.compPt y) y σ i)| ≤ C := by
    intro σ i
    have hz := (hint y).1 hy σ i
    have e1 := (h.an (O.Y.compPt y)).ph (fun τ' _ => if τ' = τ then 1 else 0) σ _ hz
    have e2 := (h.an (O.Y.compPt y)).ph (fun τ' _ => if τ' = τ then (-1 : ℝ) else 0) σ _ hz
    have e3 : (fun τ' (_ : Fin O.N) => if τ' = τ then (-1 : ℝ) else 0) =
        fun τ' i => -((fun τ' (_ : Fin O.N) => if τ' = τ then (1 : ℝ) else 0) τ' i) := by
      funext τ' i; by_cases hτ : τ' = τ <;> simp [hτ]
    have e5 : ∀ σ' z, O.chg (O.Y.compPt y) none (fun τ' (_ : Fin O.N) => if τ' = τ then (-1 : ℝ) else 0) σ' z =
        -O.chg (O.Y.compPt y) none (fun τ' (_ : Fin O.N) => if τ' = τ then (1 : ℝ) else 0) σ' z := fun σ' z => by
      rw [e3]; exact chg_neg O (O.Y.compPt y) none _ σ' z
    have e4 := hgeq τ (O.Y.compPt y) σ _ hz
    have : (T.F (O.Y.compPt y)).ph (fun τ' _ => if τ' = τ then 1 else 0) σ (h.pts.conj (O.Y.compPt y) y σ i) =
        -g τ (O.Y.compPt y) σ (h.pts.conj (O.Y.compPt y) y σ i) := by
      have e6 := e5 ((h.man (O.Y.compPt y)).ε σ) ((h.man (O.Y.compPt y)).pt σ (h.pts.conj (O.Y.compPt y) y σ i))
      exact e1.trans ((neg_neg _).symm.trans (congrArg Neg.neg (e4.trans (e2.trans e6)).symm))
    rw [this, abs_neg]
    exact (hB τ (O.Y.compPt y) σ _).trans (hC' ⟨(τ, (O.Y.compPt y)), rfl⟩)
  rw [hH _ y hy, add_sub_cancel_left, abs_le]
  constructor
  · exact (h.pts.mean_const (O.Y.compPt y) y (-C)).symm.le.trans (h.pts.mean_le (c := (O.Y.compPt y)) (y := y) (g := fun _ _ => -C)
      (g' := (T.F (O.Y.compPt y)).ph (fun τ' _ => if τ' = τ then 1 else 0)) fun σ i => (abs_le.1 (hval σ i)).1)
  · exact (h.pts.mean_le (c := (O.Y.compPt y)) (y := y) (g' := fun _ _ => C)
      (g := (T.F (O.Y.compPt y)).ph (fun τ' _ => if τ' = τ then 1 else 0)) fun σ i => (abs_le.1 (hval σ i)).2).trans
      (h.pts.mean_const (O.Y.compPt y) y C).le

theorem flatHt (p2 : Hypotheses2) (pH : HypothesesH) (pS : GlobalTheory.Published.ScholzeWeinsteinB) : FlatHt := by
  intro D O hC hN A T H h
  obtain ⟨C₁, h₁⟩ := GlobalTheory.T.height_indicator_bounded p2 pH pS D O hC hN A T H h
  obtain ⟨C₂, h₂⟩ := height_difference_reference_bounded p2 pH D O hC hN A T H h
  refine ⟨|C₁| + |C₂|, fun τ y => ⟨(h₁ τ y).trans ((le_abs_self C₁).trans (le_add_of_nonneg_right (abs_nonneg C₂))),
    fun hy => ?_⟩⟩
  have e₁ := h₁ τ y
  have e₂ := h₂ τ y hy
  rw [abs_le] at e₁ e₂ ⊢
  constructor <;> linarith [le_abs_self C₁, le_abs_self C₂]

end GlobalTheory.HeightParts

end
