import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.StdSteps

theorem even_N (R : Ranks) (j : ℕ) : Even (R.N j) :=
  R.k_even.add (R.t_odd.add_one.mul_left j)

theorem N_lt_succ (R : Ranks) (j : ℕ) : R.N j < R.N (j + 1) := by
  unfold Ranks.N
  rw [Nat.add_mul]
  omega

theorem realPlace_cmTrace_zero_element_eq_I_mul_abs (D : D7) (h : D.host.ccK = ⊤) (τ : D.what₂.Tau) :
    tauE D τ D.host.xi0 = Complex.I * ((Real.sqrt D.host.d)⁻¹ : ℝ) := by
  have h1 : tauE D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) :=
    ((factEmb D.R D.host).2 _).2 (D.eTau τ).2
  have h2 : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have h3 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2.ne'
  rw [Host.xi0, h, Ideal.absNorm_top, map_div₀, map_neg, map_one, map_mul, h1, Nat.cast_one, map_one, one_mul, Complex.ofReal_inv]
  field_simp
  rw [Complex.I_sq]

theorem scale_eq (D : D7) {δ : ℂ} (hδ : δ ≠ 0) :
    (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf D ⊤ δ))⁻¹ * ‖δ‖ ^ 2 = 2 * (Real.sqrt D.host.d)⁻¹ := by
  have h2 : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have h3 : ‖δ‖ ≠ 0 := norm_ne_zero_iff.2 hδ
  rw [GlobalTheory.MomDict.area_lamOf D ⊤ δ top_ne_bot, Ideal.absNorm_top, Complex.normSq_eq_norm_sq]
  field_simp
  simp

theorem stdPair_steps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word) (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), StdPair θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) I.A.δ I.A.sc ψ ∧ I.A.AA = ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) ∧ (∀ τ, B.fields.embC I.A.σ₀ τ = tauE (I.rec7 l Z) τ) ∧ ∀ j, j ≤ B.R.m → ∀ g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j), ∃ x, IsDetRoot _ g x := by
  intro B X I l Z w u A ψ θ hA i hi
  obtain ⟨hs, hX, -, -⟩ := w.ok.spaces
  have oX : ∀ j, GlobalTheory.Mem.Col2.Crd.Ortho (B.sp.X j) := fun j => by rw [hX]; exact GlobalTheory.Mem.Col2.Crd.ortho_pos hs _
  have gX : ∀ j, (B.sp.X j).gram = 1 := fun j => by
    refine Matrix.ext fun a b => ?_
    rw [Matrix.one_apply]
    exact (oX j).1 a b
  have r1 := rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)
  have r2 := rankN (I.rec7 l Z) (i + 1) hi
  have hcc : (I.rec7 l Z).host.ccK = ⊤ := B.toPre.ccK_top
  refine ⟨⟨hA.std, hA.inf, gX i, gX (i + 1), (I.rec7 l Z).sp.X_sig i, (I.rec7 l Z).sp.X_sig (i + 1), ?_, hcc, I.J.δ_ne_zero,
    realPlace_cmTrace_zero_element_eq_I_mul_abs _ hcc, scale_eq (I.rec7 l Z) I.J.δ_ne_zero⟩, I.A_AA, fun τ => ?_, fun j _ g => ?_⟩
  · rw [r1, r2]
    exact ⟨Ranks.N_pos _ _, N_lt_succ _ _, even_N _ _, even_N _ _⟩
  · exact B.fields_embC τ
  · exact GlobalTheory.RecDict.exists_isDetRoot _ _ g

end GlobalTheory.AdForm.StdSteps
