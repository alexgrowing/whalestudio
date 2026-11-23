import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicEmbeddingOfDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticSectionPadicBoundStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CovHt.Link.IntPt

theorem vLa_pos {K : Type} [Field K] [NumberField K] (pl : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞 K) ∈ pl.asIdeal) : 0 < vLa pl (p : K) := by
  have e : ((p : 𝓞 K) : K) = (p : K) := by simp
  have h1 : pl.valuation K (p : K) < 1 := by
    rw [← e, HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem pl _).2 hp
  have h0 : pl.valuation K (p : K) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  unfold vLa
  have := (WithZero.log_lt_log h0 one_ne_zero).2 h1
  simp at this
  omega

end GlobalTheory.CovHt.Link.IntPt

open GlobalTheory.CovHt.Link.IntPt in

theorem GlobalTheory.CovHt.Link.exists_pt_drAt_le : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (Z : Comp s.Xo κ.c), Over Φ k Z → ∀ (la : AllWt.Weight S.Dw) (g : Rul s.Xo κ.c), g ∈ secZ s.Xo κ.c (exOf S.Dw la 0) → (Φ.C k).val g ∈ (Φ.C k).Y.H0 ((Φ.C k).Lw la) → ∀ (pl : HeightOneSpectrum (𝓞 κ.c.F)) (p : ℕ) [Fact p.Prime], (p : 𝓞 κ.c.F) ∈ pl.asIdeal → ∀ (T : CDVR) (io : κ.c.F →+* T.Fr) (e : ℕ), OverLa pl T.V io e → ∀ y : IntFr s.Xo κ.c T io, T.FinRes → (letI := io.toAlgebra; AllWt.LiesOn Z y.1) → ∃ x : Sp ℂ_[p] ⟶ (Φ.C k).Y.X, ∀ r : ℝ, drAt Φ k la p x ((Φ.C k).val g) ≤ (p : ℝ) ^ (-r) → (((vLa pl (p : κ.c.F) : ℝ) * r : ℝ) : EReal) ≤ nval T.V e (evI y g) := by
  intro h2 hH D A N j S κ s Φ k Z hZ la g hg hv pl p _ hp T io e ho y hf hy
  obtain ⟨jm, hj⟩ := GlobalTheory.T.padic_embedding_of_dvr pl p hp T io e ho hf
  obtain ⟨x, hx⟩ := GlobalTheory.T.arithmetic_section_padic_bound h2 hH D A N j S κ s Φ k Z hZ la g hg hv pl p hp T io e ho y hf hy jm hj
  refine ⟨x, fun r hr => ?_⟩
  rw [hx] at hr
  by_cases hz : evI y g = 0
  · rw [hz, nval_zero]; exact le_top
  rw [nval_of_ne hz, hj _ hz] at *
  have hvp := vLa_pos pl p hp
  have hpo : vV T.V (io (p : κ.c.F)) = (e : ℤ) * vLa pl (p : κ.c.F) := ho.2 _
  have he : (0 : ℝ) < e := by exact_mod_cast ho.1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hle : -((vV T.V (evI y g) : ℝ) / (vV T.V (io (p : κ.c.F)) : ℝ)) ≤ -r :=
    (Real.rpow_le_rpow_left_iff hp1).1 hr
  rw [hpo] at hle
  push_cast at hle
  have hv0 : (0 : ℝ) < (vLa pl (p : κ.c.F) : ℝ) := by exact_mod_cast hvp
  have : r ≤ (vV T.V (evI y g) : ℝ) / ((e : ℝ) * (vLa pl (p : κ.c.F) : ℝ)) := by linarith
  rw [le_div_iff₀ (by positivity)] at this
  apply EReal.coe_le_coe_iff.2
  rw [le_div_iff₀ he]
  nlinarith
