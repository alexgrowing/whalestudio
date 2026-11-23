import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinedAdelicMetricIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedOfPositiveNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelForRootMetricsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularMetricConjugationInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConjugateInvariantWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightConjugationCompatibilityStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.TrueGeo
open scoped ENNReal Classical
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ApproxModel

theorem isComb_mb {D : D7} (O : Setup D) (hC : O.Core) {A : SlopeTestRemainingChoices O.Y} {T : Real0 O.Y} {H : Ht O.Y}
    (hR : O.Reads A T H) {B : ℝ} (hB : 2 ≤ B) {u : Mean4.Wt O.Y} {s : ℚ} (hu : IsRat O.Y u) (hs : 0 < s)
    (hd : WeightThresholdDefs.Dominant O.Y (A.sh u s)) (c : O.s.Comp) :
    IsComb (O.Mb B u s c) (fun o : Option (DV.Rt D.what₂.Tau O.N) => o.elim (O.met.ab c) (O.root0 c (FlagAr.setB O.Y B)))
      (fun o : Option (DV.Rt D.what₂.Tau O.N) => o.elim (s : ℝ) fun x => -(u x.1 x.2 - s * O.met.dir x.1 x.2))
      (fun σ z => O.met.reg c σ (fun τ i => u τ i - s * O.met.dir τ i) (Real.exp (-((s : ℝ) ^ 2)⁻¹)) z / 2) := by
  have hdir := hR.aux.dir
  refine hC.mbIs B hB u s hu hs _ rfl ?_ c
  have e : A.sh u s = fun τ i => u τ i - s * O.met.dir τ i := by
    funext τ i; simp [Mean4.SlopeTestRemainingChoices.sh, hdir]
  rw [e] at hd; exact hd

theorem mb_isModel : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), O.Reads A T H →
  ∀ (B : ℝ), 2 ≤ B → ∀ (u : Wt O.Y) (s : ℚ), IsRat O.Y u → 0 < s → WeightThresholdDefs.Dominant O.Y (A.sh u s) →
  O.Y.semipos (O.Y.Mbar B u s) → ∀ c : O.s.Comp, (O.Mb B u s c).IsModel := by
  intro h1 h2 D O hC A T H hR B hB u s hu hs hd hsp c
  have hsp' : ∀ k, (O.Mb B u s k).SemiPos := by
    have h := hsp
    dsimp only [Setup.Y, ShFam.shimXOfPkg, ShFam.FinalTheorems.alg] at h
    exact h
  have hcomb := isComb_mb O hC hR hB hu hs hd c
  obtain ⟨M, hM, L, m, hL⟩ := GlobalTheory.T.normal_model_for_root_metrics D O hC B hB c
  obtain ⟨w, hw, hwe⟩ := GlobalTheory.T.exists_smooth_conjugate_invariant_weight _ _ _ _ _ _ _ hcomb (fun σ => (hsp' c σ).1) M L m hL
  have hwc := GlobalTheory.T.weight_conjugation_compatibility _ _ M _ w hwe (fun σ σ' y y' h => by
    rw [GlobalTheory.T.regular_metric_conjugation_invariant D O hC c σ σ' _ _ y y' h])
  obtain ⟨q, b, hq, -, hD, hinf, hfin⟩ := hcomb
  have hN : ∀ o, Norms (Cover.ofModel M hM) (L o)
      (fun x => genAt (Option.elim o (O.met.ab c) (O.root0 c (FlagAr.setB O.Y B))).D x ^ ((m : ℕ) : ℤ))
      (fun σ y => (((m : ℕ) : ℤ) : ℝ) * lnAdl (Option.elim o (O.met.ab c) (O.root0 c (FlagAr.setB O.Y B))) σ y)
      (fun v e y => (((m : ℕ) : ℤ) : ℝ) * (Option.elim o (O.met.ab c) (O.root0 c (FlagAr.setB O.Y B))).lg v e y) :=
    fun o => (norms_of_induces (Cover.induces_ofModel hM (hL o))).congr (fun x => by simp) (fun σ y => by simp)
      (fun v e y => by simp)
  have key := GlobalTheory.T.combined_adelic_metric_identity _ _ (Cover.ofModel M hM) _ _ _ _ q b hq hD hinf hfin (m : ℕ) (fun _ => ((m : ℕ) : ℤ)) b
    (fun i => mul_comm _ _) L hN w hw hwc (fun σ z y y' e1 e2 => hwe σ y y' (by rw [e2, e1]; rfl))
  exact ⟨M, _, ⟨(m : ℕ) * q, Nat.mul_pos m.pos hq⟩, 0,
    induced_of_norms _ _ _ _ M hM _ ⟨(m : ℕ) * q, Nat.mul_pos m.pos hq⟩ (fun σ z => (hinf σ z).1) key⟩
end GlobalTheory.ApproxModel
