import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DdcLogNormBoundedByKaehler
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo
open Filter Topology
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeGradInt

theorem exists_grad_le {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k} {σ : k →+* ℂ} {d : ℕ}
    {R R' : GlobalTheory.AnRead p σ d} {a : ChartForm p σ d} (ha : IsKaehlerForm R a) {S : Set (GlobalTheory.CxPts p σ)} (hS : IsOpen S)
    {f : GlobalTheory.CxPts p σ → ℝ} (hf : R'.SmoothOn S f) {y₀ : GlobalTheory.CxPts p σ} (hy : y₀ ∈ S) :
    ∃ (ch : GlobalTheory.AlgChart p σ d) (U : Set (GlobalTheory.CxPts p σ)) (C : ℝ),
      IsOpen U ∧ y₀ ∈ U ∧ U ⊆ ch.e.source ∧ ∀ y ∈ U, y ∈ S ∧ DifferentiableAt ℝ (f ∘ ch.e.symm) (ch.e y) ∧
        ∀ ξ : ReciprocityTheory.L2DbarEstimates.V d, |fderiv ℝ (f ∘ ch.e.symm) (ch.e y) ξ| ≤ C * √(a ch y ξ.ofLp) := by
  obtain ⟨W, φ, hW, ho, hs, eφ⟩ := ha.1 y₀
  obtain ⟨i, hi⟩ := R.cover y₀
  set ch := R.chart i
  have hD : ContinuousAt (fun y => fderiv ℝ (f ∘ ch.e.symm) (ch.e y)) y₀ :=
    ContinuousAt.comp (g := fderiv ℝ (f ∘ ch.e.symm)) (f := ch.e)
      ((hf.contDiffAt_two hS hi hy).fderiv_right (m := 0) (by norm_num)).continuousAt (ch.e.continuousAt hi)
  obtain ⟨K, hK⟩ := CurvBound.eventually_abs_le (E := ReciprocityTheory.L2DbarEstimates.V d) (x₀ := y₀)
    (F := fun y ξ => (fderiv ℝ (f ∘ ch.e.symm) (ch.e y) ξ) ^ 2) (G := fun y ξ => ddcForm φ ch y ξ.ofLp)
    (fun ξ => ((hD.comp (f := Prod.fst) (x := (y₀, ξ)) continuousAt_fst).clm_apply continuousAt_snd).pow 2)
    (fun ξ => (CurvBound.continuousAt_ddcForm hi (hs.contDiffAt_two ho hi hW) ξ.ofLp).comp
      (f := fun q : GlobalTheory.CxPts p σ × ReciprocityTheory.L2DbarEstimates.V d => (q.1, q.2.ofLp)) (x := (y₀, ξ)) (by fun_prop))
    (fun y r ξ => by rw [map_smul, smul_eq_mul, mul_pow])
    (fun y r ξ => by rw [WithLp.ofLp_smul, CurvBound.ddcForm_smul])
    fun ξ hξ => (ha.2 _ _ hi ξ.ofLp (by simpa using hξ)).trans_eq (eφ _ _ hi hW _)
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.1
    (hK.and ((show ∀ᶠ y in 𝓝 y₀, y ∈ S from hS.mem_nhds hy).and ((show ∀ᶠ y in 𝓝 y₀, y ∈ W from ho.mem_nhds hW).and
      (show ∀ᶠ y in 𝓝 y₀, y ∈ ch.e.source from ch.e.open_source.mem_nhds hi))))
  refine ⟨ch, U, √|K|, hUo, hyU, fun y h => (hU y h).2.2.2, fun y h => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hU y h
  refine ⟨h2, (hf.contDiffAt_two hS h4 h2).differentiableAt (by norm_num), fun ξ => ?_⟩
  have h5 := h1 ξ
  rw [← eφ _ _ h4 h3] at h5
  have h0 : 0 ≤ a ch y ξ.ofLp := by
    rcases eq_or_ne ξ.ofLp 0 with e | hξ
    · have := CurvBound.ddcForm_smul ch φ y 0 0
      rw [zero_smul] at this
      rw [e, eφ _ _ h4 h3, this]
      simp
    · exact (ha.2 _ _ h4 _ hξ).le
  rw [← Real.sqrt_mul (abs_nonneg K)]
  exact Real.abs_le_sqrt (((le_abs_self _).trans h5).trans (mul_le_mul_of_nonneg_right (le_abs_self K) h0))

theorem grad_le_int : Hypotheses2 → HypothesesH → OnCore fun D O x P => ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (ρ : DV.Rt D.what₂.Tau O.N)
  (y₀ : GlobalTheory.CxPts (O.var c).str σ), y₀ ∈ offBd O.Φ c σ →
  ∃ (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (U : Set (GlobalTheory.CxPts (O.var c).str σ)) (C : ℝ),
    IsOpen U ∧ y₀ ∈ U ∧ U ⊆ ch.e.source ∧ ∀ y ∈ U, y ∈ offBd O.Φ c σ ∧
      DifferentiableAt ℝ (lnRatio (metsOf x O.Φ c none σ (O.ex ρ)) (refMet x O.Φ c σ (O.ex ρ)) ∘ ch.e.symm) (ch.e y) ∧
      ∀ ξ : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim,
        |fderiv ℝ (lnRatio (metsOf x O.Φ c none σ (O.ex ρ)) (refMet x O.Φ c σ (O.ex ρ)) ∘ ch.e.symm) (ch.e y) ξ| ≤
          C * √(P.om c σ ch y ξ.ofLp) := by
  intro _ _ D O x P _ _ _ c σ ρ y₀ hy
  have hT := isOpen_not_liesIn (p := GlobalTheory.Toroidal.genStr O.s.T.Z) (σ := embOf O.κ.e σ) (GlobalTheory.Toroidal.genBd O.s.T.Z)
  have hm : IsOpen (offBd O.Φ c σ) ∧ (metsOf x O.Φ c none σ (O.ex ρ)).SmoothOn (offBd O.Φ c σ) :=
    FlagCpt.smoothOn_met_of_eigMet _ _ _ _ _ _ _ _ _ _ _ (O.Φ.C c) σ (x.hodge _) _ hT
      (ToroidalCompactificationData.hodge_smoothOn _ _ _ _ _ _ _ x _) _
  have h0 : (refMet x O.Φ c σ (O.ex ρ)).SmoothOn (offBd O.Φ c σ) := by
    have := (FlagCpt.smoothOn_met_of_eigMet _ _ _ _ _ _ _ _ _ _ _ (O.Φ.C c) σ (x.eigMet _) Set.univ isOpen_univ
      (x.smoothOn_eigMet _) (O.ex ρ)).2
    exact ⟨fun _ _ => this.1 trivial, fun g => (this.2 g).mono fun y hy => ⟨trivial, hy.2⟩⟩
  exact exists_grad_le (P.om_kaehler c σ) hm.1 (GlobalTheory.HodgeChgSmooth.smoothOn_lnRatio hm.2 h0) hy

end GlobalTheory.HodgeGradInt

end
