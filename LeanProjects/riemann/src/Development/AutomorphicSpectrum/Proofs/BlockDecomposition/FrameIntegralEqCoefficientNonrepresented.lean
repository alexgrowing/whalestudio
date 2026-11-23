import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegativeSchwartzBumpStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TamagawaFourierIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCoordinatesTracePairingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveOnSubspaceOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositivityPullsBackToSubspaceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramMapContinuousHermitianStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianScalarSequenceTendsZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonrepresentedSignatureObstructionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfHermEBijective
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem vanish_ring {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (ψ : AddChar A ℂ) (hψc : Continuous ψ) (hψn : ∀ x, ‖ψ x‖ = 1) (κ : Type) [Fintype κ]
    [FirstCountableTopology (κ → A)] [MeasurableSpace (κ → A)] [OpensMeasurableSpace (κ → A)]
    (μ : Measure (κ → A)) [μ.IsOpenPosMeasure]
    (Y : Type) [MeasurableSpace Y] (ν : Measure Y) (φ : Y → ℂ) (g : Y → κ → A)
    (hg : Measurable g) (N : Set (κ → A)) (hN : IsOpen N)
    (hb : Integrable φ ν → Integrable (fun v : κ → A => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ →
      ∀ N' : Set (κ → A), IsOpen N' → N' ⊆ N → ∀ z₁ ∈ N', ∃ Φ : (κ → A) → ℂ, Continuous Φ ∧ Integrable Φ μ ∧
      (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N' → Φ z = 0) ∧ 0 < (Φ z₁).re ∧
      ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0)
    (z₀ : κ → A) (hz : z₀ ∈ closure N) :
    ∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z₀)) ∂μ = 0 := by
  have hdot : Continuous (fun p : (κ → A) × (κ → A) => p.1 ⬝ᵥ p.2) := by
    unfold dotProduct
    exact continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)
  have hd1 : ∀ w, Continuous fun v : κ → A => ψ (-(v ⬝ᵥ w)) := fun w =>
    hψc.comp (hdot.comp (Continuous.prodMk continuous_id continuous_const)).neg
  have hd2 : ∀ v, Continuous fun w : κ → A => ψ (-(v ⬝ᵥ w)) := fun v =>
    hψc.comp (hdot.comp (Continuous.prodMk continuous_const continuous_id)).neg
  have hd3 : ∀ v, Continuous fun w : κ → A => ψ (v ⬝ᵥ w) := fun v =>
    hψc.comp (hdot.comp (Continuous.prodMk continuous_const continuous_id))
  by_cases hφ : Integrable φ ν
  swap
  · have h0 : ∀ v : κ → A, ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν = 0 := fun v =>
      integral_undef fun hi => hφ (integrable_of_mul_unimodular ν φ (fun y => ψ (v ⬝ᵥ g y)) hi
        ((hd3 v).measurable.comp hg).aestronglyMeasurable fun y => hψn _)
    refine (integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)).trans (integral_zero _ _)
    show (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z₀)) = 0
    rw [h0 v, zero_mul]
  by_cases hJ : Integrable (fun v : κ → A => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ
  swap
  · exact integral_undef fun hi => hJ (integrable_of_mul_unimodular μ _ (fun v => ψ (-(v ⬝ᵥ z₀))) hi
      (hd1 z₀).aestronglyMeasurable fun y => hψn _)
  exact vanish_abs μ (fun v z => ψ (-(v ⬝ᵥ z))) hd1 hd2 (fun _ _ => hψn _) _ hJ N hN (hb hφ hJ) z₀ hz

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem vanish_generic (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyReal F)
    (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)]
    [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)) (hμ : GlobalTheory.SWLit.IsTamagawa F κ μ)
    (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → AF F)
    (hg : Measurable g) (N : Set (κ → AF F)) (hN : IsOpen N) (hgN : ∀ y, g y ∉ N)
    (z₀ : κ → AF F) (hz : z₀ ∈ closure N) :
    ∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z₀)) ∂μ = 0 := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ.1
  refine vanish_ring ψ hψ.1 hψ.2.1 κ μ Y ν φ g hg N hN ?_ z₀ hz
  intro hφ hJ N' hN' hsub z₁ hz₁
  obtain ⟨Φ, hΦ, hΦ0, hΦN, hΦ1⟩ := GlobalTheory.T.exists_nonnegative_schwartz_bump F κ N' hN' z₁ hz₁
  obtain ⟨hΦc, -, hΦi⟩ := GlobalTheory.SplitSvN.schA_facts hF hΦ
  exact ⟨Φ, hΦc, hΦi μ hμ.1, hΦ0, hΦN, hΦ1,
    GlobalTheory.T.tamagawa_fourier_integrable F hF ψ hψ κ μ hμ Y ν φ g hφ hg hJ Φ hΦ (fun y => hΦN _ fun h' => hgN y (hsub h'))⟩

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

variable {D : D7}

theorem posOn_add_smul_one {n : ℕ} {ε δ : ℝ} {Z : Matrix (Fin n) (Fin n) ℂ} {S : Submodule ℂ (Fin n → ℂ)}
    (hS : NonnegOn ε Z S) (hε : ε = 1 ∨ ε = -1) (hδ : 0 < δ) :
    PosOn ε (Z + ((ε * δ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) S := by
  intro w hw hne
  have h0 := hS w hw
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  have hB : 0 < (star w ⬝ᵥ w).re := by
    have e : (star w ⬝ᵥ w).re = ∑ j, Complex.normSq (w j) := by
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re]
    rw [e]
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have e2 : (star w ⬝ᵥ (Z + ((ε * δ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).mulVec w).re =
      (star w ⬝ᵥ Z.mulVec w).re + ε * δ * (star w ⬝ᵥ w).re := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_smul,
      Complex.add_re, smul_eq_mul, Complex.re_ofReal_mul]
  rw [e2]
  have : ε * ((star w ⬝ᵥ Z.mulVec w).re + ε * δ * (star w ⬝ᵥ w).re) =
      ε * (star w ⬝ᵥ Z.mulVec w).re + (ε * ε) * δ * (star w ⬝ᵥ w).re := by ring
  rw [this, hεε, one_mul]
  exact add_pos_of_nonneg_of_pos h0 (mul_pos hδ hB)

theorem compAt_add' (θ : InfFam D) (ρ : D.what₂.Tau) {m n : ℕ} (a b : Mx D m n) :
    compAt θ ρ (a + b) = compAt θ ρ a + compAt θ ρ b := by
  exact Matrix.map_add (⇑((θ ρ).comp (infPart D))) ((θ ρ).comp (infPart D)).map_add a b

theorem compAt_neg' (θ : InfFam D) (ρ : D.what₂.Tau) {m n : ℕ} (a : Mx D m n) :
    compAt θ ρ (-a) = -compAt θ ρ a := by
  exact Matrix.map_neg (⇑((θ ρ).comp (infPart D))) ((θ ρ).comp (infPart D)).map_neg a

theorem W_eq_zero_of_obstruction (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V))
    (φ : Mx D V.rank r → ℂ) (h : Hyp D r V ψ θ μ lam ν φ) (β : HermE D r) (ρ : D.what₂.Tau) (ε : ℝ)
    (S : Submodule ℂ (Fin r → ℂ)) (hε : ε = 1 ∨ ε = -1) (hS : NonnegOn ε (β.1.map (tauE D ρ)) S)
    (hT : ∀ T : Submodule ℂ (Fin V.rank → ℂ), PosOn ε (gramAt D V ρ) T →
      Module.finrank ℂ T < Module.finrank ℂ S) :
    W ψ V μ lam φ β = 0 := by
  obtain ⟨hr, hψ, hθ, ⟨𝓕, hF⟩, ⟨𝓖, hG⟩, -, -, -⟩ := h
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele D.host.F
  haveI : BorelSpace (AF D.host.F) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D V.rank r
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : μ.IsAddHaarMeasure := hF.1
  obtain ⟨n, c, u, R, hu, hR, hRu, hcu, hTam⟩ := GlobalTheory.T.hermitian_coordinates_trace_pairing D r lam 𝓖 hG
  have hin := GlobalTheory.T.gram_map_continuous_hermitian D θ hθ V r ρ
  let g : Mx D V.rank r → Fin n → AF D.host.F := fun y => u (inner V y y)
  have hgc : Continuous g := hu.comp hin.1
  let N : Set (Fin n → AF D.host.F) := {w | PosOn ε (compAt θ ρ (R w)) S}
  have hN : IsOpen N :=
    (GlobalTheory.T.positive_on_subspace_open r ε S).preimage ((GlobalTheory.RealWeil.continuous_compAt hθ ρ r r).comp hR)
  have hgN : ∀ y, g y ∉ N := by
    intro y hy
    have h1 : PosOn ε (compAt θ ρ (R (u (inner V y y)))) S := hy
    rw [hRu _ (hin.2 y).1, (hin.2 y).2] at h1
    obtain ⟨T, hT1, hT2⟩ := GlobalTheory.T.positivity_pulls_back_to_subspace _ _ _ _ ε S h1
    have := hT T hT1
    omega
  let z₀ : Fin n → AF D.host.F := u (rat β.1)
  have hcl : ∀ e' : ℕ → Mx D r r, (∀ k, e' k ∈ hermA D r) → Filter.Tendsto e' Filter.atTop (nhds 0) →
      (∀ k : ℕ, compAt θ ρ (e' k) = ((ε * ((1 : ℝ) / ((k : ℝ) + 1)) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)) →
      z₀ ∈ closure N := by
    intro e' he' het hec
    have hlim : Filter.Tendsto (fun k => u (rat β.1 + e' k)) Filter.atTop (nhds z₀) := by
      have h2 : Filter.Tendsto (fun k => rat β.1 + e' k) Filter.atTop (nhds (rat β.1 + 0)) :=
        tendsto_const_nhds.add het
      rw [add_zero] at h2
      exact (hu.tendsto _).comp h2
    refine mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun k => ?_)
    show PosOn ε (compAt θ ρ (R (u (rat β.1 + e' k)))) S
    have hrat : compAt θ ρ (rat β.1) = β.1.map (tauE D ρ) := GlobalTheory.AdForm.RatMove.compAt_rat hθ ρ β.1
    rw [hRu _ ((hermA D r).add_mem (GlobalTheory.CompanionTheory.HermPoisson.rat_mem_hermA β) (he' k)), compAt_add', hec k, hrat]
    exact posOn_add_smul_one hS hε (by positivity)
  obtain ⟨e, he, het, hec⟩ := GlobalTheory.T.hermitian_scalar_sequence_tends_zero D θ hθ r
  have hz : z₀ ∈ closure N := by
    rcases hε with rfl | rfl
    · refine hcl e he het fun k => ?_
      rw [hec k, one_mul]
    · refine hcl (fun k => -e k) (fun k => (hermA D r).neg_mem (he k)) ?_ fun k => ?_
      · have h3 := het.neg
        rw [neg_zero] at h3
        exact h3
      · rw [compAt_neg', hec k]
        simp
  have key := vanish_generic D.host.F D.sp.cm.totReal ψ hψ (Fin n) (lam.map c.symm) hTam _ μ φ g
    hgc.measurable N hN hgN z₀ hz
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : BorelSpace (hermA D r) := Subtype.borelSpace _
  have hemb : MeasurableEmbedding (c.symm) := c.symm.toHomeomorph.measurableEmbedding
  rw [hemb.integral_map] at key
  refine Eq.trans ?_ key
  unfold W
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  have h1 : ∀ x : Mx D r r, c.symm b ⬝ᵥ u x = halfTr (Matrix.trace (HMul.hMul b.1 x : Mx D r r)) := fun x => by
    rw [← hcu]; simp
  show Jt ψ V μ φ b * _ = (∫ y, φ y * ψ (c.symm b ⬝ᵥ u (inner V y y)) ∂μ) * ψ (-(c.symm b ⬝ᵥ u (rat β.1)))
  simp only [h1]
  rw [Matrix.trace_mul_comm]
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem noFrame : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → (¬ ∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = β.1) → IfrB V ν φ β = W ψ V μ lam φ β := by
  intro D r V ψ θ μ lam ν φ h t β hβ hno
  obtain ⟨ρ, ε, S, hε, hS, hT⟩ := GlobalTheory.T.nonrepresented_signature_obstruction D r V h.1 t β hβ hno
  rw [W_eq_zero_of_obstruction r V ψ θ μ lam ν φ h β ρ ε S hε hS hT]
  haveI hemp : IsEmpty {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1} :=
    ⟨fun x => hno ⟨x.1, x.2⟩⟩
  unfold IfrB
  have h0 : (fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
      φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) q) = fun _ => (0 : ℂ) := by
    funext q
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, tsum_empty]
  rw [h0]
  simp [MeasureTheory.average]

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
