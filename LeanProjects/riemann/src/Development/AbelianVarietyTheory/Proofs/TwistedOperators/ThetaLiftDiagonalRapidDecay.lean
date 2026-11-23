import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftLowerTowerVanishing
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspRapidDecayOfSobolev
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DownApprox

open GlobalTheory.Grid GlobalTheory.ChainFr
open scoped ENNReal

variable {D : D7}

theorem jm_not {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm (fun j => !(ε j)) = -Formalism.REAL.Jm ε := by
  ext a b
  by_cases h : a = b
  · subst h
    cases hε : ε a <;> simp [Formalism.REAL.Jm, hε]
  · simp [Formalism.REAL.Jm, Matrix.diagonal_apply_ne _ h]

theorem gramAt_neg (V : HSp D) (τ : D.what₂.Tau) : gramAt D (neg V) τ = -gramAt D V τ := by
  ext i j
  simp [gramAt, neg_gram]

def negFr (N : Node D) : Fr (neg N.V) where
  ε τ j := !(N.M.ε τ j)
  fr := N.M.fr
  fr_unit := N.M.fr_unit
  fr_gram τ := by
    rw [jm_not, Matrix.mul_neg, Matrix.neg_mul, N.M.fr_gram τ, gramAt_neg]

theorem negFr_cart (N : Node D) : (negFr N).cart = cartS true N := by
  funext τ
  show (N.M.fr τ)⁻¹ * Formalism.REAL.Jm (fun j => !(N.M.ε τ j)) * N.M.fr τ = -((N.M.fr τ)⁻¹ * Formalism.REAL.Jm (N.M.ε τ) * N.M.fr τ)
  rw [jm_not, Matrix.mul_neg, Matrix.neg_mul]

theorem thetaKernel_le_sobolev_mul_height_source {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {ω : WRep S T} (hω : IsWeil ψ true S T χS χT ω) (μ : Measure (WO (neg S) T))
    (𝓓 : Set (WO (neg S) T)) (hμ : IsCovolOne (ratL T (neg S)) μ 𝓓) (U : AddSubgroup (WO (neg S) T))
    (hU : IsOpen (U : Set (WO (neg S) T))) :
    ∃ (d A : ℕ) (K : ℝ), 0 ≤ K ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel ψ (neg S) T U, ∀ (g : GA D S) (h : GA D T),
      ‖thetaKO ω g h f‖ ≤ K * (GlobalTheory.Size.sobO ψ θ μ 𝓓 d f).toReal * GlobalTheory.Grow.quotHeight S g ^ A * GlobalTheory.Grow.height T h ^ A := by
  have hω' : IsWeilDatumO ψ (neg S) T χS χT (ω.toSgn true) := hω
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (neg S).rank T.rank
  obtain ⟨C, hC0, hC⟩ := (H (neg S) T rfl rfl).real ψ hθ hU
  refine ⟨d, A, C * 2 ^ A, by positivity, fun f hf g h => ?_⟩
  have hb := (hC χS χT (ω.toSgn true) hω' μ 𝓓 hμ f hf).2
  have hinv : ∀ γ ∈ GQ S, ∀ g, thetaKO ω (γ * g) h f = thetaKO ω g h f := fun γ hγ g => by
    have e1 : (((ofSgn true S).symm (γ * g), h) : GA D (neg S) × GA D T) =
        ((ofSgn true S).symm γ, 1) * ((ofSgn true S).symm g, h) := by simp
    show (ω.toSgn true) ((ofSgn true S).symm (γ * g), h) f 0 = (ω.toSgn true) ((ofSgn true S).symm g, h) f 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hω'.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) 1 (one_mem _) _ (hω'.om_pres _ _ hf.1)
  have hs : 0 ≤ (GlobalTheory.Size.sobO ψ θ μ 𝓓 d f).toReal := ENNReal.toReal_nonneg
  have hgr : ∀ g, ‖thetaKO ω g h f‖ ≤ (C * (GlobalTheory.Size.sobO ψ θ μ 𝓓 d f).toReal * GlobalTheory.Grow.height T h ^ A) *
      GlobalTheory.Grow.height S g ^ A := fun g => by
    have := hb ((ofSgn true S).symm g) h
    refine this.trans_eq ?_
    show C * (GlobalTheory.Size.sobO ψ θ μ 𝓓 d f).toReal * (GlobalTheory.Grow.height S g * GlobalTheory.Grow.height T h) ^ A = _
    ring
  refine (GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => thetaKO ω g h f) hinv hgr g).trans_eq ?_
  ring

theorem exists_sum_of_mem_fockSpan {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A : Fr V} {B : Fr W}
    {U : AddSubgroup (WO V W)} {g : WO V W → ℂ} (hg : g ∈ fockSpan ψ θ A B U) :
    ∃ (n : ℕ) (f : Fin n → (WO V W → ℂ)) (p : Fin n → PolF D W.rank V.rank),
      (∀ l, IsVacF ψ θ A B (f l)) ∧ g = ∑ l, ptF ψ θ A B (f l) (p l) := by
  obtain ⟨n, c, u, hu⟩ := Submodule.mem_span_set'.1 hg
  have hm : ∀ l, ∃ f₀ P, IsVacF ψ θ A B f₀ ∧ f₀ ∈ GlobalTheory.Size.thetaLevel ψ V W U ∧ (u l : WO V W → ℂ) = ptF ψ θ A B f₀ P :=
    fun l => (u l).2
  choose f₀ P hv _ he using hm
  refine ⟨n, f₀, fun l => c l • P l, hv, ?_⟩
  rw [← hu]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [he l]
  exact (map_smul (pureTensorO ψ θ V W A.cart B.cart A.onb B.onb (f₀ l)) (c l) (P l)).symm

theorem isVacF_negFr {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (S T : Node D) (f : WO S.V T.V → ℂ) :
    IsVacF ψ θ (negFr S) (Fr.ofModel T.M) f ↔ IsFinVec ψ θ true S T f := by
  unfold IsVacF IsFinVec
  rw [negFr_cart]
  rfl

theorem ptF_negFr {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (S T : Node D) (f : WO S.V T.V → ℂ) (P : Pol S T) :
    ptF ψ θ (negFr S) (Fr.ofModel T.M) f P = fock ψ θ true S T f P := by
  unfold ptF fock
  rw [negFr_cart]
  rfl

set_option maxHeartbeats 1000000 in

theorem approx : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ F : (G.P (i + 1)).Maps, F ∈ (G.P (i + 1)).Cusp R.θ → ∀ v : SmT (G.P (i + 1)).M, (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * F v g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → ∀ C : Set (GA D (G.P i).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (f : Fin n → (WO (G.P (i + 1)).V (G.P i).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l)) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * F v g ∂(G.mP (i + 1)).ν) - ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) * F v g ∂(G.mP (i + 1)).ν‖ < ε := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG i hi Φ hΦ Fm hF v _ C hC ε hε
  classical
  have hθ : IsInfFam R.θ := hRB.inf
  have hW := (hG.arrows.dn i hi).weil
  have hω : IsWeilDatumO R.ψ (neg (G.P (i + 1)).V) (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i))
      ((G.dn i).ω.toSgn true) := hW
  obtain ⟨hν, hfd⟩ : (G.mP (i + 1)).ν.IsHaarMeasure ∧
      IsFundamentalDomain (GQ (G.P (i + 1)).V) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := by
    have h := hG.meas.P (i + 1) hi
    by_cases hd : i + 1 = D.R.m
    · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
    · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩
  have hFv : GlobalTheory.Grow.RapidDec (G.P (i + 1)).V (Fm v) := by
    have h := GlobalTheory.LowVanishObj.multT_apply_cusp R.θ (G.P (i + 1)).M ∅ 1 Fm hF v
    exact (GlobalTheory.Size.rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ h.1 h.2).rapidDec
  obtain ⟨μ, 𝓓, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (neg (G.P (i + 1)).V) (G.P i).V
  obtain ⟨U, hU, hΦU, happ⟩ := GlobalTheory.FockDensity.fockDense D _ _ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) R.θ R.ψ
    hω.std hθ μ 𝓓 hμ Φ hΦ
  haveI : BorelSpace (GA D (G.P (i + 1)).V) := ⟨rfl⟩
  haveI hfin : IsFiniteMeasure ((G.mP (i + 1)).ν.restrict (G.mP (i + 1)).fd) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.Chain.LiftReg.vol_ne_top hν hfd)
  obtain ⟨H, hH⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact (G.P i).V hC

  have hbound : ∀ U' : AddSubgroup (WO (neg (G.P (i + 1)).V) (G.P i).V), IsOpen (U' : Set (WO (neg (G.P (i + 1)).V) (G.P i).V)) →
      ∃ (d : ℕ) (M : ℝ), 0 ≤ M ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel R.ψ (neg (G.P (i + 1)).V) (G.P i).V U', ∀ h ∈ C,
        IntegrableOn (fun g => thetaKO (G.dn i).ω g h f * Fm v g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν ∧
        ‖∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h f * Fm v g ∂(G.mP (i + 1)).ν‖ ≤
          M * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal := by
    intro U' hU'
    obtain ⟨d, Ae, K, hK0, hK⟩ := thetaKernel_le_sobolev_mul_height_source hθ hW μ 𝓓 hμ U' hU'
    obtain ⟨B, hB⟩ := hFv.decay Ae
    refine ⟨d, K * max H 1 ^ Ae * max B 0 * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal, by positivity,
      fun f hf h hh => ?_⟩
    have hs : 0 ≤ (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal := ENNReal.toReal_nonneg
    have hcont : Continuous fun g => thetaKO (G.dn i).ω g h f * Fm v g :=
      ((hω.om_cont f hf.1 0).comp ((continuous_ofSgn_symm true _).prodMk continuous_const)).mul hFv.continuous
    have hpt : ∀ g, ‖thetaKO (G.dn i).ω g h f * Fm v g‖ ≤
        K * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * max H 1 ^ Ae * max B 0 := by
      intro g
      rw [norm_mul]
      have h1 := hK f hf g h
      have h2 : GlobalTheory.Grow.height (G.P i).V h ^ Ae ≤ max H 1 ^ Ae :=
        pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ h).le ((hH h hh).trans (le_max_left _ _)) Ae
      have h3 : ‖Fm v g‖ * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae ≤ max B 0 := (hB g).trans (le_max_left _ _)
      have h4 : 0 ≤ GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae := pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le Ae
      have h5 : 0 ≤ GlobalTheory.Grow.height (G.P i).V h ^ Ae := pow_nonneg (GlobalTheory.Grow.height_pos _ h).le Ae
      calc ‖thetaKO (G.dn i).ω g h f‖ * ‖Fm v g‖
          ≤ K * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae *
              GlobalTheory.Grow.height (G.P i).V h ^ Ae * ‖Fm v g‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = K * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * GlobalTheory.Grow.height (G.P i).V h ^ Ae *
              (‖Fm v g‖ * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae) := by ring
        _ ≤ K * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * max H 1 ^ Ae * max B 0 := by
          gcongr
    refine ⟨Integrable.of_bound hcont.aestronglyMeasurable _ (.of_forall hpt), ?_⟩
    refine (norm_integral_le_of_norm_le_const (.of_forall hpt)).trans (le_of_eq ?_)
    simp only [Measure.real, Measure.restrict_apply_univ]
    ring
  obtain ⟨d, M, hM0, hMb⟩ := hbound U hU
  have hδ : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / (M + 1)) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨g, hgS, hgU, hlt⟩ := happ d _ hδ
  obtain ⟨n, f, p, hf, rfl⟩ := exists_sum_of_mem_fockSpan hgS
  refine ⟨n, f, p, fun l => (isVacF_negFr _ _ (f l)).1 (hf l), fun h hh => ?_⟩
  have hpt : ∀ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l) =
      fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l) := fun l => ptF_negFr _ _ (f l) (p l)
  have hint : ∀ l, IntegrableOn (fun g => thetaKO (G.dn i).ω g h (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) *
      Fm v g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := by
    intro l
    have ht : IsThetaFunO R.ψ (neg (G.P (i + 1)).V) (G.P i).V
        (ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l)) :=
      GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hθ _ _ _ _ (hf l).1 (p l)
    obtain ⟨U', hU', hl'⟩ := GlobalTheory.Size.isTheta_iff_level.1 ht
    obtain ⟨_, _, _, hb⟩ := hbound U' hU'
    rw [← hpt l]
    exact (hb _ hl' h hh).1
  have e : (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * Fm v g ∂(G.mP (i + 1)).ν) -
      ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) *
        Fm v g ∂(G.mP (i + 1)).ν =
      ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (Φ - ∑ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l)) * Fm v g ∂(G.mP (i + 1)).ν := by
    rw [← integral_finset_sum _ fun l _ => hint l, ← integral_sub (hMb Φ hΦU h hh).1 (integrable_finset_sum _ fun l _ => hint l)]
    refine integral_congr_ae (.of_forall fun g => ?_)
    simp only [thetaKO, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_mul, hpt]
  rw [e]
  have hs := ENNReal.toReal_lt_of_lt_ofReal hlt
  have hs0 : 0 ≤ (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d (Φ - ∑ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l))).toReal :=
    ENNReal.toReal_nonneg
  refine ((hMb _ (sub_mem hΦU hgU) h hh).2).trans_lt ?_
  have hM1 : 0 < M + 1 := by linarith
  calc M * _ ≤ (M + 1) * _ := mul_le_mul_of_nonneg_right (by linarith) hs0
    _ < (M + 1) * (ε / (M + 1)) := mul_lt_mul_of_pos_left hs hM1
    _ = ε := by field_simp

end GlobalTheory.DownApprox
