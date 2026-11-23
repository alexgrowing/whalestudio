import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalFunctionBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalFunctionBoundStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate
namespace GlobalTheory.UpArrowApprox
end GlobalTheory.UpArrowApprox
namespace GlobalTheory.UpArrowApprox
theorem upperArrow_approx : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ F : (G.P i).Maps, F ∈ (G.P i).Cusp R.θ → ∀ v : SmT (G.P i).M, (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g) (G.mP i).fd (G.mP i).ν) → ∀ C : Set (GA D (G.P (i + 1)).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (f : Fin n → (WO (G.P (i + 1)).V (G.P i).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l)) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g ∂(G.mP i).ν) - ∑ l, ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l))) * F v g ∂(G.mP i).ν‖ < ε := by
  intro hLC hP D hSz G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ F hF v hint C hC ε hε
  have hθ : IsInfFam R.θ := hR.inf
  have hω := (hG.arrows.dn i hi).weil
  have hψ : IsStdChar D R.ψ (-1) := IsWeilDatumO.std hω
  have hm := (hG.meas.P i hi.le).2 (by omega)
  have hCA := hLC D hSz G₀ Pl0 T A Ks R G hR hG
  obtain ⟨-, -, hFr⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP.cuspRapidDecay D _ _ _ R.θ hθ _ _ F hF v
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V
  obtain ⟨U, hU, hΦU, hdense⟩ := GlobalTheory.FockDensity.fockDense D _ _
    (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel (G.P (i + 1)).M)) (GlobalTheory.ChainFr.Fr.ofModel (G.P i).M) R.θ R.ψ hψ hθ
    μ 𝓕 hμ Φ hΦ
  obtain ⟨a, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (GlobalTheory.Grid.neg (G.P (i + 1)).V).rank (G.P i).V.rank
  obtain ⟨K, hK0, hK⟩ := (H (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V rfl rfl).real R.ψ hθ hU
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ h ∈ C,
      GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) ((GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V).symm h) ≤ M := by
    obtain ⟨M, hM⟩ := hC.bddAbove_image
      ((GlobalTheory.Grow.continuous_height _).comp (GlobalTheory.Grid.continuous_ofSgn_symm true _)).continuousOn
    exact ⟨M, fun h hh => hM ⟨h, hh, rfl⟩⟩
  obtain ⟨B, hB⟩ := hFr.decay a
  have hfin : (G.mP i).ν (G.mP i).fd < ⊤ := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hm.1.1 hm.2
  set L : ℝ := K * max M 1 ^ a * 2 ^ a * max B 0 * ((G.mP i).ν (G.mP i).fd).toReal with hL
  have hL0 : 0 ≤ L := by
    have : 0 ≤ max M 1 := le_trans zero_le_one (le_max_right _ _)
    have : 0 ≤ max B 0 := le_max_right _ _
    positivity
  have hδ : 0 < ε / (2 * (L + 1)) := div_pos hε (by linarith)
  obtain ⟨g₀, hg₀, hg₀U, hg₀d⟩ := hdense d (ENNReal.ofReal (ε / (2 * (L + 1)))) (ENNReal.ofReal_pos.2 hδ)
  obtain ⟨n, c, w, hw⟩ := Submodule.mem_span_set'.1 hg₀
  choose f₀ P hvac hlev hgeq using fun l => (w l).2
  refine ⟨n, f₀, fun l => c l • P l, fun l => isFinVec_of_isVacF (hvac l), fun h hh => ?_⟩
  have hsum : g₀ = ∑ l, GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f₀ l) (c l • P l) := by
    rw [← hw]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hgeq l, ← ptF_eq_fock]
    simp only [GlobalTheory.ChainFr.ptF, map_smul]
  have he : Φ - g₀ ∈ GlobalTheory.Size.thetaLevel R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V U := sub_mem hΦU hg₀U
  have hint' : ∀ l, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f₀ l) (c l • P l))) * F v g) (G.mP i).fd (G.mP i).ν :=
    fun l => ((hCA.up i hi (f₀ l) (isFinVec_of_isVacF (hvac l)) F hF).choose_spec.2 (c l • P l) v h).1
  have hlin : ∀ g, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g -
      ∑ l, starRingEnd ℂ (thetaKO (G.dn i).ω h g
        (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f₀ l) (c l • P l))) * F v g =
      starRingEnd ℂ (thetaKO (G.dn i).ω h g (Φ - g₀)) * F v g := by
    intro g
    rw [hsum]
    simp only [thetaKO, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_mul]
  rw [← integral_finset_sum _ fun l _ => hint' l, ← integral_sub (hint h) (integrable_finset_sum _ fun l _ => hint' l)]
  have e0 : (∫ g in (G.mP i).fd, (starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g -
      ∑ l, starRingEnd ℂ (thetaKO (G.dn i).ω h g
        (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f₀ l) (c l • P l))) * F v g) ∂(G.mP i).ν) =
      ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g (Φ - g₀)) * F v g ∂(G.mP i).ν := by
    congr 1
    funext g
    exact hlin g
  rw [e0]
  set s : ℝ := (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d (Φ - g₀)).toReal with hs
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  set h' := (GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V).symm h with hh'
  have hpt : ∀ g, ‖starRingEnd ℂ (thetaKO (G.dn i).ω h g (Φ - g₀)) * F v g‖ ≤ K * max M 1 ^ a * 2 ^ a * max B 0 * s := by
    intro g
    have e1 : thetaKO (G.dn i).ω h g (Φ - g₀) = thetaKO ((G.dn i).ω.toSgn true) h' g (Φ - g₀) :=
      GlobalTheory.UpArrowConv.thetaKO_toSgn _ _ _ _
    have hbd : ∀ g, ‖thetaKO ((G.dn i).ω.toSgn true) h' g (Φ - g₀)‖ ≤
        (K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a) * GlobalTheory.Grow.height (G.P i).V g ^ a := fun g => by
      have := (hK _ _ _ hω μ 𝓕 hμ _ he).2 h' g
      rw [mul_pow, ← mul_assoc] at this
      exact this
    have hq := GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => thetaKO ((G.dn i).ω.toSgn true) h' g (Φ - g₀))
      (GlobalTheory.UpArrowConv.thetaKO_left_snd hω he.1 h') hbd g
    rw [norm_mul, RCLike.norm_conj, e1]
    have hh1 : GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a ≤ max M 1 ^ a :=
      pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ _).le ((hM h hh).trans (le_max_left _ _)) a
    have hFB : ‖F v g‖ * GlobalTheory.Grow.quotHeight (G.P i).V g ^ a ≤ max B 0 := (hB g).trans (le_max_left _ _)
    have a0 : 0 ≤ K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a * 2 ^ a :=
      mul_nonneg (mul_nonneg (mul_nonneg hK0 hs0) (pow_nonneg (GlobalTheory.Grow.height_pos _ _).le _)) (by positivity)
    have a1 : K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a * 2 ^ a ≤ K * s * max M 1 ^ a * 2 ^ a :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh1 (mul_nonneg hK0 hs0)) (by positivity)
    calc ‖thetaKO ((G.dn i).ω.toSgn true) h' g (Φ - g₀)‖ * ‖F v g‖
        ≤ K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a * 2 ^ a *
            GlobalTheory.Grow.quotHeight (G.P i).V g ^ a * ‖F v g‖ := mul_le_mul_of_nonneg_right hq (norm_nonneg _)
      _ = K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a * 2 ^ a *
            (‖F v g‖ * GlobalTheory.Grow.quotHeight (G.P i).V g ^ a) := by ring
      _ ≤ K * s * max M 1 ^ a * 2 ^ a * max B 0 :=
          mul_le_mul a1 hFB (mul_nonneg (norm_nonneg _) (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ _).le _))
            (a0.trans a1)
      _ = K * max M 1 ^ a * 2 ^ a * max B 0 * s := by ring
  refine (norm_setIntegral_le_of_norm_le_const hfin fun g _ => hpt g).trans_lt ?_
  have hslt : s < ε / (2 * (L + 1)) := ENNReal.toReal_lt_of_lt_ofReal hg₀d
  calc K * max M 1 ^ a * 2 ^ a * max B 0 * s * ((G.mP i).ν (G.mP i).fd).toReal = L * s := by rw [hL]; ring
    _ ≤ (L + 1) * s := by nlinarith
    _ < (L + 1) * (ε / (2 * (L + 1))) := mul_lt_mul_of_pos_left hslt (by linarith)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith
end GlobalTheory.UpArrowApprox
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_upperArrow_approx : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ F : (G.P i).Maps, F ∈ (G.P i).Cusp R.θ → ∀ v : SmT (G.P i).M, (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g) (G.mP i).fd (G.mP i).ν) → ∀ C : Set (GA D (G.P (i + 1)).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (f : Fin n → (WO (G.P (i + 1)).V (G.P i).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l)) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g ∂(G.mP i).ν) - ∑ l, ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l))) * F v g ∂(G.mP i).ν‖ < ε := by
  first | exact @_root_.GlobalTheory.UpArrowApprox.upperArrow_approx | exact _root_.GlobalTheory.UpArrowApprox.upperArrow_approx | (intros; apply _root_.GlobalTheory.UpArrowApprox.upperArrow_approx <;> assumption)
end
