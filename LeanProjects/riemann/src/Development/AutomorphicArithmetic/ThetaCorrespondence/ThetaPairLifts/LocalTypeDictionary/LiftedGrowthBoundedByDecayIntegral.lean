import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftBoundedNorm
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftBoundedNormStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DownLiftGrowth
theorem growthSize_lift_le_decayIntegral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∃ C : NNReal, ∀ f : GA D (G.P (i + 1)).V → ℂ, GlobalTheory.Size.growthSize (G.P i).V N (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * f g ∂(G.mP (i + 1)).ν) ≤ (C : ENNReal) * GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd N f := by
  intro _ D _ G₀ _ _ Pl0 T Af Ks _ _ _ R G hB hG i hi
  obtain ⟨N, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (GlobalTheory.Grid.sgn true (G.P (i + 1)).V).rank (G.P i).V.rank
  refine ⟨N, fun Φ hΦ => ?_⟩
  have hω := (hG.arrows.dn i hi).weil
  obtain ⟨U, hU, hl⟩ := GlobalTheory.Size.isTheta_iff_level.1 hΦ
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (GlobalTheory.Grid.sgn true (G.P (i + 1)).V) (G.P i).V
  obtain ⟨C, hC0, hC⟩ := (H _ _ rfl rfl).real R.ψ hB.inf hU
  have hb := (hC _ _ _ hω μ 𝓕 hμ Φ hl).2
  set K := C * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d Φ).toReal with hK
  have hK0 : 0 ≤ K := mul_nonneg hC0 ENNReal.toReal_nonneg
  have e : ∀ g h, thetaKO (G.dn i).ω g h Φ =
      thetaKO ((G.dn i).ω.toSgn true) ((GlobalTheory.Grid.ofSgn true _).symm g) h Φ := fun g h => by
    show (G.dn i).ω (g, h) Φ 0 = (G.dn i).ω (GlobalTheory.Grid.ofSgn true _ ((GlobalTheory.Grid.ofSgn true _).symm g), h) Φ 0
    rw [MulEquiv.apply_symm_apply]
  have hinv : ∀ h, ∀ γ ∈ GQ (G.P (i + 1)).V, ∀ g,
      thetaKO (G.dn i).ω (γ * g) h Φ = thetaKO (G.dn i).ω g h Φ := fun h γ hγ g => by
    rw [e, e, map_mul]
    refine GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hω hΦ h _ ?_ _
    rw [GlobalTheory.SgnIdent.mem_GQ_sgn, MulEquiv.apply_symm_apply]
    exact hγ
  have hk : ∀ g h, ‖thetaKO (G.dn i).ω g h Φ‖ ≤
      K * 2 ^ N * GlobalTheory.Grow.height (G.P i).V h ^ N * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ N := by
    intro g h
    have h1 : ∀ g, ‖thetaKO (G.dn i).ω g h Φ‖ ≤
        (K * GlobalTheory.Grow.height (G.P i).V h ^ N) * GlobalTheory.Grow.height (G.P (i + 1)).V g ^ N := fun g => by
      rw [e]
      have h2 := hb ((GlobalTheory.Grid.ofSgn true _).symm g) h
      have hh : GlobalTheory.Grow.height (GlobalTheory.Grid.sgn true (G.P (i + 1)).V) ((GlobalTheory.Grid.ofSgn true _).symm g) =
          GlobalTheory.Grow.height (G.P (i + 1)).V g := rfl
      rw [hh] at h2
      exact h2.trans_eq (by rw [hK, mul_pow]; ring)
    exact (GlobalTheory.Grow.norm_le_quotHeight_pow (hinv h) h1 g).trans_eq (by ring)
  refine ⟨(K * 2 ^ N).toNNReal, fun f => iSup_le fun h => ?_⟩
  have hg := pow_pos (GlobalTheory.Grow.height_pos (G.P i).V h) N
  rw [ENNReal.ofReal_div_of_pos hg, ofReal_norm_eq_enorm]
  refine ENNReal.div_le_of_le_mul ((enorm_integral_le_lintegral_enorm _).trans ?_)
  rw [mul_right_comm, GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt]
  refine (lintegral_mono fun g => ?_).trans_eq
    (lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top))
  have hq := (pow_pos (GlobalTheory.Grow.quotHeight_pos (G.P (i + 1)).V g) N).le
  rw [← ofReal_norm_eq_enorm]
  change ENNReal.ofReal _ ≤ ENNReal.ofReal (K * 2 ^ N) * _ * _
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [norm_mul]
  calc ‖thetaKO (G.dn i).ω g h Φ‖ * ‖f g‖
      ≤ (K * 2 ^ N * GlobalTheory.Grow.height (G.P i).V h ^ N * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ N) * ‖f g‖ :=
        mul_le_mul_of_nonneg_right (hk g h) (norm_nonneg _)
    _ = _ := by ring
end GlobalTheory.DownLiftGrowth
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lifted_growth_bounded_by_decay_integral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∃ C : NNReal, ∀ f : GA D (G.P (i + 1)).V → ℂ, GlobalTheory.Size.growthSize (G.P i).V N (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * f g ∂(G.mP (i + 1)).ν) ≤ (C : ENNReal) * GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd N f := by
  first | exact @_root_.GlobalTheory.DownLiftGrowth.growthSize_lift_le_decayIntegral | exact _root_.GlobalTheory.DownLiftGrowth.growthSize_lift_le_decayIntegral | (intros; apply _root_.GlobalTheory.DownLiftGrowth.growthSize_lift_le_decayIntegral <;> assumption)
end
