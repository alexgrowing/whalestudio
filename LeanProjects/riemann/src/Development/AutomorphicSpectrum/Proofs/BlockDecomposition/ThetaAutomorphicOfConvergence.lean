import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbsThetaIntegralLeSobolevSeminormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableThetaKernelWeilRange
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevSeminormWeilThetaPolynomialInHeight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelMulConjCuspFormIntegrableOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDetRoot
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelSobolevBoundWeilCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSobolevBoundThetaPointwise
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSobolevSeminormSubTendstoZeroOfWordsUnif
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousWeilSchrodingerStandardUnnEvalZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelEqTsumSchrodingerFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIffStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Topology Filter GlobalTheory.Size

namespace GlobalTheory.CompanionTheory.ThetaAutoPf

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem exists_bound (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) {K : Set (GA D S)} (hK : IsCompact K) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x ∈ K, ∀ w, ‖om (x, 1) f w‖ₑ ≤ M := by
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨U', hU', hlev, hsob⟩ := GlobalTheory.ThetaDens.om_compact_sobCont D ψ S T χS χT om hom θ hθ μ 𝓕 hμ
    (K ×ˢ ({1} : Set (GA D T))) (hK.prod isCompact_singleton) U hU
  obtain ⟨d, C, hC⟩ := GlobalTheory.ThetaDensSup.sup_le_sobO D ψ hom.std θ hθ S T μ 𝓕 hμ U' hU'
  obtain ⟨d', C', hC'⟩ := hsob d
  refine ⟨C * (C' * sobO ψ θ μ 𝓕 d' f), ?_, fun x hx w => ?_⟩
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (sobO_ne_top hom.std hθ hμ.1 hμ.2.1 hf d'))
  · have hx' : ((x, 1) : GA D S × GA D T) ∈ K ×ˢ ({1} : Set (GA D T)) := ⟨hx, rfl⟩
    refine (hC _ (hlev f hl _ hx') w).trans ?_
    gcongr
    exact hC' f hl _ hx'

theorem l2_om_tendsto (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Tendsto (fun x : GA D S => l2O μ 𝓕 (om (x, 1) f - f)) (𝓝 1) (𝓝 0) := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : GA D S)
  obtain ⟨M, hM, hb⟩ := exists_bound hom hθ hμ hK hf
  have h1K : (1 : GA D S) ∈ K := mem_of_mem_nhds hK1
  have hf1 : ∀ w, ‖f w‖ₑ ≤ M := fun w => by
    have := hb 1 h1K w
    rwa [show ((1 : GA D S), (1 : GA D T)) = 1 from rfl, map_one, Module.End.one_apply] at this
  have hsq : Tendsto (fun x : GA D S => ∫⁻ w, ‖(om (x, 1) f - f) w‖ₑ ^ 2 ∂μ.restrict 𝓕) (𝓝 1)
      (𝓝 (∫⁻ _, 0 ∂μ.restrict 𝓕)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => (M + M) ^ 2)
      (Eventually.of_forall fun x => ?_) ?_ ?_ (Eventually.of_forall fun w => ?_)
    · exact (((hom.om_pres _ f hf).cont.sub hf.cont).enorm.measurable).pow_const 2
    · filter_upwards [hK1] with x hx
      refine Eventually.of_forall fun w => ?_
      gcongr
      exact (enorm_sub_le).trans (add_le_add (hb x hx w) (hf1 w))
    · rw [lintegral_const, Measure.restrict_apply_univ, hμ.2.2, mul_one]
      exact ENNReal.pow_ne_top (ENNReal.add_ne_top.2 ⟨hM, hM⟩)
    · have hc : Continuous fun x : GA D S => om (x, 1) f w :=
        (hom.om_cont f hf w).comp (Continuous.prodMk_left 1)
      have h0 : Tendsto (fun x : GA D S => om (x, 1) f w - f w) (𝓝 1) (𝓝 0) := by
        have := hc.tendsto 1
        have e : om ((1 : GA D S), (1 : GA D T)) f w = f w := by
          rw [show ((1 : GA D S), (1 : GA D T)) = 1 from rfl, map_one, Module.End.one_apply]
        rw [e] at this
        simpa using this.sub_const (f w)
      have h2 := (ENNReal.continuous_pow 2).continuousAt.tendsto.comp
        ((continuous_enorm.tendsto (0 : ℂ)).comp h0)
      simpa [Function.comp_def] using h2
  have hz : (∫⁻ _ : WO S T, (0 : ℝ≥0∞) ∂μ.restrict 𝓕) = 0 := lintegral_zero
  rw [hz] at hsq
  have e : ∀ x : GA D S, l2O μ 𝓕 (om (x, 1) f - f) =
      (∫⁻ w, ‖(om (x, 1) f - f) w‖ₑ ^ 2 ∂μ.restrict 𝓕) ^ (1 / 2 : ℝ) := fun x => by
    rw [← l2O_sq_eq_lintegral, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simp only [e]
  have := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp hsq
  simpa [Function.comp_def] using this

end GlobalTheory.CompanionTheory.ThetaAutoPf

namespace GlobalTheory.CompanionTheory.ThetaAutoPf

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem dRho_dir_split (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (τ : D.what₂.Tau) (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z' f + Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (z - z') f := by
  rw [dRho_eq_sum_heisDer hψ hθ hf, dRho_eq_sum_heisDer hψ hθ hf, dRho_eq_sum_heisDer hψ hθ hf,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.sub_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_sub, sub_smul]
  abel

theorem wordAct_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) :
    wordAct (heisDer ψ θ) l (f + g) = wordAct (heisDer ψ θ) l f + wordAct (heisDer ψ θ) l g := by
  have := GlobalTheory.ThetaDens.wordAct_heisDer_sub hψ hθ (GlobalTheory.OrientedHeis.theta_add hf hg) hg l
  rw [add_sub_cancel_right] at this
  rw [this, sub_add_cancel]

theorem l2_word_tendsto (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) :
    ∀ f, IsThetaFunO ψ S T f →
      Tendsto (fun x : GA D S => l2O μ 𝓕 (wordAct (heisDer ψ θ) l (om (x, 1) f - f))) (𝓝 1) (𝓝 0) := by
  have hψ := hom.std
  induction l using List.reverseRecOn with
  | nil => exact fun f hf => l2_om_tendsto hom hθ hμ hf
  | append_singleton l a ih =>
    intro f hf
    obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : GA D S)
    have hKK : IsCompact (K ×ˢ ({1} : Set (GA D T))) := hK.prod isCompact_singleton
    obtain ⟨B0, hB0⟩ := hKK.bddAbove_image (GlobalTheory.ThetaDens.WeilCompact.continuous_dirSize hθ S T).continuousOn
    have hB : ∀ x ∈ K ×ˢ ({1} : Set (GA D T)), GlobalTheory.ThetaDens.WeilCompact.dirSize θ S T x ≤ (B0.toNNReal : ℝ) :=
      fun x hx => (hB0 ⟨x, hx, rfl⟩).trans (Real.le_coe_toNNReal B0)
    obtain ⟨C, hC⟩ := GlobalTheory.ThetaDens.WeilCompact.word_om_le hom hθ hμ _ hB l.length
    set z : Matrix (Fin T.rank) (Fin S.rank) ℂ := Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) with hz
    set zx : GA D S → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun x =>
      compAt θ a.1 (Formalism.L2.Theta.mt T (1 : GA D T)⁻¹) * z * compAt θ a.1 (Formalism.L2.Theta.mt S x) with hzx
    have hg : IsThetaFunO ψ S T (heisDer ψ θ a f) := GlobalTheory.OrientedHeis.theta_dRho hθ hψ a.1 _ hf
    have hr : ∀ x, IsThetaFunO ψ S T (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ a.1 (zx x - z) f) := fun x =>
      GlobalTheory.OrientedHeis.theta_dRho hθ hψ a.1 _ hf

    have key : ∀ x : GA D S, wordAct (heisDer ψ θ) (l ++ [a]) (om (x, 1) f - f) =
        wordAct (heisDer ψ θ) l (om (x, 1) (heisDer ψ θ a f) - heisDer ψ θ a f) +
          wordAct (heisDer ψ θ) l (om (x, 1) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ a.1 (zx x - z) f)) := fun x => by
      have hof := hom.om_pres (x, 1) f hf
      have hog := hom.om_pres (x, 1) _ hg
      have hor := hom.om_pres (x, 1) _ (hr x)
      have e1 : heisDer ψ θ a (om (x, 1) f) =
          om (x, 1) (heisDer ψ θ a f) + om (x, 1) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ a.1 (zx x - z) f) := by
        rw [← map_add]
        have := GlobalTheory.ThetaDens.WeilCompact.dRho_om hom hθ x 1 a.1 z hf
        refine this.trans (congrArg _ ?_)
        exact dRho_dir_split hψ hθ hf a.1 _ z
      have e2 : heisDer ψ θ a (om (x, 1) f - f) = heisDer ψ θ a (om (x, 1) f) - heisDer ψ θ a f :=
        GlobalTheory.ThetaDens.wordAct_heisDer_sub hψ hθ hof hf [a]
      rw [wordAct_append, wordAct_cons, wordAct_nil, e2, e1, add_sub_right_comm,
        wordAct_add hψ hθ (GlobalTheory.OrientedHeis.theta_add hog (GlobalTheory.OrientedHeis.theta_smul (-1) hg) |> fun h => by
          simpa [sub_eq_add_neg] using h) hor]
    have hM : sobO ψ θ μ 𝓕 (l.length + 1) f ≠ ⊤ := sobO_ne_top hψ hθ hμ.1 hμ.2.1 hf _
    have hzc : Continuous zx := (continuous_const.matrix_mul continuous_const).matrix_mul
      ((GlobalTheory.RealWeil.continuous_compAt hθ a.1 _ _).comp (GlobalTheory.ThetaDens.WeilCompact.continuous_mt_eq S))
    have hz1 : zx 1 = z := by
      simp only [hzx, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, Matrix.one_mul, Matrix.mul_one]
    set c : GA D S → ℝ := fun x => ∑ i, ∑ j, (|((zx x - z) i j).re| + |((zx x - z) i j).im|) with hc
    have hcc : Continuous c := by
      refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
      have h3 : Continuous fun x => (zx x - z) i j := (hzc.sub continuous_const).matrix_elem i j
      exact (continuous_abs.comp (Complex.continuous_re.comp h3)).add (continuous_abs.comp (Complex.continuous_im.comp h3))
    have hc1 : c 1 = 0 := by simp [hc, hz1]
    have hup : Tendsto (fun x : GA D S => l2O μ 𝓕 (wordAct (heisDer ψ θ) l (om (x, 1) (heisDer ψ θ a f) - heisDer ψ θ a f)) +
        (C : ℝ≥0∞) * (ENNReal.ofReal (c x) * sobO ψ θ μ 𝓕 (l.length + 1) f)) (𝓝 1) (𝓝 0) := by
      have h1 : Tendsto (fun x => ENNReal.ofReal (c x)) (𝓝 1) (𝓝 0) := by
        have := (ENNReal.continuous_ofReal.comp hcc).tendsto 1
        simpa [Function.comp_def, hc1] using this
      have h2 := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞))
        (ENNReal.Tendsto.mul_const (b := sobO ψ θ μ 𝓕 (l.length + 1) f) h1 (Or.inr hM)) (Or.inr ENNReal.coe_ne_top)
      simpa using (ih _ hg).add h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hK1] with x hx
    rw [key x]
    have hog := hom.om_pres (x, 1) _ hg
    refine (l2O_add_le_of_continuous μ 𝓕 (theta_word hψ hθ l (GlobalTheory.OrientedHeis.theta_add hog
      (by simpa using GlobalTheory.OrientedHeis.theta_smul (-1) hg) |> fun h => by simpa [sub_eq_add_neg] using h)).cont
      (theta_word hψ hθ l (hom.om_pres (x, 1) _ (hr x))).cont).trans ?_
    gcongr
    refine (hC l rfl (x, 1) ⟨hx, rfl⟩ _ (hr x)).trans ?_
    gcongr
    exact sobO_dRho_le hψ hθ hf a.1 _ l.length

theorem sobO_om_tendsto (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (d : ℕ) :
    Tendsto (fun x : GA D S => sobO ψ θ μ 𝓕 d (om (x, 1) f - f)) (𝓝 1) (𝓝 0) := by
  have := tendsto_finset_sum (Finset.range (d + 1)) fun k _ =>
    tendsto_finset_sum (Finset.univ : Finset (Fin k → D.what₂.Tau × Fin T.rank × Fin S.rank × Bool))
      fun a _ => l2_word_tendsto hom hθ hμ (List.ofFn a) f hf
  simp only [Finset.sum_const_zero] at this
  exact this

end GlobalTheory.CompanionTheory.ThetaAutoPf

namespace GlobalTheory.CompanionTheory.ThetaAutoPf

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χ : (AE D)ˣ →* Circle}
  {om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)}

theorem thetaMean_sub (m : Measure (GA D B)) {f f' : WO (dblSp A) B → ℂ} {g : GA D (dblSp A)}
    (hi : Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO om g h f) (autMeasure B m))
    (hi' : Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO om g h f') (autMeasure B m)) :
    GlobalTheory.ThetaMean.thetaMean om m (f - f') g = GlobalTheory.ThetaMean.thetaMean om m f g - GlobalTheory.ThetaMean.thetaMean om m f' g := by
  have e : (GlobalTheory.AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO om g h (f - f')) =
      (GlobalTheory.AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO om g h f) - (GlobalTheory.AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO om g h f') := by
    funext q; simp [thetaKO, GlobalTheory.AutomorphicL2Unitary.descend]
  simp only [GlobalTheory.ThetaMean.thetaMean]
  rw [e, average_eq, average_eq, average_eq, integral_sub' hi hi', smul_sub]

theorem thetaMean_translate (m : Measure (GA D B)) (f : WO (dblSp A) B → ℂ) (x g : GA D (dblSp A)) :
    GlobalTheory.ThetaMean.thetaMean om m (om (x, 1) f) g = GlobalTheory.ThetaMean.thetaMean om m f (g * x) := by
  have e : ∀ h, thetaKO om g h (om (x, 1) f) = thetaKO om (g * x) h f := fun h => by
    simp only [thetaKO, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [GlobalTheory.ThetaMean.thetaMean, e]

theorem continuous_thetaMean (hP : GlobalTheory.Published.WeilThetaConvergence) (hW : IsWeilDatumO ψ (dblSp A) B 1 χ om)
    (hA : 1 ≤ A.rank) (hw : Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank)
    {m : Measure (GA D B)} (hm : m.IsHaarMeasure) {f : WO (dblSp A) B → ℂ} (hf : IsThetaFunO ψ (dblSp A) B f) :
    Continuous (GlobalTheory.ThetaMean.thetaMean om m f) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (dblSp A) B
  have hi : ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ g,
      Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO om g h f) (autMeasure B m) :=
    fun f hf g => GlobalTheory.WeilThetaInt.integrable_thetaKO hP D A B m hm hA hw ψ χ om hW f hf g
  have hint := GlobalTheory.T.absThetaIntegral_le_sobolevSeminorm D ψ (dblSp A) B 1 χ om hW θ hθ μ 𝓕 hμ m hm id (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) (GlobalTheory.ThetaDens.sobCont_id ψ θ μ 𝓕) (fun _ _ _ => rfl) (fun f hf => hi f hf 1)
  rw [continuous_iff_continuousAt]
  intro g₀
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : GA D (dblSp A))
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨U', hU', hlev, -⟩ := GlobalTheory.ThetaDens.om_compact_sobCont D ψ (dblSp A) B 1 χ om hW θ hθ μ 𝓕 hμ
    (K ×ˢ ({1} : Set (GA D B))) (hK.prod isCompact_singleton) U hU
  have hlx : ∀ x ∈ K, om (x, 1) f ∈ GlobalTheory.Size.thetaLevel ψ (dblSp A) B U' := fun x hx => hlev f hl _ ⟨hx, rfl⟩
  have hl1 : f ∈ GlobalTheory.Size.thetaLevel ψ (dblSp A) B U' := by
    have := hlx 1 (mem_of_mem_nhds hK1)
    rwa [show ((1 : GA D (dblSp A)), (1 : GA D B)) = 1 from rfl, map_one, Module.End.one_apply] at this
  obtain ⟨d, C, hC⟩ := hint U' hU' {g₀} isCompact_singleton
  set c : ℝ≥0∞ := ‖((autMeasure B m).real Set.univ)⁻¹‖ₑ with hc
  have hct : c ≠ ⊤ := enorm_ne_top
  have hbound : ∀ u ∈ GlobalTheory.Size.thetaLevel ψ (dblSp A) B U', ‖GlobalTheory.ThetaMean.thetaMean om m u g₀‖ₑ ≤
      c * (C * sobO ψ θ μ 𝓕 d u) := fun u hu => by
    calc ‖GlobalTheory.ThetaMean.thetaMean om m u g₀‖ₑ
        ≤ c * ∫⁻ q, ‖GlobalTheory.AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO om g₀ h u) q‖ₑ ∂autMeasure B m := by
          rw [GlobalTheory.ThetaMean.thetaMean, average_eq, enorm_smul]
          gcongr
          exact enorm_integral_le_lintegral_enorm _
      _ ≤ c * (C * sobO ψ θ μ 𝓕 d u) := by
          gcongr; exact hC u hu g₀ rfl
  have hlim : Tendsto (fun x : GA D (dblSp A) => c * (C * sobO ψ θ μ 𝓕 d (om (x, 1) f - f))) (𝓝 1) (𝓝 0) := by
    have h2 := ENNReal.Tendsto.const_mul (a := c) (ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞))
      (sobO_om_tendsto hW hθ hμ hf d) (Or.inr ENNReal.coe_ne_top)) (Or.inr hct)
    simpa using h2
  have hT : Tendsto (fun x : GA D (dblSp A) => GlobalTheory.ThetaMean.thetaMean om m f (g₀ * x)) (𝓝 1)
      (𝓝 (GlobalTheory.ThetaMean.thetaMean om m f g₀)) := by
    rw [tendsto_iff_edist_tendsto_0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hK1] with x hx
    rw [edist_eq_enorm_sub, ← thetaMean_translate m f x g₀,
      ← thetaMean_sub m (hi _ (hW.om_pres _ f hf) g₀) (hi f hf g₀)]
    exact hbound _ (Submodule.sub_mem _ (hlx x hx) hl1)
  rw [ContinuousAt, ← map_mul_left_nhds_one g₀, tendsto_map'_iff]
  simpa [Function.comp_def] using hT

end GlobalTheory.CompanionTheory.ThetaAutoPf

namespace GlobalTheory.CompanionTheory.ThetaAutoPf

open GlobalTheory.StdUnn

theorem thetaInt_auto (hP : GlobalTheory.Published.WeilThetaConvergence) (D : D7) (A V : HSp D) (hA : 1 ≤ A.rank)
    (hr : A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D} (hθ : IsInfFam θ)
    {μ : Measure (WO A V)} {𝓕 : Set (WO A V)} (hμ : IsCovolOne (ratL V A) μ 𝓕)
    {ω : G D A.rank →* Module.End ℂ (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ V.rank A.rank)} (hω : IsWeilSch ψ χ θ V μ ω)
    {ν : Measure (GA D V)} (hν : ν.IsHaarMeasure) (Φ : GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ V.rank A.rank) :
    Continuous (thetaInt ω ν Φ) ∧ LeftInv (GF D A.rank) (thetaInt ω ν Φ) := by
  obtain ⟨ψ₀, μ', lam, κ, omh, hs0, hsk, _, _, hκ, hW, hT⟩ := GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hs0 θ hθ A V μ 𝓕 hμ).2.1 Φ.1 Φ.2
  have hth : ∀ g : GA D (dblSp A), GlobalTheory.StdUnn.theta ω Φ (κ g) = fun h => thetaKO omh g h f := fun g => by
    funext h
    rw [GlobalTheory.T.thetaKernel_eq_tsum_schrodingerFunction D ψ₀ A V χ⁻¹ omh hW μ 𝓕 hμ f hf g h, GlobalTheory.StdUnn.theta, hT g f hf Φ hfΦ.symm]
  have hmean : thetaInt ω ν Φ = fun g => GlobalTheory.ThetaMean.thetaMean omh ν f (κ.symm g) := by
    funext g
    have e := hth (κ.symm g)
    rw [κ.apply_symm_apply] at e
    rw [thetaInt, e]
    rfl
  refine ⟨?_, fun γ hγ g => ?_⟩
  · rw [hmean]
    exact (continuous_thetaMean hP hW hA (Or.inr hr) hν hf).comp (GlobalTheory.StdUnn.chart_continuous D A μ' hsk κ hκ).2
  · have hq : κ.symm γ ∈ GQ (dblSp A) :=
      (GlobalTheory.T.standardUnitaryChart_mem_rational_iff D A μ' hsk κ hκ _).2 (by rwa [κ.apply_symm_apply])
    rw [hmean]
    simp only [map_mul, GlobalTheory.ThetaMean.thetaMean,
      GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hW hf _ _ hq]

theorem thetaAuto : GlobalTheory.Published.WeilThetaConvergence → PositivityTheory.PfSWUS.ThetaAuto := by
  intro hP D n V ψ χ θ μ ω H l s ν Φ hstd hr
  obtain ⟨𝓕, hμ⟩ := hstd.hμ
  obtain ⟨h1, h2, h3⟩ := hr
  exact thetaInt_auto hP D (Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n) V
    (show 1 ≤ n by omega) h3 hstd.hψ hstd.hχ hstd.hη hstd.hθ hμ hstd.hω hstd.hν Φ

end GlobalTheory.CompanionTheory.ThetaAutoPf
