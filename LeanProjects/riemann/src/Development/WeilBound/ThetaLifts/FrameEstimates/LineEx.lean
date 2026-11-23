import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExtensionEmbeddingEvInfRealAd
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfPiInf
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExistsAdelePiInf

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace ExponentialLineExistence

open GlobalTheory.CompanionTheory.CMAdele

section Cx

variable {d : ℕ}

theorem exp_line_add (Y : Matrix (Fin d) (Fin d) ℂ) (s t : ℝ) :
    NormedSpace.exp (((s + t : ℝ) : ℂ) • Y) = NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp ((t : ℂ) • Y) := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _), Complex.ofReal_add, add_smul]

theorem exp_map_star (A : Matrix (Fin d) (Fin d) ℂ) :
    (NormedSpace.exp A).map star = NormedSpace.exp (A.map star) := by
  have e : ∀ B : Matrix (Fin d) (Fin d) ℂ, B.map star = Bᴴᵀ := fun B => rfl
  rw [e, e, Matrix.exp_transpose, Matrix.exp_conjTranspose]

set_option backward.isDefEq.respectTransparency false in
theorem exp_semiconj {J A B : Matrix (Fin d) (Fin d) ℂ} (h : SemiconjBy J A B) :
    NormedSpace.exp (-B) * J * NormedSpace.exp A = J :=
  open scoped Matrix.Norms.Operator in h.exp_neg_mul_mul_exp_eq_self

set_option backward.isDefEq.respectTransparency false in
theorem continuous_exp_mat : Continuous (NormedSpace.exp : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) :=
  open scoped Matrix.Norms.Operator in NormedSpace.exp_continuous

theorem exp_unitary {J Y : Matrix (Fin d) (Fin d) ℂ} (h : Yᵀ * J + J * Y.map star = 0) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • Y))ᵀ * J * (NormedSpace.exp ((t : ℂ) • Y)).map star = J := by
  have h1 : SemiconjBy J (((t : ℂ) • Y).map star) (-((t : ℂ) • Y)ᵀ) := by
    have e : ((t : ℂ) • Y).map star = (t : ℂ) • Y.map star := by
      ext i j
      simp
    rw [SemiconjBy, e, Matrix.transpose_smul, Matrix.mul_smul, neg_mul, Matrix.smul_mul, ← smul_neg,
      eq_neg_of_add_eq_zero_right h]
  have h2 := exp_semiconj h1
  rwa [neg_neg, Matrix.exp_transpose, ← exp_map_star] at h2

end Cx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | add x y hx hy => simp only [map_add, hx, hy, star_add]
  | tmul a x =>
    change piInf τ (a ⊗ₜ[F] σ x) = _
    rw [piInf_tmul, piInf_tmul, h.2.2.2, star_mul', show star (InfinitePlace.Completion.extensionEmbedding w (a.1 w)) = _ from
      Complex.conj_eq_iff_im.2 (im_extension h.1 w _)]

theorem map_incM {w : InfinitePlace F} (τ : EmbOver E w) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  exact (piInf_tmul τ 1 (J i j)).trans (by rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]; rfl)

theorem continuous_realAd : Continuous (realAd F) := by
  refine Continuous.prodMk (f := fun t => (realAd F t).1) (g := fun _ => (0 : Af F)) ?_ continuous_const
  refine continuous_pi fun w => ?_
  refine (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.isInducing.continuous_iff.2 ?_
  have e : (InfinitePlace.Completion.extensionEmbedding w) ∘ (fun t => (realAd F t).1 w) = fun t : ℝ => (t : ℂ) :=
    funext fun t => GlobalTheory.CompanionTheory.RealAdeleComponent.extensionEmbedding_evInf_realAd w t
  exact e ▸ Complex.continuous_ofReal

theorem exists_section (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ s : (InfinitePlace F → ℂ) → AE F E, Continuous s ∧ (∀ z, At (evI F) (s z)) ∧ ∀ z w, piInf (τ w) (s z) = z w := by
  classical
  choose x hx hx' using fun w : InfinitePlace F =>
    GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h τ (Pi.single w 1)
  choose y hy hy' using fun w : InfinitePlace F =>
    GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h τ (Pi.single w Complex.I)
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine ⟨fun z => ∑ w, (realAd F (z w).re • x w + realAd F (z w).im • y w), ?_, fun z c hc => ?_, fun z w => ?_⟩
  · have hr : ∀ (a : AE F E) (f : (InfinitePlace F → ℂ) → ℝ), Continuous f → Continuous fun z => realAd F (f z) • a :=
      fun a f hf => ((continuous_realAd (F := F)).comp hf).smul (continuous_const (y := a))
    refine continuous_finsetSum _ fun w _ => Continuous.add (hr _ _ ?_) (hr _ _ ?_)
    · exact Complex.continuous_re.comp (continuous_apply (A := fun _ => ℂ) w)
    · exact Complex.continuous_im.comp (continuous_apply (A := fun _ => ℂ) w)
  · rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [smul_add, smul_comm c, smul_comm c, hx w c hc, hy w c hc, smul_zero, smul_zero, add_zero]
  · rw [map_sum, Finset.sum_eq_single w]
    · rw [map_add, GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, hx', hy',
        Pi.single_eq_same, Pi.single_eq_same, mul_one, Complex.re_add_im]
    · intro v _ hv
      rw [map_add, GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, hx', hy',
        Pi.single_eq_of_ne hv.symm, Pi.single_eq_of_ne hv.symm, mul_zero, mul_zero, add_zero]
    · simp

variable {d : ℕ}

theorem mat_ext (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {u v : Matrix (Fin d) (Fin d) (AE F E)}
    (hf : ∀ c : AF F, evI F c = 0 → c • u = c • v) (e : ∀ w, u.map (piInf (τ w)) = v.map (piInf (τ w))) : u = v := by
  ext i j
  refine sub_eq_zero.1 (eq_zero_of_piInf σ h τ _ (fun c hc => ?_) fun w => ?_)
  · rw [smul_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (hf c hc) i) j)
  · rw [map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (e w) i) j)

omit [NumberField E] in
theorem at_iff {u : Matrix (Fin d) (Fin d) (AE F E)} :
    At (evI F) (u - 1) ↔ ∀ c : AF F, evI F c = 0 → c • u = c • (1 : Matrix (Fin d) (Fin d) (AE F E)) :=
  forall_congr' fun c => forall_congr' fun _ => by rw [smul_sub, sub_eq_zero]

theorem exists_matSection (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) :
    ∃ S : (InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) → Matrix (Fin d) (Fin d) (AE F E), Continuous S ∧
      (∀ z (c : AF F), evI F c = 0 → c • S z = c • (1 : Matrix (Fin d) (Fin d) (AE F E))) ∧
      ∀ z w, (S z).map (piInf (τ w)) = z w := by
  obtain ⟨s, hs, hA, hp⟩ := exists_section h τ
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine ⟨fun z => Matrix.of fun i j => (1 : Matrix (Fin d) (Fin d) (AE F E)) i j +
    s fun w => z w i j - (1 : Matrix (Fin d) (Fin d) ℂ) i j, ?_, fun z c hc => ?_, fun z w => ?_⟩
  · refine continuous_matrix fun i j => continuous_const.add (hs.comp (continuous_pi fun w => ?_))
    exact ((continuous_apply w).matrix_elem i j).sub continuous_const
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply]
    rw [smul_add, hA _ c hc, add_zero]
  · ext i j
    have e := congrFun (congrFun (Matrix.map_one (n := Fin d) (piInf (τ w)) (map_zero _) (map_one _)) i) j
    rw [Matrix.map_apply] at e
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [map_add, hp, e, add_sub_cancel]

end ExponentialLineExistence

open ExponentialLineExistence in
theorem lineEx_of : LineEx := by
  intro F E _ _ _ _ _ σ h τ d W _ Y hY
  obtain ⟨S, hS, hf, hp⟩ := exists_matSection h τ d
  let g : ℝ → Matrix (Fin d) (Fin d) (AE F E) := fun t => S fun w => NormedSpace.exp ((t : ℂ) • Y w)
  have gp : ∀ t w, (g t).map (piInf (τ w)) = NormedSpace.exp ((t : ℂ) • Y w) := fun t w => hp _ w
  have gf : ∀ t (c : AF F), evI F c = 0 → c • g t = c • (1 : Matrix (Fin d) (Fin d) (AE F E)) := fun t => hf _
  have gc : Continuous g := hS.comp (continuous_pi fun w =>
    continuous_exp_mat.comp (Complex.continuous_ofReal.smul continuous_const))
  have g0 : g 0 = 1 := mat_ext h τ (gf 0) fun w => by
    rw [gp, Matrix.map_one _ (map_zero _) (map_one _), Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
  have ga : ∀ s t, g (s + t) = g s * g t := fun s t => mat_ext h τ
    (fun c hc => by rw [gf _ c hc, ← Matrix.smul_mul, gf _ c hc, Matrix.smul_mul, Matrix.one_mul, gf _ c hc])
    fun w => by rw [Matrix.map_mul, gp, gp, gp, exp_line_add]
  have gu : ∀ t, (g t)ᵀ * incM F W.J * (g t).map (cA σ) = incM F W.J := fun t => mat_ext h τ
    (fun c hc => by
      have e : ∀ u : Matrix (Fin d) (Fin d) (AE F E), c • u.map (cA σ) = (c • u).map (cA σ) := fun u => by
        ext i j
        simp only [Matrix.smul_apply, Matrix.map_apply, map_smul]
      rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, gf _ c hc, Matrix.transpose_smul,
        Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, ← Matrix.mul_smul, e, gf _ c hc, ← e,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_smul, Matrix.mul_one])
    fun w => by
      have e : ((g t).map (cA σ)).map (piInf (τ w)) = ((g t).map (piInf (τ w))).map star := by
        ext i j
        exact piInf_cA h _ _
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, map_incM, e, gp]
      exact exp_unitary (hY w) t
  let G : ℝ → GL (Fin d) (AE F E) := fun t =>
    ⟨g t, g (-t), by rw [← ga, add_neg_cancel, g0], by rw [← ga, neg_add_cancel, g0]⟩
  let γ : Multiplicative ℝ →* UA σ W.J :=
    { toFun := fun t => ⟨G t.toAdd, gu _⟩
      map_one' := Subtype.ext (Units.ext g0)
      map_mul' := fun s t => Subtype.ext (Units.ext (ga _ _)) }
  refine ⟨γ, ⟨?_, fun t => at_iff.2 (gf _)⟩, fun w t => gp t w, fun γ' hγ' hG => ?_⟩
  · refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · exact gc.comp continuous_toAdd
    · exact (gc.comp continuous_neg).comp continuous_toAdd
  · refine MonoidHom.ext fun t => Subtype.ext (Units.ext ?_)
    refine mat_ext h τ (u := mat (γ' t)) (v := g t.toAdd) (fun c hc => ?_) fun w => ?_
    · rw [at_iff.1 (hγ'.2 t) c hc, gf _ c hc]
    · rw [gp]
      exact hG w t.toAdd

end PositivityTheory.ThKEst

end
