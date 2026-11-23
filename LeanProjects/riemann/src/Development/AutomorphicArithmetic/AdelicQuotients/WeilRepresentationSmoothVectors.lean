import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
import Development.WeilBound.ThetaLifts.LatticeBasics.PolFin
import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsL

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions

open UpperTheory.TP

section Left

open PositivityTheory.ThKEst PositivityTheory.ThKEst.levelStructure PositivityTheory.ThKEst.LatticeQuotientMeasure PositivityTheory.ThKF0.Grow PositivityTheory.ThKF0.Grow.Fi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem schr_left {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {g : (Fin n × Fin d → Af F) → ℂ} (hg : g ∈ SB _) {C : Set (Ten F E n d)} (hC : IsCompact C) :
    ∀ᶠ u in 𝓝 (1 : UA σ X.J), levelStructure.IsFin u → ∀ z : Ten F E n d, (∃ c ∈ C, At (evI F) (z - c)) → ∀ f,
      schr ψ (M.co.e (mat u * z)) (pureA F f g) = schr ψ (M.co.e z) (pureA F f g) := by
  have := ring_AE F E
  have : IsModuleTopology (AF F) (Ten F E n d) := inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hV := schr_near hψ hg (hC.image he)
  have hm : Continuous fun p : UA σ X.J × Ten F E n d => M.co.e ((mat p.1 - 1) * p.2) :=
    he.comp ((((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).sub continuous_const).matrix_mul
      continuous_snd)
  have h1 := hC.eventually_forall_of_forall_eventually (x₀ := (1 : UA σ X.J))
    (P := fun u c => M.co.e ((mat u - 1) * c) ∈ _) fun c _ => hm.continuousAt.preimage_mem_nhds (by
      rwa [show mat (1 : UA σ X.J) = 1 from rfl, sub_self, Matrix.zero_mul, map_zero])
  filter_upwards [h1] with u h1 hu z hz f
  obtain ⟨c, hc, hz⟩ := hz
  rw [at_iff, smul_sub, sub_eq_zero] at hz
  have hu' : e0 F • (mat u - 1) = mat u - 1 := hu
  have e : mat u * z = z + (mat u - 1) * c := by
    have e1 : (mat u - 1) * c = (mat u - 1) * z := by
      rw [← hu', Matrix.smul_mul, ← Matrix.mul_smul, ← hz, Matrix.mul_smul, Matrix.smul_mul]
    rw [e1, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
  rw [e, map_add]
  exact h1 c hc (by rw [← map_smul, ← Matrix.smul_mul, hu']) _ ⟨c, hc, rfl⟩ _ (by rw [← map_smul, ← map_smul, hz]) f

end Left

theorem UpperTheory.weil_representation_smooth_vectors :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), ∀ r s r' s', IsPair B M χX χW om r s r' s' → ∀ φ ∈ SB (Fin n × Fin d → Af F), ∃ U ∈ 𝓝 (1 : UA σ X.J), ∀ u ∈ U, (∀ w, (mat u).map (piInf (B.emb w)) = 1) → ∀ f : SInf F (Fin n × Fin d), om (u, 1) (pureA F f φ) = pureA F f φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ
  by_cases h0 : ∀ f : SInf F (Fin n × Fin d), pureA F f φ = 0
  · exact ⟨Set.univ, univ_mem, fun u _ _ f => by rw [h0, map_zero]⟩
  push Not at h0
  obtain ⟨f₀, h0⟩ := h0
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h0
  have hy : pureA F f₀ φ y ≠ 0 := hy
  have hs := IsUWeilPair.isUSplitting hp.weil
  have mem : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d) := fun f =>
    Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  obtain ⟨μ, hμ, -⟩ := PositivityTheory.ThKEst.ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨p, C, -, hCc, hb⟩ := PositivityTheory.ThKEst.coefBd_of PositivityTheory.ThKEst.coefReal_of F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ 0
  have h1 := schr_left M hp.base.std hφ hCc
  have := PositivityTheory.ThKEst.LatticeQuotientMeasure.ring_AE F E
  have hi : Continuous fun u : UA σ X.J => u⁻¹ :=
    ((continuous_inv (G := GL (Fin n) (AE F E))).comp continuous_subtype_val).subtype_mk fun u => (u⁻¹).2
  have h2 := (hi.tendsto' 1 1 inv_one).eventually h1
  have hc : Continuous fun u : UA σ X.J => ‖om (u, 1) (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ :=
    ((((hs.cont _ (PositivityTheory.ThKEst.levelStructure.ev_adm y) _ (mem f₀)).comp (continuous_id.prodMk continuous_const)).div_const _).sub
      continuous_const).norm
  have h3 := PositivityTheory.ThKEst.levelStructure.pow_near _ ((isOpen_lt hc (continuous_const (y := (1 / 2 : ℝ)))).mem_nhds (by
    change ‖om 1 (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ < 1 / 2
    rw [map_one, Module.End.one_apply, div_self hy]
    norm_num))
  refine ⟨_, h1.and (h2.and h3), fun u ⟨h1, h2, h3⟩ hu => ?_⟩
  have hu := PositivityTheory.ThKEst.levelStructure.isFin_of hp.base.cm B.emb hu
  have key : ∀ (f : SInf F (Fin n × Fin d)) x, om (u, 1) (pureA F f φ) x * (starRingEnd ℂ) (om (u, 1) (pureA F f₀ φ) y) =
      pureA F f φ x * (starRingEnd ℂ) (pureA F f₀ φ y) := by
    intro f x
    refine PositivityTheory.ThKEst.fourierInj_of F _ B.ψ hp.base.std μ hμ _ (hs.pres _ _ (mem f)) _ (hs.pres _ _ (mem f₀)) _ (mem f) _ (mem f₀) ?_ x y
    funext w
    obtain ⟨z, rfl⟩ := M.co.e.surjective w
    rw [PositivityTheory.ThKEst.coefEq_of F E σ B n d X W M χX χW om r s r' s' hp μ hμ _ (mem f) _ (mem f₀), PositivityTheory.ThKEst.ParityOfCoefficients.mat_one_inv,
      Matrix.transpose_one, Matrix.mul_one]
    by_cases a : ∃ c ∈ C, At (evI F) (z - c)
    · unfold PositivityTheory.ThKEst.coef
      rw [h2 hu.inv z a]
    by_cases a' : ∃ c ∈ C, At (evI F) (mat u⁻¹ * z - c)
    · unfold PositivityTheory.ThKEst.coef
      rw [← h1 hu _ a', ← Matrix.mul_assoc, show mat u * mat u⁻¹ = 1 from Units.mul_inv u.1, Matrix.one_mul]
    have b := hb f f₀ z
    have b' := hb f f₀ (mat u⁻¹ * z)
    rw [PositivityTheory.ThKEst.maj, if_neg a, mul_zero, norm_le_zero_iff] at b
    rw [PositivityTheory.ThKEst.maj, if_neg a', mul_zero, norm_le_zero_iff] at b'
    rw [b, b']
  have h4 : (starRingEnd ℂ) (om (u, 1) (pureA F f₀ φ) y) ≠ 0 := fun h => by
    have := key f₀ y
    rw [h, mul_zero, eq_comm, mul_eq_zero, map_eq_zero, or_self] at this
    exact hy this
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ f : SInf F (Fin n × Fin d), om (u, 1) (pureA F f φ) = c • pureA F f φ :=
    ⟨(starRingEnd ℂ) (pureA F f₀ φ y) / (starRingEnd ℂ) (om (u, 1) (pureA F f₀ φ) y), fun f => funext fun x => by
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key, mul_comm]⟩
  have h5 : ∀ k : ℕ, om (u ^ k, 1) (pureA F f₀ φ) = c ^ k • pureA F f₀ φ := fun k => by
    induction k with
    | zero => rw [pow_zero, pow_zero, one_smul]; exact congrArg (· (pureA F f₀ φ)) (map_one om)
    | succ k ih =>
      rw [pow_succ, show ((u ^ k * u, 1) : UA σ X.J × UA σ W.J) = (u ^ k, 1) * (u, 1) from by simp, map_mul,
        Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ']
  have h6 : c = 1 := PositivityTheory.ThKH.Locrep.eq_one_of_pow_near fun k => by
    have := h3 hu k
    rwa [Set.mem_ofPred_eq, h5, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hy, mul_one] at this
  intro f
  rw [hc, h6, one_smul]
