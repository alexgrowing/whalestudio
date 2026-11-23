import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HodgeTateFromSandwich
import Development.WeilBound.ThetaLifts.LatticeBasics.RealInvL
import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SchwartzLogDerivLinearGaussian
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfForallNhds

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal ENNReal Matrix Classical SchwartzMap
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace Dense

theorem exists_fixed {S H P : Type} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [AddCommGroup P] [Module ℂ P] (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι) (p : S →ₗ[ℂ] P) (N : Submodule ℂ S)
    [FiniteDimensional ℂ N] {f : S} (hf : f ∈ N) (hp : p f ≠ 0) :
    ∃ f₀ ∈ N, f₀ ≠ 0 ∧ ∀ g ∈ N, p g = p f₀ → ‖ι g‖ = ‖ι f₀‖ → g = f₀ := by
  let Z := (N ⊓ LinearMap.ker p).map ι
  haveI : FiniteDimensional ℂ (N ⊓ LinearMap.ker p : Submodule ℂ S) := Submodule.finiteDimensional_of_le inf_le_left
  haveI : CompleteSpace Z := FiniteDimensional.complete ℂ Z
  obtain ⟨_, ⟨z, hz, rfl⟩, y, hy, e⟩ := Z.exists_add_mem_mem_orthogonal (ι f)
  have e' : ι (f - z) = y := by rw [map_sub, e, add_sub_cancel_left]
  refine ⟨f - z, sub_mem hf hz.1, fun h => hp ?_, fun g hg h1 h2 => ?_⟩
  · rw [sub_eq_zero.1 h]
    exact hz.2
  · have hm : ι (g - (f - z)) ∈ Z := ⟨_, ⟨sub_mem hg (sub_mem hf hz.1), by simp [h1]⟩, rfl⟩
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (hy _ hm)
    rw [← e', ← map_add, sub_add_cancel, h2, right_eq_add, mul_self_eq_zero, norm_eq_zero] at this
    exact sub_eq_zero.1 (hι (this.trans (map_zero ι).symm))

def dopL {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (L : V →L[ℝ] ℝ) : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ) where
  toFun := dop a L
  map_add' f g := by
    ext x
    simp only [dop_apply, SchwartzMap.add_apply]
    rw [show ⇑(f + g) = ⇑f + ⇑g from rfl, fderiv_add f.differentiableAt g.differentiableAt, ContinuousLinearMap.add_apply]
    ring
  map_smul' c f := by
    ext x
    simp only [dop_apply, SchwartzMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [show ⇑(c • f) = c • ⇑f from rfl, fderiv_const_smul f.differentiableAt, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

theorem exists_dop_fin {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (N : Submodule ℂ 𝓢(V, ℂ))
    [FiniteDimensional ℂ N] : ∃ N' : Submodule ℂ 𝓢(V, ℂ), FiniteDimensional ℂ N' ∧ ∀ a L, ∀ f ∈ N, dop a L f ∈ N' := by
  let b := Module.finBasis ℝ (V × (V →L[ℝ] ℝ))
  refine ⟨⨆ i, N.map (dopL (b i).1 (b i).2), inferInstance, fun a L f hf => ?_⟩
  have : ∀ q ∈ Submodule.span ℝ (Set.range b), dop q.1 q.2 f ∈ ⨆ i, N.map (dopL (b i).1 (b i).2) := fun q hq => by
    induction hq using Submodule.span_induction with
    | mem q h => obtain ⟨i, rfl⟩ := h; exact Submodule.mem_iSup_of_mem i ⟨f, hf, rfl⟩
    | zero => convert Submodule.zero_mem _; ext x; simp [dop_apply]
    | add x y _ _ hx hy => rw [Prod.fst_add, Prod.snd_add, dop_add]; exact add_mem hx hy
    | smul t q _ h =>
      convert Submodule.smul_mem _ (t : ℂ) h
      ext x
      simp only [dop_apply, Prod.smul_fst, Prod.smul_snd, map_smul, ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply,
        smul_eq_mul, Complex.real_smul]
      push_cast
      ring
  exact this (a, L) (b.span_eq ▸ trivial)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def vacSp (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (ε : InfinitePlace F → ℤˣ) :
    Submodule ℂ (SInf F (Fin n × Fin d)) where
  carrier := {f | ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
    (∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ)) →
    dopL (aOf M u') (lOf M u') f = Complex.I • dopL (aOf M u) (lOf M u) f}
  zero_mem' _ _ _ _ _ := by simp
  add_mem' hf hg u u' h1 h2 h3 := by rw [map_add, map_add, hf u u' h1 h2 h3, hg u u' h1 h2 h3, smul_add]
  smul_mem' c f hf u u' h1 h2 h3 := by rw [map_smul, map_smul, hf u u' h1 h2 h3, smul_comm]

theorem vacSp_fin (h : IsCMExt F E σ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (ε : InfinitePlace F → ℤˣ) :
    FiniteDimensional ℂ (vacSp M τ ε) := by
  let ev : SInf F (Fin n × Fin d) →L[ℂ] ℂ :=
    BoundedContinuousFunction.evalCLM ℂ 0 ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ
  refine FiniteDimensional.of_injective (ev.toLinearMap ∘ₗ (vacSp M τ ε).subtype)
    ((injective_iff_map_eq_zero _).2 fun f h0 => Subtype.ext ?_)
  by_contra hf
  let C : InfinitePlace F → Matrix (Fin n) (Fin d) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin d) ℂ := fun w =>
    { toFun := fun x => (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * x * (W.θ w)ᵀ)
      map_add' := fun x y => by rw [Matrix.mul_add, Matrix.add_mul, smul_add]
      map_smul' := fun t x => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
        rw [smul_comm] }
  obtain ⟨S, J, sAt, sev, sJ⟩ := exists_real_structure σ h τ M.co.e C
  let T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun y b => linForm b y) (fun y y' b => map_add _ y y') (fun t y b => map_smul _ t y)
      (fun y b b' => by simp only [linForm_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add])
      (fun t y b => by simp only [linForm_apply, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul])
  obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.Twist.FockLogDeriv.main T (fun b hb => funext fun i => trace_mul_eq_zero _ fun y => by
      have : linForm b (Pi.single i y) = 0 := hb _
      rw [linForm_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, mul_comm] at this
      exact this) J f.1 hf fun p y => by
    have := congrArg (fun g : SInf F (Fin n × Fin d) => g y) (f.2 (S p) (S (J p)) (sAt _) (sAt _) fun w => sJ p w)
    simp only [dopL, LinearMap.coe_mk, AddHom.coe_mk, SchwartzMap.smul_apply, smul_eq_mul, dop_apply, aOf, lOf] at this
    rw [show aOf M (S p) = p.1 from (sev _).1, show aOf M (S (J p)) = (J p).1 from (sev _).1, (sev _).2, (sev _).2] at this
    exact this
  obtain ⟨c, Q, Q', hc, -, e⟩ := GlobalTheory.CompanionTheory.Twist.schwartz_logDeriv_linear_gaussian f.1 hf m hm
  have : f.1 0 = 0 := h0
  rw [e] at this
  exact mul_ne_zero hc (Complex.exp_ne_zero _) this

variable {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W}

theorem vacSp_map (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om)
    {τ : ∀ w : InfinitePlace F, EmbOver E w} {k : UA σ X.J} (hk : k ∈ KInf σ X τ) {A} (hA : Impl om (k, 1) A) {ε f}
    (hf : f ∈ vacSp M τ ε) : A f ∈ vacSp M τ ε := by
  intro u u' hu hu' hrel
  have e0 : ∀ g v, actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) v = mat g * v := fun g v => by simp [actAB, mat]
  have e1 : mat k * mat k⁻¹ = 1 := by show k.1.1 * ((k⁻¹ : UA σ X.J).1.1) = 1; simp
  have e2 : mat k⁻¹ * mat k = 1 := by show ((k⁻¹ : UA σ X.J).1.1) * k.1.1 = 1; simp
  have a1 := at_act (W := W) (k⁻¹, 1) hu
  have a2 := at_act (W := W) (k⁻¹, 1) hu'
  have i1 := inter hψ hs hA a1 f
  have i2 := inter hψ hs hA a2 f
  simp only [e0, ← Matrix.mul_assoc, e1, Matrix.one_mul] at i1 i2 a1 a2
  have := hf _ _ a1 a2 fun w => by
    have h1 : (mat k⁻¹).map (piInf (τ w)) * (mat k).map (piInf (τ w)) = 1 := by
      rw [← Matrix.map_mul, e2, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : (mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w)) = 1 := by
      rw [← Matrix.map_mul, e1, Matrix.map_one _ (map_zero _) (map_one _)]
    have hc : (mat k⁻¹).map (piInf (τ w)) * X.θ w = X.θ w * (mat k⁻¹).map (piInf (τ w)) := by
      rw [← Matrix.one_mul (X.θ w * _), ← h1, Matrix.mul_assoc, ← Matrix.mul_assoc _ (X.θ w), (hk.2 w).eq, Matrix.mul_assoc,
        h2, Matrix.mul_one]
    rw [Matrix.map_mul, Matrix.map_mul, hrel w, Matrix.mul_smul]
    simp only [← Matrix.mul_assoc, hc]
  change dop _ _ _ = Complex.I • dop _ _ _ at this ⊢
  rw [← i1, ← i2, this, map_smul]

theorem pol_finite (h : IsCMExt F E σ) (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) {f} (hf : f ∈ M.Pol ψ τ) :
    ∃ N : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ N ∧ f ∈ N ∧
      ∀ k ∈ KInf σ X τ, ∀ A, Impl om (k, 1) A → ∀ g ∈ N, A g ∈ N := by
  let S : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {f | ∃ N : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ N ∧ f ∈ N ∧
        ∀ k ∈ KInf σ X τ, ∀ A, Impl om (k, 1) A → ∀ g ∈ N, A g ∈ N}
      zero_mem' := ⟨⊥, inferInstance, zero_mem _, fun k _ A _ g hg => by rw [(Submodule.mem_bot ℂ).1 hg, map_zero]; exact zero_mem _⟩
      add_mem' := by
        rintro f g ⟨N, _, h1, h2⟩ ⟨N', _, h1', h2'⟩
        refine ⟨N ⊔ N', inferInstance, Submodule.add_mem_sup h1 h1', fun k hk A hA g hg => ?_⟩
        obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hg
        rw [map_add]
        exact Submodule.add_mem_sup (h2 k hk A hA x hx) (h2' k hk A hA y hy)
      smul_mem' := fun c f ⟨N, h0, h1, h2⟩ => ⟨N, h0, N.smul_mem c h1, h2⟩ }
  refine (sInf_le (a := S) ⟨fun f₀ ⟨ε, hε⟩ => ?_, fun u hu g ⟨N, h0, h1, h2⟩ g₁ hg => ?_⟩ : M.Pol ψ τ ≤ S) hf
  · exact ⟨vacSp M τ ε, vacSp_fin h M τ ε, fun u u' hu hu' e => hε u u' hu hu' e _ _ (actsD_dop M hψ hu f₀)
      (actsD_dop M hψ hu' f₀), fun k hk A hA g hg => vacSp_map hψ hs hk hA hg⟩
  · obtain ⟨N', h3, h4⟩ := exists_dop_fin N
    refine ⟨Submodule.span ℂ {z | ∃ v, At (evI F) v ∧ ∃ x ∈ N, z = dop (aOf M v) (lOf M v) x},
      Submodule.finiteDimensional_of_le (S₂ := N') (Submodule.span_le.2 ?_),
      Submodule.subset_span ⟨u, hu, g, h1, actsD_unique' M hψ hu hg⟩, fun k hk A hA z hz => ?_⟩
    · rintro _ ⟨v, -, x, hx, rfl⟩
      exact h4 _ _ x hx
    · refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap A.toLinearMap (Submodule.span ℂ
        {z | ∃ v, At (evI F) v ∧ ∃ x ∈ N, z = dop (aOf M v) (lOf M v) x}))).2 ?_ hz)
      rintro _ ⟨v, hv, x, hx, rfl⟩
      exact Submodule.subset_span ⟨_, at_act _ hv, _, h2 k hk A hA x hx, inter hψ hs hA hv x⟩

end Dense

theorem realInv_of (hA : PositivityTheory.ThKF.ArchOp) : RealInv := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp _ P _ _ _ p hq
  obtain ⟨f, hf, h0⟩ : ∃ f ∈ M.Pol B.ψ B.emb, p f ≠ 0 := by
    obtain ⟨y, hy⟩ := exists_ne (0 : P)
    obtain ⟨f, hf, rfl⟩ : y ∈ (M.Pol B.ψ B.emb).map p := hq.onto ▸ trivial
    exact ⟨f, hf, hy⟩
  have hs := hp.weil.isUSplitting
  obtain ⟨N, _, h1, h2⟩ := Dense.pol_finite hp.base.cm hp.base.std hs.toIsSplitting B.emb hf
  haveI : FiniteDimensional ℂ (N ⊓ M.Pol B.ψ B.emb : Submodule ℂ _) := Submodule.finiteDimensional_of_le inf_le_left
  haveI := Dense.volume_isAddHaar F (Fin n × Fin d)
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  obtain ⟨f₀, hf₀, hne, hfix⟩ := Dense.exists_fixed
    (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F))).toLinearMap
    (SchwartzMap.injective_toLp 2 _) p (N ⊓ M.Pol B.ψ B.emb) ⟨h1, hf⟩ h0
  refine ⟨f₀, hf₀.2, hne, fun k hk => ?_⟩
  have h1W : (1 : UA σ W.J) ∈ UAt σ W (evI F) := fun u _ => by simp [mat]
  obtain ⟨T, hT, hP⟩ := hA F E σ B n d X W M χX χW om r s r' s' hp k hk.1 1 h1W
  have hP' := hP hk ⟨h1W, fun w => by simp [mat]⟩
  have hn := Dense.lintegral_eq (S := om (k, 1)) (fun μ hμ => hs.unit μ hμ (k, 1)) (hT.1 f₀)
  have := hfix (T f₀) ⟨h2 k hk T hT.1 _ hf₀.1, hP' _ hf₀.2⟩ (hq.cpt k hk f₀ hf₀.2 _ (hT.2 f₀)) (by
    change ‖(T f₀).toLp 2 _‖ = ‖f₀.toLp 2 _‖
    simp only [SchwartzMap.norm_toLp, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofNat, ENNReal.rpow_two, hn])
  simpa only [this] using hT.2 f₀

end GlobalTheory.ThK.Dbl

end
