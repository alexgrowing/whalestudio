import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzValuedIntegralLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableIdelesPowerDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists

open scoped TensorProduct Matrix
open MeasureTheory Filter Topology NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
  GlobalTheory.ConeSoB
open scoped Classical

noncomputable section

namespace GlobalTheory.ConeArchB

open GlobalTheory.XTermDecay GlobalTheory.HeisSchA GlobalTheory.DiffDecay GlobalTheory.EvZeroInf GlobalTheory.Published.Metaplectic

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem continuous_eval {X : Type} [TopologicalSpace X] {f : X → SInf F κ} (hf : Continuous f)
    {y : X → κ → mixedEmbedding.mixedSpace F} (hy : Continuous y) : Continuous fun x => f x (y x) := by
  have h := (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ).continuous.comp hf
  exact h.eval hy

theorem continuous_of_bound {X : Type} [TopologicalSpace X] {f : X → SInf F κ} (hp : ∀ y, Continuous fun x => f x y)
    (hb : ∀ a n : ℕ, ∃ c : X → ℝ, Continuous c ∧ ∀ x, SchwartzMap.seminorm ℂ a n (f x) ≤ c x) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x₀ => GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded f x₀
    (fun y => (hp y).continuousAt) fun a n => ?_
  obtain ⟨c, hc, hcb⟩ := hb a n
  refine ⟨c x₀ + 1, (hc.continuousAt.eventually (gt_mem_nhds (lt_add_one (c x₀)))).mono fun x hx v => ?_⟩
  exact ((SchwartzMap.le_seminorm ℂ a n (f x) v).trans (hcb x)).trans hx.le

theorem continuous_archOp {X : Type} [TopologicalSpace X] {f : X → SInf F κ} (hf : Continuous f)
    {w : X → (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)} (hw : Continuous w) :
    Continuous fun x => archOp (w x) (f x) := by
  refine continuous_of_bound (fun y => ?_) fun a n => ?_
  · have e : ∀ x, archOp (w x) (f x) y = eChar ((-trL (w x).2) y +
        -(Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (qA (⅟(2 : AF F)) * ((w x).1 ⬝ᵥ (w x).2)))) * f x (y + (w x).1) :=
      fun x => archS_apply (f x) (w x).2 (w x).1 _ y
    simp only [e, eChar_apply, ContinuousLinearMap.neg_apply, trL_apply]
    have ht := (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).continuous_of_finiteDimensional
    refine Continuous.mul (Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp ?_)).mul
      continuous_const)) (continuous_eval hf (continuous_const.add hw.fst))
    exact (ht.comp (continuous_const.dotProduct hw.snd)).neg.add
      (ht.comp (continuous_const.mul (hw.fst.dotProduct hw.snd))).neg
  · obtain ⟨q, M, hq, hb⟩ := (tame_archOp (F := F) (κ := κ)).growth (SchwartzMap.seminorm ℂ a n)
      ((schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm (a, n))
    exact ⟨fun x => (1 + ‖w x‖) ^ M * q (f x), ((continuous_const.add hw.norm).pow M).mul (hq.comp hf), fun x => hb _ _⟩

theorem continuous_of_weak {T : Type} [TopologicalSpace T] [CompactSpace T] (f : T → SInf F κ) {g : (κ → Af F) → ℂ}
    {c : κ → Af F} (hc : g c ≠ 0) (h : ∀ l ∈ (adeleClass F).adm κ, Continuous fun t => l (pureA F (f t) g)) :
    Continuous f := by
  obtain ⟨r, hr⟩ := (coeL (F := F) (κ := κ)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 DFunLike.coe_injective)
  have hr' : ∀ f, r (coeL f) = f := fun f => LinearMap.congr_fun hr f
  let β : ((κ → Af F) → ℂ) →ₗ[ℂ] ℂ := (g c)⁻¹ • LinearMap.proj c
  have hβ : β g = 1 := inv_mul_cancel₀ hc
  have hw : ∀ l : SInf F κ →L[ℂ] ℂ, Continuous fun t => l (f t) := fun l => by
    have := h (l.toLinearMap ∘ₗ r ∘ₗ coefFun β) fun g' _ => ⟨β g' • l, fun f => by
      simp only [LinearMap.comp_apply, coefFun_pureA, hr', map_smul]
      rfl⟩
    simpa only [LinearMap.comp_apply, coefFun_pureA, hr', hβ, one_smul, ContinuousLinearMap.coe_coe] using this
  refine continuous_of_bound (fun y => hw ((BoundedContinuousFunction.evalCLM ℂ y).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ))) fun a n => ?_
  obtain ⟨C, hC⟩ := bounded_of_weak f (fun l => by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hw l).continuousOn
    exact ⟨C, fun t => hC t trivial⟩) (SchwartzMap.seminorm ℂ a n) ((schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm (a, n))
  exact ⟨fun _ => C, continuous_const, hC⟩

theorem continuous_iteratedFDeriv (n : ℕ) (y : κ → mixedEmbedding.mixedSpace F) :
    Continuous fun f : SInf F κ => iteratedFDeriv ℝ n (⇑f) y := by
  refine continuous_iff_continuousAt.2 fun f₀ => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h : Continuous fun f : SInf F κ => SchwartzMap.seminorm ℂ 0 n (f - f₀) :=
    ((schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm (0, n)).comp (continuous_id.sub continuous_const)
  have h' := h.tendsto f₀
  rw [sub_self, map_zero] at h'
  refine squeeze_zero (fun _ => norm_nonneg _) (fun f => ?_) h'
  rw [← iteratedFDeriv_sub_apply ((f.smooth n).contDiffAt) ((f₀.smooth n).contDiffAt)]
  exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (f - f₀) n y

theorem secondCountable_multilinear (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (n : ℕ) :
    SecondCountableTopology (V [×n]→L[ℝ] ℂ) := by
  haveI : FiniteDimensional ℝ (V [×n]→L[ℝ] ℂ) := Module.Finite.of_injective
    (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ)) ContinuousMultilinearMap.toMultilinearMap_injective
  haveI := FiniteDimensional.proper_real (V [×n]→L[ℝ] ℂ)
  infer_instance

theorem continuous_qA : Continuous (qA (F := F)) := by
  have h : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply v.1)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply v.1)
  exact h.comp continuous_fst

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem locOpInf_rho_eq {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    (hM : M.IsGood ψ) (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) :
    M.co.rho ψ (partInf F u) (pure f M.vac) = pure (locOpInf (M.co.rho ψ (partInf F u)) f) M.vac ∧
      locOpInf (M.co.rho ψ (partInf F u)) f = archOp (archW (M.co.e (partInf F u))) f := by
  have h1 : M.co.rho ψ (partInf F u) (pure f M.vac) = pure (locOpInf (M.co.rho ψ (partInf F u)) f) M.vac :=
    (locOpInf_rho M.co hψ u f).1 _ ⟨fun x z hz => finPart_add _ x z hz,
      GlobalTheory.TensUniq.pure_mem_schA f _ (fun v => (hM.vac v).1) hM.std⟩
  refine ⟨h1, eq_of_pure_eq _ (fun v => (hM.vac v).2.1) hM.std _ _ ?_⟩
  rw [← h1]
  have h2 := schr_pureA ψ hψ (M.co.e (partInf F u)) f fun y => ∏ᶠ v, M.vac v fun i => evalV F v (y i)
  have h3 : M.co.e (partInf F u) = mk (realAd F 1).1 0 • M.co.e u := map_smul M.co.e _ _
  rw [show finOp ψ _ (M.co.e (partInf F u)) = _ from h3 ▸ finOp_arch ψ _ _ _] at h2
  exact h2

theorem exists_piInf_le (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z : AE F E, 1 + ∑ w, ‖piInf (τ w) z‖ ≤
      A * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (cA σ z) i).1 v‖) := by
  have hσ : ∀ z, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  have hc : ∀ z : AE F E, cA σ (cA σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [cA, hσ]
    | add x y hx hy => simp only [map_add, hx, hy]
  set A := ∑ i, ∑ w, ‖(τ w).1 (σ (Module.finBasis F E i))‖ with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨1 + A, by linarith, fun z => ?_⟩
  set x := GlobalTheory.XTermMaj.crd F E (cA σ z) with hx
  have hz : z = ∑ i, x i ⊗ₜ[F] σ (Module.finBasis F E i) := by
    rw [← hc z, ← (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).sum_equivFun (cA σ z), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  have h1 : ∑ w, ‖piInf (τ w) z‖ ≤ A * ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖ := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    conv_lhs => rw [hz, map_sum]
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    change ‖InfinitePlace.Completion.extensionEmbedding w ((x i).1 w) * (τ w).1 _‖ ≤ _
    rw [norm_mul, (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), mul_comm]
    gcongr
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ w, ‖(τ w).1 (σ (Module.finBasis F E i))‖)
      (fun _ _ => by positivity) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun w => ‖(τ w).1 (σ (Module.finBasis F E i))‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ w)
  have h2 : 0 ≤ ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖ := by positivity
  nlinarith

theorem shift_decay {B : Base F E} {n d n₁ d₁ r s i₀ i₁ j₀ j₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁}
    {W₁ : Spc F E d₁} {M : Model σ X W} {M₁ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} (hB : B.IsGood σ)
    (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁) (hH' : H'.IsAdapted σ B W W₁ j₀ j₁)
    (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} (he : IsEv B M M₁ H.ι H'.ι (isoB H H') e)
    {ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)} (hei : ∀ f, e (pure f M.vac) = pure (ei f) M₁.vac)
    {T : Type} (f : T → SInf F (Fin n × Fin d))
    (hf : ∀ p : Seminorm ℂ (SInf F (Fin n × Fin d)), Continuous p → ∃ C : ℝ, ∀ t, p (f t) ≤ C)
    (p : Seminorm ℂ (SInf F (Fin n₁ × Fin d₁))) (hp : Continuous p) (N : ℕ) :
    ∃ C : ℝ, ∀ t (l : (AE F E)ˣ), p (ei (locOpInf (M.co.rho B.ψ (partInf F (shiftB σ H H' l))) (f t))) ≤
      C / (1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖) ^ N := by
  have hcm := hB.cm
  have hσ : ∀ z, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  have hyx : form σ X.J H.y H.x = 1 := by
    have h1 : form σ X.J H.y H.x = σ (form σ X.J H.x H.y) := by
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hX.herm, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [h1, hH.xy, map_one]
  have hxy : form σ W.J H'.x (-H'.y) = -1 := by
    rw [← hH'.xy]
    simp only [form, dotProduct, Matrix.mulVec, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]
  obtain ⟨t, ht⟩ := GlobalTheory.T.symplectic_trace_basis_exists F E σ _ _ X.J W.J H.y H.x (-H'.y) H'.x hyx hxy
  obtain ⟨c, hc⟩ := exists_finPart_ne_zero M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std
  set g₁ : ℂ := ∏ᶠ v, M₁.vac v fun i => evalV F v (c i) with hg₁
  have hc' : g₁ ≠ 0 := hc (fun i => mk 0 (c i)) fun _ => rfl
  let S := fun j => M.co.e (inclR (F := F) (AF F) (Module.finBasis F E j) • Matrix.vecMulVec (incV F H.y) (incV F H'.x))
  let U := fun i => M.co.e (Matrix.vecMulVec (inclR (F := F) (AF F) (t i) • incV F H.x) (incV F (-H'.y)))
  have hg : (fun y : Fin n × Fin d → Af F => ∏ᶠ v, M.vac v fun i => evalV F v (y i)) ∈ SB _ :=
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV M.vac (fun v => (hM.vac v).1) hM.std,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod M.vac (fun v => (hM.vac v).1) hM.std⟩
  obtain ⟨C, hC⟩ := slice_decay B.ψ hB.std S U (fun i j => by rw [← M.co.form]; convert ht i j)
    (sliceL c ∘ₗ e) (exists_slice_clm hM he c) (fun i a Ψ hΨ => by
      have := he.inv (Matrix.vecMulVec (incV F H.x) (a • inclR (F := F) (AF F) (t i) • incV F (-H'.y)))
        (Or.inl ⟨_, rfl⟩) Ψ hΨ
      rw [Matrix.vecMulVec_smul, Matrix.vecMulVec_smul, ← Matrix.smul_vecMulVec _ (incV F H.x), Darboux.rho, map_smul] at this
      exact congrArg (sliceL c) this) hg f hf (isCompact_singleton (x := 0)) p hp N
  obtain ⟨A, hA0, hA⟩ := exists_piInf_le hcm B.emb
  refine ⟨‖g₁‖⁻¹ * (|C| * A ^ N), fun k l => ?_⟩
  set x := GlobalTheory.XTermMaj.crd F E (cA σ (l : AE F E)) with hx
  have hx1 : ∀ i, (realAd F 1 * x i).1 = (x i).1 := fun i => by
    have h1 : (realAd F 1).1 = 1 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by
      rw [map_one]; exact evI_realAd_one)
    change (realAd F 1).1 * (x i).1 = _
    rw [h1, one_mul]
  obtain ⟨f₁, hf₁, hb⟩ := hC k (fun i => realAd F 1 * x i) (funext fun i => show (0 : Af F) * (x i).2 = 0 from zero_mul _)
  have hS : M.co.e (partInf F (shiftB σ H H' l)) = ∑ i, (realAd F 1 * x i) • S i := by
    simp only [S, mul_smul, ← Finset.smul_sum, ← map_smul, ← map_sum, ← smul_assoc (x _), ← Finset.sum_smul]
    rw [partInf, shiftB]
    congr 3
    refine ((Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).sum_equivFun (cA σ (l : AE F E))).symm.trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  set h := ei (locOpInf (M.co.rho B.ψ (partInf F (shiftB σ H H' l))) (f k)) with hh
  have e1 : f₁ = g₁ • h := by
    refine DFunLike.coe_injective (hf₁.trans ?_)
    rw [← hS]
    change sliceL c (e (M.co.rho B.ψ (partInf F (shiftB σ H H' l)) (pure (f k) M.vac))) = _
    rw [(locOpInf_rho_eq hB.std hM _ _).1, hei]
    funext y
    change h (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i))) * g₁ = g₁ * h y
    simp only [RingEquiv.apply_symm_apply, mul_comm]
  simp only [hx1] at hb
  set R := 1 + ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖ with hR
  set P := 1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖ with hP
  have hR0 : 0 < R := by positivity
  have hP0 : 0 < P := by positivity
  have hPR : P ^ N ≤ A ^ N * R ^ N := by rw [← mul_pow]; exact pow_le_pow_left₀ hP0.le (hA _) N
  rw [e1, map_smul_eq_mul, Real.rpow_neg hR0.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)] at hb
  rw [le_div_iff₀ (by positivity), le_inv_mul_iff₀ (norm_pos_iff.2 hc')]
  have hp0 := apply_nonneg p h
  calc ‖g₁‖ * (p h * P ^ N) ≤ ‖g₁‖ * (p h * (A ^ N * R ^ N)) := by gcongr
    _ = ‖g₁‖ * p h * R ^ N * A ^ N := by ring
    _ ≤ _ := by gcongr; exact hb.trans (le_abs_self C)

theorem coneInfFun_schwartz : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)), IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (μKi : Measure (KAt K (evI F))) (μi : Measure (idelesAt E (evI F))), IsNormK K (evI F) μKi → μi.IsHaarMeasure →
    ∀ f : SInf F (Fin (b + 2) × Fin (a + (b + 2))), ∃ g : SInf F (Fin b × Fin (a + b)),
      ⇑g = coneInfFun B G.M' om' ei K μKi μi (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) f := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he K hK X om om' om₁ om₁' hT hT₁ ei ev _ hev hloc μK μ hμK hμ f
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  haveI : IsFiniteMeasure μK := ⟨by rw [hμK.2]; exact ENNReal.one_lt_top⟩
  haveI := hμ
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have hM := hT.geo.hM'
  have hψ := hT.base.std
  have hKc : IsCompact (K : Set (UA σ G.V'.J)) := by
    obtain ⟨K', _, _, hK', hc, -, -⟩ := GlobalTheory.StabHaar.stabEx hP F E σ B _ G.V' _ _ hT.base hT.geo.hV'
    rwa [show K = K' from Subgroup.ext fun g => (hK g).trans (hK' g).symm]
  haveI : CompactSpace (KAt K (evI F)) := isCompact_iff_compactSpace.1 (isCompact_KAt hKc _)
  have hSB : ∀ v, G.M'.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hpure : pure f G.M'.vac ∈ schA F _ := GlobalTheory.TensUniq.pure_mem_schA f _ hSB hM.std
  have hei : ∀ f, e' (pure f G.M'.vac) = pure (ei f) G₁.M'.vac := fun f => by
    rw [hloc f _ hSB (Eventually.of_forall fun _ => rfl)]
    exact congrArg _ (funext fun v => (hev v).1)
  set Φ : KAt K (evI F) → SInf F (Fin (b + 2) × Fin (a + (b + 2))) := fun k => locOpInf (om' (k.1, 1)) f with hΦ
  have hΦc : Continuous Φ := by
    obtain ⟨c, hc⟩ := exists_finPart_ne_zero G.M'.vac (fun v => (hM.vac v).2.1) hM.std
    refine continuous_of_weak Φ (g := fun y => ∏ᶠ v, G.M'.vac v fun i => evalV F v (y i)) (c := c)
      (hc (fun i => mk 0 (c i)) fun _ => rfl) fun l hl => ?_
    have hw : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co X.α (X.α / X.β) om' :=
      hT.weil'
    refine ((hw.2.2 l hl _ hpure).comp
      (continuous_subtype_val.prodMk continuous_const : Continuous fun k : KAt K (evI F) => (k.1, (1 : UA σ G.W.J)))).congr
      fun k => congrArg l ?_
    exact acts_locOpInf (GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ _ _ _ _ G.M' B.ψ _ _ om' hT.base.cm hψ hT.weil' k.1 k.2.2 f)
      _ ⟨fun x z hz => finPart_add _ x z hz, hpure⟩
  set z := (a - (b + 2)) / 2 + 1 with hz
  have hI : Continuous fun q : KAt K (evI F) × idelesAt E (evI F) =>
      coneInfInt B G.M' om' ei (shiftB σ H H') X.ν z f q.1.1 q.2.1 := by
    have hl : Continuous fun q : KAt K (evI F) × idelesAt E (evI F) => q.2.1 := continuous_subtype_val.comp continuous_snd
    have hν : Continuous X.ν := hT.chars.heckeα.1.div' hT.chars.heckeβ.1
    simp only [coneInfInt, (locOpInf_rho_eq hψ hM _ _).2]
    refine (((continuous_subtype_val.comp hν).comp hl).mul ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
      (GlobalTheory.Doubling.continuous_absE.comp hl))).pow z)).smul (ei.continuous.comp (continuous_archOp (hΦc.comp continuous_fst) ?_))
    let L := G.M'.co.e.toLinearMap ∘ₗ (realAd F 1 • ((LinearMap.toSpanSingleton (AE F E) _
      (Matrix.vecMulVec (incV F H.y) (incV F H'.x))).restrictScalars (AF F) ∘ₗ (cA σ).toLinearMap))
    have hL : Continuous fun q : KAt K (evI F) × idelesAt E (evI F) => G.M'.co.e (partInf F (shiftB σ H H' q.2.1)) :=
      (IsModuleTopology.continuous_of_linearMap L).comp (Units.continuous_val.comp hl)
    exact (continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp hL.fst)).prodMk
      (continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp hL.snd))
  obtain ⟨N, hN⟩ := GlobalTheory.T.integrable_ideles_power_decay F E σ B hT.base μ hμ z (by omega)
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F Unit
  obtain ⟨T, hTf⟩ := GlobalTheory.ParamSchwartz.iteratedIntegral_clm μK μ
    (fun (h : SInf F Unit) k l => h 0 • coneInfInt B G.M' om' ei (shiftB σ H H') X.ν z f k.1 l.1)
    (fun a b h h' k l => by
      simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, add_smul, smul_smul, smul_eq_mul])
    (fun h n y => by
      haveI := secondCountable_multilinear (Fin b × Fin (a + b) → mixedEmbedding.mixedSpace F) n
      haveI := secondCountableTopologyEither_of_right (KAt K (evI F) × idelesAt E (evI F))
        ((Fin b × Fin (a + b) → mixedEmbedding.mixedSpace F) [×n]→L[ℝ] ℂ)
      exact ((continuous_iteratedFDeriv n y).comp (hI.const_smul (h 0))).stronglyMeasurable)
    (fun a' n => by
      obtain ⟨C, hCb⟩ := shift_decay hT.base hT.geo.hV' hC.hH hC.hH' hM hT₁.geo.hM' he hei Φ
        (fun p hp => by
          obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hp.comp hΦc).continuousOn
          exact ⟨C, fun t => (le_abs_self _).trans (hC t trivial)⟩)
        (SchwartzMap.seminorm ℂ a' n) ((schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm (a', n)) N
      refine ⟨{(0, 0)}, C, _, hN, fun h k l => ?_⟩
      have h0 : ‖h 0‖ ≤ SchwartzMap.seminorm ℂ 0 0 h := SchwartzMap.norm_le_seminorm ℂ h 0
      have h1 := hCb k l.1
      rw [Finset.sup_singleton, map_smul_eq_mul, coneInfInt, map_smul_eq_mul, norm_mul, Circle.norm_coe, one_mul, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq, mul_comm, mul_div_left_comm]
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h0 (norm_nonneg _)
        (mul_nonneg (by positivity) ((apply_nonneg _ _).trans h1)))
  refine ⟨T ((f₀ 0)⁻¹ • f₀), (hTf _).trans ?_⟩
  simp only [SchwartzMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₀, one_smul]
  rfl

end GlobalTheory.ConeArchB

end
