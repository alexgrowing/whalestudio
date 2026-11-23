import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerGlobalEval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableIdelesPowerDecay

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ConeArchA

open GlobalTheory.XTermDecay GlobalTheory.HeisSchA GlobalTheory.DiffDecay GlobalTheory.EvZeroInf GlobalTheory.Published.Metaplectic GlobalTheory.ConeArchB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_piInf_le_crd (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z : AE F E, 1 + ∑ w, ‖piInf (τ w) z‖ ≤
      A * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E z i).1 v‖) := by
  set A := ∑ i, ∑ w, ‖(τ w).1 (Module.finBasis F E i)‖ with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨1 + A, by linarith, fun z => ?_⟩
  set x := GlobalTheory.XTermMaj.crd F E z with hx
  have hz : z = ∑ i, x i ⊗ₜ[F] Module.finBasis F E i := by
    rw [← (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).sum_equivFun z]
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
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ w, ‖(τ w).1 (Module.finBasis F E i)‖)
      (fun _ _ => by positivity) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun w => ‖(τ w).1 (Module.finBasis F E i)‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ w)
  have h2 : 0 ≤ ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖ := by positivity
  nlinarith

theorem shift_decay {B : Base F E} {b a' : ℕ} {G : Geo σ (b + 2) a'} {G₁ : Geo σ b a'}
    {H : Plane E (b + 2) b} {H' : Plane E (b + 2 + a') (b + a')} (hC : CfgA B G G₁ H H')
    (hB : B.IsGood σ) (hG : G.IsGood B) (hG₁ : G₁.IsGood B)
    {e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')} (he : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e)
    {ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a'))}
    (hei : ∀ f, e (pure f G.M.vac) = pure (ei f) G₁.M.vac)
    {T : Type} (f : T → SInf F (Fin (b + 2) × Fin (b + 2 + a')))
    (hf : ∀ p : Seminorm ℂ (SInf F (Fin (b + 2) × Fin (b + 2 + a'))), Continuous p → ∃ C : ℝ, ∀ t, p (f t) ≤ C)
    (p : Seminorm ℂ (SInf F (Fin b × Fin (b + a')))) (hp : Continuous p) (N : ℕ) :
    ∃ C : ℝ, ∀ t (l : (AE F E)ˣ), p (ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) (f t))) ≤
      C / (1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖) ^ N := by
  have hM := hG.hM
  have hM₁ := hG₁.hM
  obtain ⟨t, ht⟩ := GlobalTheory.T.symplectic_trace_basis_exists F E σ _ _ G.V.J G.W.J H.x H.y H'.x H'.y hC.hH.xy (by
    rw [form_swap hB.cm hG.hW.skew, hC.hH'.xy, map_one])
  obtain ⟨c, hc⟩ := exists_finPart_ne_zero G₁.M.vac (fun v => (hM₁.vac v).2.1) hM₁.std
  set g₁ : ℂ := ∏ᶠ v, G₁.M.vac v fun i => evalV F v (c i) with hg₁
  have hc' : g₁ ≠ 0 := hc (fun i => mk 0 (c i)) fun _ => rfl
  let S := fun j => G.M.co.e (inclR (F := F) (AF F) (Module.finBasis F E j) • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
  let U := fun i => G.M.co.e (Matrix.vecMulVec (inclR (F := F) (AF F) (t i) • incV F H.y) (incV F H'.x))
  have hg : (fun y : Fin (b + 2) × Fin (b + 2 + a') → Af F => ∏ᶠ v, G.M.vac v fun i => evalV F v (y i)) ∈ SB _ :=
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV G.M.vac (fun v => (hM.vac v).1) hM.std,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod G.M.vac (fun v => (hM.vac v).1) hM.std⟩
  obtain ⟨C, hCb⟩ := slice_decay B.ψ hB.std S U (fun i j => by rw [← G.M.co.form]; convert ht i j)
    (sliceL c ∘ₗ e) (exists_slice_clm hM he c) (fun i a Ψ hΨ => by
      have := he.inv (Matrix.vecMulVec (a • inclR (F := F) (AF F) (t i) • incV F H.y) (incV F H'.x)) (Or.inl ⟨_, rfl⟩) Ψ hΨ
      rw [Matrix.smul_vecMulVec, Darboux.rho, map_smul] at this
      exact congrArg (sliceL c) this) hg f hf (isCompact_singleton (x := 0)) p hp N
  obtain ⟨A, hA0, hA⟩ := exists_piInf_le_crd (E := E) B.emb
  refine ⟨‖g₁‖⁻¹ * (|C| * A ^ N), fun k l => ?_⟩
  set x := GlobalTheory.XTermMaj.crd F E (l : AE F E) with hx
  have hx1 : ∀ i, (realAd F 1 * x i).1 = (x i).1 := fun i => by
    have h1 : (realAd F 1).1 = 1 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by
      rw [map_one]; exact evI_realAd_one)
    change (realAd F 1).1 * (x i).1 = _
    rw [h1, one_mul]
  obtain ⟨f₁, hf₁, hb⟩ := hCb k (fun i => realAd F 1 * x i) (funext fun i => show (0 : Af F) * (x i).2 = 0 from zero_mul _)
  have hS : G.M.co.e (partInf F (shiftA H H' l)) = ∑ i, (realAd F 1 * x i) • S i := by
    simp only [S, mul_smul, ← Finset.smul_sum, ← map_smul, ← map_sum, ← smul_assoc (x _), ← Finset.sum_smul]
    rw [partInf, shiftA]
    congr 3
    refine ((Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).sum_equivFun (l : AE F E)).symm.trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  set h := ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) (f k)) with hh
  have e1 : f₁ = g₁ • h := by
    refine DFunLike.coe_injective (hf₁.trans ?_)
    rw [← hS]
    change sliceL c (e (G.M.co.rho B.ψ (partInf F (shiftA H H' l)) (pure (f k) G.M.vac))) = _
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

theorem integrable_cone : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))),
    μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ l : SInf F (Fin b × Fin (b + a')) →L[ℂ] ℂ,
    ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
      Integrable (fun p : KAt K (evI F) × idelesAt E (evI F) =>
        l (coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f p.1.1 p.2.1)) (μK.prod μ) := by
  intro hP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he ei ev hloc X om om' om₁ om₁' hT hT₁ K hK μK μ hμK hμ l f
  obtain ⟨-, hev, hloc⟩ := hloc
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  haveI := hμ
  haveI := hμK
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have hM := hT.geo.hM
  have hψ := hT.base.std
  have hKc : IsCompact (K : Set (UA σ G.V.J)) := by
    obtain ⟨K', _, _, hK', hc, -, -⟩ := GlobalTheory.StabHaar.stabEx hP F E σ B _ G.V _ _ hT.base hT.geo.hV
    rwa [show K = K' from Subgroup.ext fun g => (hK g).trans (hK' g).symm]
  haveI : CompactSpace (KAt K (evI F)) := isCompact_iff_compactSpace.1 (isCompact_KAt hKc _)
  haveI : IsFiniteMeasure μK := ⟨isCompact_univ.measure_lt_top⟩
  have hSB : ∀ v, G.M.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hpure : pure f G.M.vac ∈ schA F _ := GlobalTheory.TensUniq.pure_mem_schA f _ hSB hM.std
  have hei : ∀ f, e (pure f G.M.vac) = pure (ei f) G₁.M.vac := fun f => by
    rw [hloc f _ hSB (Eventually.of_forall fun _ => rfl)]
    exact congrArg _ (funext fun v => (hev v).1)
  set Φ : KAt K (evI F) → SInf F (Fin (b + 2) × Fin (b + 2 + a')) := fun k => locOpInf (om (k.1, 1)) f with hΦ
  have hΦc : Continuous Φ := by
    obtain ⟨c, hc⟩ := exists_finPart_ne_zero G.M.vac (fun v => (hM.vac v).2.1) hM.std
    refine continuous_of_weak Φ (g := fun y => ∏ᶠ v, G.M.vac v fun i => evalV F v (y i)) (c := c)
      (hc (fun i => mk 0 (c i)) fun _ => rfl) fun l hl => ?_
    have hw : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om :=
      hT.weil
    refine ((hw.2.2 l hl _ hpure).comp
      (continuous_subtype_val.prodMk continuous_const : Continuous fun k : KAt K (evI F) => (k.1, (1 : UA σ G.W.J)))).congr
      fun k => congrArg l ?_
    exact acts_locOpInf (GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ _ _ _ _ G.M B.ψ _ _ om hT.base.cm hψ hT.weil k.1 k.2.2 f)
      _ ⟨fun x z hz => finPart_add _ x z hz, hpure⟩
  set z := (b + 2 - a') / 2 with hz
  have hz1 : 1 ≤ z := by
    have := hT.geo.eBig
    omega
  have hI : Continuous fun q : KAt K (evI F) × idelesAt E (evI F) =>
      coneInfInt B G.M om ei (shiftA H H') X.ν z f q.1.1 q.2.1 := by
    have hl : Continuous fun q : KAt K (evI F) × idelesAt E (evI F) => q.2.1 := continuous_subtype_val.comp continuous_snd
    have hν : Continuous X.ν := hT.chars.heckeα.1.div' hT.chars.heckeβ.1
    simp only [coneInfInt, (locOpInf_rho_eq hψ hM _ _).2]
    refine (((continuous_subtype_val.comp hν).comp hl).mul ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
      (GlobalTheory.Doubling.continuous_absE.comp hl))).pow z)).smul (ei.continuous.comp (continuous_archOp (hΦc.comp continuous_fst) ?_))
    let L := G.M.co.e.toLinearMap ∘ₗ (realAd F 1 • ((LinearMap.toSpanSingleton (AE F E) _
      (Matrix.vecMulVec (incV F H.x) (incV F H'.y))).restrictScalars (AF F)))
    have hL : Continuous fun q : KAt K (evI F) × idelesAt E (evI F) => G.M.co.e (partInf F (shiftA H H' q.2.1)) :=
      (IsModuleTopology.continuous_of_linearMap L).comp (Units.continuous_val.comp hl)
    exact (continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp hL.fst)).prodMk
      (continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp hL.snd))
  obtain ⟨N, hN⟩ := GlobalTheory.ArchIdeleDecay.integrable_absE_pow_div F E σ B hT.base μ hμ z hz1
  obtain ⟨C, hCb⟩ := shift_decay hC hT.base hT.geo hT₁.geo he hei Φ
    (fun p hp => by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hp.comp hΦc).continuousOn
      exact ⟨C, fun t => (le_abs_self _).trans (hC t trivial)⟩)
    ((normSeminorm ℂ ℂ).comp (l : SInf F (Fin b × Fin (b + a')) →ₗ[ℂ] ℂ)) (continuous_norm.comp l.continuous) N
  refine Integrable.mono' ((integrable_const C).mul_prod hN) (l.continuous.comp hI).aestronglyMeasurable
    (Eventually.of_forall fun q => ?_)
  have h1 : ‖l (ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' q.2.1))) (Φ q.1)))‖ ≤ _ := hCb q.1 q.2.1
  rw [coneInfInt, map_smul, smul_eq_mul, norm_mul, norm_mul, Circle.norm_coe, one_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq, mul_div_left_comm]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

end GlobalTheory.ConeArchA

end
