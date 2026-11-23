import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingModelsCompatibleEval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerActionLocallyConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelePowerIntegrableCompactStatement

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

noncomputable section

namespace GlobalTheory.ThK.ConeLocInt

theorem integrable_integral_map_prod {α β α' β' : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace α']
    [MeasurableSpace β'] {i : α' → α} {j : β' → β} (hi : MeasurableEmbedding i) (hj : MeasurableEmbedding j)
    (μ : Measure α') (ν : Measure β') [SFinite μ] [SFinite ν] (f : α → β → ℂ)
    (hf : Integrable (fun q : α' × β' => f (i q.1) (j q.2)) (μ.prod ν)) :
    Integrable (fun q : α × β => f q.1 q.2) ((μ.map i).prod (ν.map j)) ∧
      ∫ q : α × β, f q.1 q.2 ∂((μ.map i).prod (ν.map j)) = ∫ a, ∫ b, f (i a) (j b) ∂ν ∂μ := by
  rw [Measure.map_prod_map _ _ hi.measurable hj.measurable, (hi.prodMap hj).integrable_map_iff, (hi.prodMap hj).integral_map]
  exact ⟨hf, integral_prod _ hf⟩

theorem integrable_prod_of_locallyConstant {α β γ : Type} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [SFinite ν]
    {p : α → γ} (hp : IsLocallyConstant p) (f : γ → β → ℂ) (hf : ∀ k, Integrable (f (p k)) ν) :
    Integrable (fun q : α × β => f (p q.1) q.2) (μ.prod ν) := by
  classical
  have e : (fun q : α × β => f (p q.1) q.2) = fun q => ∑ c ∈ hp.range_finite.toFinset,
      ({k | p k = c}.indicator (fun _ => (1 : ℂ)) q.1) * f c q.2 := by
    funext q
    rw [Finset.sum_eq_single (p q.1)]
    · simp
    · intro c _ hc
      rw [Set.indicator_of_notMem (by simpa using hc.symm), zero_mul]
    · intro h
      exact absurd (hp.range_finite.mem_toFinset.2 ⟨q.1, rfl⟩) h
  rw [e]
  refine integrable_finsetSum _ fun c hc => ?_
  obtain ⟨k, rfl⟩ := hp.range_finite.mem_toFinset.1 hc
  exact ((integrable_const _).indicator (hp.isOpen_fiber _).measurableSet).mul_prod (hf k)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_compact_of_annih (v : Pl F) (χ : AddChar (Fv F v) ℂ) (hχ : χ ≠ 1) {V : Set (Fv F v)} (hV : V ∈ 𝓝 0) :
    ∃ U : Set (Fv F v), IsCompact U ∧ ∀ t, (∀ a ∈ V, χ (a * t) = 1) → t ∈ U := by
  haveI : ProperSpace (Fv F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.1 hχ
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨Metric.closedBall 0 (‖x‖ / ε), isCompact_closedBall _ _, fun t ht => ?_⟩
  by_contra h
  rw [mem_closedBall_zero_iff, not_le] at h
  have hp : 0 < ‖t‖ := lt_of_le_of_lt (by positivity) h
  have ht0 : t ≠ 0 := norm_pos_iff.1 hp
  refine hx ?_
  have := ht (x / t) (hb (by
    rw [mem_ball_zero_iff, norm_div, div_lt_iff₀ hp, mul_comm]
    exact (div_lt_iff₀ hε).1 h))
  rwa [div_mul_cancel₀ _ ht0] at this

variable (E) in

def crdV (v : Pl F) : (Fv F v ⊗[F] E) ≃ₗ[Fv F v] (Fin (Module.finrank F E) → Fv F v) :=
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)).equivFun

theorem continuous_crdV (v : Pl F) : Continuous (crdV E v) := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap (crdV E v).toLinearMap

theorem continuous_crdV_symm (v : Pl F) : Continuous (crdV E v).symm := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
  exact IsModuleTopology.continuous_of_linearMap (crdV E v).symm.toLinearMap

theorem crdV_compFin (v : Pl F) (x : AE F E) (i : Fin (Module.finrank F E)) :
    crdV E v (compFin F E v x) i = evFin F v (GlobalTheory.XTermMaj.crd F E x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [GlobalTheory.XTermMaj.crd]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, GlobalTheory.XTermMaj.crd]
  | tmul r x =>
    have h : compFin F E v (r ⊗ₜ[F] x) = evFin F v r ⊗ₜ[F] x := rfl
    rw [h]
    simp [crdV, GlobalTheory.XTermMaj.crd]

theorem locCo_smul {V : Type} [AddCommGroup V] [Module (AF F) V] {Bf : V → V → AF F} {κ : Type} [Fintype κ]
    (co : Darboux Bf κ) (v : Pl F) (a : AF F) (u : V) :
    GlobalTheory.LatVac.locCo co v (a • u) = evFin F v a • GlobalTheory.LatVac.locCo co v u := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> simp [GlobalTheory.LatVac.locCo]

theorem exists_locCo_smul {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (v : Pl F)
    (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ∃ L : (Fv F v ⊗[F] E) → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v), Continuous L ∧
      ∀ l : AE F E, GlobalTheory.LatVac.locCo M.co v (l • u) = L (compFin F E v l) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  refine ⟨fun x => ∑ i, crdV E v x i • GlobalTheory.LatVac.locCo M.co v (b i • u),
    continuous_finsetSum _ fun i _ => ((continuous_apply i).comp (continuous_crdV v)).smul continuous_const, fun l => ?_⟩
  conv_lhs => rw [← b.sum_repr l, Finset.sum_smul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_assoc, locCo_smul, crdV_compFin]
  rfl

open scoped GlobalTheory.VacAny in

theorem schr_locCo_comm {V : Type} [AddCommGroup V] [Module (AF F) V] {Bf : V → V → AF F} {κ : Type} [Fintype κ]
    (co : Darboux Bf κ) (v : Pl F) (χ : AddChar (Fv F v) ℂ) (s u : V) (φ : (κ → Fv F v) → ℂ) :
    schr χ (GlobalTheory.LatVac.locCo co v s) (schr χ (GlobalTheory.LatVac.locCo co v u) φ) =
      χ (evFin F v (Bf s u)) • schr χ (GlobalTheory.LatVac.locCo co v u) (schr χ (GlobalTheory.LatVac.locCo co v s) φ) := by
  have h : evFin F v (Bf s u) = (GlobalTheory.LatVac.locCo co v s).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v u).2 -
      (GlobalTheory.LatVac.locCo co v u).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v s).2 := by
    rw [co.form]
    simp [GlobalTheory.LatVac.locCo, dotProduct]
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, h, ← mul_assoc, ← AddChar.map_add_eq_mul]
  rw [add_right_comm x (GlobalTheory.LatVac.locCo co v s).1]
  congr 2
  simp only [add_dotProduct]
  ring

theorem isLocallyConstant_locOp_om (hA : ActsEx) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') (K : Subgroup (UA σ X.J))
    (v : Pl F) {φ : (Fin n × Fin d → Fv F v) → ℂ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) :
    IsLocallyConstant fun k : KAt K (evFin F v) => locOp v (om (k.1, 1)) φ := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil
  have h1W : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := (UAtSub σ W (evFin F v)).one_mem
  obtain ⟨U, hU, hUact⟩ := (hA F E σ B n d X W M χX χW om r s r' s' hP v).2.2 φ hφ
  rw [IsLocallyConstant.iff_eventually_eq]
  intro k₀
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have hc : Continuous fun k : KAt K (evFin F v) => ((k₀⁻¹ * k : KAt K (evFin F v)).1, (1 : UA σ W.J)) :=
    (continuous_subtype_val.comp (continuous_const.mul continuous_id)).prodMk continuous_const
  have h0 : ((k₀⁻¹ * k₀ : KAt K (evFin F v)).1, (1 : UA σ W.J)) = 1 := by
    rw [inv_mul_cancel]; rfl
  have hev : ∀ᶠ k in 𝓝 k₀, ((k₀⁻¹ * k : KAt K (evFin F v)).1, (1 : UA σ W.J)) ∈ U :=
    hc.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)
  filter_upwards [hev] with k hk
  have hfix : Acts (evFin F v) (om ((k₀⁻¹ * k).1, 1)) φ φ := hUact _ hk (mem_KAt.1 (k₀⁻¹ * k).2).2 h1W
  have ha := acts_locOp_om hA hP (mem_KAt.1 k₀.2).2 h1W hφ
  have ek : (k.1, (1 : UA σ W.J)) = (k₀.1, 1) * ((k₀⁻¹ * k).1, 1) := by
    rw [Prod.mk_mul_mk, mul_one, ← Subgroup.coe_mul, mul_inv_cancel_left]
  refine locOp_eq hφ (locOp_mem _ _ _) fun ρ hρ => ?_
  rw [ek, map_mul, Module.End.mul_apply, hfix ρ hρ, ha ρ hρ]

open scoped GlobalTheory.VacAny in

theorem exists_locallyConstant_compact {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} (hB : B.IsGood σ)
    (M : Model σ X W) (hJ : ∀ i j, σ (W.J j i) = -W.J i j) (H : Plane E n n₁) (H' : Plane E d d₁)
    (hH : form σ X.J H.x H.y = 1) (hH' : form σ W.J H'.x H'.y = 1) (v : Pl F) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (ev : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Y)
    (hinv : ∀ u ∈ iso0 (F := F) n H', At (evFin F v) u → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ev (locOp v (M.co.rho B.ψ u) φ) = ev φ)
    {ψ : (Fin n × Fin d → Fv F v) → ℂ} (hψ : ψ ∈ SB (Fin n × Fin d → Fv F v)) :
    ∃ (g : (Fv F v ⊗[F] E) → Y) (C : Set (Fv F v ⊗[F] E)), IsLocallyConstant g ∧ IsCompact C ∧
      ∀ l : (AE F E)ˣ, ev (locOp v (M.co.rho B.ψ (partFin v (shiftA H H' l))) ψ) = g (compFin F E v l) ∧
        (compFin F E v l ∉ C → g (compFin F E v l) = 0) := by
  have hc : Continuous B.ψ := hB.std.1
  set χ := GlobalTheory.LatVac.psiAt B.ψ v with hχ
  have hχl : IsLocallyConstant χ := GlobalTheory.SchrSB.isLocallyConstant_addChar _ (GlobalTheory.SchrSB.continuous_psiAt B.ψ hc v)
  have hχ0 : ∀ᶠ y in 𝓝 (0 : Fv F v), χ y = 1 := by simpa using hχl.eventually_eq 0
  have hS := GlobalTheory.SchrLocConst.schr_isLocallyConstant χ hχ0 ψ hψ
  obtain ⟨L, hL, hLe⟩ := exists_locCo_smul M v (Matrix.vecMulVec (incV F H.x) (incV F H'.y))
  choose c hcc using GlobalTheory.XTermSupp.trace_mul_dual (F := F) (E := E)
  let u : Fin (Module.finrank F E) → Matrix (Fin n) (Fin d) (AE F E) := fun i =>
    inclR (F := F) (AF F) (σ (c i)) • Matrix.vecMulVec (incV F H.y) (incV F H'.x)
  have hfix : ∀ᶠ a in 𝓝 (0 : Fv F v), ∀ i, schr χ (a • GlobalTheory.LatVac.locCo M.co v (u i)) ψ = ψ := by
    refine Filter.eventually_all.2 fun i => ?_
    have hct : Continuous fun a : Fv F v => a • GlobalTheory.LatVac.locCo M.co v (u i) := continuous_id.smul continuous_const
    have ht : Tendsto (fun a : Fv F v => a • GlobalTheory.LatVac.locCo M.co v (u i)) (𝓝 0) (𝓝 0) :=
      hct.tendsto' _ _ (zero_smul _ _)
    filter_upwards [ht.eventually (hS.eventually_eq 0)] with a ha
    rw [ha]
    funext x
    simp [schr]
  obtain ⟨U, hU, hUm⟩ := exists_compact_of_annih v χ (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hB.std v) hfix
  refine ⟨fun x => ev (schr χ (L x) ψ), (crdV E v).symm '' Set.pi Set.univ fun _ => U,
    (hS.comp_continuous hL).comp ev, (isCompact_univ_pi fun _ => hU).image (continuous_crdV_symm v), fun l => ?_⟩
  have hl : GlobalTheory.LatVac.locCo M.co v (shiftA H H' l) = L (compFin F E v l) := hLe l.1
  refine ⟨by rw [(locOp_rho M.co hc v _ hψ).2, hl], fun hn => ?_⟩
  beta_reduce
  rw [← hl]
  by_contra hne
  refine hn ⟨crdV E v (compFin F E v l), fun i _ => hUm _ fun a ha => ?_, (crdV E v).symm_apply_apply _⟩
  have hat : At (evFin F v) (GlobalTheory.LatVac.liftV v a • u i) := fun b hb => by
    rw [smul_smul, ← smul_eq_mul, GlobalTheory.LatVac.at_liftV v a b hb, zero_smul]
  have h1 := congrArg ev (schr_locCo_comm M.co v χ (shiftA H H' l) (GlobalTheory.LatVac.liftV v a • u i) ψ)
  have h2 := hinv (GlobalTheory.LatVac.liftV v a • u i) ⟨GlobalTheory.LatVac.liftV v a • inclR (F := F) (AF F) (σ (c i)) • incV F H.y, by
      rw [Matrix.smul_vecMulVec, Matrix.smul_vecMulVec]⟩ hat _
      (GlobalTheory.SchrSB.schr_mem_SB B.ψ hc v (GlobalTheory.LatVac.locCo M.co v (shiftA H H' l)) ψ hψ)
  have h3 := (locOp_rho M.co hc v (GlobalTheory.LatVac.liftV v a • u i)
    (GlobalTheory.SchrSB.schr_mem_SB B.ψ hc v (GlobalTheory.LatVac.locCo M.co v (shiftA H H' l)) ψ hψ)).2
  rw [partFin_of_at hat] at h3
  rw [h3] at h2
  have h4 : schr χ (GlobalTheory.LatVac.locCo M.co v (GlobalTheory.LatVac.liftV v a • u i)) ψ = ψ := by
    rw [locCo_smul, GlobalTheory.LatVac.evFin_liftV]
    exact ha i
  rw [h4, map_smul, h2, GlobalTheory.XTermSupp.symp_shiftA hB.cm hJ H H' hH hH', hcc, map_mul, GlobalTheory.LatVac.evFin_liftV,
    ← crdV_compFin] at h1
  exact smul_left_injective ℂ hne (h1.symm.trans (one_smul ℂ _).symm)

set_option synthInstance.maxHeartbeats 100000 in

theorem coneFinInt_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.FunPr.Hypotheses₂ → ∀ (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')), IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
    (ei ≠ 0 ∧ (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) ∧
      ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ (μKv : ∀ v : Pl F, Measure (KAt K (evFin F v))), (∀ v, IsNormK K (evFin F v) (μKv v)) →
    ∀ (μEv : ∀ v : Pl F, Measure (idelesAt E (evFin F v))), (∀ v, IsNormE E v (μEv v)) →
    ∀ (μKi : Measure (KAt K (evI F))), IsNormK K (evI F) μKi → ∀ (μEi : Measure (idelesAt E (evI F))), μEi.IsHaarMeasure →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G₁.M.IsGood B.ψ →
    ∀ (v : Pl F) (φ : (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ), φ ∈ SB _ → ∀ y : Fin b × Fin (b + a') → Fv F v,
      Integrable (fun q : UA σ G.V.J × (AE F E)ˣ => coneFinInt B G.M om v (ev v) (shiftA H H') X.ν ((b + 2 - a') / 2) φ q.1 q.2 y)
        (((μKv v).map Subtype.val).prod ((μEv v).map Subtype.val)) ∧
      ∫ q : UA σ G.V.J × (AE F E)ˣ, coneFinInt B G.M om v (ev v) (shiftA H H') X.ν ((b + 2 - a') / 2) φ q.1 q.2 y
        ∂(((μKv v).map Subtype.val).prod ((μEv v).map Subtype.val)) =
        coneFin B G.M om v (ev v) K (μKv v) (μEv v) (shiftA H H') X.ν ((b + 2 - a') / 2) φ y := by
  intro F E _ _ _ _ _ σ hP B b a' G G₁ H H' hC e hE ei ev hL K hK μKv hμK μEv hμE _ _ _ _ X om om' hT hM₁ v φ hφ y
  have hPair : IsPair B G.M X.β (X.β / X.α) om (b + 2 - G.p) G.p (b + 2 + a' - (G.p + G.q)) (G.p + G.q) :=
    { base := hT.base, herm := hT.geo.hV, skew := hT.geo.hW, good := hT.geo.hM, hX := hT.chars.heckeβ,
      hW := GlobalTheory.ThKRatInv.isHecke_div hT.chars.heckeβ hT.chars.heckeα, resX := hT.chars.resβ,
      resW := GlobalTheory.ThKRatInv.resEtaPow_div hT.chars.resβ hT.chars.resα, weil := hT.weil }
  have hKc : IsCompact (K : Set (UA σ G.V.J)) := by
    obtain ⟨K₀, -, -, h1, h2, -⟩ := GlobalTheory.StabHaar.stabEx hP F E σ B (b + 2) G.V _ _ hT.base hT.geo.hV
    rwa [show K = K₀ from Subgroup.ext fun g => (hK g).trans (h1 g).symm]
  haveI : CompactSpace (KAt K (evFin F v)) := isCompact_iff_compactSpace.1 (isCompact_KAt hKc _)
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  haveI : IsProbabilityMeasure (μKv v) := ⟨(hμK v).2⟩
  haveI := (hμE v).1
  haveI hKf : IsFiniteMeasure (μKv v) := ⟨by rw [(hμK v).2]; exact ENNReal.one_lt_top⟩
  haveI : SigmaFinite (μKv v) := IsFiniteMeasure.toSigmaFinite _
  haveI : SFinite (μKv v) := instSFiniteOfSigmaFinite
  haveI : SigmaFinite (μEv v) := inferInstance
  have hz : 1 ≤ (b + 2 - a') / 2 := by have := hT.geo.eBig; omega
  refine integrable_integral_map_prod
    (MeasurableEmbedding.subtype_coe (isCompact_KAt hKc (evFin F v)).isClosed.measurableSet)
    (MeasurableEmbedding.subtype_coe (isClosed_idelesAt (E := E) (evFin F v)).measurableSet) (μKv v) (μEv v)
    (fun k l => coneFinInt B G.M om v (ev v) (shiftA H H') X.ν ((b + 2 - a') / 2) φ k l y) ?_
  refine integrable_prod_of_locallyConstant (μKv v) (μEv v)
    (isLocallyConstant_locOp_om (GlobalTheory.T.theta_action_exists hP) hPair K v hφ)
    (fun ψ l => ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l.1))) ψ) y * (X.ν l.1 : ℂ) *
      ((absE F E l.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) fun k => ?_
  obtain ⟨g, C, hg, hCc, hgC⟩ := exists_locallyConstant_compact hT.base G.M hT.geo.hW.skew H H' hC.hH.xy hC.hH'.xy v (ev v)
    (fun u hu => (GlobalTheory.ThK.EvLocParts.locParts F E σ B _ _ _ _ _ _ _ _ G.M G₁.M _ _ _ e hT.base hT.geo.hM hM₁ hE ei ev
      hL.1 hL.2.1 hL.2.2 v).2 u (Or.inl hu)) (locOp_mem v (om (k.1, 1)) φ)
  have hcl : Continuous fun l : idelesAt E (evFin F v) => compFin F E v l.1.1 :=
    Units.continuous_val.comp ((GlobalTheory.Doubling.continuous_unitFin v).comp continuous_subtype_val)
  have hgy : Continuous fun x => g x y := (hg.comp fun f => f y).continuous
  have hν : Continuous fun l : (AE F E)ˣ => (X.ν l : ℂ) :=
    continuous_subtype_val.comp
      (show Continuous fun l => X.α l / X.β l from hT.chars.heckeα.1.div' hT.chars.heckeβ.1)
  have habs : Continuous fun l : idelesAt E (evFin F v) => ((absE F E l.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp continuous_subtype_val))
  obtain ⟨R, hR⟩ := hCc.exists_bound_of_continuousOn hgy.continuousOn
  haveI : T2Space (Fv F v ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have hA : MeasurableSet {l : idelesAt E (evFin F v) | compFin F E v l.1.1 ∈ C} :=
    (hCc.isClosed.preimage hcl).measurableSet
  have hI := ((integrable_indicator_iff hA).2 (GlobalTheory.T.idele_power_integrable_compact F E v (μEv v) (hμE v).1 C hCc _ hz)).const_mul R
  simp only [fun l => (hgC l).1]
  refine hI.mono' (((hgy.comp hcl).mul (hν.comp continuous_subtype_val)).mul (habs.pow _)).aestronglyMeasurable
    (ae_of_all _ fun l => ?_)
  by_cases hl : compFin F E v l.1.1 ∈ C
  · rw [Set.indicator_of_mem (show l ∈ {l : idelesAt E (evFin F v) | compFin F E v l.1.1 ∈ C} from hl)]
    simp only [norm_mul, norm_pow, Circle.norm_coe, mul_one, Complex.norm_real, NNReal.norm_eq]
    exact mul_le_mul_of_nonneg_right (hR _ hl) (by positivity)
  · rw [Set.indicator_of_notMem (show l ∉ {l : idelesAt E (evFin F v) | compFin F E v l.1.1 ∈ C} from hl), (hgC l.1).2 hl]
    all_goals simp

end GlobalTheory.ThK.ConeLocInt

end
