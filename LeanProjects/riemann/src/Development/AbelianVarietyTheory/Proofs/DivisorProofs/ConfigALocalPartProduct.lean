import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ArchWeilCont

theorem bounded_of_weakly_bounded {V : Type} [SeminormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type} (x : ι → V)
    (h : ∀ T : V →L[ℂ] ℂ, ∃ C, ∀ i, ‖T (x i)‖ ≤ C) : ∃ C, ∀ i, ‖x i‖ ≤ C := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun i => NormedSpace.inclusionInDoubleDual ℂ V (x i)) h
  refine ⟨C, fun i => NormedSpace.norm_le_dual_bound ℂ (x i) ((norm_nonneg _).trans (hC i)) fun f => ?_⟩
  exact ((NormedSpace.inclusionInDoubleDual ℂ V (x i)).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _))

theorem seminorm_bounded {V : Type} [AddCommGroup V] [Module ℂ V] (p : Seminorm ℂ V) {ι : Type} (x : ι → V)
    (h : ∀ (T : V →ₗ[ℂ] ℂ) (c : ℝ), 0 ≤ c → (∀ v, ‖T v‖ ≤ c * p v) → ∃ C, ∀ i, ‖T (x i)‖ ≤ C) :
    ∃ C, ∀ i, p (x i) ≤ C := by
  letI : SeminormedAddCommGroup V := p.toAddGroupSeminorm.toSeminormedAddCommGroup
  letI : NormedSpace ℂ V := ⟨fun a v => (map_smul_eq_mul p a v).le⟩
  exact bounded_of_weakly_bounded x fun T => h T.toLinearMap ‖T‖ (norm_nonneg _) fun v => T.le_opNorm v

theorem continuous_of_weak {X : Type} [TopologicalSpace X] [WeaklyLocallyCompactSpace X] {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Φ : X → SchwartzMap V ℂ)
    (h : ∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, Continuous fun x => T (Φ x)) : Continuous Φ := by
  refine continuous_iff_continuousAt.2 fun x₀ => GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded Φ x₀ (fun v => ?_) ?_
  · exact (h ((BoundedContinuousFunction.evalCLM ℂ v).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ))).continuousAt
  · intro k n
    obtain ⟨K, hK, hx⟩ := exists_compact_mem_nhds x₀
    obtain ⟨C, hC⟩ := seminorm_bounded (SchwartzMap.seminorm ℂ k n) (fun i : K => Φ i) fun T c hc hT => by
      let T' : SchwartzMap V ℂ →L[ℂ] ℂ := SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) T (map_add T)
        (map_smul T) ⟨{(k, n)}, c, hc, fun f => by simpa using hT f⟩
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (h T').continuousOn
      exact ⟨C, fun i => hC i.1 i.2⟩
    refine ⟨C, ?_⟩
    filter_upwards [hx] with x hxK v
    exact (SchwartzMap.le_seminorm ℂ k n (Φ x) v).trans (hC ⟨x, hxK⟩)

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def resInf : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun y i => GlobalTheory.HeisSchA.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) 0

theorem resInf_tens {r : (κ → AF F) → ℂ} (hr : ∀ x z, At (evI F) z → r (x + z) = r x)
    (h : (κ → mixedEmbedding.mixedSpace F) → ℂ) : resInf (tens (evI F) h r) = r 0 • h := by
  funext y
  let z : κ → AF F := fun i => GlobalTheory.HeisSchA.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) 0
  have hz : At (evI F) z := fun u hu => funext fun i => GlobalTheory.HeisSchA.at_mk _ u hu
  have hy : (fun i => evI F (z i)) = y := funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
  have hrz : r z = r 0 := by simpa using hr 0 z hz
  change tens (evI F) h r z = r 0 * h y
  simp only [tens, hy, hrz]
  ring

theorem exists_adm (T : SInf F κ →L[ℂ] ℂ) : ∃ l ∈ (adeleClass F).adm κ, ∀ r : (κ → AF F) → ℂ,
    (∀ x z, At (evI F) z → r (x + z) = r x) → ∀ h : SInf F κ, l (tens (evI F) h r) = r 0 * T h := by
  let c : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
    { toFun := fun f => f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  obtain ⟨s, hs⟩ := c.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 DFunLike.coe_injective)
  have hs' : ∀ f : SInf F κ, s f = f := fun f => LinearMap.congr_fun hs f
  have key : ∀ r : (κ → AF F) → ℂ, (∀ x z, At (evI F) z → r (x + z) = r x) → ∀ h : SInf F κ,
      (T.toLinearMap ∘ₗ s ∘ₗ resInf) (tens (evI F) h r) = r 0 * T h := fun r hr h => by
    simp only [LinearMap.comp_apply, resInf_tens hr, map_smul, hs', smul_eq_mul, ContinuousLinearMap.coe_coe]
  refine ⟨T.toLinearMap ∘ₗ s ∘ₗ resInf, fun g _ => ⟨g 0 • T, fun f => ?_⟩, key⟩
  have e : resInf (pureA F f g) = g 0 • (f : _ → ℂ) := by
    funext y
    change f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i))) *
      g 0 = g 0 * f y
    simp only [RingEquiv.apply_symm_apply]
    ring
  simp only [LinearMap.comp_apply, e, map_smul, hs', smul_eq_mul, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.smul_apply]

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open Classical in

theorem continuousOn_locOpInf (hP : GlobalTheory.FunPr.Hypotheses₂) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E} {om : Rep σ X W} (hcm : IsCMExt F E σ) (hψ : IsStd ψ)
    (hW : M.IsWeil ψ χX χW om) (f : SInf F (Fin n × Fin d)) :
    ContinuousOn (fun x : UA σ X.J => locOpInf (om (x, 1)) f) (UAt σ X (evI F)) := by
  obtain ⟨_, _, _, _⟩ := GlobalTheory.UnipCT.topFacts σ X.J
  haveI : LocallyCompactSpace (UAt σ X (evI F)) := (isClosed_UAtSub X (evI F)).locallyCompactSpace
  rw [continuousOn_iff_continuous_restrict]
  refine continuous_of_weak _ fun T => ?_
  obtain ⟨r, h0, hr⟩ := exists_rest_inf F (Fin n × Fin d)
  obtain ⟨l, hl, hlT⟩ := exists_adm T
  have hc := (IsUWeilPair.isUSplitting hW).cont l hl _ (hr f).2
  have h1 : Continuous fun x : UAt σ X (evI F) => ((x.1, 1) : UA σ X.J × UA σ W.J) :=
    continuous_subtype_val.prodMk continuous_const
  refine ((hc.comp h1).const_mul (r 0)⁻¹).congr fun x => ?_
  have ha := acts_locOpInf (GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ n d X W M ψ χX χW om hcm hψ hW x.1 x.2 f) r (hr f)
  change (r 0)⁻¹ * l (om (x.1, 1) (tens (evI F) f r)) = T (locOpInf (om (x.1, 1)) f)
  rw [ha, hlT r (hr f).1, inv_mul_cancel_left₀ h0]

open GlobalTheory.ArchUniq Classical in

theorem continuous_locOpInf_rho {V : Type} [AddCommGroup V] [Module (AF F) V] {Bf : V → V → AF F} (co : Darboux Bf κ)
    {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (u : V) :
    Continuous fun f : SInf F κ => locOpInf (co.rho ψ (partInf F u)) f := by
  have e : ∀ f : SInf F κ, locOpInf (co.rho ψ (partInf F u)) f = GlobalTheory.HeisSchA.archS f (locV (co.e u).2) (locV (co.e u).1)
      (trP F κ (locV (co.e u).1) (locV (co.e u).2) / 2) := fun f => by
    refine DFunLike.coe_injective ?_
    refine (locOpInf_rho co hψ u f).2.trans ?_
    funext y
    rw [GlobalTheory.HeisSchA.archS_apply, GlobalTheory.Published.Metaplectic.eChar_apply, schrF, ContinuousLinearMap.neg_apply,
      GlobalTheory.HeisSchA.trL_apply]
    congr 2
    simp only [trP, dotProduct]
    push_cast
    ring
  simp only [e, GlobalTheory.HeisSchA.archS]
  exact (ContinuousLinearMap.continuous _).comp (ContinuousLinearMap.continuous _)

theorem continuousOn_eval_shift : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
      ContinuousOn (fun x : UA σ G.V.J => ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' 1))) (locOpInf (om (x, 1)) f)))
        (UAt σ G.V (evI F)) := by
  intro hP F E _ _ _ _ _ σ B b a' G G₁ H H' _ e _ ei ev _ X om om' om₁ om₁' hT _ f
  exact (ei.continuous.comp (continuous_locOpInf_rho G.M.co hT.base.std (shiftA H H' 1))).comp_continuousOn
    (continuousOn_locOpInf hP G.M hT.base.cm hT.base.std hT.weil f)

end GlobalTheory.ArchWeilCont
