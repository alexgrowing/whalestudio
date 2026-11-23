import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelPolynomial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfTensEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSmulSemi

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM Filter Topology
open scoped SchwartzMap GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical

noncomputable section

namespace GlobalTheory.ArchJointCont

theorem continuous_of_weak {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (A : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)) (h : ∀ T : 𝓢(V, ℂ) →L[ℂ] ℂ, Continuous fun f => T (A f)) : Continuous A := by
  haveI : BarrelledSpace ℂ 𝓢(V, ℂ) := GlobalTheory.schwartzMap_barrelledSpace V
  refine (schwartz_withSeminorms ℂ V ℂ).continuous_of_continuous_comp A fun i => ?_
  set p : Seminorm ℂ 𝓢(V, ℂ) := schwartzSeminormFamily ℂ V ℂ i
  have hp : Continuous p := (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i
  let j₀ : 𝓢(V, ℂ) →ₗ[ℂ] GlobalTheory.DiffDecay.WithSemi p := LinearMap.id
  have hj : Continuous j₀ := by
    refine continuous_of_continuousAt_zero j₀ ?_
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    have := hp.tendsto 0
    rw [map_zero] at this
    exact this
  let j : 𝓢(V, ℂ) →L[ℂ] GlobalTheory.DiffDecay.WithSemi p := ⟨j₀, hj⟩
  have hnorm : ∀ x, ‖j x‖ = p x := fun x => rfl
  refine Seminorm.continuous_of_lowerSemicontinuous _ fun f₀ y hy => ?_
  change y < p (A f₀) at hy
  rcases lt_or_ge y 0 with hy0 | hy0
  · exact Eventually.of_forall fun f => lt_of_lt_of_le hy0 (apply_nonneg _ _)
  have hex : ∃ L : StrongDual ℂ (GlobalTheory.DiffDecay.WithSemi p), y * ‖L‖ < ‖L (j (A f₀))‖ := by
    by_contra hne
    push_neg at hne
    have h1 : ‖NormedSpace.inclusionInDoubleDual ℂ (GlobalTheory.DiffDecay.WithSemi p) (j (A f₀))‖ ≤ y :=
      ContinuousLinearMap.opNorm_le_bound _ hy0 fun L => by
        rw [NormedSpace.dual_def]; exact hne L
    rw [show NormedSpace.inclusionInDoubleDual ℂ (GlobalTheory.DiffDecay.WithSemi p) (j (A f₀)) =
      NormedSpace.inclusionInDoubleDualLi ℂ (j (A f₀)) from rfl, LinearIsometry.norm_map, hnorm] at h1
    exact absurd hy (not_lt.2 h1)
  obtain ⟨L, hL⟩ := hex
  have hc : Continuous fun f => ‖L (j (A f))‖ := (h (L.comp j)).norm
  filter_upwards [(hc.tendsto f₀).eventually_const_lt hL] with f hf
  change y < p (A f)
  have h2 : ‖L (j (A f))‖ ≤ ‖L‖ * p (A f) := by rw [← hnorm]; exact L.le_opNorm _
  have h4 : y * ‖L‖ < ‖L‖ * p (A f) := lt_of_lt_of_le hf h2
  by_contra hcon
  push_neg at hcon
  nlinarith [norm_nonneg L]

theorem exists_adm (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (T : SInf F κ →L[ℂ] ℂ) :
    ∃ l ∈ (adeleClass F).adm κ, ∀ (f : SInf F κ) (g : (κ → IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) → ℂ),
      l (pureA F ⇑f g) = g 0 * T f := by
  let lift : (κ → mixedEmbedding.mixedSpace F) → (κ → AF F) := fun y i =>
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0)
  let sl : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) := LinearMap.funLeft ℂ ℂ lift
  let co : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
    { toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hco : Function.Injective co := DFunLike.coe_injective
  let e := LinearEquiv.ofInjective co hco
  obtain ⟨T₂, hT₂⟩ := LinearMap.exists_extend (T.toLinearMap ∘ₗ e.symm.toLinearMap)
  have hT₂f : ∀ f : SInf F κ, T₂ ⇑f = T f := fun f => by
    have := congrArg (fun m => m (e f)) hT₂
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      ContinuousLinearMap.coe_coe] at this
    rw [LinearEquiv.ofInjective_apply] at this
    exact this
  have hsl : ∀ (f : SInf F κ) g, sl (pureA F ⇑f g) = g 0 • ⇑f := fun f g => by
    funext y
    show pureA F ⇑f g (lift y) = g 0 * f y
    simp only [pureA, lift, RingEquiv.apply_symm_apply]
    rw [mul_comm]
    rfl
  refine ⟨T₂ ∘ₗ sl, fun g _ => ⟨g 0 • T, fun f => ?_⟩, fun f g => ?_⟩
  · simp [hsl, hT₂f]
  · simp [hsl, hT₂f]

theorem tendsto_line : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (r : (Fin n × Fin d → AF F) → ℂ), r 0 ≠ 0 →
    (∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r) →
    ∀ (h k : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (h₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
    (∀ t : ℝ, om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (h t) r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (k t) r) →
    Filter.Tendsto h (nhds 0) (nhds h₀) → Filter.Tendsto k (nhds 0) (nhds h₀) := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ _hM hW γ hγ r hr0 hR h k h₀ hk hh
  have hs := IsUWeilPair.isUSplitting hW
  let δ : ℝ → UA σ Y.J × UA σ Wd.J := fun t => (γ (Multiplicative.ofAdd t), 1)
  have hδc : Continuous δ := (hγ.1.comp continuous_ofAdd).prodMk continuous_const
  have hδ0 : δ 0 = 1 := by
    show (γ (Multiplicative.ofAdd 0), 1) = 1
    rw [ofAdd_zero, map_one]; rfl
  have hδm : ∀ s t, δ (s + t) = δ s * δ t := fun s t => by
    show (γ (Multiplicative.ofAdd (s + t)), 1) = (γ (Multiplicative.ofAdd s), 1) * (γ (Multiplicative.ofAdd t), 1)
    rw [ofAdd_add, map_mul, Prod.mk_mul_mk, one_mul]
  have ex := fun f => GlobalTheory.ArchLinePair.exists_orbit_pair hP M ψ χX χW om hψ hW δ hδc hδ0 hδm (fun t => hγ.2 _)
    (fun t u _ => by simp [δ, mat]) f
  choose c g hc0 hslope hact using ex
  have hrr : ∀ x z, At (evI F) z → r (x + z) = r x := (hR 0).1
  have hinj := GlobalTheory.ArchCancel.eq_of_tens_eq F r hrr ⟨0, hr0⟩
  have hA : ∀ t (f : SInf F (Fin n × Fin d)), om (δ t) (tens (evI F) ⇑f r) = tens (evI F) ⇑(c f t) r :=
    fun t f => hact f t r (hR f)
  have tadd : ∀ f g : SInf F (Fin n × Fin d),
      tens (evI F) ⇑(f + g) r = tens (evI F) ⇑f r + tens (evI F) ⇑g r := by
    intro f g; funext x; simp [tens, add_mul]
  have tsmul : ∀ (a : ℂ) (f : SInf F (Fin n × Fin d)), tens (evI F) ⇑(a • f) r = a • tens (evI F) ⇑f r := by
    intro a f; funext x; simp [tens, mul_assoc]
  let A : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun t =>
    { toFun := fun f => c f t
      map_add' := fun f g => hinj _ _ (by rw [← hA, tadd, map_add, hA, hA, tadd])
      map_smul' := fun a f => hinj _ _ (by rw [← hA, tsmul, map_smul, hA, RingHom.id_apply, tsmul]) }
  have hAf : ∀ t f, A t f = c f t := fun _ _ => rfl
  have hmul : ∀ s t f, c f (s + t) = c (c f t) s := fun s t f => hinj _ _ (by
    rw [← hA (s + t) f, ← hA s (c f t), ← hA t f, hδm, map_mul, Module.End.mul_apply])
  have hcont0 : ∀ f, Tendsto (fun s => c f s) (𝓝 0) (𝓝 f) := by
    intro f
    have h1 : Tendsto (fun s : ℝ => s • (s⁻¹ • (c f s - f))) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • g f)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul (hslope f)
    rw [zero_smul] at h1
    have h2 : Tendsto (fun s => c f s) (𝓝[≠] 0) (𝓝 f) := by
      have h1' := h1.add_const f
      rw [zero_add] at h1'
      refine h1'.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
      rw [smul_smul, mul_inv_cancel₀ hs, one_smul, sub_add_cancel]
    have h3 : ContinuousAt (fun s => c f s) 0 := by
      rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hc0]; exact h2
    have h4 := h3.tendsto
    rwa [hc0] at h4
  have hcont : ∀ f, Continuous fun s => c f s := by
    intro f
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    have ht : Tendsto (fun s : ℝ => s - t₀) (𝓝 t₀) (𝓝 0) := by
      have h5 := (continuous_sub_right t₀).tendsto t₀
      rwa [sub_self] at h5
    refine ((hcont0 (c f t₀)).comp ht).congr fun s => ?_
    show c (c f t₀) (s - t₀) = c f s
    rw [← hmul, sub_add_cancel]
  let g₀ := GlobalTheory.ArchLocality.intInd (F := F) (Fin n × Fin d)
  have hg₀ : g₀ ∈ SB _ := GlobalTheory.ArchLocality.intInd_mem _
  have hg₀0 : g₀ 0 = 1 := by
    simp only [g₀, GlobalTheory.ArchLocality.intInd]
    rw [Set.indicator_of_mem (show (0 : Fin n × Fin d → IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
      fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) from
        fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
    rfl
  let r₀ : (Fin n × Fin d → AF F) → ℂ := fun x => g₀ fun i => (x i).2
  have hrr₀ : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    refine congrArg g₀ (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.ArchLocality.snd_eq_zero_of_at hz i, add_zero]
  have hR₀ : ∀ f : SInf F (Fin n × Fin d), Rest (evI F) ⇑f r₀ := fun f =>
    ⟨hrr₀, Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩⟩
  have hAcont : ∀ t, Continuous (A t) := by
    intro t
    refine continuous_of_weak (A t) fun T => ?_
    obtain ⟨l, hl, hlf⟩ := exists_adm F T
    obtain ⟨T', hT'⟩ := hs.adm (δ t) l hl g₀ hg₀
    refine T'.continuous.congr fun f => ?_
    have e1 : om (δ t) (pureA F ⇑f g₀) = pureA F ⇑(c f t) g₀ := hact f t r₀ (hR₀ f)
    have e2 := hT' f
    rw [LinearMap.comp_apply, e1, hlf, hg₀0, one_mul] at e2
    exact e2.symm
  let 𝓕 : Set.Icc (-1 : ℝ) 1 → SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) := fun i => ⟨A i, hAcont i⟩
  haveI : BarrelledSpace ℂ (SInf F (Fin n × Fin d)) := GlobalTheory.schwartzMap_barrelledSpace _
  have hq := schwartz_withSeminorms ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ
  have hUE : UniformEquicontinuous ((↑) ∘ 𝓕) := hq.banach_steinhaus fun q x => by
    have hc : Continuous fun t : ℝ => schwartzSeminormFamily ℂ _ ℂ q (c x t) :=
      (hq.continuous_seminorm q).comp (hcont x)
    have := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image hc.continuousOn
    rw [Set.image_eq_range] at this
    exact this
  have hk' : ∀ t, k t = c (h t) t := fun t => hinj _ _ ((hk t).symm.trans (hA t (h t)))
  have h1 : Tendsto (fun t => A t (h t - h₀)) (𝓝 0) (𝓝 0) := by
    have hE := hUE.equicontinuous 0
    intro U hU
    have hU' : {p : SInf F (Fin n × Fin d) × SInf F (Fin n × Fin d) | p.2 - p.1 ∈ U} ∈
        uniformity (SInf F (Fin n × Fin d)) := by
      rw [uniformity_eq_comap_nhds_zero]; exact ⟨U, hU, fun p hp => hp⟩
    have ev := hE _ hU'
    have hz : Tendsto (fun t => h t - h₀) (𝓝 0) (𝓝 0) := by simpa using hh.sub_const h₀
    have ev3 : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Set.Icc (-1 : ℝ) 1 := Icc_mem_nhds (by norm_num) (by norm_num)
    refine Filter.mem_map.2 ?_
    filter_upwards [hz.eventually ev, ev3] with t ht ht'
    have := ht ⟨t, ht'⟩
    simpa [𝓕] using this
  have h2 : Tendsto (fun t => A t (h t - h₀) + c h₀ t) (𝓝 0) (𝓝 (0 + h₀)) := h1.add (hcont0 h₀)
  rw [zero_add] at h2
  refine h2.congr fun t => ?_
  rw [hk' t, map_sub]
  show c (h t) t - c h₀ t + c h₀ t = c (h t) t
  exact sub_add_cancel _ _

end GlobalTheory.ArchJointCont
