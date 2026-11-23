import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicMapModuliLiftsLocallyToPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRelativeExpOfParts
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LatContMapContinuous
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsComplexArcDatumCmFibre

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open Filter Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFamily

open GlobalTheory.LocLift

theorem exists_core {X : Scheme.{0}} (s : X ⟶ Sp ℂ) (G : Over X) [GrpObj G] {g m : ℕ} {B : Set (Fin m → ℂ)}
    {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} {b₀ : Fin m → ℂ} (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶ G))
    (hs : LocallyOfFiniteType s) (hG : IsAbelianScheme G) (hg : SmoothOfRelativeDimension g G.hom) (hB : IsOpen B)
    (hb₀ : b₀ ∈ B) (hys : ∀ b ∈ B, y b ≫ s = spMap (RingHom.id ℂ)) (hy : IsHolTo B y) (he₀ : IsExp (y b₀) e₀)
    {La : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (P₀ : La →+ (Fin g → ℂ))
    (hi : Function.Injective P₀) (hsp : Submodule.span ℝ (Set.range P₀) = ⊤) (hk : ∀ z, e₀ z = 1 ↔ z ∈ P₀.range) :
    ∃ (C : Set (Fin m → ℂ)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (P : (Fin m → ℂ) → (La →+ (Fin g → ℂ))),
      IsOpen C ∧ b₀ ∈ C ∧ C ⊆ B ∧ e b₀ = e₀ ∧ P b₀ = P₀ ∧
      IsHolTo (C ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧
      (∀ b ∈ C, IsExp (y b) (e b) ∧ (∀ z, e b z = 1 ↔ z ∈ (P b).range) ∧ Function.Injective (P b) ∧
        Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ DiscreteTopology (P b).range) ∧
      (∀ x, DifferentiableOn ℂ (fun b => P b x) C) ∧
      ∀ (α : G ⟶ G) [IsMonHom α] (M₀ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ w, e₀ (M₀ w) = e₀ w ≫ α) →
        ∀ b ∈ C, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ w, e b (M w) = e b w ≫ α) ∧
          ∀ x x', P₀ x' = M₀ (P₀ x) → P b x' = M (P b x) := by
  classical
  have : IsProper G.hom := hG.proper
  obtain ⟨B', e, r, hB'o, hb₀', hB'B, he0, hr, hol, hexp, hlift⟩ :=
    GlobalTheory.RelExp.exists_relative_exp ℂ (RingHom.id ℂ) X s G g m B y b₀ e₀ hs hG hg hB hb₀ hys hy he₀
  have hl : HasLifts B' y e := hlift
  have hyB' : IsHolTo B' y := isHolTo_mono hy hB'o hB'B
  have hk' : ∀ z, e b₀ z = 1 ↔ z ∈ P₀.range := by rw [he0]; exact hk
  obtain ⟨P, hP0, hev⟩ := exists_periods GlobalTheory.latContinuation hB'o hb₀' hyB' hr hol
    (fun b hb => ⟨(hexp b hb).1, (hexp b hb).2⟩) hl P₀ hi hsp hk'
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (Filter.Eventually.and (hB'o.mem_nhds hb₀' : ∀ᶠ b in 𝓝 b₀, b ∈ B') hev)
  have hCo : IsOpen (Metric.ball b₀ ε) := Metric.isOpen_ball
  have hb₀C : b₀ ∈ Metric.ball b₀ ε := Metric.mem_ball_self hε
  have hCB' : Metric.ball b₀ ε ⊆ B' := fun b hb => (hball b hb).1
  have hadd : ∀ b ∈ B', ∀ z w, e b (z + w) = e b z * e b w := fun b hb => (hexp b hb).1.1
  have hsurj : ∀ b ∈ B', Function.Surjective (e b) := fun b hb => (hexp b hb).1.2.1
  have hrad : ∀ b ∈ B', ∀ z, ‖z‖ < r → e b z = 1 → z = 0 := fun b hb => (hexp b hb).2
  refine ⟨Metric.ball b₀ ε, e, P, hCo, hb₀C, hCB'.trans hB'B, he0, hP0,
    isHolTo_mono hol (hCo.prod isOpen_univ) (Set.prod_mono hCB' subset_rfl),
    fun b hb => ⟨(hexp b (hCB' hb)).1, (hball b hb).2.2⟩,
    fun x b hb => ((hball b hb).2.1 x).differentiableWithinAt, ?_⟩
  intro α _ M₀ hM₀
  have hxadd : ∀ b ∈ B', ∀ z w, e b (z + w) ≫ α = (e b z ≫ α) * (e b w ≫ α) := by
    intro b hb z w
    rw [hadd b hb, MonObj.mul_comp]
  have huniq : ∀ b ∈ B', ∀ M M' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ w, e b (M w) = e b w ≫ α) →
      (∀ w, e b (M' w) = e b w ≫ α) → M = M' :=
    fun b hb M M' h h' => linear_lift_unique (hadd b hb) hr (hrad b hb) (fun z => (h z).trans (h' z).symm)
  have hloc : ∀ b₁ ∈ Metric.ball b₀ ε, ∃ F : (Fin m → ℂ) → ((Fin g → ℂ) →L[ℂ] (Fin g → ℂ)),
      ContinuousAt F b₁ ∧ ∀ᶠ b in 𝓝 b₁, ∀ z, e b (F b z) = e b z ≫ α := by
    intro b₁ hb₁
    have hW : IsOpen (B' ×ˢ (Set.univ : Set (Fin g → ℂ))) := hB'o.prod isOpen_univ
    have hxhol : IsHolTo (B' ×ˢ (Set.univ : Set (Fin g → ℂ)))
        (fun q : (Fin m → ℂ) × (Fin g → ℂ) => (e q.1 q.2 ≫ α).left) :=
      isHolTo_congr (isHolTo_comp_hom hol α.left) (fun q _ => by simp only [Over.comp_left])
    have h0 : e b₁ 0 = e b₁ 0 ≫ α := by
      rw [hom_zero (hadd b₁ (hCB' hb₁)), MonObj.one_comp]
    obtain ⟨ζ, -, hζa, hζe⟩ := hl.lift (V := (Fin m → ℂ) × (Fin g → ℂ))
      (W := B' ×ˢ (Set.univ : Set (Fin g → ℂ))) (β := Prod.fst)
      (fun q => e q.1 q.2 ≫ α) hW
      (show ((b₁, 0) : (Fin m → ℂ) × (Fin g → ℂ)) ∈ B' ×ˢ (Set.univ : Set (Fin g → ℂ)) from ⟨hCB' hb₁, trivial⟩)
      differentiableOn_fst (fun q hq => hq.1) hxhol h0
    have hpt : Continuous (fun b : Fin m → ℂ => (b, (0 : Fin g → ℂ))) := by fun_prop
    have hcont : ContinuousAt (fun b : Fin m → ℂ => fderiv ℂ ζ (b, 0)) b₁ :=
      ContinuousAt.comp (g := fderiv ℂ ζ) (f := fun b : Fin m → ℂ => (b, (0 : Fin g → ℂ)))
        hζa.fderiv.continuousAt hpt.continuousAt
    have hA : ∀ᶠ b in 𝓝 b₁, AnalyticAt ℂ ζ (b, 0) :=
      Filter.Tendsto.eventually hpt.continuousAt hζa.eventually_analyticAt
    have hE : ∀ᶠ b in 𝓝 b₁, ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), e b (ζ (b, w)) = e b w ≫ α := by
      have h := hζe
      rw [nhds_prod_eq] at h
      exact h.curry
    refine ⟨fun b => (fderiv ℂ ζ (b, 0)).comp (ContinuousLinearMap.inr ℂ (Fin m → ℂ) (Fin g → ℂ)),
      hcont.clm_comp continuousAt_const, ?_⟩
    filter_upwards [hA, hE, hB'o.mem_nhds (hCB' hb₁)] with b hAb hEb hb
    intro z
    have hζb0 : e b (ζ (b, 0)) = 1 := by
      rw [hEb.self_of_nhds, hom_zero (hadd b hb), MonObj.one_comp]
    have hinr : HasFDerivAt (fun w : Fin g → ℂ => (b, w))
        (ContinuousLinearMap.inr ℂ (Fin m → ℂ) (Fin g → ℂ)) 0 := by
      exact hasFDerivAt_prodMk_right b 0
    have hder := (hAb.differentiableAt.hasFDerivAt.comp (0 : Fin g → ℂ) hinr).sub_const (ζ (b, 0))
    have hev0 : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), e b ((fun w => ζ (b, w) - ζ (b, 0)) w) = e b w ≫ α := by
      filter_upwards [hEb] with w hw
      have h1 : e b (ζ (b, w)) = e b (ζ (b, w) - ζ (b, 0)) * e b (ζ (b, 0)) := by
        rw [← hadd b hb, sub_add_cancel]
      rw [hζb0, _root_.mul_one] at h1
      rw [← h1]
      exact hw
    have key := fderiv_lift (x := fun w => e b w ≫ α) (hxadd b hb) (hadd b hb) (hsurj b hb) hr (hrad b hb)
      hder.differentiableAt hev0 z
    rw [hder.fderiv] at key
    exact key
  have hexM : ∀ b, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), b ∈ Metric.ball b₀ ε → ∀ w, e b (M w) = e b w ≫ α := by
    intro b
    by_cases hb : b ∈ Metric.ball b₀ ε
    · obtain ⟨F, -, hF⟩ := hloc b hb
      exact ⟨(F b).toLinearMap, fun _ w => hF.self_of_nhds w⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose Mf hMf using hexM
  have hPx : ∀ c ∈ Metric.ball b₀ ε, ∀ x, e c (P c x) = 1 :=
    fun c hc x => ((hball c hc).2.2.1 _).2 (AddMonoidHom.mem_range.2 ⟨x, rfl⟩)
  intro b hb
  refine ⟨Mf b, hMf b hb, ?_⟩
  intro x x' hxx'
  have hzero := eq_zero_of_small (B := Metric.ball b₀ ε) (convex_ball b₀ ε).isPreconnected
    (d := fun c => Mf c (P c x) - P c x') ?_ hr ?_ hb₀C ?_
  · exact (sub_eq_zero.1 (hzero b hb)).symm
  · intro c hc
    obtain ⟨F, hFc, hF⟩ := hloc c hc
    have hPc : ContinuousAt (fun c' => P c' x) c := ((hball c hc).2.1 x).continuousAt
    have hPc' : ContinuousAt (fun c' => P c' x') c := ((hball c hc).2.1 x').continuousAt
    have hcont : ContinuousAt (fun c' => F c' (P c' x) - P c' x') c := (hFc.clm_apply hPc).sub hPc'
    refine (hcont.congr ?_).continuousWithinAt
    filter_upwards [hF, hCo.mem_nhds hc] with c' hc' hc'C
    have hM : Mf c' = (F c').toLinearMap :=
      huniq c' (hCB' hc'C) _ _ (hMf c' hc'C) (fun w => hc' w)
    rw [hM]
    rfl
  · intro c hc hlt
    beta_reduce at hlt ⊢
    apply hrad c (hCB' hc) _ hlt
    rw [hom_sub_eq_one (hadd c (hCB' hc)), hMf c hc, hPx c hc x, hPx c hc x', MonObj.one_comp]
  · have hM : Mf b₀ = M₀ := huniq b₀ (hCB' hb₀C) _ _ (hMf b₀ hb₀C) (fun w => by rw [he0]; exact hM₀ w)
    show Mf b₀ (P b₀ x) - P b₀ x' = 0
    rw [hM, hP0, hxx', sub_self]

theorem exists_fibre {X : Scheme.{0}} {G : Over X} [GrpObj G] (hG : IsAbelianScheme G) {t t' : Sp ℂ ⟶ X} (ht : t' = t)
    {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ G.left} (hφ : IsGrpPullback A G t φ) {L : LB A.left} (hL : L.IsLB) {g : ℕ}
    {e : (Fin g → ℂ) → (Over.mk t' ⟶ G)} (he : IsExp t' e) {La : Type} [AddCommGroup La] (P : La →+ (Fin g → ℂ))
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) (hi : Function.Injective P) (hsp : Submodule.span ℝ (Set.range P) = ⊤)
    (hd : DiscreteTopology P.range) :
    ∃ (u : HolUnif A L g) (τ : La ≃+ u.Λ), (∀ w, (u.ex w).left ≫ φ = (e w).left) ∧ ∀ x, (τ x : Fin g → ℂ) = P x := by
  subst ht
  have hA : IsAbelianScheme A := by
    obtain ⟨h1, h2, h3, h4⟩ := hG
    refine ⟨?_, MorphismProperty.of_isPullback hφ.1 h2, MorphismProperty.of_isPullback hφ.1 h3,
      MorphismProperty.of_isPullback hφ.1 h4⟩
    haveI := h1
    refine ⟨?_⟩
    apply Over.OverMorphism.ext
    apply hφ.1.hom_ext
    · have hw : φ ≫ G.hom = A.hom ≫ t' := hφ.1.w
      let x₀ : Over.mk ((A ⊗ A).hom ≫ t') ⟶ G := Over.homMk ((fst A A).left ≫ φ) (by
        rw [Category.assoc, hw, ← Category.assoc, Over.w]; rfl)
      let y₀ : Over.mk ((A ⊗ A).hom ≫ t') ⟶ G := Over.homMk ((snd A A).left ≫ φ) (by
        rw [Category.assoc, hw, ← Category.assoc, Over.w]; rfl)
      have e1 := hφ.2 (A ⊗ A) (fst A A) (snd A A) x₀ y₀ rfl rfl
      have e2 := hφ.2 (A ⊗ A) (snd A A) (fst A A) y₀ x₀ rfl rfl
      have hb : (β_ A A).hom = lift (snd A A) (fst A A) := by ext <;> simp
      have m1 : fst A A * snd A A = (μ : A ⊗ A ⟶ A) := by simp [Hom.mul_def]
      have m2 : snd A A * fst A A = (β_ A A).hom ≫ (μ : A ⊗ A ⟶ A) := by rw [hb, Hom.mul_def]
      rw [← m2, ← m1, ← e1, ← e2, mul_comm]
    · exact (Over.w _).trans (Over.w _).symm
  have hcomm : IsCommMonObj A := hA.1
  obtain ⟨d, hdim⟩ : ∃ d : ℕ, SmoothOfRelativeDimension d A.hom := by
    exact GlobalTheory.AbelianDim.exists_relDim _ A hA
  obtain ⟨L₀, ⟨u₀⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A d hA hdim
  obtain ⟨u₁, -, -, -, -⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ d u₀ L hL
  have htan := GlobalTheory.TorusTransfer.tangent_bijective u₁ hdim
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv hφ (𝟙_ (Over (Sp ℂ))) t' (by simp)
  set ε : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A) := fun z => Φ.symm (e z) with hε
  have hεadd : ∀ z w, ε (z + w) = ε z * ε w := by
    intro z w; simp only [hε, he.1 z w, map_mul]
  have hεleft : ∀ z, (ε z).left ≫ φ = (e z).left := by
    intro z; rw [← hΦ]; simp [hε]
  have hεhol : IsHolTo Set.univ (fun z => (ε z).left) := by
    refine GlobalTheory.FibreUnif.isHolTo_of_isPullback hφ.1 (fun z => ?_) ?_
    · have := Over.w (ε z)
      simpa using this
    · simp only [hεleft]
      exact he.2.2.1
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA L d g u₁ htan.1 htan.2 ε hεadd hεhol
  have hker : ∀ z, ε z = 1 ↔ z ∈ P.range := by
    intro z; rw [← hk z]; simp only [hε]
    constructor
    · intro h; have := congrArg Φ h; simpa using this
    · intro h; rw [h]; simp
  obtain ⟨r, hr, hk1⟩ : ∃ r > 0, ∀ z : Fin d → ℂ, ‖z‖ < r → u₁.ex z = 1 → z = 0 := by
    have hdisc : DiscreteTopology u₁.Λ := u₁.discrete
    obtain ⟨U, hU, hU0⟩ : ∃ U ∈ 𝓝 (0 : Fin d → ℂ), ∀ z ∈ U, z ∈ u₁.Λ → z = 0 := by
      have ho := isOpen_discrete ({⟨0, u₁.Λ.zero_mem⟩} : Set u₁.Λ)
      obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.1 ho
      refine ⟨V, hV.mem_nhds ?_, fun z hz hzΛ => ?_⟩
      · have h0 : (⟨0, u₁.Λ.zero_mem⟩ : u₁.Λ) ∈ Subtype.val ⁻¹' V := by
          rw [hVeq]; exact Set.mem_singleton _
        exact h0
      · have h0 : (⟨z, hzΛ⟩ : u₁.Λ) ∈ Subtype.val ⁻¹' V := hz
        rw [hVeq] at h0
        exact congrArg Subtype.val (Set.mem_singleton_iff.1 h0)
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
    exact ⟨r, hr, fun z hz h1 => hU0 z (hball (mem_ball_zero_iff.2 hz)) ((u₁.ker z).1 h1)⟩
  have hkx : IsDiscrete {z | ε z = 1} := by
    have hs : {z | ε z = 1} = (P.range : Set (Fin g → ℂ)) := Set.ext fun z => hker z
    rw [hs]
    exact ⟨hd⟩
  have hεsurj : Function.Surjective ε := fun a => by
    obtain ⟨z, hz⟩ := he.2.1 (Φ a)
    exact ⟨z, by simp [hε, hz]⟩
  obtain ⟨Lq, hLq⟩ := GlobalTheory.LocLift.exists_linearEquiv_lift (x := ε) (e := u₁.ex) hεadd u₁.ex_add hεsurj
    u₁.ex_onto hkx hr hk1 (ζ := ⇑(LinearMap.toContinuousLinearMap F))
    (LinearMap.toContinuousLinearMap F).differentiableAt
    (Filter.Eventually.of_forall fun z => by simpa using hF z)
  have hgd : g = d := by
    have := Lq.toLinearEquiv.finrank_eq
    simpa using this
  subst hgd
  let Λ : Submodule ℤ (Fin g → ℂ) := P.range.toIntSubmodule
  have hΛd : DiscreteTopology Λ := hd
  have hΛf : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ := by
    have hs : (Λ : Set (Fin g → ℂ)) = Set.range P := by ext; simp [Λ]
    rw [hs]; exact hsp
  have hΛ : ∀ z, Lq.toLinearEquiv z ∈ u₁.Λ ↔ z ∈ Λ := by
    intro z
    rw [← u₁.ker, show u₁.ex (Lq.toLinearEquiv z) = ε z from hLq z]
    show ε z = 1 ↔ z ∈ P.range.toIntSubmodule
    exact hker z
  let u := GlobalTheory.TorusTransfer.reparam u₁ Lq.toLinearEquiv (fun _ => 0) (differentiable_const _) Λ hΛd hΛf hΛ
  have hPΛ : P.range = Λ.toAddSubgroup := by ext; simp [Λ]
  refine ⟨u, (AddMonoidHom.ofInjective hi).trans (AddEquiv.addSubgroupCongr hPΛ), fun w => ?_, fun x => rfl⟩
  show (u₁.ex (Lq.toLinearEquiv w)).left ≫ φ = (e w).left
  rw [show u₁.ex (Lq.toLinearEquiv w) = ε w from hLq w, hεleft]

private theorem nonempty_addEquiv_of_discrete_span_eq_univ {g : ℕ} (Λ Λ' : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [DiscreteTopology Λ'] (h : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (h' : Submodule.span ℝ (Λ' : Set (Fin g → ℂ)) = ⊤) : Nonempty (Λ ≃+ Λ') := by
  have : IsZLattice ℝ Λ := ⟨h⟩
  have : IsZLattice ℝ Λ' := ⟨h'⟩
  exact ⟨(LinearEquiv.ofFinrankEq Λ Λ' ((ZLattice.rank ℝ Λ).trans (ZLattice.rank ℝ Λ').symm)).toAddEquiv⟩

theorem exists_any {A : Over (Sp ℂ)} [GrpObj A] (hA : IsAbelianScheme A) {g : ℕ} (hg : SmoothOfRelativeDimension g A.hom)
    {L : LB A.left} (hL : L.IsLB) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hf : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) : ∃ u : HolUnif A L g, Nonempty (Λ ≃+ u.Λ) := by
  obtain ⟨L₀, ⟨u₀⟩⟩ := HomDescentQb.exists_holUnif A g hA hg
  have : IsCommMonObj A := hA.comm
  obtain ⟨u, -⟩ := exists_isFactorAH_frame_of_unif A hA L₀ g u₀ L hL
  have : DiscreteTopology u.Λ := u.discrete
  exact ⟨u, nonempty_addEquiv_of_discrete_span_eq_univ Λ u.Λ hf u.full⟩

theorem famUnif_holds : FamUnif := by
  intro B _ _ _ 𝒜 _ g h𝒜 hg I _ _ U y hU h0U hy A _ φ hφ L hL A₀ _ φ₀ hφ₀ L₀ u₀

  let eI : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let ψ : (Fin (Fintype.card I) → ℂ) ≃L[ℂ] (I → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : I => ℂ) eI.symm
  let s : Sp B ⟶ Sp ℂ := spMap (algebraMap ℂ B)
  let yb : (Fin (Fintype.card I) → ℂ) → (Sp ℂ ⟶ Sp B) := fun b => spMap ((y (ψ b) : B →ₐ[ℂ] ℂ) : B →+* ℂ)
  have hψ0 : ψ 0 = 0 := map_zero ψ
  have hUo : IsOpen (ψ ⁻¹' U) := hU.preimage ψ.continuous
  have h0 : (0 : Fin (Fintype.card I) → ℂ) ∈ ψ ⁻¹' U := by simpa [Set.mem_preimage, hψ0] using h0U
  have hys : ∀ b ∈ ψ ⁻¹' U, yb b ≫ s = spMap (RingHom.id ℂ) := fun b _ =>
    PelTangent.spMap_comp _ _ _ (by ext c; simp)
  have hyb : IsHolTo (ψ ⁻¹' U) yb :=
    ThetaValueCont.isHolTo_spMap hUo (fun b => ((y (ψ b) : B →ₐ[ℂ] ℂ) : B →+* ℂ)) fun a =>
      (hy a).comp ψ.differentiable.differentiableOn (Set.mapsTo_preimage _ _)

  have hs : LocallyOfFiniteType s := by
    show LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ B)))
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)

  have : DiscreteTopology u₀.Λ := u₀.discrete
  have : IsZLattice ℝ u₀.Λ := ⟨u₀.full⟩
  let P₀ : u₀.Λ →+ (Fin g → ℂ) := u₀.Λ.subtype.toAddMonoidHom
  have hi : Function.Injective P₀ := Subtype.val_injective
  have hsp : Submodule.span ℝ (Set.range P₀) = ⊤ := by
    simpa [P₀, Subtype.range_coe] using u₀.full

  have hbc : ∀ (f : B →+* ℂ) (A' : Over (Sp ℂ)) [GrpObj A'] (φ' : A'.left ⟶ 𝒜.left),
      IsGrpPullback A' 𝒜 (spMap f) φ' → IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom := by
    intro f A' _ φ' hpb
    obtain ⟨hc, hsm, hpr, hgc⟩ := h𝒜
    have hp := hpb.1
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
    have : IsCommMonObj 𝒜 := hc
    have key : ∀ (T : Over (Sp ℂ)) (x y : T ⟶ A'), x * y = y * x := by
      intro T x y
      let x₀ : Over.mk (T.hom ≫ spMap f) ⟶ 𝒜 := Over.homMk (x.left ≫ φ') (by
        simp only [Over.mk_hom, Category.assoc, hpb.1.w, Over.w_assoc])
      let y₀ : Over.mk (T.hom ≫ spMap f) ⟶ 𝒜 := Over.homMk (y.left ≫ φ') (by
        simp only [Over.mk_hom, Category.assoc, hpb.1.w, Over.w_assoc])
      have h1 := hpb.2 T x y x₀ y₀ rfl rfl
      have h2 := hpb.2 T y x y₀ x₀ rfl rfl
      apply Over.OverMorphism.ext
      apply hpb.1.hom_ext
      · rw [← h1, ← h2, mul_comm]
      · simp
    have hcomm : IsCommMonObj A' := ⟨by
      have := key (A' ⊗ A') (fst A' A') (snd A' A')
      have hb : (β_ A' A').hom = lift (snd A' A') (fst A' A') := by ext <;> simp
      rw [hb]
      simpa [Hom.mul_def] using this.symm⟩
    exact ⟨⟨hcomm, MorphismProperty.of_isPullback (P := @Smooth) hp hsm,
      MorphismProperty.of_isPullback (P := @IsProper) hp hpr,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hp hgc⟩,
      MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hp hg⟩
  have hexp : ∃ e₀ : (Fin g → ℂ) → (Over.mk (yb 0) ⟶ 𝒜), IsExp (yb 0) e₀ ∧ (∀ z, e₀ z = 1 ↔ z ∈ P₀.range) ∧
      (∀ w, (e₀ w).left = (u₀.ex w).left ≫ φ₀) := by
    have hφ₀' : IsGrpPullback A₀ 𝒜 (yb 0) φ₀ := by simpa [yb, hψ0] using hφ₀
    have htb := TorusTransfer.tangent_bijective u₀ (hbc _ A₀ φ₀ hφ₀).2
    obtain ⟨Φ, hΦ⟩ := LiePull.exists_pushEquiv hφ₀' (𝟙_ (Over (Sp ℂ))) (yb 0) (by simp)
    refine ⟨fun z => Φ (u₀.ex z), PointUnif.isExp_push hφ₀' u₀ htb.1 htb.2 Φ hΦ, fun z => ?_, fun w => hΦ _⟩
    rw [MulEquiv.map_eq_one_iff, u₀.ker z]
    exact ⟨fun h => ⟨⟨z, h⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.2⟩
  obtain ⟨e₀, he₀, hk, he₀u⟩ := hexp
  obtain ⟨C, e, P, hCo, hC0, hCB, he0, hP0, hhol, hfib, hdiff, hend⟩ :=
    exists_core s 𝒜 e₀ hs h𝒜 hg hUo h0 hys hyb he₀ P₀ hi hsp hk
  have hAz : ∀ z, IsAbelianScheme (A z) ∧ SmoothOfRelativeDimension g (A z).hom := fun z =>
    hbc _ (A z) (φ z) (hφ z)

  have hW : ∃ (r : ℝ) (W : 𝒜.left.Opens), 0 < r ∧ IsAffineOpen W ∧
      Metric.ball (0 : I → ℂ) r ⊆ ψ.symm ⁻¹' C ∧ ∀ b ∈ C, ψ b ∈ Metric.ball (0 : I → ℂ) r → ⊤ ≤ (e b 0).left ⁻¹ᵁ W := by
    have hsub : Subsingleton (Sp ℂ : Scheme.{0}) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
    obtain ⟨q₀⟩ : Nonempty (Sp ℂ : Scheme.{0}) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
    obtain ⟨_, ⟨W, hWa, rfl⟩, hxW, -⟩ :=
      𝒜.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ((e 0 0).left.base q₀)) isOpen_univ
    have hO := ((hhol W 0).1).preimage (continuous_id.prodMk continuous_const :
      Continuous fun b : Fin (Fintype.card I) → ℂ => (b, (0 : Fin g → ℂ)))
    have h0O : (0 : Fin (Fintype.card I) → ℂ) ∈ (fun b : Fin (Fintype.card I) → ℂ => (b, (0 : Fin g → ℂ))) ⁻¹'
        {q | q ∈ C ×ˢ Set.univ ∧ ⊤ ≤ (e q.1 q.2).left ⁻¹ᵁ W} := by
      refine ⟨⟨hC0, Set.mem_univ _⟩, fun q _ => ?_⟩
      obtain rfl : q = q₀ := @Subsingleton.elim (Sp ℂ : Scheme.{0}) hsub q q₀
      exact hxW
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hO.preimage ψ.symm.continuous) 0
      (by rw [Set.mem_preimage, show ψ.symm 0 = 0 from map_zero _]; exact h0O)
    refine ⟨r, W, hr, hWa, fun z hz => (hball hz).1.1, fun b _ hb => ?_⟩
    have := (hball hb).2
    rw [ContinuousLinearEquiv.symm_apply_apply] at this
    exact this
  obtain ⟨r, W, hr, hWa, hrC, hWb⟩ := hW
  have hmem : ∀ z ∈ Metric.ball (0 : I → ℂ) r, ψ.symm z ∈ C := fun z hz => hrC hz
  have hex : ∀ z : I → ℂ, ∃ p : (Σ u : HolUnif (A z) (L z) g, u₀.Λ ≃+ u.Λ), z ∈ Metric.ball (0 : I → ℂ) r →
      (∀ w, (p.1.ex w).left ≫ φ z = (e (ψ.symm z) w).left) ∧ ∀ x, (p.2 x : Fin g → ℂ) = P (ψ.symm z) x := by
    intro z
    by_cases hz : z ∈ Metric.ball (0 : I → ℂ) r
    · have hb := hfib _ (hmem z hz)
      have ht : yb (ψ.symm z) = spMap ((y z : B →ₐ[ℂ] ℂ) : B →+* ℂ) := by simp [yb]
      obtain ⟨u, τ, hu, hτ⟩ := exists_fibre h𝒜 ht (hφ z) (hL z) hb.1 (P (ψ.symm z)) hb.2.1 hb.2.2.1 hb.2.2.2.1
        hb.2.2.2.2
      exact ⟨⟨u, τ⟩, fun _ => ⟨hu, hτ⟩⟩
    · obtain ⟨u, ⟨τ⟩⟩ := exists_any (hAz z).1 (hAz z).2 (hL z) u₀.Λ u₀.full
      exact ⟨⟨u, τ⟩, fun h => absurd h hz⟩
  choose p hp using hex
  refine ⟨r, fun z => (p z).1, fun z => (p z).2, hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have := hCB (hmem z hz)
    simpa using this
  · let β : (I → ℂ) × (Fin g → ℂ) →L[ℂ] (Fin (Fintype.card I) → ℂ) × (Fin g → ℂ) :=
      ContinuousLinearMap.prodMap (ψ.symm : (I → ℂ) →L[ℂ] (Fin (Fintype.card I) → ℂ)) (ContinuousLinearMap.id ℂ _)
    have h1 := isHolTo_comp hhol (Metric.isOpen_ball.prod isOpen_univ) β.differentiable.differentiableOn
      (fun q hq => ⟨hmem q.1 hq.1, Set.mem_univ _⟩)
    refine isHolTo_congr (isHolTo_comp_hom h1 (𝟙 _)) ?_
    intro q hq
    simpa [β] using (hp q.1 hq.1).1 q.2
  · refine ⟨W, hWa, fun z hz => ?_⟩
    have h := (hp z hz).1 0
    rw [h]
    exact hWb _ (hmem z hz) (by simpa using hz)
  · intro w
    have h := (hp 0 (Metric.mem_ball_self hr)).1 w
    rw [show ψ.symm 0 = 0 from map_zero _] at h
    rw [h, he0, he₀u]
  · intro x
    have h := (hp 0 (Metric.mem_ball_self hr)).2 x
    rw [show ψ.symm 0 = 0 from map_zero _] at h
    rw [h, hP0]
    rfl
  · intro x
    exact ((hdiff x).comp ψ.symm.differentiable.differentiableOn (fun z hz => hmem z hz)).congr
      (fun z hz => (hp z hz).2 x)
  · intro α _ M₀ hM₀ z hz
    have hM : ∀ w, e₀ (M₀ w) = e₀ w ≫ α := fun w => by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, he₀u, he₀u, hM₀ w, Category.assoc]
    obtain ⟨M, hMe, hMP⟩ := hend α M₀ hM (ψ.symm z) (hmem z hz)
    refine ⟨M, fun w => ?_, fun x x' hx => ?_⟩
    · rw [(hp z hz).1 (M w), ← Category.assoc, (hp z hz).1 w, hMe w, Over.comp_left]
    · rw [(hp z hz).2, (hp z hz).2]
      exact hMP x x' hx

end GlobalTheory.PeriodFamily
