import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOHZeroRight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPa
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfIsTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
open scoped ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ContrSmooth

section Gen

variable {X E : Type} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

def LocSm (K : X → E → ℂ) : Prop :=
  ∀ x₀, ∃ (G : Type) (_ : NormedAddCommGroup G) (_ : NormedSpace ℝ G) (ρ : X → G) (c : X → ℂ) (F : G → E → ℂ),
    ContinuousAt ρ x₀ ∧ ContinuousAt c x₀ ∧ ContDiff ℝ ∞ (Function.uncurry F) ∧ ∀ᶠ x in 𝓝 x₀, ∀ t, K x t = c x * F (ρ x) t

theorem LocSm.continuous {K : X → E → ℂ} (h : LocSm K) : Continuous (Function.uncurry K) := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  obtain ⟨G, _, _, ρ, c, F, hρ, hc, hF, he⟩ := h p.1
  have h1 : ContinuousAt (fun q : X × E => c q.1 * Function.uncurry F (ρ q.1, q.2)) p :=
    (hc.comp continuousAt_fst).mul
      (hF.continuous.continuousAt.comp ((hρ.comp continuousAt_fst).prodMk continuousAt_snd))
  refine h1.congr ?_
  filter_upwards [continuousAt_fst.eventually he] with q hq
  exact (hq q.2).symm

theorem LocSm.differentiable {K : X → E → ℂ} (h : LocSm K) (x : X) : Differentiable ℝ (K x) := by
  obtain ⟨G, _, _, ρ, c, F, -, -, hF, he⟩ := h x
  rw [funext he.self_of_nhds]
  exact ((hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)).const_mul _

theorem LocSm.fderiv {K : X → E → ℂ} (h : LocSm K) (y : E) : LocSm fun x t => fderiv ℝ (K x) t y := by
  intro x₀
  obtain ⟨G, _, _, ρ, c, F, hρ, hc, hF, he⟩ := h x₀
  refine ⟨G, inferInstance, inferInstance, ρ, c, fun g t => _root_.fderiv ℝ (F g) t y, hρ, hc, ?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (Function.uncurry fun (p : G × E) (t : E) => F p.1 t) :=
      hF.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
    exact (ContDiff.fderiv (m := ∞) h1 contDiff_snd (by simp)).clm_apply contDiff_const
  · filter_upwards [he] with x hx t
    have hd : DifferentiableAt ℝ (F (ρ x)) t :=
      (hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) t
    rw [funext hx, fderiv_const_mul hd]
    rfl

theorem LocSm.mul {K K' : X → E → ℂ} (h : LocSm K) (h' : LocSm K') : LocSm fun x t => K x t * K' x t := by
  intro x₀
  obtain ⟨G, _, _, ρ, c, F, hρ, hc, hF, he⟩ := h x₀
  obtain ⟨G', _, _, ρ', c', F', hρ', hc', hF', he'⟩ := h' x₀
  refine ⟨G × G', inferInstance, inferInstance, fun x => (ρ x, ρ' x), fun x => c x * c' x,
    fun g t => F g.1 t * F' g.2 t, hρ.prodMk hρ', hc.mul hc', ?_, ?_⟩
  · exact (hF.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)).mul
      (hF'.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))
  · filter_upwards [he, he'] with x hx hx' t
    rw [hx, hx']
    ring

theorem LocSm.comp {Y : Type} [TopologicalSpace Y] {K : X → E → ℂ} (h : LocSm K) {φ : Y → X} (hφ : Continuous φ) :
    LocSm fun y => K (φ y) := by
  intro y₀
  obtain ⟨G, _, _, ρ, c, F, hρ, hc, hF, he⟩ := h (φ y₀)
  exact ⟨G, inferInstance, inferInstance, ρ ∘ φ, c ∘ φ, F, hρ.comp hφ.continuousAt, hc.comp hφ.continuousAt, hF,
    hφ.continuousAt.eventually he⟩

theorem LocSm.continuous_fderiv [FiniteDimensional ℝ E] {K : X → E → ℂ} (h : LocSm K) :
    Continuous fun p : X × E => _root_.fderiv ℝ (K p.1) p.2 :=
  continuous_clm_apply.2 fun y => (h.fderiv y).continuous

end Gen

variable {D : D7}

section Int

variable {m n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem hasFDerivAt_integral (v : VolM D m n) {K : Mx D m n → E → ℂ} (h : LocSm K)
    (hp : ∀ γ ∈ ratMx D m n, ∀ x t, K (γ + x) t = K x t) (t₀ : E) :
    Integrable (fun x => fderiv ℝ (K x) t₀) (v.μ.restrict v.𝓕) ∧
      HasFDerivAt (fun t => ∫ x in v.𝓕, K x t ∂v.μ) (∫ x in v.𝓕, fderiv ℝ (K x) t₀ ∂v.μ) t₀ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  have : BorelSpace (Mx D m n) := ⟨rfl⟩
  have hi := (ParCont.parCont D m n v E K h.continuous hp).1
  have hc : Continuous (Function.uncurry fun x t => ((‖fderiv ℝ (K x) t‖ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp h.continuous_fderiv.norm
  obtain ⟨C, hC⟩ := (ParCont.parCont D m n v E _ hc fun γ hγ x t => by rw [funext (hp γ hγ x)]).2.2.1 t₀
  have : IsFiniteMeasure (v.μ.restrict v.𝓕) := ⟨by
    rw [Measure.restrict_apply_univ, v.covol.2.2]; exact ENNReal.one_lt_top⟩
  have hm : AEStronglyMeasurable (fun x => fderiv ℝ (K x) t₀) (v.μ.restrict v.𝓕) :=
    (h.continuous_fderiv.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hC' : ∀ᶠ t in 𝓝 t₀, ∀ x, ‖fderiv ℝ (K x) t‖ ≤ C := hC.mono fun t ht x => by simpa using ht x
  refine ⟨Integrable.of_bound hm C (Filter.Eventually.of_forall hC'.self_of_nhds), ?_⟩
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun t x => K x t) (F' := fun t x => fderiv ℝ (K x) t)
    (bound := fun _ => C) hC' (Filter.Eventually.of_forall fun t => (hi t).aestronglyMeasurable) (hi t₀) hm
    (Filter.Eventually.of_forall fun x t ht => ht x) (integrable_const C)
    (Filter.Eventually.of_forall fun x t _ => (h.differentiable x t).hasFDerivAt)

theorem contDiff_integral (v : VolM D m n) {K : Mx D m n → E → ℂ} (h : LocSm K)
    (hp : ∀ γ ∈ ratMx D m n, ∀ x t, K (γ + x) t = K x t) : ContDiff ℝ ∞ fun t => ∫ x in v.𝓕, K x t ∂v.μ := by
  rw [contDiff_infty]
  intro k
  induction k generalizing K with
  | zero => exact contDiff_zero.2 (ParCont.parCont D m n v E K h.continuous hp).2.1
  | succ k ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun t => (hasFDerivAt_integral v h hp t).2.differentiableAt, by simp, fun y => ?_⟩
    have e : (fun t => fderiv ℝ (fun t => ∫ x in v.𝓕, K x t ∂v.μ) t y) = fun t => ∫ x in v.𝓕, fderiv ℝ (K x) t y ∂v.μ := by
      funext t
      rw [(hasFDerivAt_integral v h hp t).2.fderiv, ContinuousLinearMap.integral_apply (hasFDerivAt_integral v h hp t).1]
    rw [e]
    exact ih (h.fderiv y) fun γ hγ x t => by rw [funext (hp γ hγ x)]

end Int

open GlobalTheory.DualPairCompare in

theorem locSm_theta {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (M : E →+ WO S T) (hM : Continuous M)
    (h0 : ∀ t, (M t).map (finPart D) = 0) : LocSm fun x t => f (x + M t) := by
  intro x₀
  have : IsTopologicalAddGroup (AE D) := inferInstance
  have : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
  have : ContinuousSub (WO S T) := IsTopologicalAddGroup.to_continuousSub
  obtain ⟨co, c1, c2, c3⟩ := exists_coMat D T.rank S.rank
  obtain ⟨U, hU, hl⟩ := hf.level
  have hs : ContDiff ℝ ∞ fun p => f (x₀ + realMat D T.rank S.rank p) := (smoothAlong_iff f).1 hf.smooth x₀
  let N := (co.comp M).toRealLinearMap (c1.comp hM)
  have hN : ∀ t, realMat D T.rank S.rank (N t) = M t := fun t => c3 _ (h0 t)
  have hd : Continuous fun x : WO S T => x - x₀ := continuous_id.sub continuous_const
  let a : WO S T → WO S T := fun x => (x - x₀) - realMat D T.rank S.rank (co (x - x₀))
  have ha : Continuous a := hd.sub ((continuous_realMat D _ _).comp (c1.comp hd))
  have hev : ∀ᶠ x in 𝓝 x₀, a x ∈ U := (hU.preimage ha).mem_nhds (show a x₀ ∈ U by simp [a])
  have key : ∀ x, a x ∈ U → ∀ p, f (x₀ + realMat D T.rank S.rank p + a x) =
      ψ (-symplOH S T x₀ (a x)) * f (x₀ + realMat D T.rank S.rank p) := by
    intro x hx p
    have h1 := congrFun (hl _ hx (c2 _)) (x₀ + realMat D T.rank S.rank p)
    have h2 : symplOH S T (realMat D T.rank S.rank p) (a x) = 0 :=
      GlobalTheory.FinTranslate.symplOH_real_fin (c2 _) (Matrix.ext fun i j => finPart_realPt D (p i j))
    rw [heisO, GlobalTheory.FinTranslate.symplOH_add_left, h2, add_zero] at h1
    rw [← h1, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  have dec : ∀ x t, x + M t = x₀ + realMat D T.rank S.rank (co (x - x₀) + N t) + a x := by
    intro x t
    rw [map_add, hN]
    simp only [a]
    abel
  have hF : ContDiff ℝ ∞ (Function.uncurry fun p t => f (x₀ + realMat D T.rank S.rank (p + N t))) :=
    hs.comp (contDiff_fst.add (N.contDiff.comp contDiff_snd))
  by_cases hz : ∀ p, f (x₀ + realMat D T.rank S.rank p) = 0
  · refine ⟨_, inferInstance, inferInstance, fun x => co (x - x₀), fun _ => 0, _, (c1.comp hd).continuousAt,
      continuousAt_const, hF, ?_⟩
    filter_upwards [hev] with x hx t
    rw [dec, key x hx, hz, mul_zero, mul_zero]
  · obtain ⟨p, hp⟩ := not_forall.1 hz
    refine ⟨_, inferInstance, inferInstance, fun x => co (x - x₀),
      fun x => f (x₀ + realMat D T.rank S.rank p + a x) / f (x₀ + realMat D T.rank S.rank p), _, (c1.comp hd).continuousAt,
      ((hf.cont.comp (continuous_const.add ha)).div_const _).continuousAt, hF, ?_⟩
    filter_upwards [hev] with x hx t
    rw [dec, key x hx, key x hx, mul_div_cancel_right₀ _ hp]

theorem extL_fin {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO A S) (h : u.map (finPart D) = 0) :
    (ContrComb.extL (S := S) o u).map (finPart D) = 0 := by
  rw [ContrComb.extL_apply, OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
  rw [Matrix.map_mul, h, Matrix.zero_mul]

theorem extR_fin {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO S A) (h : u.map (finPart D) = 0) :
    (ContrComb.extR (S := S) o u).map (finPart D) = 0 := by
  rw [ContrComb.extR_apply, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
  rw [Matrix.map_mul, h, Matrix.mul_zero]

theorem integrand_periodic {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    {ψ : AddChar (AF D.host.F) ℂ} {f₁ : WO B.V₀ S → ℂ} {f₂ : WO S B'.V₀ → ℂ} (h₁ : IsThetaFunO ψ B.V₀ S f₁)
    (h₂ : IsThetaFunO ψ S B'.V₀ f₂) (u : WO B.A S) (v : WO S B'.A) (γ : WO S B'.L) (hγ : γ ∈ ratMx D B'.L.rank S.rank)
    (a : WO S B'.L) :
    f₂ ((B'.o.resT S).symm (v, γ + a)) * f₁ ((B.o.resS S).symm (u, l.κ S (γ + a))) =
      f₂ ((B'.o.resT S).symm (v, a)) * f₁ ((B.o.resS S).symm (u, l.κ S a)) := by
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  obtain ⟨hadd, -, hrat, -, hsym, -⟩ := GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)
  have hκ : symplOH B.L S (l.κ S γ) (l.κ S a) = -symplOH S B'.L γ a := by
    rw [symplOH, symplOH, hsym, Int.cast_one, one_mul, mul_neg]
  have r2 : (B'.o.resT S).symm (0, γ) ∈ ratMx D B'.V₀.rank S.rank := by
    refine (B'.o.mem_ratL_resT S _).2 ?_
    rw [AddEquiv.apply_symm_apply]
    exact ⟨zero_mem _, hγ⟩
  have r1 : (B.o.resS S).symm (0, l.κ S γ) ∈ ratMx D S.rank B.V₀.rank := by
    refine (B.o.mem_ratL_resS S _).2 ?_
    rw [AddEquiv.apply_symm_apply]
    exact ⟨zero_mem _, hrat γ hγ⟩
  obtain ⟨γ₂, hγ₂⟩ := r2
  obtain ⟨γ₁, hγ₁⟩ := r1
  have q2 := h₂.quasi γ₂ ((B'.o.resT S).symm (v, a))
  have q1 := h₁.quasi γ₁ ((B.o.resS S).symm (u, l.κ S a))
  have e2 : ratW B'.V₀ S γ₂ = (B'.o.resT S).symm (0, γ) := hγ₂
  have e1 : ratW S B.V₀ γ₁ = (B.o.resS S).symm (0, l.κ S γ) := hγ₁
  rw [e2, ← map_add, Prod.mk_add_mk, zero_add, B'.o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    ContrComb.symplOH_zero_left, zero_add] at q2
  rw [e1, ← map_add, Prod.mk_add_mk, zero_add, B.o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    ContrComb.symplOH_zero_left, zero_add, hκ, neg_neg] at q1
  rw [hadd, q2, q1]
  have e : ψ (-symplOH S B'.L γ a) * ψ (symplOH S B'.L γ a) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  linear_combination (f₂ ((B'.o.resT S).symm (v, a)) * f₁ ((B.o.resS S).symm (u, l.κ S a))) * e

theorem contr_isBiSmooth : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (ψ : AddChar (AF D.host.F) ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S f₁ → IsThetaFunO ψ S B'.V₀ f₂ → IsBiSmooth (contr l S vL f₁ f₂) := by
  intro D ρ σ B B' l S vL ψ f₁ f₂ h₁ h₂ n L L' hL hL' h0 h0' u v
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  have hκ : Continuous (l.κ S) := (GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)).2.1
  have k₁ := (locSm_theta h₁ ((ContrComb.extL B.o).comp L) ((ContrComb.continuous_extL B.o).comp hL)
    fun t => extL_fin B.o _ (h0 t)).comp (φ := fun w : WO S B'.L => (B.o.resS S).symm (u, l.κ S w))
    ((B.o.continuous_resS_symm S).comp (continuous_const.prodMk hκ))
  have k₂ := (locSm_theta h₂ ((ContrComb.extR B'.o).comp L') ((ContrComb.continuous_extR B'.o).comp hL')
    fun t => extR_fin B'.o _ (h0' t)).comp (φ := fun w : WO S B'.L => (B'.o.resT S).symm (v, w))
    ((B'.o.continuous_resT_symm S).comp (continuous_const.prodMk continuous_id))
  have k : LocSm fun (w : WO S B'.L) (t : Fin n → ℝ) =>
      f₂ ((B'.o.resT S).symm (v + L' t, w)) * f₁ ((B.o.resS S).symm (u + L t, l.κ S w)) := by
    convert k₂.mul k₁ using 5 with w t w t
    · rw [AddMonoidHom.comp_apply, ContrComb.extR_apply, ← map_add, Prod.mk_add_mk, add_zero]
    · rw [AddMonoidHom.comp_apply, ContrComb.extL_apply, ← map_add, Prod.mk_add_mk, add_zero]
  exact contDiff_integral vL k fun γ hγ w t => integrand_periodic l S h₁ h₂ _ _ γ hγ w

end GlobalTheory.ContrSmooth
end
