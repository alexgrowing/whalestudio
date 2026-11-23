import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneIntegralSkewHermitianTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchIntegralScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTwoLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentHaarFundamentalDomainExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegralBisStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ThK.DescB.Nondeg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_zero_of_cartan (B : Base F E) {n : ℕ} (Y : Spc F E n)
    (h : ∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w)) : Y.J.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  let w : InfinitePlace F := Classical.arbitrary _
  let τ : E →+* ℂ := (B.emb w).1
  let M : Matrix (Fin n) (Fin n) ℂ := Complex.I • Y.J.map τ
  let v' : Fin n → ℂ := fun i => τ (v i)
  have hv' : v' ≠ 0 := fun h => hv (funext fun i => τ.injective (by simpa [v'] using congrFun h i))
  have hMv : M *ᵥ v' = 0 := by
    ext i
    have := congrArg τ (congrFun hJv i)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at this
    simp only [M, v', Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, Matrix.smul_apply, mul_assoc, ← Finset.mul_sum, this, mul_zero]
  have hx : star v' ≠ 0 := fun h => hv' (by simpa using congrArg star h)
  have := (h w).2.2 (star v') hx
  rw [star_star] at this
  change 0 < (_ ⬝ᵥ M *ᵥ v').re at this
  rw [hMv, dotProduct_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

theorem levi_mul {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {a b : UA σ Y₁.J}
    {m m' : UA σ Y.J} (ha : IsLevi (W₁ := Y₁) H 1 a m) (hb : IsLevi (W₁ := Y₁) H 1 b m') :
    IsLevi (W₁ := Y₁) H 1 (a * b) (m * m') := by
  obtain ⟨h1, h2, h3⟩ := ha
  obtain ⟨k1, k2, k3⟩ := hb
  simp only [Units.val_one, inv_one, map_one, one_smul] at h1 h2 k1 k2 ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [GlobalTheory.UnipCT.mat_mul', ← Matrix.mulVec_mulVec, k1, h1]; simp
  · rw [GlobalTheory.UnipCT.mat_mul', ← Matrix.mulVec_mulVec, k2, h2]; simp
  · rw [GlobalTheory.UnipCT.mat_mul', GlobalTheory.UnipCT.mat_mul', Matrix.mul_assoc, k3, ← Matrix.mul_assoc, h3, Matrix.mul_assoc]

theorem ct_continuous {n n₁ : ℕ} {Y : Spc F E n} (H : Plane E n n₁)
    (hcc : ∃ K : Set (unip σ Y H), IsCompact K ∧ ∀ u : unip σ Y H, ∃ γ ∈ (ratU σ Y.J).subgroupOf (unip σ Y H), γ * u ∈ K)
    (hdom : ∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1)
    {f c : UA σ Y.J → ℂ} (hct : IsCT H f c) (hf : Continuous f) (hfi : ∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x) :
    Continuous c := by
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := hdom
  have e : c = fun h => ∫ u in 𝓕, f (u.1 * h) ∂μ := funext fun h => hct μ 𝓕 hμ h𝓕 h1 h
  rw [e]
  obtain ⟨i1, -, i3, -⟩ := GlobalTheory.UnipCT.topFacts σ Y.J
  haveI := i1
  haveI : FirstCountableTopology (UA σ Y.J) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  exact GlobalTheory.CtLeviCont.continuous_setIntegral_of_cocompact hcc hfi hf μ 𝓕 (by rw [h1]; exact ENNReal.one_ne_top)

theorem alphaSpan_reg {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} (H : Plane E n n₁) (χa χb : Chr F E) (za zb : ℝ)
    (Kh : Set (UA σ Y.J)) (S : Submodule ℂ (UA σ Y.J → ℂ))
    (hcc : ∃ K : Set (unip σ Y H), IsCompact K ∧ ∀ u : unip σ Y H, ∃ γ ∈ (ratU σ Y.J).subgroupOf (unip σ Y H), γ * u ∈ K)
    (hdom : ∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1)
    (M : UA σ Y₁.J → UA σ Y.J) (hMc : Continuous M) (hML : ∀ h₁, IsLevi (W₁ := Y₁) H 1 h₁ (M h₁))
    (hMr : ∀ γ ∈ ratU σ Y₁.J, M γ ∈ ratU σ Y.J)
    (hS : ∀ f ∈ S, Continuous f ∧ ∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x)
    (hβ : BetaZero Y₁ H χa χb za zb S) :
    ∀ g ∈ alphaSpan Y₁ H χa χb za zb Kh S, Continuous g ∧ ∀ γ ∈ ratU σ Y₁.J, ∀ x, g (γ * x) = g x := by
  obtain ⟨i1, -, -, -⟩ := GlobalTheory.UnipCT.topFacts σ Y.J
  haveI := i1
  intro g hg
  unfold alphaSpan at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, fa, fb, hs, h, -, -, hx'⟩ := hx
    have hfb := hβ f hf fa fb hs
    subst hfb
    have hct : IsCT H f fa := by simpa using hs.1
    obtain ⟨hfc, hfi⟩ := hS f hf
    have hfac := ct_continuous H hcc hdom hct hfc hfi
    have ex : x = fun h₁ => fa (M h₁ * h) := funext fun h₁ => hx' h₁ (M h₁) (hML h₁)
    refine ⟨?_, fun γ hγ y => ?_⟩
    · rw [ex]; exact hfac.comp (hMc.mul continuous_const)
    · rw [hx' (γ * y) (M γ * M y) (levi_mul (hML γ) (hML y)), ex, mul_assoc]
      exact GlobalTheory.T.constant_term_unipotent_integral_bis H f fa hct hfi hdom γ (M γ) (hML γ) (hMr γ hγ) _
  | zero => exact ⟨continuous_const, fun _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    exact ⟨hx.1.add hy.1, fun γ hγ z => by simp only [Pi.add_apply, hx.2 γ hγ z, hy.2 γ hγ z]⟩
  | smul r x _ hx =>
    exact ⟨continuous_const.mul hx.1, fun γ hγ z => by simp only [Pi.smul_apply, smul_eq_mul, hx.2 γ hγ z]⟩

theorem diffs_reg (hK : KP) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'} (hM : IsMatched B G X om om' R Rf) (c : ℂ) :
    ∀ f ∈ Diffs B G X om om' R Rf c, Continuous f ∧ ∀ γ ∈ ratU σ G.W.J, ∀ x, f (γ * x) = f x := by
  intro f hf
  unfold Diffs at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Φ, Φ', hΦ', hm, rfl⟩ := hx
    obtain ⟨hP, hP'⟩ := GlobalTheory.ThKSelfOrth.polData_of_polMatch hm
    obtain ⟨c1, i1⟩ := GlobalTheory.T.continuous_left_invariant_theta hK F E σ B a a' G X om om' hM.triple Φ hP
    obtain ⟨c2, i2⟩ := GlobalTheory.T.continuous_left_invariant_dual hK F E σ B a a' G X om om' hM.triple Φ' ⟨hP', hΦ'⟩
    refine ⟨c1.sub (continuous_const.mul c2), fun γ hγ y => ?_⟩
    simp only [i1 γ hγ, i2 γ hγ]
  | zero => exact ⟨continuous_const, fun _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    exact ⟨hx.1.add hy.1, fun γ hγ z => by simp only [Pi.add_apply, hx.2 γ hγ z, hy.2 γ hγ z]⟩
  | smul r x _ hx =>
    exact ⟨continuous_const.mul hx.1, fun γ hγ z => by simp only [Pi.smul_apply, smul_eq_mul, hx.2 γ hγ z]⟩

theorem lev_reg (hK : KP) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'} (hM : IsMatched B G X om om' R Rf)
    {d₁ : ℕ} {H' : Plane E (a + a') d₁} {i₀ i₁ : ℕ} {sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j)}
    {pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))} (hH : H'.IsAdapted σ B G.W (sp 0) i₀ i₁)
    (hiso : ∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) (c : ℂ)
    (h0 : BetaZero (sp 0) H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (Diffs B G X om om' R Rf c))
    (hj : ∀ j < G.p, BetaZero (sp (j + 1)) (pl j) X.α X.β ((a' : ℝ) / 2) (zb a j)
      (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) j)) :
    ∀ i < G.p, ∀ f ∈ Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) i,
      Continuous f ∧ ∀ γ ∈ ratU σ (sp i).J, ∀ x, f (γ * x) = f x := by
  have hT := hM.triple
  have hcm := hT.base.cm
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hsk := NextStep.skew_sp hσ B hT.geo.hW.skew hH hiso
  intro i
  induction i with
  | zero =>
    intro hp f hf
    rw [lev_zero] at hf
    have hI := hiso 0 hp
    have hdet1 : (sp 0).J.det ≠ 0 := det_ne_zero_of_cartan B (sp 0) hI.2.2.2.2.2.2.1
    obtain ⟨M, hMc, hML, hMr⟩ := GlobalTheory.T.hyperbolic_plane_complement_form G.W (sp 0) H' hσ hT.geo.hW.skew hH.rank hH.xx hH.yy hH.xy hH.orth
      hH.gram hdet1
    have hcc := GlobalTheory.T.hyperbolic_plane_complement_det G.W (sp 0) H' hcm hT.geo.hW.skew hH.rank hH.xx hH.yy hH.xy hH.orth hH.gram
      (det_ne_zero_of_cartan B G.W hT.geo.hW.cartan) hdet1
    obtain ⟨μ, 𝓕, hμ, h𝓕, h1, -⟩ := GlobalTheory.T.unipotent_haar_fundamental_domain_exists F E σ B a a' G X om om' hK hT d₁ (sp 0) H' i₀ i₁ hH
    exact alphaSpan_reg H' _ _ _ _ _ _ hcc ⟨μ, 𝓕, hμ, h𝓕, h1⟩ M hMc hML hMr (diffs_reg hK hM c) h0 f hf
  | succ j ih =>
    intro hp f hf
    rw [lev_succ] at hf
    have hI := hiso j (by omega)
    have hdet0 := det_ne_zero_of_cartan B (sp j) hI.2.2.2.2.2.2.1
    have hdet1 := det_ne_zero_of_cartan B (sp (j + 1)) hI.2.2.2.2.2.2.2
    have hskj := hsk j (by omega)
    obtain ⟨M, hMc, hML, hMr⟩ := GlobalTheory.T.hyperbolic_plane_complement_form (sp j) (sp (j + 1)) (pl j) hσ hskj hI.1 hI.2.1 hI.2.2.1 hI.2.2.2.1
      hI.2.2.2.2.1 hI.2.2.2.2.2.1 hdet1
    have hcc := GlobalTheory.T.hyperbolic_plane_complement_det (sp j) (sp (j + 1)) (pl j) hcm hskj hI.1 hI.2.1 hI.2.2.1 hI.2.2.2.1
      hI.2.2.2.2.1 hI.2.2.2.2.2.1 hdet0 hdet1
    have hdom := GlobalTheory.T.unipotent_quotient_unit_volume F E σ B hT.base _ _ (sp j) (sp (j + 1)) (pl j) hskj hI
    exact alphaSpan_reg (pl j) _ _ _ _ _ _ hcc hdom M hMc hML hMr (ih (by omega)) (hj j (by omega)) f hf

end GlobalTheory.ThK.DescB.Nondeg
