import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerComposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationTriplePeriodCaseASecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingEvaluationIntegrandContinuousInva
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentThirteenthStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKTermCont

theorem form_symm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hcm : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    form σ J y x = σ (form σ J x y) := by
  have hσ : ∀ z, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem form_add_left {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (a b w : Fin n → E) : form σ J (a + b) w = form σ J a w + form σ J b w := by
  simp only [form, add_dotProduct]

theorem form_smul_left {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (c : E) (a w : Fin n → E) : form σ J (c • a) w = c * form σ J a w := by
  simp only [form, smul_dotProduct, smul_eq_mul]

theorem form_zero_left {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (w : Fin n → E) : form σ J 0 w = 0 := by
  simp only [form, zero_dotProduct]

theorem span_plane {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hcm : IsCMExt F E σ) {n d₂ : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = J i j) (H : Plane E n d₂)
    (hn : d₂ + 2 = n) (hxx : form σ J H.x H.x = 0) (hyy : form σ J H.y H.y = 0) (hxy : form σ J H.x H.y = 1)
    (horth : ∀ u, form σ J (H.ι *ᵥ u) H.x = 0 ∧ form σ J (H.ι *ᵥ u) H.y = 0) (hinj : Function.Injective H.ι.mulVec) :
    ∀ v : Fin n → E, ∃ (s t : E) (u : Fin d₂ → E), v = s • H.x + H.ι *ᵥ u + t • H.y := by
  let L : ((E × E) × (Fin d₂ → E)) →ₗ[E] (Fin n → E) :=
    { toFun := fun p => p.1.1 • H.x + H.ι *ᵥ p.2 + p.1.2 • H.y
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Matrix.mulVec_add, add_smul]; abel
      map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, Matrix.mulVec_smul, smul_eq_mul, mul_smul, RingHom.id_apply,
          smul_add] }
  have hyx : form σ J H.y H.x = 1 := by rw [form_symm hcm hJ, hxy, map_one]
  have hinjL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨s, t⟩, u⟩ hp
    have hp' : s • H.x + H.ι *ᵥ u + t • H.y = 0 := hp
    have h1 := congrArg (fun v => form σ J v H.y) hp'
    have h2 := congrArg (fun v => form σ J v H.x) hp'
    simp only [form_add_left, form_smul_left, form_zero_left, hxy, hyy, (horth u).1, (horth u).2, hxx, hyx] at h1 h2
    have hs : s = 0 := by simpa using h1
    have ht : t = 0 := by simpa using h2
    subst hs ht
    have hu : H.ι *ᵥ u = H.ι *ᵥ 0 := by simpa using hp'
    have := hinj hu
    subst this
    rfl
  have hsurj : Function.Surjective L := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinjL
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun]
    omega
  intro v
  obtain ⟨⟨⟨s, t⟩, u⟩, hp⟩ := hsurj v
  exact ⟨s, t, u, hp.symm⟩

theorem cont : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ (μ : Measure (unip σ X H)) (𝓕 : Set (unip σ X H)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕 μ → μ 𝓕 = 1 →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∀ g : UA σ X.J,
      Continuous fun h : UA σ W.J => ∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) (om (u.1, 1) (om (g, h) Φ)))) ∂μ := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hHc V₁ M₁ e hJ hM₁ hev μ 𝓕 hμ h𝓕 h1 Φ hΦ g
  obtain ⟨hn, hxx, hyy, hxy, horth, hinj⟩ := hHc
  set z := Matrix.vecMulVec (incV F H.y) (incV F H'.x) with hz
  obtain ⟨l₀, hl₀, hl₀'⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin d₂ × Fin d)
  have hl₁ := GlobalTheory.ThKEvAdm.comp_mem_adm F E σ B n d d₂ d X W V₁ W M M₁ H.ι 1 _ e hP.good hM₁ hev l₀ hl₀
  have hl := GlobalTheory.ThKPointCont.comp_schrLin_mem_adm B.ψ hP.base.std (M.co.e z) _ hl₁
  have hS := IsUWeilPair.isUSplitting hP.weil
  have hrho : ∀ Ψ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ z Ψ ∈ schA F (Fin n × Fin d) := by
    have : schA F (Fin n × Fin d) ≤ (schA F (Fin n × Fin d)).comap (GlobalTheory.ThKPointCont.schrLin B.ψ (M.co.e z)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, g', hg', rfl⟩
      obtain ⟨T, g'', hg'', hT⟩ := GlobalTheory.ThetaHeisCLM.exists_schr_pureA_eq B.ψ hP.base.std (M.co.e z) hg'
      show schr B.ψ (M.co.e z) (pureA F f g') ∈ schA F (Fin n × Fin d)
      rw [hT f]
      exact Submodule.subset_span ⟨T f, g'', hg'', rfl⟩
    exact fun Ψ hΨ => this hΨ
  have hlval : ∀ Ψ ∈ schA F (Fin n × Fin d),
      ((l₀ ∘ₗ e) ∘ₗ GlobalTheory.ThKPointCont.schrLin B.ψ (M.co.e z)) Ψ = thetaSum F (e (M.co.rho B.ψ z Ψ)) := fun Ψ hΨ =>
    hl₀' _ (hev.maps _ (hrho Ψ hΨ))
  let K : unip σ X H → UA σ W.J → ℂ := fun u h =>
    ((l₀ ∘ₗ e) ∘ₗ GlobalTheory.ThKPointCont.schrLin B.ψ (M.co.e z)) (om (u.1 * g, h) Φ)
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnipCT.topFacts (F := F) σ X.J
  obtain ⟨hTG', hLC', hSC', hT2'⟩ := GlobalTheory.UnipCT.topFacts (F := F) σ W.J
  have hKc : Continuous fun q : unip σ X H × UA σ W.J => K q.1 q.2 :=
    (hP.weil.2.2 _ hl Φ hΦ).comp
      (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)
  have hKeq : ∀ (u : unip σ X H) h,
      thetaSum F (e (M.co.rho B.ψ z (om (u.1, 1) (om (g, h) Φ)))) = K u h := by
    intro u h
    have : om (u.1, 1) (om (g, h) Φ) = om (u.1 * g, h) Φ := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
    rw [this]
    exact (hlval _ (hS.pres _ Φ hΦ)).symm
  have hinv : ∀ γ ∈ (ratU σ X.J).subgroupOf (unip σ X H), ∀ (u : unip σ X H) h, K (γ * u) h = K u h := by
    intro γ hγ u h
    have hsplit : om ((γ * u).1 * g, h) Φ = om (γ.1, 1) (om (u.1 * g, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, Subgroup.coe_mul, mul_assoc]
    have hΨ : om (u.1 * g, h) Φ ∈ schA F (Fin n × Fin d) := hS.pres _ Φ hΦ
    show ((l₀ ∘ₗ e) ∘ₗ _) (om ((γ * u).1 * g, h) Φ) = ((l₀ ∘ₗ e) ∘ₗ _) (om (u.1 * g, h) Φ)
    rw [hsplit, hlval _ (hS.pres _ _ hΨ), hlval _ hΨ]
    exact GlobalTheory.T.seesaw_pair_plane_descent_thirteenth hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H
      ⟨hn, hxx, hyy, hxy, horth, hinj⟩ V₁ M₁ e hJ hM₁ hev γ.1 γ.2 (Subgroup.mem_subgroupOf.1 hγ) _ hΨ
  have hspan := span_plane hP.base.cm hP.herm.herm H hn hxx hyy hxy horth hinj
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.UnipHermCover.cocompact_herm F E σ hP.base.cm n d₂ X H hP.herm.herm hxx hyy hxy horth hspan
  have hcov' : ∀ u : unip σ X H, ∃ γ ∈ (ratU σ X.J).subgroupOf (unip σ X H), γ * u ∈ C := fun u => by
    obtain ⟨γ, hγ⟩ := hcov u
    exact ⟨γ.1, γ.2, by simpa [Subgroup.smul_def] using hγ⟩
  haveI := hTG; haveI := hLC; haveI := hSC; haveI := hT2
  haveI := hTG'; haveI := hLC'; haveI := hSC'; haveI := hT2'
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI := GlobalTheory.UnipCT.countable_ratU (σ := σ) X.J
  haveI : Countable ((ratU σ X.J).subgroupOf (unip σ X H)) :=
    Function.Injective.countable (f := fun γ : (ratU σ X.J).subgroupOf (unip σ X H) => (⟨γ.1.1, γ.2⟩ : ratU σ X.J))
      fun a b hab => by
        apply Subtype.ext; apply Subtype.ext
        simpa using congrArg Subtype.val hab
  haveI := hμ
  haveI : FirstCountableTopology (UA σ W.J) := by
    first
      | exact @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ hSC'
      | exact @SecondCountableTopology.to_firstCountableTopology _ _ hSC'
  have hm := GlobalTheory.Unf.EvalInv.mean_continuous hC hcov' h𝓕 K hKc hinv
  simpa only [hKeq] using hm.2

end GlobalTheory.ThKTermCont

end
