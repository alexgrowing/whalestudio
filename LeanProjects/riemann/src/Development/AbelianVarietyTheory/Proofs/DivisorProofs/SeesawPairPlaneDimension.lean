import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationMapAdaptedPlaneContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveHomogeneousFunctionalLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlanePairDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairPlaneIntertwiningIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairPlaneLocalFunctionalIdentityStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKExpandY

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_invol (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem form_add_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    form σ J (a + b) y = form σ J a y + form σ J b y := by
  unfold form; rw [add_dotProduct]

theorem form_smul_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    form σ J (c • a) y = c * form σ J a y := by
  unfold form; rw [smul_dotProduct, smul_eq_mul]

theorem form_swap {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j)
    (a b : Fin n → E) : form σ J a b = σ (form σ J b a) := by
  unfold form
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

end GlobalTheory.ThKExpandY

namespace GlobalTheory.ThKExpandY

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_split_vec {n d₂ : ℕ} (J : Matrix (Fin n) (Fin n) E) (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = J i j) (H : Plane E n d₂)
    (hH : d₂ + 2 = n ∧ form σ J H.x H.x = 0 ∧ form σ J H.y H.y = 0 ∧ form σ J H.x H.y = 1 ∧
        (∀ u, form σ J (H.ι *ᵥ u) H.x = 0 ∧ form σ J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec)
    (r : Fin n → E) : ∃ (s t : E) (u : Fin d₂ → E), r = s • H.x + H.ι *ᵥ u + t • H.y := by
  obtain ⟨hn, hxx, hyy, hxy, horth, hinj⟩ := hH
  have hyx : form σ J H.y H.x = 1 := by rw [form_swap J hσ hJ, hxy, map_one]
  let L : (E × E × (Fin d₂ → E)) →ₗ[E] (Fin n → E) :=
    { toFun := fun p => p.1 • H.x + H.ι *ᵥ p.2.2 + p.2.1 • H.y
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Matrix.mulVec_add, add_smul]; abel
      map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, Matrix.mulVec_smul, smul_eq_mul, mul_smul, RingHom.id_apply,
          smul_add] }
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s, t, u⟩ h
    change s • H.x + H.ι *ᵥ u + t • H.y = 0 at h
    have e1 := congrArg (fun z => form σ J z H.y) h
    have e2 := congrArg (fun z => form σ J z H.x) h
    simp only [form_add_left, form_smul_left, hxy, hyy, (horth u).2, (horth u).1, hxx, hyx] at e1 e2
    have hz : ∀ z : Fin n → E, form σ J 0 z = 0 := fun z => by unfold form; simp
    rw [hz] at e1 e2
    have hs : s = 0 := by simpa using e1
    have ht : t = 0 := by simpa using e2
    subst hs ht
    simp only [zero_smul, zero_add, add_zero] at h
    have hu : u = 0 := hinj (by rw [h, Matrix.mulVec_zero])
    subst hu; rfl
  have hdim : Module.finrank E (E × E × (Fin d₂ → E)) = Module.finrank E (Fin n → E) := by
    simp [Module.finrank_prod, Module.finrank_fin_fun, ← hn]; ring
  have hS : Function.Surjective L := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hL
  obtain ⟨⟨s, t, u⟩, hp⟩ := hS r
  exact ⟨s, t, u, hp.symm⟩

theorem exists_split_mat {n d₂ d : ℕ} (J : Matrix (Fin n) (Fin n) E) (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = J i j) (H : Plane E n d₂)
    (hH : d₂ + 2 = n ∧ form σ J H.x H.x = 0 ∧ form σ J H.y H.y = 0 ∧ form σ J H.x H.y = 1 ∧
        (∀ u, form σ J (H.ι *ᵥ u) H.x = 0 ∧ form σ J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec)
    (x : Matrix (Fin n) (Fin d) E) : ∃ (a t : Fin d → E) (U : Matrix (Fin d₂) (Fin d) E),
      x = Matrix.vecMulVec H.x a + H.ι * U + Matrix.vecMulVec H.y t := by
  choose a t u hu using fun j : Fin d => exists_split_vec J hσ hJ H hH (fun i => x i j)
  refine ⟨a, t, Matrix.of fun k j => u j k, ?_⟩
  ext i j
  have h := congrFun (hu j) i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [h]
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, dotProduct]
  ring

end GlobalTheory.ThKExpandY

namespace GlobalTheory.ThKExpandY

theorem incM_mul_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n n₁ d : ℕ} (ι : Matrix (Fin n) (Fin n₁) E) (U : Matrix (Fin n₁) (Fin d) E) :
    incM F (ι * U) = incM F ι * incM F U * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ := by
  have h1 : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  rw [h1, Matrix.transpose_one, Matrix.mul_one]
  unfold incM
  rw [Matrix.map_mul]

theorem inv : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ x : Matrix (Fin n) (Fin d) E, ∀ Ψ ∈ schA F (Fin n × Fin d), (∑' w : Fin d → E, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (M.co.rho B.ψ (incM F x) Ψ)))) = (∑' w : Fin d → E, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (Ψ)))) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₂ H hH V₁ M₁ e hJ hM₁ he x Ψ hΨ
  have hψ : IsStd B.ψ := hP.base.std
  have hM : M.IsGood B.ψ := hP.good
  obtain ⟨a, t, U, hx⟩ := exists_split_mat X.J (sigma_invol hP.base.cm) hP.herm.herm H hH x
  have key : ∀ w : Fin d → E,
      thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (M.co.rho B.ψ (incM F x) Ψ))) =
        thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F (w + t))) Ψ)) := by
    intro w
    have hsum : Matrix.vecMulVec H.y w + x =
        Matrix.vecMulVec H.x a + (H.ι * U + Matrix.vecMulVec H.y (w + t)) := by
      rw [hx, Matrix.vecMulVec_add]; abel
    have hiso : incM F (Matrix.vecMulVec H.x a) ∈
        ({u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} : Set (Matrix (Fin n) (Fin d) (AE F E))) :=
      ⟨incV F a, GlobalTheory.ThetaExpandInv.incM_vecMulVec H.x a⟩
    rw [← GlobalTheory.ThetaExpandInv.incM_vecMulVec, GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M hψ hM, hsum,
      ← GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M hψ hM,
      he.inv _ hiso _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ Ψ hΨ), ← GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M hψ hM,
      incM_mul_one', he.Heisenberg₂ _ _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ Ψ hΨ),
      GlobalTheory.ThetaExpandInv.thetaSum_rho_rat M₁ hψ hM₁, GlobalTheory.ThetaExpandInv.incM_vecMulVec]
  rw [tsum_congr key]
  exact (Equiv.addRight t).tsum_eq
    (fun w : Fin d → E => thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) Ψ)))

end GlobalTheory.ThKExpandY

namespace GlobalTheory.ThKExpandY

theorem rho_add {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (Φ Ψ : Fn F n d) :
    M.co.rho ψ u (Φ + Ψ) = M.co.rho ψ u Φ + M.co.rho ψ u Ψ := by
  funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]

theorem rho_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (c : ℂ) (Φ : Fn F n d) :
    M.co.rho ψ u (c • Φ) = c • M.co.rho ψ u Φ := by
  funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]; ring

theorem lin_of_summable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {ι : Type} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (he : ∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n₁ × Fin d₁))
    (u : ι → Matrix (Fin n) (Fin d) (AE F E))
    (hs : ∀ Ψ ∈ schA F (Fin n × Fin d), Summable fun w => thetaSum F (e (M.co.rho ψ (u w) Ψ))) :
    (∀ Ψ ∈ schA F (Fin n × Fin d), ∀ Ψ' ∈ schA F (Fin n × Fin d),
      (∑' w, thetaSum F (e (M.co.rho ψ (u w) (Ψ + Ψ')))) =
        (∑' w, thetaSum F (e (M.co.rho ψ (u w) Ψ))) + ∑' w, thetaSum F (e (M.co.rho ψ (u w) Ψ'))) ∧
    ∀ c : ℂ, ∀ Ψ : Fn F n d,
      (∑' w, thetaSum F (e (M.co.rho ψ (u w) (c • Ψ)))) = c * ∑' w, thetaSum F (e (M.co.rho ψ (u w) Ψ)) := by
  refine ⟨fun Ψ hΨ Ψ' hΨ' => ?_, fun c Ψ => ?_⟩
  · have h : ∀ w, thetaSum F (e (M.co.rho ψ (u w) (Ψ + Ψ'))) =
        thetaSum F (e (M.co.rho ψ (u w) Ψ)) + thetaSum F (e (M.co.rho ψ (u w) Ψ')) := fun w => by
      rw [rho_add, map_add]
      exact GlobalTheory.WeilM.thetaSum_add F (he _ (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ _ Ψ hΨ))
        (he _ (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ _ Ψ' hΨ'))
    rw [tsum_congr h]
    exact (hs Ψ hΨ).tsum_add (hs Ψ' hΨ')
  · have h : ∀ w, thetaSum F (e (M.co.rho ψ (u w) (c • Ψ))) = c * thetaSum F (e (M.co.rho ψ (u w) Ψ)) := fun w => by
      rw [rho_smul, map_smul]
      exact GlobalTheory.WeilM.thetaSum_smul F c _
    rw [tsum_congr h, tsum_mul_left]

theorem thetaSum_eq_mixedY : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∃ C₀ : ℂ, C₀ ≠ 0 ∧ ∀ Ψ ∈ schA F (Fin n × Fin d),
      Summable (fun w : Fin d → E => thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (Ψ)))) ∧ thetaSum F Ψ = C₀ * ∑' w : Fin d → E, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (Ψ))) := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ _ d₂ H hH V₁ M₁ e hJ hM₁ hev
  have hs := GlobalTheory.T.hyperbolic_plane_pair_decomposition hKP F E σ B n d X W M χX χW om r s r' s' hP d₂ H hH V₁ M₁ e hJ hM₁ hev
  obtain ⟨hl1, hl2⟩ := lin_of_summable M B.ψ hP.base.std e hev.maps _ hs
  obtain ⟨c, hc⟩ := GlobalTheory.T.additive_homogeneous_functional_linear hKP F E σ B n d X W M hP.base hP.good ⟨r, s, r', s', hP.herm, hP.skew⟩
    (fun Ψ => ∑' w : Fin d → E, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) Ψ)))
    hl1 (fun c Ψ _ => hl2 c Ψ)
    (GlobalTheory.T.pair_plane_intertwining_integral hKP F E σ B n d X W M χX χW om r s r' s' hP d₂ H hH V₁ M₁ e hJ hM₁ hev)
    (inv hKP F E σ B n d X W M χX χW om r s r' s' hP d₂ H hH V₁ M₁ e hJ hM₁ hev)
  obtain ⟨Ψ₀, hΨ₀, hne⟩ := GlobalTheory.T.pair_plane_local_functional_identity hKP F E σ B n d X W M χX χW om r s r' s' hP d₂ H hH V₁ M₁ e hJ hM₁ hev
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hc Ψ₀ hΨ₀)
  refine ⟨c⁻¹, inv_ne_zero hc0, fun Ψ hΨ => ⟨hs Ψ hΨ, ?_⟩⟩
  have := hc Ψ hΨ
  beta_reduce at this
  rw [this, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

end GlobalTheory.ThKExpandY
