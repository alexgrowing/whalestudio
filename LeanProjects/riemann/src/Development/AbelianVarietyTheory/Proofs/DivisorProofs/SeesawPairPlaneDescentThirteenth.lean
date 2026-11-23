import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationMapAdaptedPlaneContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentFirstStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.UnipHermRatInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem incV_inj {n : ℕ} : Function.Injective (incV F (E := E) (n := n)) := fun a b h =>
  funext fun i => inclR_inj (congrFun h i)

theorem mem_unip_fix {σ : E →ₐ[F] E} {n n₁ : ℕ} {X : Spc F E n} {H : Plane E n n₁} {g : UA σ X.J}
    (hg : g ∈ unip σ X H) : mat g *ᵥ incV F H.x = incV F H.x := by
  induction hg using Subgroup.closure_induction with
  | mem g h => exact h.1
  | one => show ((1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ _ = _; simp
  | mul a b _ _ ha hb =>
    show ((a.1 * b.1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ _ = _
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (congrArg _ hb).trans ha
  | inv a _ ha =>
    have h1 : mat a⁻¹ * mat a = 1 := Units.inv_mul a.1
    calc mat a⁻¹ *ᵥ incV F H.x = mat a⁻¹ *ᵥ (mat a *ᵥ incV F H.x) := by rw [ha]
      _ = incV F H.x := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem exists_rat_mat {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : UA σ J} (hg : g ∈ ratU σ J) :
    ∃ G : Matrix (Fin n) (Fin n) E, mat g = incM F G := by
  obtain ⟨G, hG⟩ := Subgroup.mem_subgroupOf.1 hg
  exact ⟨G, by rw [mat, ← hG]; rfl⟩

theorem unitary_of_rat {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (G : Matrix (Fin n) (Fin n) E)
    (hG : mat g = incM F G) : Gᵀ * J * G.map σ = J := by
  have h' : (incM F G)ᵀ * incM F J * (incM F G).map (cA σ) = incM F J := by rw [← hG]; exact g.2
  have h3 : (incM F G).map (cA σ) = incM F (G.map σ) := by
    ext i j; simp [incM, GlobalTheory.UnipMass.cA_inclR]
  have e : incM F (Gᵀ * J * G.map σ) = incM F J := by
    rw [← h', h3]; simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  exact Matrix.map_injective inclR_inj e

theorem form_mulVec_mulVec (σ : E →ₐ[F] E) {n : ℕ} (J G : Matrix (Fin n) (Fin n) E) (hG : Gᵀ * J * G.map σ = J)
    (v w : Fin n → E) : form σ J (G *ᵥ v) (G *ᵥ w) = form σ J v w := by
  unfold form
  have : (fun i => σ ((G *ᵥ w) i)) = G.map σ *ᵥ fun i => σ (w i) := by
    funext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [this, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, hG]

theorem form_swap_herm (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (v w : Fin n → E) : form σ J w v = σ (form σ J v w) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem form_add_l (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → E) :
    form σ J (v + v') w = form σ J v w + form σ J v' w := add_dotProduct _ _ _

theorem form_sub_l (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → E) :
    form σ J (v - v') w = form σ J v w - form σ J v' w := sub_dotProduct _ _ _

theorem form_smul_l (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : E) (v w : Fin n → E) :
    form σ J (a • v) w = a * form σ J v w := smul_dotProduct _ _ _

theorem exists_split_plane (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (H : Plane E n n₁) (hn : n₁ + 2 = n)
    (hxx : form σ J H.x H.x = 0) (hyy : form σ J H.y H.y = 0) (hxy : form σ J H.x H.y = 1) (hyx : form σ J H.y H.x = 1)
    (horth : ∀ u, form σ J (H.ι *ᵥ u) H.x = 0 ∧ form σ J (H.ι *ᵥ u) H.y = 0) (hinj : Function.Injective H.ι.mulVec)
    (r : Fin n → E) : ∃ (s t : E) (u : Fin n₁ → E), r = s • H.x + H.ι *ᵥ u + t • H.y := by
  let f : (Fin n₁ → E) × E × E →ₗ[E] (Fin n → E) :=
    (Matrix.mulVecLin H.ι).coprod ((LinearMap.id.smulRight H.x).coprod (LinearMap.id.smulRight H.y))
  have hf : ∀ p : (Fin n₁ → E) × E × E, f p = H.ι *ᵥ p.1 + p.2.1 • H.x + p.2.2 • H.y := by
    intro p; simp [f, add_assoc]
  have hinjf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hf] at hp
    have h1 := congrArg (fun v => form σ J v H.y) hp
    have h2 := congrArg (fun v => form σ J v H.x) hp
    simp only [form_add_l, form_smul_l, (horth _).1, (horth _).2, hxx, hyy, hxy, hyx] at h1 h2
    have hz : ∀ w, form σ J 0 w = 0 := fun w => zero_dotProduct _
    rw [hz] at h1 h2
    have hs : p.2.1 = 0 := by simpa using h1
    have ht : p.2.2 = 0 := by simpa using h2
    rw [hs, ht, zero_smul, zero_smul, add_zero, add_zero] at hp
    have hu : p.1 = 0 := hinj (by rw [hp, Matrix.mulVec_zero])
    exact Prod.ext hu (Prod.ext hs ht)
  have hdim : Module.finrank E ((Fin n₁ → E) × E × E) = Module.finrank E (Fin n → E) := by
    simp [Module.finrank_prod, Module.finrank_fin_fun, ← hn]
  obtain ⟨p, hp⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinjf r
  refine ⟨p.2.1, p.2.2, p.1, ?_⟩
  rw [← hp, hf]; abel

theorem mul_vecMulVec' {n m d : ℕ} (G : Matrix (Fin n) (Fin m) E) (y : Fin m → E) (w : Fin d → E) :
    G * Matrix.vecMulVec y w = Matrix.vecMulVec (G *ᵥ y) w := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem incM_mul_mul_transpose {n m d d' : ℕ} (A : Matrix (Fin n) (Fin m) E) (Z : Matrix (Fin m) (Fin d') E)
    (C : Matrix (Fin d) (Fin d') E) : incM F (A * Z * Cᵀ) = incM F A * incM F Z * (incM F C)ᵀ := by
  simp only [incM, Matrix.map_mul, Matrix.transpose_map]

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ γ : UA σ X.J, γ ∈ unip σ X H → γ ∈ ratU σ X.J → ∀ Ψ ∈ schA F (Fin n × Fin d),
      thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) (om (γ, 1) Ψ))) =
        thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) Ψ)) := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he γ hγu hγr Ψ hΨ
  obtain ⟨hn, hxx, hyy, hxy, horth, hinj⟩ := hH
  have hψ : IsStd B.ψ := hP.base.std
  have hM : M.IsGood B.ψ := hP.good
  have hσ : ∀ a, σ (σ a) = a := fun a => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hP.base.cm.2.2.2, hP.base.cm.2.2.2, star_star])
  have hspl := IsUWeilPair.isUSplitting hP.weil
  have hyx : form σ X.J H.y H.x = 1 := by
    rw [form_swap_herm σ hσ hP.herm.herm, hxy, map_one]
  obtain ⟨G, hG⟩ := exists_rat_mat (inv_mem hγr)
  have hGu : Gᵀ * X.J * G.map σ = X.J := unitary_of_rat _ G hG
  have hGx : G *ᵥ H.x = H.x := incV_inj (F := F) (by
    rw [← GlobalTheory.UnipMass.incM_mulVec_incV, ← hG]; exact mem_unip_fix (inv_mem hγu))
  obtain ⟨a, t, b, hv⟩ := exists_split_plane σ X.J H hn hxx hyy hxy hyx horth hinj (G *ᵥ H.y - H.y)
  have ht : t = 0 := by
    have h0 : form σ X.J (G *ᵥ H.y - H.y) H.x = 0 := by
      rw [form_sub_l]
      conv_lhs => rw [← hGx]
      rw [form_mulVec_mulVec σ X.J G hGu, hGx, sub_self]
    rw [hv, form_add_l, form_add_l, form_smul_l, form_smul_l, hxx, (horth b).1, hyx] at h0
    linear_combination h0
  subst ht
  have hGy : G *ᵥ H.y = H.y + a • H.x + H.ι *ᵥ b := by
    rw [zero_smul, add_zero, sub_eq_iff_eq_add'] at hv
    rw [hv, add_assoc]
  have hw' : actAB (cA σ) (γ⁻¹, (1 : UA σ W.J)) (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) =
      incM F (Matrix.vecMulVec (G *ᵥ H.y) H'.x) := by
    show mat γ⁻¹ * _ * ((1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E))ᵀ = _
    rw [Units.val_one, Matrix.transpose_one, Matrix.mul_one, hG, ← GlobalTheory.ThetaExpandInv.incM_vecMulVec, incM,
      incM, ← Matrix.map_mul, mul_vecMulVec']
    rfl
  have hact : actAB (cA σ) (γ, (1 : UA σ W.J)) (actAB (cA σ) (γ⁻¹, (1 : UA σ W.J))
      (Matrix.vecMulVec (incV F H.y) (incV F H'.x))) = Matrix.vecMulVec (incV F H.y) (incV F H'.x) := by
    show mat γ * (mat γ⁻¹ * _ * ((1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E))ᵀ) *
      ((1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E))ᵀ = _
    have h1 : mat γ * mat γ⁻¹ = 1 := Units.mul_inv γ.1
    rw [Units.val_one, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have step : M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) (om (γ, 1) Ψ) =
      om (γ, 1) (M.co.rho B.ψ (incM F (Matrix.vecMulVec (G *ᵥ H.y) H'.x)) Ψ) := by
    rw [← hw', hspl.impl _ _ _ hΨ, hact]
  rw [step, GlobalTheory.T.seesaw_pair_plane_descent_first hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H
    ⟨hn, hxx, hyy, hxy, horth, hinj⟩ V₁ M₁ e hV₁ hM₁ he γ hγu _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ _ hΨ)]
  have hsum : Matrix.vecMulVec (G *ᵥ H.y) H'.x =
      Matrix.vecMulVec (a • H.x) H'.x + (H.ι * Matrix.vecMulVec b H'.x * (1 : Matrix (Fin d) (Fin d) E)ᵀ +
        Matrix.vecMulVec H.y H'.x) := by
    rw [hGy, Matrix.transpose_one, Matrix.mul_one, mul_vecMulVec', Matrix.add_vecMulVec, Matrix.add_vecMulVec]
    abel
  have hiso : incM F (Matrix.vecMulVec (a • H.x) H'.x) ∈
      ({u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} : Set (Matrix (Fin n) (Fin d) (AE F E))) := by
    refine ⟨incV F (a • H'.x), ?_⟩
    ext i j
    simp only [incM, incV, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  rw [hsum, ← GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M hψ hM,
    he.inv _ hiso _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ _ hΨ), ← GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M hψ hM,
    incM_mul_mul_transpose, he.Heisenberg₂ _ _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ _ hΨ),
    GlobalTheory.ThetaExpandInv.thetaSum_rho_rat M₁ hψ hM₁, GlobalTheory.ThetaExpandInv.incM_vecMulVec]

end GlobalTheory.UnipHermRatInv
