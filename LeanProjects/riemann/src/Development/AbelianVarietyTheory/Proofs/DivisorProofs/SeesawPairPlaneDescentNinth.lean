import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationMapAdaptedPlaneContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementSplitBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingVectorPreserves
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentFirstStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.UnipThetaTermX

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem incM_injective {m k : Type} : Function.Injective (incM (E := E) F : Matrix m k E → Matrix m k (AE F E)) :=
  Matrix.map_injective inclR_inj

theorem incV_injective {m : ℕ} : Function.Injective (incV (E := E) F : (Fin m → E) → Fin m → AE F E) :=
  fun a b h => funext fun i => inclR_inj (congrFun h i)

theorem unip_fix {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁} (u : UA σ W.J) (hu : u ∈ unip σ W H') :
    mat u *ᵥ incV F H'.x = incV F H'.x := by
  induction hu using Subgroup.closure_induction with
  | mem x hx => exact hx.1
  | one => exact Matrix.one_mulVec _
  | mul x y _ _ hx hy => rw [GlobalTheory.UnipLine.mulVec_mul, hy, hx]
  | inv x _ hx => exact GlobalTheory.UnipLine.inv_mulVec_of_mulVec hx

theorem rat_mat {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (γ : UA σ J) (hγ : γ ∈ ratU σ J) :
    ∃ h : Matrix (Fin d) (Fin d) E, mat γ = incM F h := by
  obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.mp hγ
  exact ⟨g.1, by rw [mat, ← hg]; rfl⟩

theorem unitary_of_rat {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (γ : UA σ J) (h : Matrix (Fin d) (Fin d) E)
    (hh : mat γ = incM F h) : hᵀ * J * h.map σ = J := by
  apply incM_injective (F := F)
  have hU : (mat γ)ᵀ * incM F J * (mat γ).map (cA σ) = incM F J := γ.2
  rw [hh] at hU
  rw [← hU]
  have e : (incM F h).map (cA σ) = incM F (h.map σ) := by
    ext i j; simp only [incM, Matrix.map_apply]; exact GlobalTheory.UnipLine.cA_inclR _
  rw [e]
  unfold incM
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

theorem form_mulVec {d : ℕ} {J h : Matrix (Fin d) (Fin d) E} (hU : hᵀ * J * h.map σ = J) (a b : Fin d → E) :
    form σ J (h *ᵥ a) (h *ᵥ b) = form σ J a b := by
  unfold form
  have e1 : (fun i => σ ((h *ᵥ b) i)) = h.map σ *ᵥ fun i => σ (b i) := by
    funext i; exact RingHom.map_mulVec (σ : E →+* E) h b i
  rw [e1, Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    dotProduct_comm, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hU]

theorem form_add_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J (a + b) c = form σ J a c + form σ J b c := by
  simp only [form, add_dotProduct]

theorem form_smul_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (t : E) (a c : Fin n → E) :
    form σ J (t • a) c = t * form σ J a c := by
  simp only [form, smul_dotProduct, smul_eq_mul]

theorem form_zero_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : Fin n → E) : form σ J 0 c = 0 := by
  simp only [form, zero_dotProduct]

theorem form_herm_swap {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = J i j) (v w : Fin n → E) : form σ J v w = σ (form σ J w v) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem span_plane {n d₂ : ℕ} (J : Matrix (Fin n) (Fin n) E) (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j)
    (x y : Fin n → E) (ι : Matrix (Fin n) (Fin d₂) E) (hn : d₂ + 2 = n) (hxx : form σ J x x = 0)
    (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (hinj : Function.Injective ι.mulVec) :
    ∀ v : Fin n → E, ∃ (s t : E) (u : Fin d₂ → E), v = s • x + ι *ᵥ u + t • y := by
  let Φ : E × (Fin d₂ → E) × E →ₗ[E] (Fin n → E) :=
    (LinearMap.smulRight LinearMap.id x).comp (LinearMap.fst E E ((Fin d₂ → E) × E)) +
    (Matrix.mulVecLin ι).comp ((LinearMap.fst E (Fin d₂ → E) E).comp (LinearMap.snd E E ((Fin d₂ → E) × E))) +
    (LinearMap.smulRight LinearMap.id y).comp ((LinearMap.snd E (Fin d₂ → E) E).comp (LinearMap.snd E E ((Fin d₂ → E) × E)))
  have hΦ : ∀ s u r, Φ (s, u, r) = s • x + ι *ᵥ u + r • y := fun s u r => by simp [Φ]
  have hyx : form σ J y x = 1 := by rw [form_herm_swap hσ hJ, hxy, map_one]
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s, u, r⟩ h
    rw [hΦ] at h
    have h1 := congrArg (fun v => form σ J v y) h
    have h2 := congrArg (fun v => form σ J v x) h
    simp only [form_add_left, form_smul_left, hxy, hyy, hxx, hyx, (horth u).1, (horth u).2, form_zero_left] at h1 h2
    have hs : s = 0 := by simpa using h1
    have hr : r = 0 := by simpa using h2
    subst hs hr
    have hu : ι *ᵥ u = 0 := by simpa using h
    have hu0 : u = 0 := hinj (by rw [hu, Matrix.mulVec_zero])
    simp [hu0]
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp; omega)).mp hΦinj
  intro v
  obtain ⟨⟨s, u, r⟩, h⟩ := hsurj v
  exact ⟨s, r, u, by rw [← h, hΦ]⟩

theorem mul_vecMulVec' {n d : ℕ} (h : Matrix (Fin n) (Fin n) E) (y : Fin n → E) (w : Fin d → E) :
    h * Matrix.vecMulVec y w = Matrix.vecMulVec (h *ᵥ y) w := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem incM_mul_one {n d d₂ : ℕ} (ι : Matrix (Fin n) (Fin d₂) E) (U : Matrix (Fin d₂) (Fin d) E) :
    incM F (ι * U) = incM F ι * incM F U * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ := by
  have h1 : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  rw [h1, Matrix.transpose_one, Matrix.mul_one]
  unfold incM
  rw [Matrix.map_mul]

theorem vecMulVec_split {n d d₂ : ℕ} (x y : Fin n → E) (ι : Matrix (Fin n) (Fin d₂) E) (s : E) (a : Fin d₂ → E)
    (w : Fin d → E) :
    Matrix.vecMulVec (s • x + ι *ᵥ a + y) w =
      Matrix.vecMulVec x (s • w) + (ι * Matrix.vecMulVec a w + Matrix.vecMulVec y w) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, add_mul, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun k _ => mul_assoc (ι i k) (a k) (w j)]
  ring

end GlobalTheory.UnipThetaTermX

open GlobalTheory.UnipThetaTermX in

theorem GlobalTheory.UnipThetaTermX.main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ (w : Fin d → E) (γ u : unip σ X H), γ.1 ∈ ratU σ X.J →
      thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om ((γ * u).1, 1) Ψ))) = thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ))) := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he Ψ hΨ w γ u hγ
  have hev := GlobalTheory.T.seesaw_pair_plane_descent_first hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he
  obtain ⟨hn, hxx, hyy, hxy, horth, hinj⟩ := hH
  have hB := hP.base
  have hψ : IsStd B.ψ := hB.std
  have hM := hP.good
  have hS := hP.weil.isUSplitting
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hB.cm
  have rmem : ∀ (z : Matrix (Fin n) (Fin d) (AE F E)) (Φ : Fn F n d), Φ ∈ schA F (Fin n × Fin d) →
      M.co.rho B.ψ z Φ ∈ schA F (Fin n × Fin d) := fun z Φ hΦ => GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ z Φ hΦ
  have hYs : om (u.1, 1) Ψ ∈ schA F (Fin n × Fin d) := hS.pres _ _ hΨ
  have hsplit : om ((γ * u).1, 1) Ψ = om (γ.1, 1) (om (u.1, 1) Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]; rfl
  obtain ⟨h, hh⟩ := rat_mat (γ.1⁻¹) (inv_mem hγ)
  have hU := unitary_of_rat _ h hh
  have hfix : h *ᵥ H.x = H.x := by
    apply incV_injective (F := F)
    rw [← GlobalTheory.UnipLine.incM_mulVec_incV, ← hh]
    exact unip_fix _ (inv_mem γ.2)
  have hA : Matrix.vecMulVec (incV F H.y) (incV F w) = incM F (Matrix.vecMulVec H.y w) :=
    (GlobalTheory.ThetaExpandInv.incM_vecMulVec H.y w).symm
  have hact : actAB (cA σ) (γ.1, (1 : UA σ W.J)) (incM F (Matrix.vecMulVec (h *ᵥ H.y) w)) =
      Matrix.vecMulVec (incV F H.y) (incV F w) := by
    have e1 : incM F (Matrix.vecMulVec (h *ᵥ H.y) w) = mat γ.1⁻¹ * Matrix.vecMulVec (incV F H.y) (incV F w) := by
      rw [← mul_vecMulVec', hh, hA]
      unfold incM
      rw [Matrix.map_mul]
    rw [e1]
    show mat γ.1 * (mat γ.1⁻¹ * Matrix.vecMulVec (incV F H.y) (incV F w)) * (1 : Matrix (Fin d) (Fin d) (AE F E))ᵀ = _
    rw [Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, ← GlobalTheory.UnipLine.mat_mul, mul_inv_cancel,
      GlobalTheory.UnipLine.mat_one, Matrix.one_mul]
  have key1 : M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (γ.1, 1) (om (u.1, 1) Ψ)) =
      om (γ.1, 1) (M.co.rho B.ψ (incM F (Matrix.vecMulVec (h *ᵥ H.y) w)) (om (u.1, 1) Ψ)) := by
    rw [hS.impl _ _ _ hYs, hact]
  rw [hsplit, key1, hev γ.1 γ.2 _ (rmem _ _ hYs)]
  obtain ⟨c, t, a, hx⟩ := span_plane X.J hσ hP.herm.herm H.x H.y H.ι hn hxx hyy hxy horth hinj (h *ᵥ H.y)
  have hyx : form σ X.J H.y H.x = 1 := by rw [form_herm_swap hσ hP.herm.herm, hxy, map_one]
  have ht : t = 1 := by
    have e2 : form σ X.J (h *ᵥ H.y) H.x = 1 := by
      conv_lhs => rw [← hfix]
      rw [form_mulVec hU, hyx]
    rw [hx, form_add_left, form_add_left, form_smul_left, form_smul_left, hxx, (horth _).1, hyx] at e2
    linear_combination e2
  rw [ht, one_smul] at hx
  have m1 : M.co.rho B.ψ (incM F (Matrix.vecMulVec H.y w)) (om (u.1, 1) Ψ) ∈ schA F (Fin n × Fin d) := rmem _ _ hYs
  have m2 := rmem (incM F (H.ι * Matrix.vecMulVec a w)) _ m1
  have hiso : incM F (Matrix.vecMulVec H.x (c • w)) ∈
      {u : Matrix (Fin n) (Fin d) (AE F E) | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} :=
    ⟨incV F (c • w), GlobalTheory.ThetaExpandInv.incM_vecMulVec H.x (c • w)⟩
  rw [hx, vecMulVec_split, ← GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M hψ hM, ← GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M hψ hM,
    he.inv _ hiso _ m2, incM_mul_one, he.Heisenberg₂ _ _ m1, GlobalTheory.ThetaExpandInv.thetaSum_rho_rat M₁ hψ hM₁, hA]
