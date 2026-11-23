import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationMapAdaptedPlaneContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentFirstStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.RatUnipTheta

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem inclR_injective : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (R := F) (A := AF F) (B := E)
    (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F)

theorem cA_inclR (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

theorem conj_conj (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

omit [NumberField F] [NumberField E] in
theorem form_swap {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (hσ : ∀ x, σ (σ x) = x)
    (x y : Fin n → E) : form σ J y x = σ (form σ J x y) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

omit [NumberField F] [NumberField E] in
theorem form_lin {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : E) (x y z : Fin n → E) {d₂ : ℕ}
    (ι : Matrix (Fin n) (Fin d₂) E) (u : Fin d₂ → E) :
    form σ J (a • x + b • y + ι *ᵥ u) z = a * form σ J x z + b * form σ J y z + form σ J (ι *ᵥ u) z := by
  simp only [form, add_dotProduct, smul_dotProduct, smul_eq_mul]

omit [NumberField F] [NumberField E] in

theorem exists_decomp {n d₂ : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (hσ : ∀ x, σ (σ x) = x) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin d₂) E) (hn : d₂ + 2 = n)
    (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (hinj : Function.Injective ι.mulVec)
    (r : Fin n → E) (hr : form σ J r x = 0) : ∃ (c : E) (v : Fin d₂ → E), r = c • x + ι *ᵥ v := by
  have hyx : form σ J y x = 1 := by rw [form_swap J hJ hσ, hxy, map_one]
  let L : E × E × (Fin d₂ → E) →ₗ[E] (Fin n → E) :=
    (LinearMap.fst E E (E × (Fin d₂ → E))).smulRight x +
      ((LinearMap.fst E E (Fin d₂ → E)).comp (LinearMap.snd E E (E × (Fin d₂ → E)))).smulRight y +
      (Matrix.mulVecLin ι).comp ((LinearMap.snd E E (Fin d₂ → E)).comp (LinearMap.snd E E (E × (Fin d₂ → E))))
  have hL : ∀ p : E × E × (Fin d₂ → E), L p = p.1 • x + p.2.1 • y + ι *ᵥ p.2.2 := fun p => by
    simp [L, Matrix.mulVecLin_apply]
  have hinjL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hL] at hp
    have h1 := congrArg (fun z => form σ J z x) hp
    have h2 := congrArg (fun z => form σ J z y) hp
    simp only [form_lin, hxx, hyx, hxy, hyy, (horth _).1, (horth _).2] at h1 h2
    have e0 : (0 : Fin n → E) = (0 : E) • x + (0 : E) • y + ι *ᵥ 0 := by simp
    simp only [form, zero_dotProduct] at h1 h2
    have hb : p.2.1 = 0 := by simpa using h1
    have ha : p.1 = 0 := by simpa using h2
    rw [ha, hb, zero_smul, zero_smul, zero_add, zero_add] at hp
    have hu : p.2.2 = 0 := hinj (by rw [hp, Matrix.mulVec_zero])
    exact Prod.ext ha (Prod.ext hb hu)
  have hsurj : Function.Surjective L := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinjL
    simp [Module.finrank_prod, Module.finrank_fin_fun]
    omega
  obtain ⟨p, hp⟩ := hsurj r
  rw [hL] at hp
  have h1 := congrArg (fun z => form σ J z x) hp
  simp only [form_lin, hxx, hyx, (horth _).1, hr] at h1
  have hb : p.2.1 = 0 := by simpa using h1
  refine ⟨p.1, p.2.2, ?_⟩
  rw [← hp, hb, zero_smul, add_zero]

theorem exists_mat_of_mem_ratU {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {γ : UA σ J} (h : γ ∈ ratU σ J) :
    ∃ g : Matrix (Fin n) (Fin n) E, mat γ = incM F g := by
  rw [ratU, Subgroup.mem_subgroupOf] at h
  obtain ⟨g0, hg0⟩ := h
  refine ⟨g0.1, ?_⟩
  simp only [mat, ← hg0]
  rfl

theorem unitary_of_incM {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (γ : UA σ J) (g : Matrix (Fin n) (Fin n) E)
    (hg : mat γ = incM F g) : gᵀ * J * g.map σ = J := by
  have h := γ.2
  change (mat γ)ᵀ * incM F J * (mat γ).map (cA σ) = incM F J at h
  rw [hg] at h
  have e1 : (incM F g).map (cA σ) = incM F (g.map σ) := by
    ext i j; simp [incM, cA_inclR]
  rw [e1] at h
  apply Matrix.map_injective (inclR_injective (F := F) (E := E))
  unfold incM at h
  show (gᵀ * J * g.map σ).map (inclR (F := F) (AF F)) = J.map (inclR (F := F) (AF F))
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  exact h

theorem fix_of_incM {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (γ : UA σ J) (g : Matrix (Fin n) (Fin n) E)
    (hg : mat γ = incM F g) (x : Fin n → E) (h : mat γ *ᵥ incV F x = incV F x) : g *ᵥ x = x := by
  funext i
  apply inclR_injective (F := F) (E := E)
  have := congrFun h i
  rw [hg] at this
  rw [RingHom.map_mulVec]
  exact this

theorem mulVec_x_of_mem_unip {n d₂ : ℕ} {X : Spc F E n} {H : Plane E n d₂} {u : UA σ X.J}
    (hu : u ∈ unip σ X H) : mat u *ᵥ incV F H.x = incV F H.x := by
  unfold unip at hu
  induction hu using Subgroup.closure_induction with
  | mem u hu => exact hu.1
  | one => exact Matrix.one_mulVec _
  | mul a b _ _ ha hb =>
    rw [show mat (a * b) = mat a * mat b from rfl, ← Matrix.mulVec_mulVec, hb, ha]
  | inv a _ ha =>
    calc mat a⁻¹ *ᵥ incV F H.x = mat a⁻¹ *ᵥ (mat a *ᵥ incV F H.x) := by rw [ha]
      _ = incV F H.x := by
        rw [Matrix.mulVec_mulVec, show mat a⁻¹ * mat a = mat (a⁻¹ * a) from rfl, inv_mul_cancel]
        exact Matrix.one_mulVec _

omit [NumberField F] [NumberField E] in
theorem form_fix {n : ℕ} (J g : Matrix (Fin n) (Fin n) E) (hu : gᵀ * J * g.map σ = J) (x y : Fin n → E)
    (hx : g *ᵥ x = x) : form σ J (g *ᵥ y) x = form σ J y x := by
  have hs : (fun i => σ (x i)) = g.map σ *ᵥ (fun i => σ (x i)) := by
    funext i
    conv_lhs => rw [← hx]
    exact RingHom.map_mulVec (σ : E →+* E) g x i
  unfold form
  have key : (g *ᵥ y) ᵥ* J ᵥ* g.map σ = y ᵥ* J := by
    rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hu]
  calc (g *ᵥ y) ⬝ᵥ J *ᵥ (fun i => σ (x i)) = (g *ᵥ y) ⬝ᵥ J *ᵥ (g.map σ *ᵥ fun i => σ (x i)) := by
        rw [← hs]
    _ = ((g *ᵥ y) ᵥ* J ᵥ* g.map σ) ⬝ᵥ (fun i => σ (x i)) := by
        rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
    _ = y ⬝ᵥ J *ᵥ (fun i => σ (x i)) := by rw [key, Matrix.dotProduct_mulVec]

omit [NumberField F] [NumberField E] in
theorem vecMulVec_mulVec {m k l : ℕ} (A : Matrix (Fin m) (Fin k) E) (v : Fin k → E) (w : Fin l → E) :
    Matrix.vecMulVec (A *ᵥ v) w = A * Matrix.vecMulVec v w := by
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul, mul_assoc]

omit [NumberField F] [NumberField E] in
theorem smul_vecMulVec' {m l : ℕ} (c : E) (x : Fin m → E) (w : Fin l → E) :
    Matrix.vecMulVec (c • x) w = Matrix.vecMulVec x (c • w) := by
  ext i j
  simp [Matrix.vecMulVec_apply]
  ring

end GlobalTheory.RatUnipTheta

namespace GlobalTheory.RatUnipTheta

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ γ ∈ ratU σ X.J, γ ∈ unip σ X H → ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ w : Fin d → E,
      ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (γ, 1) Ψ)))‖ = ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (Ψ)))‖ := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hgeo V₁ M₁ e hV hM₁ hev
    γ hγ hγu Ψ hΨ w
  obtain ⟨hn, hxx, hyy, hxy, horth, hinj⟩ := hgeo
  have hψ : IsStd B.ψ := hP.base.std
  have hM : M.IsGood B.ψ := hP.good
  have hσ : ∀ x, σ (σ x) = x := conj_conj hP.base.cm
  obtain ⟨h0, hh0⟩ := exists_mat_of_mem_ratU ((ratU σ X.J).inv_mem hγ)
  have hunit := unitary_of_incM γ⁻¹ h0 hh0
  have hfix : h0 *ᵥ H.x = H.x :=
    fix_of_incM γ⁻¹ h0 hh0 H.x (mulVec_x_of_mem_unip ((unip σ X H).inv_mem hγu))
  have hr : form σ X.J (h0 *ᵥ H.y - H.y) H.x = 0 := by
    have := form_fix X.J h0 hunit H.x H.y hfix
    unfold form at this ⊢
    rw [sub_dotProduct, this, sub_self]
  obtain ⟨c, v, hcv⟩ := exists_decomp X.J hP.herm.herm hσ H.x H.y H.ι hn hxx hyy hxy horth hinj _ hr
  have hsplit : h0 *ᵥ H.y = H.y + (c • H.x + H.ι *ᵥ v) := by rw [← hcv]; abel
  have hY : Matrix.vecMulVec (incV F H.y) (incV F w) = incM F (Matrix.vecMulVec H.y w) :=
    (GlobalTheory.ThetaExpandInv.incM_vecMulVec _ _).symm
  have hact : actAB (cA σ) (γ, (1 : UA σ W.J)) (incM F (Matrix.vecMulVec (h0 *ᵥ H.y) w)) =
      incM F (Matrix.vecMulVec H.y w) := by
    show mat γ * incM F (Matrix.vecMulVec (h0 *ᵥ H.y) w) * (mat (1 : UA σ W.J))ᵀ = _
    rw [vecMulVec_mulVec, incM, Matrix.map_mul, ← incM, ← incM, ← hh0, ← Matrix.mul_assoc,
      show mat γ * mat γ⁻¹ = mat (γ * γ⁻¹) from rfl, mul_inv_cancel]
    show (1 : Matrix (Fin n) (Fin n) (AE F E)) * _ * (1 : Matrix (Fin d) (Fin d) (AE F E))ᵀ = _
    rw [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hS := IsUWeilPair.isUSplitting hP.weil
  have himpl := hS.impl (γ, 1) (incM F (Matrix.vecMulVec (h0 *ᵥ H.y) w)) Ψ hΨ
  rw [hact] at himpl
  have hmem : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ u Φ ∈ schA F (Fin n × Fin d) :=
    fun u Φ hΦ => GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ u Φ hΦ
  rw [hY, ← himpl, GlobalTheory.T.seesaw_pair_plane_descent_first hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H
    ⟨hn, hxx, hyy, hxy, horth, hinj⟩ V₁ M₁ e hV hM₁ hev γ hγu _ (hmem _ Ψ hΨ)]
  congr 1
  have hdec : Matrix.vecMulVec (h0 *ᵥ H.y) w =
      Matrix.vecMulVec (c • H.x) w + (Matrix.vecMulVec (H.ι *ᵥ v) w + Matrix.vecMulVec H.y w) := by
    rw [hsplit, Matrix.add_vecMulVec, Matrix.add_vecMulVec]; abel
  rw [hdec, ← GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M hψ hM, ← GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M hψ hM]
  have hC : incM F (Matrix.vecMulVec (c • H.x) w) ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} :=
    ⟨incV F (c • w), by rw [smul_vecMulVec', GlobalTheory.ThetaExpandInv.incM_vecMulVec]⟩
  rw [hev.inv _ hC _ (hmem _ _ (hmem _ _ hΨ))]
  have hB : incM F (Matrix.vecMulVec (H.ι *ᵥ v) w) =
      incM F H.ι * incM F (Matrix.vecMulVec v w) * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ := by
    have h1 : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1, Matrix.transpose_one, Matrix.mul_one, vecMulVec_mulVec]
    exact Matrix.map_mul
  rw [hB, hev.Heisenberg₂ _ _ (hmem _ _ hΨ), GlobalTheory.ThetaExpandInv.thetaSum_rho_rat M₁ hψ hM₁]

end GlobalTheory.RatUnipTheta
