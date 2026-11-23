import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.RealTest
import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.GeoAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace PositivityTheory.ThKF0.Geo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

def HasLag (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ψ : AddChar (AF F) ℂ) (ι : Matrix (Fin n) (Fin n₁) E)
    (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E))) : Prop :=
  ∃ L : Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
    Module.finrank F L = Fintype.card (Fin n × Fin d) ∧
    ∀ (t : AF F), ∀ w ∈ L, ∃ u ∈ I, ∃ z : Matrix (Fin n₁) (Fin d₁) (AE F E),
      (M₁.co.e z).1 = 0 ∧ ∀ φ : Fn F n d,
        schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ =
          M.co.rho ψ u (M.co.rho ψ (incM F ι * z * (incM F ι')ᵀ) φ)

theorem alg_inj : Function.Injective (algebraMap F (AF F)) := NumberField.AdeleRing.algebraMap_injective (𝓞 F) F

variable (F E) in

def incL (α β : Type) : Matrix α β E →ₗ[F] Matrix α β (AE F E) :=
  (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E).toLinearMap.mapMatrix

theorem incL_apply {α β : Type} (x : Matrix α β E) : incL F E α β x = incM F x := rfl

theorem incL_inj {α β : Type} : Function.Injective (incL F E α β) := fun _ _ h => Matrix.ext fun i j =>
  Algebra.TensorProduct.includeRight_injective alg_inj (congrFun (congrFun h i) j)

theorem incM_mul {α β γ : Type} [Fintype β] (a : Matrix α β E) (b : Matrix β γ E) :
    incM F (a * b) = incM F a * incM F b := Matrix.map_mul

theorem cA_incl (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := rfl

theorem incM_gram {m m₁ : ℕ} {J : Matrix (Fin m) (Fin m) E} {J₁ : Matrix (Fin m₁) (Fin m₁) E} {ι : Matrix (Fin m) (Fin m₁) E}
    (h : ιᵀ * J * ι.map σ = J₁) : (incM F ι)ᵀ * incM F J * (incM F ι).map (cA σ) = incM F J₁ := by
  rw [← h, incM_mul, incM_mul]
  rfl

theorem incM_vec {α β : Type} (a : α → E) (b : β → E) : incM F (Matrix.vecMulVec a b) =
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (a i)) (fun i => inclR (F := F) (AF F) (b i)) := by
  ext i j
  simp [incM, Matrix.vecMulVec_apply]

theorem incM_mulVec {α β : Type} [Fintype β] (a : Matrix α β E) (b : β → E) :
    incM F a *ᵥ (fun i => inclR (F := F) (AF F) (b i)) = fun i => inclR (F := F) (AF F) ((a *ᵥ b) i) := by
  funext i
  simp [incM, Matrix.mulVec, dotProduct]

theorem inc_dot {α : Type} [Fintype α] (a b : α → E) :
    (fun i => inclR (F := F) (AF F) (a i)) ⬝ᵥ (fun i => inclR (F := F) (AF F) (b i)) = inclR (F := F) (AF F) (a ⬝ᵥ b) := by
  simp [dotProduct]

theorem hasLag_of (h2 : Module.finrank F E = 2) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ψ : AddChar (AF F) ℂ)
    (hM : M.IsGood ψ) (hM₁ : M₁.IsGood ψ) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E)
    (hι : ιᵀ * X.J * ι.map σ = X₁.J) (hι' : ι'ᵀ * W.J * ι'.map σ = W₁.J) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    {m : ℕ} (s : (Fin m → E) →ₗ[F] Matrix (Fin n) (Fin d) E) (hs : Function.Injective s)
    (hI : ∀ (t : AF F) u, t • incM F (s u) ∈ I)
    (hss : ∀ u u', hTens (cA σ) (incM F X.J) (incM F W.J) (incM F (s u)) (incM F (s u')) = 0)
    (hjs : ∀ (z : Matrix (Fin n₁) (Fin d₁) (AE F E)) u, hTens (cA σ) (incM F X.J) (incM F W.J) (incM F ι * z * (incM F ι')ᵀ) (incM F (s u)) = 0)
    (hd : m * 2 + n₁ * d₁ = n * d) : HasLag M M₁ ψ ι ι' I := by
  let j : Matrix (Fin n₁) (Fin d₁) E →ₗ[F] Matrix (Fin n) (Fin d) E :=
    { toFun := fun z => ι * z * ι'ᵀ
      map_add' := fun _ _ => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun _ _ => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  let jA : Matrix (Fin n₁) (Fin d₁) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun z => incM F ι * z * (incM F ι')ᵀ
      map_add' := fun _ _ => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun _ _ => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  obtain ⟨L, h1, h3, h4⟩ := exists_lag alg_inj M.co (incL F E _ _) incL_inj
    (fun x => by obtain ⟨y, z, h⟩ := hM.rat x; exact ⟨(y, z), h⟩) M₁.co (incL F E _ _) incL_inj
    (fun x => by obtain ⟨y, z, h⟩ := hM₁.rat x; exact ⟨(y, z), h⟩)
    (by rw [Module.finrank_matrix, h2]; simp; ring) j jA
    (fun z => by
      show incM F (ι * z * ι'ᵀ) = incM F ι * incM F z * (incM F ι')ᵀ
      rw [incM_mul, incM_mul]; rfl)
    (fun z z' => by
      show symp _ _ _ _ (incM F ι * z * (incM F ι')ᵀ) (incM F ι * z' * (incM F ι')ᵀ) = _
      rw [symp, symp, hTens_mul, incM_gram hι, incM_gram hι'])
    s hs (fun u u' => by rw [symp, incL_apply, incL_apply, hss, mul_zero, map_zero])
    (fun z u => by
      show symp _ _ _ _ (incM F ι * z * (incM F ι')ᵀ) (incM F (s u)) = _
      rw [symp, hjs, mul_zero, map_zero])
    (by rw [Module.finrank_pi_fintype]; simp [h2, hd])
  refine ⟨L, h1, h3, fun t w hw => ?_⟩
  obtain ⟨u, z, hz, h⟩ := h4 t w hw
  exact ⟨_, hI t u, z, hz, h ψ⟩

theorem x_ne {B : Base F E} {m m₁ i₀ i₁ : ℕ} {Y : Spc F E m} {Y₁ : Spc F E m₁} {H : Plane E m m₁}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) : ∃ i, H.x i ≠ 0 := by
  by_contra h
  push Not at h
  have := hH.xy
  rw [form, show H.x = 0 from funext h, zero_dotProduct] at this
  exact zero_ne_one this

theorem orth_alt {B : Base F E} {m m₁ i₀ i₁ : ℕ} {Y : Spc F E m} {Y₁ : Spc F E m₁} {H : Plane E m m₁}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) :
    (incM F H.ι)ᵀ *ᵥ (incM F Y.J *ᵥ fun i => cA σ (inclR (F := F) (AF F) (H.x i))) = 0 := by
  have h : H.ιᵀ *ᵥ (Y.J *ᵥ fun i => σ (H.x i)) = 0 := funext fun k => by
    have := (hH.orth (Pi.single k 1)).1
    rw [form, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_single, mul_one, ← Matrix.mulVec_transpose] at this
    exact this
  simp only [cA_incl]
  rw [incM_mulVec, show (incM F H.ι)ᵀ = incM F H.ιᵀ from rfl, incM_mulVec, h]
  exact funext fun _ => map_zero _

theorem adapted_plane_isotropic_vector {B : Base F E} {m m₁ i₀ i₁ : ℕ} {Y : Spc F E m} {Y₁ : Spc F E m₁} {H : Plane E m m₁}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) :
    (fun i => inclR (F := F) (AF F) (H.x i)) ⬝ᵥ (incM F Y.J *ᵥ fun i => cA σ (inclR (F := F) (AF F) (H.x i))) = 0 := by
  simp only [cA_incl]
  rw [incM_mulVec, inc_dot]
  exact (congrArg _ hH.xx).trans (map_zero _)

theorem gram_one {m : ℕ} (J : Matrix (Fin m) (Fin m) E) : (1 : Matrix (Fin m) (Fin m) E)ᵀ * J * (1 : Matrix _ _ E).map σ = J := by
  rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem hasLagrangian_skew_adapted {B : Base F E} (hB : B.IsGood σ) (M : Model σ X W) (M₁ : Model σ X W₁) (hM : M.IsGood B.ψ)
    (hM₁ : M₁.IsGood B.ψ) {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B W W₁ i₀ i₁) :
    HasLag M M₁ B.ψ 1 H'.ι (iso0 n H') := by
  let s : (Fin n → E) →ₗ[F] Matrix (Fin n) (Fin d) E :=
    { toFun := fun y => Matrix.vecMulVec y H'.x
      map_add' := fun _ _ => by ext i j; simp [Matrix.vecMulVec_apply, add_mul]
      map_smul' := fun _ _ => by ext i j; simp [Matrix.vecMulVec_apply] }
  have hs : ∀ y, s y = Matrix.vecMulVec y H'.x := fun _ => rfl
  obtain ⟨k, hk⟩ := x_ne hH
  refine hasLag_of hB.cm.2.2.1 M M₁ B.ψ hM hM₁ 1 H'.ι (gram_one _) hH.gram _ s (fun y y' h => funext fun i => ?_)
    (fun t u => ⟨t • fun i => inclR (F := F) (AF F) (u i), ?_⟩) (fun u u' => ?_) (fun z u => ?_) ?_
  · exact mul_right_cancel₀ hk (congrFun (congrFun h i) k)
  · rw [hs, incM_vec]
    ext i j
    simp [Matrix.vecMulVec_apply, incV]
  · rw [hs, hs, incM_vec, incM_vec, hTens_vec, Matrix.vecMulVec_mulVec, adapted_plane_isotropic_vector hH]
    simp
  · rw [hs, incM_vec, hTens_vec, ← Matrix.mulVec_mulVec, orth_alt hH]
    simp
  · rw [hH.rank]; ring

theorem hasLag_X {B : Base F E} (hB : B.IsGood σ) (M : Model σ X W) (M₁ : Model σ X₁ W) (hM : M.IsGood B.ψ)
    (hM₁ : M₁.IsGood B.ψ) {H : Plane E n n₁} {i₀ i₁ : ℕ} (hH : H.IsAdapted σ B X X₁ i₀ i₁) :
    HasLag M M₁ B.ψ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} := by
  let s : (Fin d → E) →ₗ[F] Matrix (Fin n) (Fin d) E :=
    { toFun := fun y => Matrix.vecMulVec H.x y
      map_add' := fun _ _ => by ext i j; simp [Matrix.vecMulVec_apply, mul_add]
      map_smul' := fun _ _ => by ext i j; simp [Matrix.vecMulVec_apply] }
  have hs : ∀ y, s y = Matrix.vecMulVec H.x y := fun _ => rfl
  obtain ⟨k, hk⟩ := x_ne hH
  refine hasLag_of hB.cm.2.2.1 M M₁ B.ψ hM hM₁ H.ι 1 hH.gram (gram_one _) _ s (fun y y' h => funext fun i => ?_)
    (fun t u => ⟨t • fun i => inclR (F := F) (AF F) (u i), ?_⟩) (fun u u' => ?_) (fun z u => ?_) ?_
  · exact mul_left_cancel₀ hk (congrFun (congrFun h k) i)
  · rw [hs, incM_vec]
    ext i j
    simp [Matrix.vecMulVec_apply, incV]
  · rw [hs, hs, incM_vec, incM_vec, hTens_vec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMulVec, dotProduct_comm _ (fun i => inclR (F := F) (AF F) (H.x i)),
      adapted_plane_isotropic_vector hH]
    simp
  · rw [hs, incM_vec, hTens_vec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, orth_alt hH]
    simp
  · rw [hH.rank]; ring

open scoped Classical in

theorem proj_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (y : κ → AF F) :
    (LinearMap.proj y : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (y i).2) • ((BoundedContinuousFunction.evalCLM ℂ (fun i => evI F (y i))).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp only [LinearMap.coe_proj, Function.eval, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, smul_eq_mul, pureA]
  rw [mul_comm]
  rfl

theorem form_line (h : LagLine) {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E} {I : Set (Matrix (Fin n) (Fin d) (AE F E))}
    (hL : HasLag M M₁ ψ ι ι' I) (l l' : Fn F n d →ₗ[ℂ] ℂ) (hl : l ∈ (adeleClass F).adm (Fin n × Fin d))
    (hl' : l' ∈ (adeleClass F).adm (Fin n × Fin d))
    (hI : ∀ u ∈ I, ∀ Φ ∈ schA F (Fin n × Fin d), l (M.co.rho ψ u Φ) = l Φ ∧ l' (M.co.rho ψ u Φ) = l' Φ)
    (hz : ∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E), (M₁.co.e z).1 = 0 → ∀ Φ ∈ schA F (Fin n × Fin d),
      l (M.co.rho ψ (incM F ι * z * (incM F ι')ᵀ) Φ) = l Φ ∧ l' (M.co.rho ψ (incM F ι * z * (incM F ι')ᵀ) Φ) = l' Φ)
    (h0 : ∃ Φ ∈ schA F (Fin n × Fin d), l' Φ ≠ 0) : ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), l Φ = c * l' Φ := by
  obtain ⟨L, h1, h2, h3⟩ := hL
  refine h F ψ hψ _ L (lag_of_finrank L h1 h2) l hl l' hl' (fun t w hw Φ hΦ => ?_) (fun t w hw Φ hΦ => ?_) h0
  · obtain ⟨u, hu, z, hz0, e⟩ := h3 t w hw
    rw [e, (hI u hu _ (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ _ Φ hΦ)).1, (hz z hz0 Φ hΦ).1]
  · obtain ⟨u, hu, z, hz0, e⟩ := h3 t w hw
    rw [e, (hI u hu _ (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ _ Φ hΦ)).2, (hz z hz0 Φ hΦ).2]

theorem map_line (h : LagLine) {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E} {I : Set (Matrix (Fin n) (Fin d) (AE F E))}
    (hL : HasLag M M₁ ψ ι ι' I) (T e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
    (hT : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), T (M.co.rho ψ (incM F ι * z * (incM F ι')ᵀ) Φ) = M₁.co.rho ψ z (T Φ))
    (he : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho ψ (incM F ι * z * (incM F ι')ᵀ) Φ) = M₁.co.rho ψ z (e Φ))
    (hTI : ∀ u ∈ I, ∀ Φ ∈ schA F (Fin n × Fin d), T (M.co.rho ψ u Φ) = T Φ)
    (heI : ∀ u ∈ I, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho ψ u Φ) = e Φ)
    (aT : (LinearMap.proj 0 : Fn F n₁ d₁ →ₗ[ℂ] ℂ) ∘ₗ T ∈ (adeleClass F).adm (Fin n × Fin d))
    (ae : (LinearMap.proj 0 : Fn F n₁ d₁ →ₗ[ℂ] ℂ) ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d))
    (h0 : ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0) : ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), T Φ = c • e Φ := by
  have r0 : ∀ z, (M₁.co.e z).1 = 0 → ∀ Ψ : Fn F n₁ d₁, M₁.co.rho ψ z Ψ 0 = Ψ 0 := fun z hz Ψ => by
    simp [Darboux.rho, schr, hz]
  have r1 : ∀ y (Ψ : Fn F n₁ d₁), M₁.co.rho ψ (M₁.co.e.symm (y, 0)) Ψ 0 = Ψ y := fun y Ψ => by
    simp [Darboux.rho, schr]
  obtain ⟨Φ₀, hΦ₀, hne⟩ := h0
  obtain ⟨y₀, hy₀⟩ := Function.ne_iff.1 hne
  obtain ⟨c, hc⟩ := form_line h hψ hL _ _ aT ae
    (fun u hu Φ hΦ => ⟨congrFun (hTI u hu Φ hΦ) 0, congrFun (heI u hu Φ hΦ) 0⟩)
    (fun z hz Φ hΦ => ⟨(congrFun (hT z Φ hΦ) 0).trans (r0 z hz _), (congrFun (he z Φ hΦ) 0).trans (r0 z hz _)⟩)
    ⟨_, GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ _ Φ₀ hΦ₀, fun h' =>
      hy₀ (((congrFun (he (M₁.co.e.symm (y₀, 0)) Φ₀ hΦ₀) 0).trans (r1 y₀ _)).symm.trans h')⟩
  refine ⟨c, fun Φ hΦ => funext fun y => ?_⟩
  have := hc _ (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ (incM F ι * M₁.co.e.symm (y, 0) * (incM F ι')ᵀ) Φ hΦ)
  rw [Pi.smul_apply, smul_eq_mul, ← r1 y (T Φ), ← r1 y (e Φ), ← hT _ Φ hΦ, ← he _ Φ hΦ]
  exact this

end PositivityTheory.ThKF0.Geo
