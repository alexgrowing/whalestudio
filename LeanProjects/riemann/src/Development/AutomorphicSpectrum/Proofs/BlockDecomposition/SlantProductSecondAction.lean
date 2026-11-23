import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialActionSecondFactor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechNerveFaceOneZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackZeroCochainsAlgebraMap

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx

namespace GlobalTheory.CompanionTheory.HopfLe

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]

section Slant

variable {ι : Type} [Fintype ι] {M : ι → Type} [∀ i, CommRing (M i)] [∀ i, Algebra R (M i)]
  {V : Type} [CommRing V] [Algebra R V]

open Classical in

def slv (Λ : (∀ i, M i) →ₗ[R] R) : (∀ i, M i ⊗[R] V) →ₗ[R] V :=
  ∑ i, (TensorProduct.lid R V).toLinearMap ∘ₗ LinearMap.rTensor V (Λ ∘ₗ LinearMap.single R M i) ∘ₗ
    LinearMap.proj (φ := fun i ↦ M i ⊗[R] V) i

theorem slv_pure (Λ : (∀ i, M i) →ₗ[R] R) (f : ∀ i, M i) (v : V) :
    slv Λ (fun i ↦ f i ⊗ₜ[R] v) = Λ f • v := by
  classical
  simp only [slv, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.rTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul]
  rw [← Finset.sum_smul, ← map_sum]
  congr 2
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem slv_ext {W : Type} [AddCommGroup W] [Module R W] (A B : (∀ i, M i ⊗[R] V) →ₗ[R] W)
    (h : ∀ (f : ∀ i, M i) (v : V), A (fun i ↦ f i ⊗ₜ[R] v) = B (fun i ↦ f i ⊗ₜ[R] v)) : A = B := by
  classical
  refine LinearMap.pi_ext' fun i ↦ TensorProduct.ext' fun a v ↦ ?_
  have e : (LinearMap.single R (fun i ↦ M i ⊗[R] V) i) (a ⊗ₜ[R] v) =
      fun j ↦ (Pi.single i a : ∀ j, M j) j ⊗ₜ[R] v := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_apply, hj]
  simp only [LinearMap.comp_apply, e, h]

theorem slv_add (Λ Λ' : (∀ i, M i) →ₗ[R] R) (t : ∀ i, M i ⊗[R] V) :
    slv (Λ + Λ') t = slv Λ t + slv Λ' t := by
  have : (slv (Λ + Λ') : (∀ i, M i ⊗[R] V) →ₗ[R] V) = slv Λ + slv Λ' :=
    slv_ext _ _ fun f v ↦ by simp [slv_pure, add_smul]
  rw [this]; rfl

theorem slv_smul (r : R) (Λ : (∀ i, M i) →ₗ[R] R) (t : ∀ i, M i ⊗[R] V) :
    slv (r • Λ) t = r • slv Λ t := by
  have : (slv (r • Λ) : (∀ i, M i ⊗[R] V) →ₗ[R] V) = r • slv Λ :=
    slv_ext _ _ fun f v ↦ by simp [slv_pure, mul_smul]
  rw [this]; rfl

theorem slv_zero (t : ∀ i, M i ⊗[R] V) : slv (0 : (∀ i, M i) →ₗ[R] R) t = 0 := by
  have : (slv (0 : (∀ i, M i) →ₗ[R] R) : (∀ i, M i ⊗[R] V) →ₗ[R] V) = 0 :=
    slv_ext _ _ fun f v ↦ by simp [slv_pure]
  rw [this]; rfl

theorem slv_sub (Λ Λ' : (∀ i, M i) →ₗ[R] R) (t : ∀ i, M i ⊗[R] V) :
    slv (Λ - Λ') t = slv Λ t - slv Λ' t := by
  have : (slv (Λ - Λ') : (∀ i, M i ⊗[R] V) →ₗ[R] V) = slv Λ - slv Λ' :=
    slv_ext _ _ fun f v ↦ by simp [slv_pure, sub_smul]
  rw [this]; rfl

theorem map_slv {V' : Type} [CommRing V'] [Algebra R V'] (g : V →ₗ[R] V') (Λ : (∀ i, M i) →ₗ[R] R)
    (t : ∀ i, M i ⊗[R] V) : g (slv Λ t) = slv Λ (fun i ↦ TensorProduct.map LinearMap.id g (t i)) := by
  have : g ∘ₗ (slv Λ : (∀ i, M i ⊗[R] V) →ₗ[R] V) =
      (slv Λ : (∀ i, M i ⊗[R] V') →ₗ[R] V') ∘ₗ
        LinearMap.pi fun i ↦ TensorProduct.map LinearMap.id g ∘ₗ LinearMap.proj i :=
    slv_ext _ _ fun f v ↦ by
      simp only [LinearMap.comp_apply, slv_pure, map_smul]
      have := slv_pure (V := V') Λ f (g v)
      rw [← this]
      congr 1
  exact LinearMap.congr_fun this t

theorem slv_mul_right (Λ : (∀ i, M i) →ₗ[R] R) (e : V) (t : ∀ i, M i ⊗[R] V) :
    slv Λ (fun i ↦ ((1 : M i) ⊗ₜ[R] e) * t i) = e * slv Λ t := by
  have : (slv Λ : (∀ i, M i ⊗[R] V) →ₗ[R] V) ∘ₗ
        (LinearMap.pi fun i ↦ LinearMap.mulLeft R ((1 : M i) ⊗ₜ[R] e) ∘ₗ LinearMap.proj i) =
      LinearMap.mulLeft R e ∘ₗ slv Λ :=
    slv_ext _ _ fun f v ↦ by
      simp only [LinearMap.comp_apply, slv_pure, LinearMap.mulLeft_apply, mul_smul_comm]
      rw [← slv_pure]
      congr 1
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul]
  exact LinearMap.congr_fun this t

theorem slv_mul_left (Λ : (∀ i, M i) →ₗ[R] R) (x : ∀ i, M i) (t : ∀ i, M i ⊗[R] V) :
    slv Λ (fun i ↦ (x i ⊗ₜ[R] (1 : V)) * t i) = slv (Λ ∘ₗ LinearMap.mulLeft R x) t := by
  have : (slv Λ : (∀ i, M i ⊗[R] V) →ₗ[R] V) ∘ₗ
        (LinearMap.pi fun i ↦ LinearMap.mulLeft R (x i ⊗ₜ[R] (1 : V)) ∘ₗ LinearMap.proj i) =
      slv (Λ ∘ₗ LinearMap.mulLeft R x) :=
    slv_ext _ _ fun f v ↦ by
      simp only [LinearMap.comp_apply, slv_pure, LinearMap.mulLeft_apply]
      rw [← slv_pure]
      congr 1
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul]
  exact LinearMap.congr_fun this t

theorem slv_proj (i₀ : ι) (l : M i₀ →ₗ[R] R) (t : ∀ i, M i ⊗[R] V) :
    slv (l ∘ₗ LinearMap.proj i₀) t = TensorProduct.lid R V (LinearMap.rTensor V l (t i₀)) := by
  have : (slv (l ∘ₗ LinearMap.proj i₀) : (∀ i, M i ⊗[R] V) →ₗ[R] V) =
      (TensorProduct.lid R V).toLinearMap ∘ₗ LinearMap.rTensor V l ∘ₗ LinearMap.proj i₀ :=
    slv_ext _ _ fun f v ↦ by simp [slv_pure]
  exact LinearMap.congr_fun this t

end Slant

section Sl

variable (F : C ⥤ CommAlgCat.{0} R)

theorem sl_eq {p : ℕ} [Fintype (Fin (p + 1) ⥤ C)] (q : ℕ) (Λ : Cn F p →ₗ[R] R) (y : Y F p q)
    (b : Fin (q + 1) ⥤ C) :
    sl F q Λ y b = slv (M := fun c : Fin (p + 1) ⥤ C ↦ F.obj (c.obj (Fin.last p))) Λ (fun c ↦ y c b) := by
  simp [sl, slv, LinearMap.sum_apply]

theorem sl_sub {p : ℕ} [Fintype (Fin (p + 1) ⥤ C)] (q : ℕ) (Λ Λ' : Cn F p →ₗ[R] R) (y : Y F p q) :
    sl F q (Λ - Λ') y = sl F q Λ y - sl F q Λ' y := by
  funext b
  simp only [sl_eq, Pi.sub_apply]
  exact slv_sub _ _ _

theorem slant_product_first_action {p p' : ℕ} [Fintype (Fin (p + 1) ⥤ C)] [Fintype (Fin (p' + 1) ⥤ C)] (q : ℕ)
    (θ : Fin (p + 1) →o Fin (p' + 1)) (ρ : Cn F p' →ₗ[R] R) (y : Y F p q) :
    sl F q ρ (a1 F θ y) = sl F q (ρ ∘ₗ act F θ) y := by
  funext b
  simp only [sl_eq]
  have key : (slv (M := fun c : Fin (p' + 1) ⥤ C ↦ F.obj (c.obj (Fin.last p'))) (V := F.obj (b.obj (Fin.last q))) ρ) ∘ₗ
      (LinearMap.pi fun c : Fin (p' + 1) ⥤ C ↦
        TensorProduct.map (mp F (c.map (homOfLE (Fin.le_last (θ (Fin.last p)))))).toLinearMap LinearMap.id ∘ₗ
          LinearMap.proj (φ := fun c : Fin (p + 1) ⥤ C ↦ F.obj (c.obj (Fin.last p)) ⊗[R] F.obj (b.obj (Fin.last q)))
            (θ.monotone.functor ⋙ c)) =
      slv (M := fun c : Fin (p + 1) ⥤ C ↦ F.obj (c.obj (Fin.last p))) (ρ ∘ₗ act F θ) :=
    slv_ext _ _ fun f v ↦ by
      simp only [LinearMap.comp_apply, slv_pure]
      rw [← slv_pure]
      congr 1
  exact LinearMap.congr_fun key (fun c ↦ y c b)

theorem slant_product_second_action {p q q' : ℕ} [Fintype (Fin (p + 1) ⥤ C)] (ψ : Fin (q + 1) →o Fin (q' + 1))
    (ρ : Cn F p →ₗ[R] R) (y : Y F p q) :
    sl F q' ρ (a2 F ψ y) = act F ψ (sl F q ρ y) := by
  funext b
  rw [act_apply, sl_eq, sl_eq]
  exact (map_slv (mp F (b.map (homOfLE (Fin.le_last (ψ (Fin.last q)))))).toLinearMap ρ _).symm

end Sl

section Vertices

theorem th_apply (q : ℕ) (i : Fin (q + 1)) (j : Fin (q + 2)) : th q i j = if j ≤ i.castSucc then 0 else 1 := rfl

theorem sg_apply (q : ℕ) (i : Fin (q + 1)) (j : Fin (q + 2)) : sg q i j = Fin.predAbove i j := rfl

theorem cst_apply (n p : ℕ) (a : Fin (p + 1)) (j : Fin (n + 1)) : cst n a j = a := rfl

theorem front_zero (n : ℕ) : front n 0 = 0 := rfl

theorem front_one (n : ℕ) : front n 1 = 1 := by
  apply Fin.ext
  change ((1 : Fin 2) : ℕ) = ((1 : Fin (n + 2)) : ℕ)
  simp

theorem back_apply (n : ℕ) (j : Fin (n + 1)) : back n j = j.succ := by
  simp [back]

theorem th_front0 (q : ℕ) : (th (q + 1) 0).comp (front (q + 1)) = OrderHom.id := by
  ext j
  fin_cases j
  · simp [th_apply, front_zero]
  · simp [th_apply, front_one]

theorem th_back0 (q : ℕ) : (th (q + 1) 0).comp (back (q + 1)) = cst (q + 1) 1 := by
  ext j
  simp [th_apply, back_apply, cst_apply]

theorem sg_back0 (q : ℕ) : (sg (q + 1) 0).comp (back (q + 1)) = OrderHom.id := by
  ext j
  simp [sg_apply, back_apply]

theorem sg_front0 (q : ℕ) : ((sg (q + 1) 0).comp (front (q + 1))) 0 = ((sg (q + 1) 0).comp (front (q + 1))) 1 := by
  simp [sg_apply, front_zero, front_one, Fin.predAbove]

theorem th_frontS (q : ℕ) (i : Fin (q + 1)) :
    ((th (q + 1) i.succ).comp (front (q + 1))) 0 = ((th (q + 1) i.succ).comp (front (q + 1))) 1 := by
  simp [th_apply, front_zero, front_one, Fin.le_def]

theorem sg_frontS (q : ℕ) (i : Fin (q + 1)) : (sg (q + 1) i.succ).comp (front (q + 1)) = front q := by
  ext j
  fin_cases j
  · simp [sg_apply, front_zero, Fin.predAbove, Fin.lt_def]
  · simp [sg_apply, front_one, Fin.predAbove, Fin.lt_def]

theorem th_backS (q : ℕ) (i : Fin (q + 1)) : (th (q + 1) i.succ).comp (back (q + 1)) = th q i := by
  ext j
  simp [th_apply, back_apply, Fin.le_def]

theorem sg_backS (q : ℕ) (i : Fin (q + 1)) :
    (sg (q + 1) i.succ).comp (back (q + 1)) = (back q).comp (sg q i) := by
  ext j
  simp only [OrderHom.comp_coe, Function.comp_apply, sg_apply, back_apply]
  simp only [Fin.predAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs with h1 h2 h2
  · simp only [Fin.val_pred, Fin.val_succ]
    omega
  · omega
  · omega
  · simp

end Vertices

section Cup

variable (F : C ⥤ CommAlgCat.{0} R)

theorem S_apply (q : ℕ) (w : Cn (box F) (q + 1)) :
    S F q w = ∑ i : Fin (q + 1), ((-1 : R) ^ (i : ℕ)) • bi F (th q i) (sg q i) w := by
  simp [S, LinearMap.sum_apply]

theorem shuffle_cup1_formula (q : ℕ) (y : Cn (box F) 1) (w : Cn (box F) (q + 1)) :
    S F (q + 1) (cup1 (box F) y w) = ∑ i : Fin (q + 2), ((-1 : R) ^ (i : ℕ)) •
      (bi F ((th (q + 1) i).comp (front (q + 1))) ((sg (q + 1) i).comp (front (q + 1))) y *
        bi F ((th (q + 1) i).comp (back (q + 1))) ((sg (q + 1) i).comp (back (q + 1))) w) := by
  simp only [S_apply, cup1, bi_mul, bi_act]

theorem S_cup_R (q : ℕ) (x : Cn F 1) (hx : dn F 1 x = 0) (w : Cn (box F) (q + 1))
    (c : Fin 2 ⥤ C) (b : Fin (q + 2) ⥤ C) :
    S F (q + 1) (cup1 (box F) (pulln (boxR F) 1 x) w) c b =
      ((1 : F.obj (c.obj (Fin.last 1))) ⊗ₜ[R] (- act F (front q) x b)) * a2 F (back q) (S F q w) c b := by
  rw [shuffle_cup1_formula, Fin.sum_univ_succ]
  have h0 : bi F ((th (q + 1) 0).comp (front (q + 1))) ((sg (q + 1) 0).comp (front (q + 1)))
      (pulln (boxR F) 1 x) = 0 := by
    funext c' b'
    rw [bi_boxR, act_const F x hx _ (sg_front0 q)]
    simp
  have hS : a2 F (back q) (S F q w) =
      ∑ i : Fin (q + 1), ((-1 : R) ^ (i : ℕ)) • bi F (th q i) ((back q).comp (sg q i)) w := by
    simp only [S_apply, map_sum, map_smul, bisimplicial_action_second_factor]
  rw [h0, zero_mul, smul_zero, zero_add, hS, Finset.sum_apply, Finset.sum_apply, Finset.sum_apply,
    Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Pi.smul_apply, Pi.mul_apply, bi_boxR, sg_frontS, th_backS, sg_backS, Fin.val_succ, pow_succ, mul_neg,
    mul_one, neg_smul, TensorProduct.tmul_neg, neg_mul, mul_smul_comm]
  have e : act F ((sg (q + 1) i.succ).comp (front (q + 1))) x = act F (front q) x :=
    congrArg (fun θ ↦ act F θ x) (sg_frontS q i)
  rw [e, smul_neg]

theorem S_cup_L (q : ℕ) (x : Cn F 1) (hx : dn F 1 x = 0) (w : Cn (box F) (q + 1))
    (c : Fin 2 ⥤ C) (b : Fin (q + 2) ⥤ C) :
    S F (q + 1) (cup1 (box F) (pulln (boxL F) 1 x) w) c b =
      (x c ⊗ₜ[R] (1 : F.obj (b.obj (Fin.last (q + 1))))) * a1 F (cst 0 (1 : Fin 2)) (S0 F (q + 1) w) c b := by
  rw [shuffle_cup1_formula, Fin.sum_univ_succ]
  have h0 : ∀ i : Fin (q + 1), bi F ((th (q + 1) i.succ).comp (front (q + 1)))
      ((sg (q + 1) i.succ).comp (front (q + 1))) (pulln (boxL F) 1 x) = 0 := fun i ↦ by
    funext c' b'
    rw [bi_boxL, act_const F x hx _ (th_frontS q i)]
    simp
  have e : (cst 0 (1 : Fin 2)).comp (cst (q + 1) (0 : Fin 1)) = cst (q + 1) (1 : Fin 2) := rfl
  simp only [h0, zero_mul, smul_zero, Finset.sum_const_zero, add_zero, th_front0, th_back0, sg_back0, Fin.val_zero,
    pow_zero, one_smul, S0, bisimplicial_action_first_factor, e]
  have e2 : act F ((th (q + 1) 0).comp (front (q + 1))) x = x :=
    (congrArg (fun θ ↦ act F θ x) (th_front0 q)).trans (act_id F x)
  rw [Pi.mul_apply, Pi.mul_apply, bi_boxL, e2]

theorem T_cup_R [Fintype (Fin 2 ⥤ C)] (q : ℕ) (Λ : Cn F 1 →ₗ[R] R) (x : Cn F 1) (hx : dn F 1 x = 0)
    (w : Cn (box F) (q + 1)) :
    T F (q + 1) Λ (cup1 (box F) (pulln (boxR F) 1 x) w) = - cup1 F x (T F q Λ w) := by
  funext b
  change sl F (q + 1) Λ (S F (q + 1) _) b = _
  rw [sl_eq]
  simp only [S_cup_R F q x hx w]
  rw [slv_mul_right, ← sl_eq, slant_product_second_action]
  change _ = -(act F (front q) x b * act F (back q) (sl F q Λ (S F q w)) b)
  rw [neg_mul]

theorem T_cup_L [Fintype (Fin 1 ⥤ C)] [Fintype (Fin 2 ⥤ C)] (q : ℕ) (Λ : Cn F 1 →ₗ[R] R) (x : Cn F 1)
    (hx : dn F 1 x = 0) (w : Cn (box F) (q + 1)) :
    T F (q + 1) Λ (cup1 (box F) (pulln (boxL F) 1 x) w) = U F (q + 1) (nu F Λ x) w := by
  funext b
  change sl F (q + 1) Λ (S F (q + 1) _) b = sl F (q + 1) _ (S0 F (q + 1) w) b
  rw [sl_eq]
  simp only [S_cup_L F q x hx w]
  rw [slv_mul_left (M := fun c : Fin 2 ⥤ C ↦ F.obj (c.obj (Fin.last 1))), ← sl_eq, slant_product_first_action]
  rfl

theorem T_base [Fintype (Fin 2 ⥤ C)] (Λ : Cn F 1 →ₗ[R] R) (x : Cn F 1) (hx : dn F 1 x = 0) :
    T F 0 Λ (pulln (boxL F) 1 x + pulln (boxR F) 1 x) = Λ x • (1 : Cn F 0) := by
  funext b
  change sl F 0 Λ (S F 0 _) b = _
  rw [sl_eq]
  have e1 : th 0 0 = OrderHom.id := by
    ext j
    fin_cases j <;> simp [th_apply]
  have h : ∀ c : Fin 2 ⥤ C, S F 0 (pulln (boxL F) 1 x + pulln (boxR F) 1 x) c b =
      x c ⊗ₜ[R] (1 : F.obj (b.obj (Fin.last 0))) := fun c ↦ by
    rw [S_apply, Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul, map_add, Pi.add_apply, bi_boxL, bi_boxR, e1, act_id]
    rw [act_const F x hx (sg 0 0) (Subsingleton.elim (α := Fin 1) _ _)]
    simp
  simp only [h]
  exact slv_pure (M := fun c : Fin 2 ⥤ C ↦ F.obj (c.obj (Fin.last 1))) Λ x _

theorem U_add [Fintype (Fin 1 ⥤ C)] (q : ℕ) (ν ν' : Cn F 0 →ₗ[R] R) (w : Cn (box F) q) :
    U F q (ν + ν') w = U F q ν w + U F q ν' w := by
  funext b
  change sl F q _ _ b = sl F q _ _ b + sl F q _ _ b
  simp only [sl_eq]
  exact slv_add _ _ _

theorem U_smul [Fintype (Fin 1 ⥤ C)] (q : ℕ) (r : R) (ν : Cn F 0 →ₗ[R] R) (w : Cn (box F) q) :
    U F q (r • ν) w = r • U F q ν w := by
  funext b
  change sl F q _ _ b = r • sl F q _ _ b
  simp only [sl_eq]
  exact slv_smul _ _ _

theorem U_zero [Fintype (Fin 1 ⥤ C)] (q : ℕ) (w : Cn (box F) q) :
    U F q (0 : Cn F 0 →ₗ[R] R) w = 0 := by
  funext b
  change sl F q _ _ b = 0
  simp only [sl_eq]
  exact slv_zero _

end Cup

section Tau

variable (F : C ⥤ CommAlgCat.{0} R)

theorem tau_R (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (n : ℕ) (x : Cn F n) :
    pulln (boxE F T₀ ε) n (pulln (boxR F) n x) = x := by
  funext b
  change evL F T₀ _ ε ((1 : F.obj T₀) ⊗ₜ[R] x b) = x b
  simp [evL, Algebra.ofId_apply]

theorem tau_L (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (x : Cn F 1) (hx : dn F 1 x = 0) :
    pulln (boxE F T₀ ε) 1 (pulln (boxL F) 1 x) = 0 := by
  funext b
  have hz : GlobalTheory.CompanionTheory.Dict.L1 F x ∈ Z1 F := by
    rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker, ← GlobalTheory.CompanionTheory.Dict.L2_dn_one_eq_d1_L1, hx, map_zero]
  have h1 : x (ComposableArrows.mk₁ (𝟙 T₀)) = 0 := Z1.id ⟨_, hz⟩ T₀
  have e : b ⋙ (boxE F T₀ ε).G ⋙ (boxL F).G = ComposableArrows.mk₁ (𝟙 T₀) :=
    GlobalTheory.CompanionTheory.Dict.eq_mk₁ _ _ rfl
  have h0 : (x (b ⋙ (boxE F T₀ ε).G ⋙ (boxL F).G) : F.obj T₀) = 0 :=
    eq_of_heq ((GlobalTheory.CompanionTheory.HodgeLow.cn_heq x e).trans (heq_of_eq h1))
  change evL F T₀ _ ε ((x (b ⋙ (boxE F T₀ ε).G ⋙ (boxL F).G) : F.obj T₀) ⊗ₜ[R] 1) = 0
  have h2 : ((0 : F.obj T₀) ⊗ₜ[R] (1 : F.obj (b.obj (Fin.last 1)))) = 0 := TensorProduct.zero_tmul _ _
  rw [h0]
  exact (congrArg (evL F T₀ (b.obj (Fin.last 1)) ε) h2).trans (map_zero _)

theorem lid_evL (T₀ T : C) (ε : F.obj T₀ →ₐ[R] R) (t : F.obj T₀ ⊗[R] F.obj T) :
    TensorProduct.lid R (F.obj T) (LinearMap.rTensor (F.obj T) ε.toLinearMap t) = evL F T₀ T ε t := by
  induction t with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b => simp [evL, Algebra.ofId_apply, Algebra.smul_def]

theorem U_evz [Fintype (Fin 1 ⥤ C)] (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (q : ℕ) (w : Cn (box F) q) :
    U F q (evz F T₀ ε) w = pulln (boxE F T₀ ε) q w := by
  funext b
  change sl F q (evz F T₀ ε) (S0 F q w) b = evL F T₀ _ ε (w (b ⋙ (boxE F T₀ ε).G))
  rw [sl_eq]
  have h1 := slv_proj (M := fun c : Fin 1 ⥤ C ↦ F.obj (c.obj (Fin.last 0))) (V := F.obj (b.obj (Fin.last q)))
    (ComposableArrows.mk₀ T₀) ε.toLinearMap (fun c ↦ S0 F q w c b)
  refine h1.trans ?_
  have e : pc (cst q 0) OrderHom.id (ComposableArrows.mk₀ T₀) b = b ⋙ (boxE F T₀ ε).G :=
    CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun i j f ↦ by
      refine Prod.ext ?_ ?_
      · have e1 : 𝟙 T₀ ≫ 𝟙 T₀ ≫ 𝟙 T₀ = 𝟙 T₀ := by simp
        exact ((ComposableArrows.mk₀ T₀).map_id 0).trans e1.symm
      · change b.map _ = 𝟙 _ ≫ b.map f ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id]
        exact congrArg b.map (Subsingleton.elim _ _))
  have h2 : ∀ (P : Fin (q + 1) ⥤ C × C) (_ : P = b ⋙ (boxE F T₀ ε).G)
      (g : P.obj (Fin.last q) ⟶ (T₀, b.obj (Fin.last q))) (_ : HEq g (𝟙 ((T₀, b.obj (Fin.last q)) : C × C))),
      (mp (box F) g (w P) : F.obj T₀ ⊗[R] F.obj (b.obj (Fin.last q))) = w (b ⋙ (boxE F T₀ ε).G) := by
    intro P h g hg
    subst h
    obtain rfl := eq_of_heq hg
    exact mp_id (box F) _ _
  have hl : pcLast (cst q 0) OrderHom.id (ComposableArrows.mk₀ T₀) b = 𝟙 ((T₀, b.obj (Fin.last q)) : C × C) := by
    refine Prod.ext ?_ ?_
    · exact (ComposableArrows.mk₀ T₀).map_id 0
    · exact (congrArg b.map (Subsingleton.elim _ _)).trans (b.map_id (Fin.last q))
  have h3 := h2 _ e _ (heq_of_eq hl)
  exact (congrArg (fun z ↦ TensorProduct.lid R (F.obj (b.obj (Fin.last q)))
    (LinearMap.rTensor (F.obj (b.obj (Fin.last q))) ε.toLinearMap z)) h3).trans (lid_evL F T₀ _ ε _)

end Tau

end GlobalTheory.CompanionTheory.HopfLe
