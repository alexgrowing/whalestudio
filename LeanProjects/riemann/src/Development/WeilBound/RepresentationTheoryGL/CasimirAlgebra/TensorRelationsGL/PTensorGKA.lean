import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TGK

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

def Aop (K : P → Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (TV n M P) :=
  LinearMap.pi fun I => ∑ J : P → Fin n, (∏ q, K q (I q) (J q)) • LinearMap.proj J

def mAt (p : P) (A : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (TV n M P) :=
  LinearMap.pi fun I => ∑ j, A (I p) j • LinearMap.proj (Function.update I p j)

theorem Aop_apply (K : P → Matrix (Fin n) (Fin n) ℂ) (f : TV n M P) (I : P → Fin n) :
    Aop K f I = ∑ J, (∏ q, K q (I q) (J q)) • f J := by
  simp only [Aop, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply]

theorem mAt_apply (p : P) (A : Matrix (Fin n) (Fin n) ℂ) (f : TV n M P) (I : P → Fin n) :
    mAt p A f I = ∑ j, A (I p) j • f (Function.update I p j) := by
  simp only [mAt, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply]

theorem actT_eq {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M)
    (γ : Γ) : actT lab κ ρ γ = lift (ρ γ) * Aop (fun q => κ (lab q) γ) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [actT_apply, Module.End.mul_apply, lift_apply, Aop_apply, map_sum]
  simp only [map_smul]

theorem lift_comm_Aop (B : Module.End ℂ M) (K : P → Matrix (Fin n) (Fin n) ℂ) : Commute (lift B) (Aop K) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, lift_apply, Aop_apply, map_sum, map_smul]

theorem lift_comm_mAt (B : Module.End ℂ M) (p : P) (A : Matrix (Fin n) (Fin n) ℂ) :
    Commute (lift B) (mAt p A : Module.End ℂ (TV n M P)) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, lift_apply, mAt_apply, map_sum, map_smul]

theorem prod_one_apply (I J : P → Fin n) :
    ∏ q, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q) = if I = J then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · obtain ⟨q, hq⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ q) (Matrix.one_apply_ne hq)

theorem Aop_one : (Aop (fun _ : P => (1 : Matrix (Fin n) (Fin n) ℂ)) : Module.End ℂ (TV n M P)) = 1 := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Aop_apply, prod_one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Module.End.one_apply]

theorem Aop_mul (K L : P → Matrix (Fin n) (Fin n) ℂ) :
    (Aop (fun q => K q * L q) : Module.End ℂ (TV n M P)) = Aop K * Aop L := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [Module.End.mul_apply, Aop_apply, Aop_apply]
  simp_rw [Aop_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J' _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp_rw [Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem eAt_eq (p : P) (a b : Fin n) :
    (eAt p a b : Module.End ℂ (TV n M P)) = mAt p (Matrix.single a b 1) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [eAt_apply, mAt_apply]
  simp only [Matrix.single_apply]
  rcases eq_or_ne (I p) a with h | h
  · simp [h]
  · simp [h, Ne.symm h]

def mAtL (p : P) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (TV n M P) where
  toFun := mAt p
  map_add' A B := by
    refine LinearMap.ext fun f => funext fun I => ?_
    simp only [LinearMap.add_apply, Pi.add_apply, mAt_apply, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c A := by
    refine LinearMap.ext fun f => funext fun I => ?_
    simp only [LinearMap.smul_apply, Pi.smul_apply, mAt_apply, Matrix.smul_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum, RingHom.id_apply]

theorem prod_split (p : P) (g : P → ℂ) : ∏ q, g q = g p * ∏ q ∈ Finset.univ.erase p, g q :=
  (Finset.mul_prod_erase _ g (Finset.mem_univ p)).symm

theorem mAt_mul_Aop (p : P) (A : Matrix (Fin n) (Fin n) ℂ) (K : P → Matrix (Fin n) (Fin n) ℂ) :
    (mAt p A * Aop K : Module.End ℂ (TV n M P)) = Aop (Function.update K p (A * K p)) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [Module.End.mul_apply, mAt_apply, Aop_apply]
  simp_rw [Aop_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [prod_split p (fun q => Function.update K p (A * K p) q (I q) (J q))]
  simp only [Function.update_self, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [prod_split p (fun q => K q (Function.update I p j q) (J q))]
  simp only [Function.update_self]
  rw [mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun q hq => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hq), Function.update_of_ne (Finset.ne_of_mem_erase hq)]

theorem Aop_mul_mAt (p : P) (A : Matrix (Fin n) (Fin n) ℂ) (K : P → Matrix (Fin n) (Fin n) ℂ) :
    (Aop K * mAt p A : Module.End ℂ (TV n M P)) = Aop (Function.update K p (K p * A)) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [Module.End.mul_apply, Aop_apply, Aop_apply]
  simp_rw [mAt_apply, Finset.smul_sum, smul_smul]
  let φ : (P → Fin n) × Fin n → (P → Fin n) × Fin n := fun x => (Function.update x.1 p x.2, x.1 p)
  have hφ : Function.Involutive φ := fun x => by
    simp only [φ, Function.update_idem, Function.update_self, Function.update_eq_self]
  let H : (P → Fin n) × Fin n → M := fun x =>
    ((∏ q, K q (I q) (Function.update x.1 p x.2 q)) * A x.2 (x.1 p)) • f x.1
  calc ∑ J : P → Fin n, ∑ j, ((∏ q, K q (I q) (J q)) * A (J p) j) • f (Function.update J p j)
      = ∑ x : (P → Fin n) × Fin n, H (φ x) := by
        rw [← Fintype.sum_prod_type']
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [H, φ, Function.update_idem, Function.update_self, Function.update_eq_self]
    _ = ∑ x : (P → Fin n) × Fin n, H x := Equiv.sum_comp (hφ.toPerm φ) H
    _ = _ := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun J _ => ?_
        simp only [H]
        rw [← Finset.sum_smul]
        congr 1
        rw [prod_split p (fun q => Function.update K p (K p * A) q (I q) (J q))]
        simp only [Function.update_self, Matrix.mul_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [prod_split p (fun q => K q (I q) (Function.update J p i q))]
        simp only [Function.update_self]
        have hr : ∏ q ∈ Finset.univ.erase p, K q (I q) (Function.update J p i q) =
            ∏ q ∈ Finset.univ.erase p, Function.update K p (K p * A) q (I q) (J q) :=
          Finset.prod_congr rfl fun q hq => by
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hq), Function.update_of_ne (Finset.ne_of_mem_erase hq)]
        rw [hr]
        ring

theorem pm_Aop (σ : Equiv.Perm P) (K : P → Matrix (Fin n) (Fin n) ℂ) (hK : ∀ q, K (σ q) = K q) :
    (pm σ * Aop K : Module.End ℂ (TV n M P)) = Aop K * pm σ := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, pm_apply, Aop_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl (Fin n)) : (P → Fin n) ≃ (P → Fin n)) _ _ fun J => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_def, id, Equiv.symm_apply_apply]
  congr 1
  conv_rhs => rw [← Equiv.prod_comp σ]
  simp [hK]

theorem eAt_comm (p q : P) (h : p ≠ q) (a b c d : Fin n) :
    Commute (eAt p a b : Module.End ℂ (TV n M P)) (eAt q c d) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, eAt_apply, Function.update_of_ne h, Function.update_of_ne h.symm,
    Function.update_comm h b d I]
  split_ifs <;> rfl

theorem tE_comm {ι : Type} [DecidableEq ι] (E : ι → Fin n → Fin n → Module.End ℂ M)
    (hcomm : ∀ τ τ', τ ≠ τ' → ∀ a b c d, Commute (E τ a b) (E τ' c d)) (lab : P → ι) (τ τ' : ι) (h : τ ≠ τ')
    (a b c d : Fin n) : Commute (tE (fib lab τ) (E τ) a b) (tE (fib lab τ') (E τ') c d) := by
  unfold tE
  refine Commute.add_left (Commute.add_right ?_ ?_) (Commute.add_right ?_ ?_)
  · exact (hcomm τ τ' h a b c d).map (liftA n M P)
  · exact Commute.sum_right _ _ _ fun p _ => lift_comm_eAt _ _ _ _
  · exact Commute.sum_left _ _ _ fun p _ => (lift_comm_eAt _ _ _ _).symm
  · refine Commute.sum_left _ _ _ fun p hp => Commute.sum_right _ _ _ fun q hq => eAt_comm p q ?_ _ _ _ _
    rintro rfl
    simp only [fib, Finset.mem_filter] at hp hq
    exact h (hp.2.symm.trans hq.2)

theorem actT_one {ι Γ : Type} [Group Γ] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (hκ : ∀ τ, κ τ 1 = 1) (hρ : ρ 1 = 1) : actT lab κ ρ 1 = 1 := by
  rw [actT_eq]
  simp only [hκ, hρ, Aop_one, mul_one]
  rfl

theorem actT_mul {ι Γ : Type} [Group Γ] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (hκ : ∀ τ γ δ, κ τ (γ * δ) = κ τ γ * κ τ δ) (hρ : ∀ γ δ, ρ (γ * δ) = ρ γ * ρ δ)
    (γ δ : Γ) : actT lab κ ρ (γ * δ) = actT lab κ ρ γ * actT lab κ ρ δ := by
  simp only [actT_eq, hκ, hρ, Aop_mul, lift_mul, mul_assoc]
  congr 1
  rw [← mul_assoc, (lift_comm_Aop _ _).eq, mul_assoc]

theorem conj_single (U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ∑ c, ∑ d, (U c a * star (U d b)) • Matrix.single c d (1 : ℂ) = U * Matrix.single a b 1 * Uᴴ := by
  ext i j
  simp [Matrix.sum_apply, Matrix.single_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]

theorem tE_sum (S : Finset P) (E : Fin n → Fin n → Module.End ℂ M) (k : Fin n → Fin n → ℂ) :
    ∑ c, ∑ d, k c d • tE S E c d =
      lift (∑ c, ∑ d, k c d • E c d) + ∑ p ∈ S, mAt p (∑ c, ∑ d, k c d • Matrix.single c d (1 : ℂ)) := by
  simp only [tE, smul_add, Finset.sum_add_distrib, Finset.smul_sum, eAt_eq]
  congr 1
  · refine LinearMap.ext fun f => funext fun I => ?_
    simp [LinearMap.sum_apply, Finset.sum_apply]
  · have : ∀ p, (mAt p (∑ c, ∑ d, k c d • Matrix.single c d (1 : ℂ)) : Module.End ℂ (TV n M P)) =
        ∑ c, ∑ d, k c d • mAt p (Matrix.single c d 1) := fun p => by
      rw [show (mAt p : _ → Module.End ℂ (TV n M P)) = mAtL p from rfl]
      simp only [map_sum, map_smul]
    simp only [this]
    conv_lhs => arg 2; ext c; rw [Finset.sum_comm]
    rw [Finset.sum_comm]

theorem actT_ad {ι Γ : Type} [DecidableEq ι] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M)
    (hu : ∀ τ γ, κ τ γ * (κ τ γ)ᴴ = 1)
    (had : ∀ γ τ a b, ρ γ * E τ a b = (∑ c, ∑ d, (κ τ γ c a * star (κ τ γ d b)) • E τ c d) * ρ γ)
    (γ : Γ) (τ : ι) (a b : Fin n) :
    actT lab κ ρ γ * tE (fib lab τ) (E τ) a b =
      (∑ c, ∑ d, (κ τ γ c a * star (κ τ γ d b)) • tE (fib lab τ) (E τ) c d) * actT lab κ ρ γ := by
  rw [actT_eq, tE_sum]
  unfold tE
  simp only [eAt_eq]
  rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · rw [mul_assoc, ← (lift_comm_Aop _ _).eq, ← mul_assoc, ← lift_mul, had, lift_mul, mul_assoc]
  · refine Finset.sum_congr rfl fun p hp => ?_
    simp only [fib, Finset.mem_filter] at hp
    rw [mul_assoc, Aop_mul_mAt, ← mul_assoc (mAt _ _), ← (lift_comm_mAt _ _ _).eq, mul_assoc, mAt_mul_Aop]
    congr 2
    simp only [hp.2]
    rw [conj_single (κ τ γ) a b, mul_assoc, mul_eq_one_comm.mp (hu τ γ), mul_one]

theorem pm_actT {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M)
    (σ : Equiv.Perm P) (hσ : ∀ p, lab (σ p) = lab p) (γ : Γ) : Commute (pm σ) (actT lab κ ρ γ) := by
  rw [actT_eq]
  refine Commute.mul_right (lift_comm_pm _ _).symm ?_
  exact pm_Aop σ _ fun q => by simp only [hσ]

end PositivityTheory.Rg.Cz.TGK

end
