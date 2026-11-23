import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.QdetFacts

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in
@[simp] theorem lift_apply (B : Module.End ℂ M) (f : TV n M P) (I : P → Fin n) : lift B f I = B (f I) := rfl

omit [Fintype P] in
theorem eAt_apply (p : P) (a b : Fin n) (f : TV n M P) (I : P → Fin n) :
    eAt p a b f I = if I p = a then f (Function.update I p b) else 0 := by
  simp only [eAt, LinearMap.pi_apply]
  split_ifs <;> simp

omit [Fintype P] [DecidableEq P] in
@[simp] theorem pm_apply (σ : Equiv.Perm P) (f : TV n M P) (I : P → Fin n) : pm σ f I = f (I ∘ σ) := rfl

omit [Fintype P] in
theorem tE_apply (S : Finset P) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : TV n M P) (I : P → Fin n) :
    tE S E a b f I = E a b (f I) + ∑ p ∈ S, if I p = a then f (Function.update I p b) else 0 := by
  simp only [tE, LinearMap.add_apply, Pi.add_apply, lift_apply, LinearMap.sum_apply, Finset.sum_apply, eAt_apply]

omit [Fintype P] in
theorem Om_apply (E : Fin n → Fin n → Module.End ℂ M) (p : P) (f : TV n M P) (I : P → Fin n) :
    Om E p f I = ∑ a, E a (I p) (f (Function.update I p a)) := by
  simp only [Om, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, lift_apply, eAt_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (I p)]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb), map_zero]
  · simp

omit [Fintype P] [DecidableEq P] in
theorem pm_mul (σ τ : Equiv.Perm P) : (pm (σ * τ) : Module.End ℂ (TV n M P)) = pm σ * pm τ := rfl

omit [Fintype P] [DecidableEq P] in
@[simp] theorem pm_one : (pm 1 : Module.End ℂ (TV n M P)) = 1 := rfl

omit [Fintype P] [DecidableEq P] in
theorem lift_mul (B B' : Module.End ℂ M) : (lift (B * B') : Module.End ℂ (TV n M P)) = lift B * lift B' := rfl

omit [Fintype P] [DecidableEq P] in
theorem lift_comm_pm (B : Module.End ℂ M) (σ : Equiv.Perm P) : Commute (lift B : Module.End ℂ (TV n M P)) (pm σ) := rfl

def liftA (n : ℕ) (M P : Type) [AddCommGroup M] [Module ℂ M] : Module.End ℂ M →ₐ[ℂ] Module.End ℂ (TV n M P) where
  toFun := lift
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [Fintype P] in
theorem lift_comm_eAt (B : Module.End ℂ M) (p : P) (a b : Fin n) : Commute (lift B) (eAt p a b) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, lift_apply, eAt_apply]
  split_ifs <;> simp

theorem alt_apply (G : Finset (Equiv.Perm P)) (f : TV n M P) (I : P → Fin n) :
    alt G f I = ∑ σ ∈ G, ((Equiv.Perm.sign σ : ℤ) : ℂ) • f (I ∘ σ) := by
  simp only [alt, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, pm_apply]

theorem cA_apply {C : Type} [DecidableEq C] (col : P → C) (b : P → Fin n) (f : TV n M P) :
    cA col b f = alt (colG col) f b := rfl

theorem actT_apply {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ)
    (f : TV n M P) (I : P → Fin n) :
    actT lab κ ρ γ f I = ∑ J : P → Fin n, (∏ p, κ (lab p) γ (I p) (J p)) • ρ γ (f J) := by
  simp only [actT, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

theorem curF_apply {m k : ℕ} (f : TV n M (Fin (m + k))) (J : Fin k → Fin n) (I : Fin m → Fin n) :
    curF n M m k f J I = f (Fin.append I J) := rfl

end PositivityTheory.Rg.Cz

end
