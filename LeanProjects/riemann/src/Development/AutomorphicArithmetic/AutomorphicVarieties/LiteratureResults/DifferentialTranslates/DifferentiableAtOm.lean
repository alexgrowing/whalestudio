import Mathlib

noncomputable section

open Matrix
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

def InvExact {Γ : Type} [Group Γ] {Ω : ℕ → Type} [∀ q, AddCommGroup (Ω q)] [∀ q, Module ℂ (Ω q)]
    (ρ : ∀ q, Representation ℂ Γ (Ω q)) (d : ∀ q, Ω q →ₗ[ℂ] Ω (q + 1)) : {q : ℕ} → Ω q → Prop
  | 0, x => x = 0
  | q + 1, x => ∃ y, (∀ γ, ρ q γ y = y) ∧ d q y = x

def HasAverage {Γ Ω : Type} [Group Γ] [AddCommGroup Ω] [Module ℂ Ω] (ρ : Representation ℂ Γ Ω) : Prop :=
  ∃ P : (Γ → Ω) →ₗ[ℂ] Ω, (∀ x, P (fun _ => x) = x) ∧ ∀ γ c, ρ γ (P c) = P fun g => ρ γ (c (γ⁻¹ * g))

structure Geo (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) where

  ρ : Γ →* (V →L[ℝ] V)

  σ : Γ →* Equiv.Perm S

  ξ : Γ →* Matrix (Fin d) (Fin d) ℂ

  Y : Set V
  isOpen : IsOpen Y
  maps : ∀ γ, ∀ p ∈ Y, ρ γ p ∈ Y

instance {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) : Inhabited (Geo Γ V S d) :=
  ⟨⟨1, 1, 1, Set.univ, isOpen_univ, fun _ _ h => h⟩⟩

def mulVecL {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) :=
  LinearMap.toContinuousLinearMap ((Matrix.toLin' A).restrictScalars ℝ)

@[simp] theorem mulVecL_apply {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) : mulVecL A v = A *ᵥ v := rfl

section Pull

variable {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

def pull (l : V → ℝ) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V) : V [⋀^Fin q]→L[ℝ] F :=
  (w (l p • p)).compContinuousLinearMap (fderiv ℝ (fun x => l x • x) p)

def RadBasic (Y : Set V) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) : Prop :=
  ∀ p ∈ Y, ∀ (v : Fin q → V) (i : Fin q), v i = p → w p v = 0

def IsCone (Y : Set V) : Prop := ∀ t : ℝ, 0 < t → ∀ p ∈ Y, t • p ∈ Y

def IsGauge (Y : Set V) (l : V → ℝ) : Prop :=
  ContDiffOn ℝ ∞ l Y ∧ (∀ p ∈ Y, 0 < l p) ∧ ∀ t : ℝ, 0 < t → ∀ p ∈ Y, l (t • p) = t⁻¹ * l p

end Pull

namespace Geo

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} (G : Geo Γ V S d)

theorem ρ_inv_apply (γ : Γ) (p : V) : G.ρ γ⁻¹ (G.ρ γ p) = p := by
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem ρ_mem_iff (γ : Γ) (p : V) : G.ρ γ p ∈ G.Y ↔ p ∈ G.Y :=
  ⟨fun h => G.ρ_inv_apply γ p ▸ G.maps γ⁻¹ _ h, G.maps γ p⟩

def lev : Representation ℂ Γ (S → Fin d → ℂ) where
  toFun γ :=
    { toFun := fun f s => G.ξ γ *ᵥ f (G.σ γ⁻¹ s)
      map_add' := fun f g => funext fun x => by simp [Matrix.mulVec_add]
      map_smul' := fun c f => funext fun x => by simp [Matrix.mulVec_smul] }
  map_one' := by ext f x; simp
  map_mul' γ δ := by ext f x; simp

theorem lev_apply (γ : Γ) (f : S → Fin d → ℂ) (s : S) : G.lev γ f s = G.ξ γ *ᵥ f (G.σ γ⁻¹ s) := rfl

def Om (q : ℕ) : Submodule ℂ (S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) where
  carrier := {w | ∀ s, ContDiffOn ℝ ∞ (w s) G.Y ∧ ∀ p ∉ G.Y, w s p = 0}
  add_mem' {w w'} h h' s := ⟨(h s).1.add (h' s).1, fun p hp => by simp [(h s).2 p hp, (h' s).2 p hp]⟩
  zero_mem' s := ⟨contDiffOn_const, fun _ _ => rfl⟩
  smul_mem' c w h s := ⟨(h s).1.const_smul c, fun p hp => by simp [(h s).2 p hp]⟩

theorem mem_Om {q : ℕ} {w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)} :
    w ∈ G.Om q ↔ ∀ s, ContDiffOn ℝ ∞ (w s) G.Y ∧ ∀ p ∉ G.Y, w s p = 0 := Iff.rfl

def tr (q : ℕ) (γ : Γ) : (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) →L[ℝ] (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) :=
  (ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ V (Fin d → ℂ) (Fin d → ℂ) (Fin q) (mulVecL (G.ξ γ))).comp
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (G.ρ γ⁻¹))

@[simp] theorem tr_apply (q : ℕ) (γ : Γ) (m : V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (v : Fin q → V) :
    G.tr q γ m v = G.ξ γ *ᵥ m (fun i => G.ρ γ⁻¹ (v i)) := rfl

def act (q : ℕ) : Representation ℂ Γ (G.Om q) where
  toFun γ :=
    { toFun := fun w => ⟨fun s p => G.tr q γ (w.1 (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)), fun s =>
        ⟨(G.tr q γ).contDiff.comp_contDiffOn ((w.2 _).1.comp (G.ρ γ⁻¹).contDiff.contDiffOn (G.maps γ⁻¹)),
          fun p hp => by beta_reduce; rw [(w.2 _).2 _ (mt (G.ρ_mem_iff _ _).1 hp), map_zero]⟩⟩
      map_add' := fun w w' => by ext s p v; simp [Matrix.mulVec_add]
      map_smul' := fun c w => by ext s p v; simp [Matrix.mulVec_smul] }
  map_one' := by ext w s p v; simp
  map_mul' γ δ := by ext w s p v; simp

theorem act_apply (q : ℕ) (γ : Γ) (w : G.Om q) (s : S) (p : V) (v : Fin q → V) :
    (G.act q γ w).1 s p v = G.ξ γ *ᵥ w.1 (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) (fun i => G.ρ γ⁻¹ (v i)) := rfl

variable {G} in
theorem contDiffAt_Om {q : ℕ} (w : G.Om q) (s : S) {p : V} (hp : p ∈ G.Y) : ContDiffAt ℝ ∞ (w.1 s) p :=
  (w.2 s).1.contDiffAt (G.isOpen.mem_nhds hp)

variable {G} in
theorem differentiableAt_Om {q : ℕ} (w : G.Om q) (s : S) {p : V} (hp : p ∈ G.Y) : DifferentiableAt ℝ (w.1 s) p :=
  (contDiffAt_Om w s hp).differentiableAt (by simp)

def dOm (q : ℕ) : G.Om q →ₗ[ℂ] G.Om (q + 1) where
  toFun w := ⟨fun s => G.Y.indicator (extDeriv (w.1 s)), fun s =>
    ⟨((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V (Fin d → ℂ)).contDiff.comp_contDiffOn
        ((w.2 s).1.fderiv_of_isOpen G.isOpen (by simp))).congr fun p hp => Set.indicator_of_mem hp _,
      fun p hp => Set.indicator_of_notMem hp _⟩⟩
  map_add' w w' := by
    refine Subtype.ext (funext fun s => funext fun p => ?_)
    by_cases hp : p ∈ G.Y
    · simpa [Set.indicator_of_mem hp] using extDeriv_add (differentiableAt_Om w s hp) (differentiableAt_Om w' s hp)
    · simp [Set.indicator_of_notMem hp]
  map_smul' c w := by
    refine Subtype.ext (funext fun s => funext fun p => ?_)
    by_cases hp : p ∈ G.Y
    · simp only [Set.indicator_of_mem hp, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, extDeriv]
      rw [fderiv_const_smul (differentiableAt_Om w s hp)]
      ext v j
      simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Finset.mul_sum, mul_left_comm]
    · simp [Set.indicator_of_notMem hp]

theorem dOm_apply {q : ℕ} (w : G.Om q) (s : S) {p : V} (hp : p ∈ G.Y) : (G.dOm q w).1 s p = extDeriv (w.1 s) p :=
  Set.indicator_of_mem hp _

def incl : (S → Fin d → ℂ) →ₗ[ℂ] G.Om 0 where
  toFun f := ⟨fun s => G.Y.indicator fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) (f s), fun _ =>
    ⟨contDiffOn_const.congr fun _ hp => Set.indicator_of_mem hp _, fun _ hp => Set.indicator_of_notMem hp _⟩⟩
  map_add' f g := by ext s p v; by_cases hp : p ∈ G.Y <;> simp [hp]
  map_smul' c f := by ext s p v; by_cases hp : p ∈ G.Y <;> simp [hp]

theorem incl_apply (f : S → Fin d → ℂ) (s : S) {p : V} (hp : p ∈ G.Y) (v : Fin 0 → V) : (G.incl f).1 s p v = f s := by
  simp [incl, hp]

def Proper : Prop :=
  ∀ K ⊆ G.Y, IsCompact K → ∀ s s' : S, {γ : Γ | G.σ γ s = s' ∧ ∃ p ∈ K, G.ρ γ p ∈ K}.Finite

def IsWindow (W : S → Set V) : Prop :=
  (∀ s, IsOpen (W s) ∧ W s ⊆ G.Y) ∧ (∀ s, ∀ p ∈ G.Y, ∃ γ : Γ, G.ρ γ⁻¹ p ∈ W (G.σ γ⁻¹ s)) ∧
    ∀ s, ∀ p ∈ G.Y, ∃ N ∈ nhds p, {γ : Γ | ∃ x ∈ N, G.ρ γ⁻¹ x ∈ W (G.σ γ⁻¹ s)}.Finite

def IsCutoff (u : S → V → ℝ) : Prop :=
  (∀ s, ContDiffOn ℝ ∞ (u s) G.Y) ∧
    (∀ s, ∀ p ∈ G.Y, ∃ N ∈ nhds p, {γ : Γ | ∃ x ∈ N, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x) ≠ 0}.Finite) ∧
    ∀ s, ∀ p ∈ G.Y, ∑ᶠ γ : Γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) = 1

def IsInvGauge (l : S → V → ℝ) : Prop :=
  (∀ s, IsGauge G.Y (l s)) ∧ ∀ γ s, ∀ p ∈ G.Y, l (G.σ γ s) (G.ρ γ p) = l s p

end Geo

end UpperTheory.V.Lit.Dr
