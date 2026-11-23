import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BasicForm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep

noncomputable section

open ReciprocityTheory.ChartRestriction.DS Matrix

namespace GlobalTheory.Kg

section Abs

variable {R : Type} [Field R] [Algebra R ℂ] {P M : Type} [AddCommGroup P] [Module R P] [AddCommGroup M] [Module ℂ M]
  [Module R M] [IsScalarTower R ℂ M]

def gdR (L : P →ₗ[R] Module.End ℂ M) {q : ℕ} (f : P [⋀^Fin q]→ₗ[R] M) : P [⋀^Fin (q + 1)]→ₗ[R] M :=
  AlternatingMap.alternatizeUncurryFin
    { toFun := fun X => ((L X).restrictScalars R).compAlternatingMap f
      map_add' := fun X Y => AlternatingMap.ext fun v => LinearMap.congr_fun (map_add L X Y) (f v)
      map_smul' := fun c X => AlternatingMap.ext fun v => LinearMap.congr_fun (map_smul L c X) (f v) }

def gdel {J : Type} [Fintype J] (e : J → P) (D : J → Module.End ℂ M) {q : ℕ} (f : P [⋀^Fin (q + 1)]→ₗ[R] M) :
    P [⋀^Fin q]→ₗ[R] M :=
  ∑ j, ((D j).restrictScalars R).compAlternatingMap (f.curryLeft (e j))

def Cocl {J : Type} [Fintype J] (e : J → P) (D : J → Module.End ℂ M) : {q : ℕ} → (P [⋀^Fin q]→ₗ[R] M) → Prop
  | 0, _ => True
  | _ + 1, f => gdel e D f = 0

def lapl {J : Type} [Fintype J] (e : J → P) (L : P →ₗ[R] Module.End ℂ M) (D : J → Module.End ℂ M) :
    {q : ℕ} → (P [⋀^Fin q]→ₗ[R] M) → P [⋀^Fin q]→ₗ[R] M
  | 0, f => gdel e D (gdR L f)
  | _ + 1, f => gdR L (gdel e D f) + gdel e D (gdR L f)

def coIp {J : Type} [Fintype J] (e : J → P) (H : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) {q : ℕ} (f g : P [⋀^Fin q]→ₗ[R] M) : ℂ :=
  ∑ I : Fin q → J, H (f fun i => e (I i)) (g fun i => e (I i))

def coIpStd {J : Type} [Fintype J] (e : J → P) (H : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) {q : ℕ} (f g : P [⋀^Fin q]→ₗ[R] M) : ℂ :=
  ((q.factorial : ℂ))⁻¹ * coIp e H f g

theorem coIpStd_zero {J : Type} [Fintype J] (e : J → P) (H : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (f g : P [⋀^Fin 0]→ₗ[R] M) :
    coIpStd e H f g = coIp e H f g := by
  simp [coIpStd]

def InfEq {Z : Type} (ad : Z → P → P) (θ : Z → Module.End ℂ M) {q : ℕ} (f : P [⋀^Fin q]→ₗ[R] M) : Prop :=
  ∀ z X, θ z (f X) = ∑ i, f (Function.update X i (ad z (X i)))

def infCo {Z : Type} (ad : Z → P → P) (θ : Z → Module.End ℂ M) (q : ℕ) : Submodule ℂ (P [⋀^Fin q]→ₗ[R] M) where
  carrier := {f | InfEq ad θ f}
  add_mem' {f g} hf hg z X := by
    simp only [AlternatingMap.add_apply, map_add, Finset.sum_add_distrib, hf z X, hg z X]
  zero_mem' z X := by simp
  smul_mem' c f hf z X := by
    simp only [AlternatingMap.smul_apply, map_smul, hf z X, Finset.smul_sum]

structure IsPos (H : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (N : Submodule ℂ M) : Prop where
  herm : ∀ x y, H y x = starRingEnd ℂ (H x y)
  nonneg : ∀ x ∈ N, 0 ≤ (H x x).re
  definite : ∀ x ∈ N, H x x = 0 → x = 0

end Abs

theorem gd_eq_gdR {P M : Type} [AddCommGroup P] [Module ℝ P] [AddCommGroup M] [Module ℂ M] [Module ℝ M]
    [IsScalarTower ℝ ℂ M] (L : P →ₗ[ℝ] Module.End ℂ M) {q : ℕ} (f : P [⋀^Fin q]→ₗ[ℝ] M) :
    GlobalTheory.BorelCoh.gd L f = gdR L f := rfl

section Unitary

variable {T : Type} [Fintype T] [DecidableEq T] {n : ℕ}

def pC (ε : T → Fin n → Bool) : Submodule ℂ (T → Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | ∀ τ a b, ε τ a = ε τ b → X τ a b = 0}
  add_mem' {X Y} hX hY τ a b h := by simp [hX τ a b h, hY τ a b h]
  zero_mem' τ a b _ := rfl
  smul_mem' c X hX τ a b h := by simp [hX τ a b h]

abbrev NC (ε : T → Fin n → Bool) : Type := {x : T × Fin n × Fin n // ε x.1 x.2.1 ≠ ε x.1 x.2.2}

abbrev CP (ε : T → Fin n → Bool) : Type := {x : T × Fin n × Fin n // ε x.1 x.2.1 = ε x.1 x.2.2}

def eNC {ε : T → Fin n → Bool} (x : NC ε) : pC ε :=
  ⟨fun τ a b => if τ = x.1.1 ∧ a = x.1.2.1 ∧ b = x.1.2.2 then 1 else 0, fun τ a b h => by
    refine if_neg ?_
    rintro ⟨rfl, rfl, rfl⟩
    exact x.2 h⟩

def adC {ε : T → Fin n → Bool} (z : CP ε) (X : pC ε) : pC ε :=
  ⟨fun τ a b => if τ = z.1.1 then
      (if a = z.1.2.1 then X.1 τ z.1.2.2 b else 0) - (if b = z.1.2.2 then X.1 τ a z.1.2.1 else 0) else 0,
    fun τ a b h => by
      have hz := z.2
      by_cases hτ : τ = z.1.1
      · subst hτ
        have h1 : (if a = z.1.2.1 then X.1 z.1.1 z.1.2.2 b else 0) = 0 := by
          split_ifs with ha
          · exact X.2 _ _ _ (by rw [← hz, ← ha, h])
          · rfl
        have h2 : (if b = z.1.2.2 then X.1 z.1.1 a z.1.2.1 else 0) = 0 := by
          split_ifs with hb
          · exact X.2 _ _ _ (by rw [hz, ← hb, h])
          · rfl
        simp only [if_true, h1, h2, sub_zero]
      · exact if_neg hτ⟩

def prP {ε : T → Fin n → Bool} (τ₀ : T) (X : pC ε) : pC ε :=
  ⟨fun τ a b => if τ = τ₀ ∧ ε τ a = true then X.1 τ a b else 0, fun τ a b h => by
    have := X.2 τ a b h
    simp [this]⟩

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def IsGlFam (E : T → Fin n → Fin n → Module.End ℂ W) : Prop :=
  (∀ τ, IsGlRep (E τ)) ∧ ∀ τ τ', τ ≠ τ' → ∀ a b c d, Commute (E τ a b) (E τ' c d)

def actP (ε : T → Fin n → Bool) (E : T → Fin n → Fin n → Module.End ℂ W) : pC ε →ₗ[ℂ] Module.End ℂ W where
  toFun X := ∑ τ, actM (E τ) (X.1 τ)
  map_add' X Y := by simp [actM, add_smul, Finset.sum_add_distrib]
  map_smul' c X := by simp [actM, Finset.smul_sum, smul_smul]

def coC (ε : T → Fin n → Bool) (E : T → Fin n → Fin n → Module.End ℂ W) (q : ℕ) :
    Submodule ℂ (pC ε [⋀^Fin q]→ₗ[ℂ] W) :=
  infCo (adC (ε := ε)) (fun z => E z.1.1 z.1.2.1 z.1.2.2) q

def trOp {ε : T → Fin n → Bool} (E : T → Fin n → Fin n → Module.End ℂ W) (x : NC ε) : Module.End ℂ W :=
  E x.1.1 x.1.2.2 x.1.2.1

variable {M : Type} [AddCommGroup M] [Module ℂ M] {d : ℕ}

def onEach (d : ℕ) (A : Module.End ℂ M) : Module.End ℂ (Fin d → M) := A.compLeft (Fin d)

def onIdx (M : Type) [AddCommGroup M] [Module ℂ M] (x : Matrix (Fin d) (Fin d) ℂ) : Module.End ℂ (Fin d → M) :=
  LinearMap.pi fun i => ∑ j, x i j • LinearMap.proj j

def famA (d : ℕ) (E : T → Fin n → Fin n → Module.End ℂ M) : T → Fin n → Fin n → Module.End ℂ (Fin d → M) :=
  fun τ a b => onEach d (E τ a b)

def famB (M : Type) [AddCommGroup M] [Module ℂ M] (ξ : T → Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) :
    T → Fin n → Fin n → Module.End ℂ (Fin d → M) := fun τ a b => onIdx M (ξ τ a b)

def famT (E : T → Fin n → Fin n → Module.End ℂ M) (ξ : T → Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) :
    T → Fin n → Fin n → Module.End ℂ (Fin d → M) := famA d E + famB M ξ

def codOp {ε : T → Fin n → Bool} (E : T → Fin n → Fin n → Module.End ℂ M)
    (ξ : T → Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) (x : NC ε) : Module.End ℂ (Fin d → M) :=
  trOp (famB M ξ) x - trOp (famA d E) x

theorem codOp_eq {ε : T → Fin n → Bool} (E : T → Fin n → Fin n → Module.End ℂ M)
    (ξ : T → Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) :
    codOp (ε := ε) E ξ = fun x => trOp (famB M ξ) x - trOp (famA d E) x := rfl

theorem trOp_apply {ε : T → Fin n → Bool} (E : T → Fin n → Fin n → Module.End ℂ M) (x : NC ε) :
    trOp E x = E x.1.1 x.1.2.2 x.1.2.1 := rfl

structure IsAlgLow (ξ : T → Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) (κ : T → Fin n → ℝ) : Prop where
  gl : IsGlFam fun τ a b => Matrix.toLin' (ξ τ a b)
  adj : ∀ τ a b, (ξ τ a b)ᴴ = ξ τ b a
  low : ∃ v : Fin d → ℂ, v ≠ 0 ∧ (∀ τ a, ξ τ a a *ᵥ v = (κ τ a : ℂ) • v) ∧ (∀ τ a b, b < a → ξ τ a b *ᵥ v = 0) ∧
    ∀ S : Submodule ℂ (Fin d → ℂ), v ∈ S → (∀ τ a b, ∀ w ∈ S, ξ τ a b *ᵥ w ∈ S) → S = ⊤

def zXi (ε : T → Fin n → Bool) (ξ : T → Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) (τ : T) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ a ∈ Finset.univ.filter fun a => ε τ a = true, ξ τ a a

def hodgeCo (ε : T → Fin n → Bool) (E : T → Fin n → Fin n → Module.End ℂ M)
    (ξ : T → Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) (q : ℕ) (p : T → ℝ) :
    Submodule ℂ (pC ε [⋀^Fin q]→ₗ[ℂ] (Fin d → M)) where
  carrier := {f | f ∈ coC ε (famT E ξ) q ∧ ∀ τ X,
    ∑ i, f (Function.update X i (prP τ (X i))) - onIdx M (zXi ε ξ τ) (f X) = (p τ : ℂ) • f X}
  add_mem' {f g} hf hg := ⟨add_mem hf.1 hg.1, fun τ X => by
    simp only [AlternatingMap.add_apply, map_add, Finset.sum_add_distrib, smul_add, ← hf.2 τ X, ← hg.2 τ X]
    abel⟩
  zero_mem' := ⟨zero_mem _, fun τ X => by simp⟩
  smul_mem' c f hf := ⟨Submodule.smul_mem _ c hf.1, fun τ X => by
    simp only [AlternatingMap.smul_apply, map_smul, ← Finset.smul_sum, ← smul_sub, hf.2 τ X]
    exact smul_comm _ _ _⟩

def IsKHWFam (ε : T → Fin n → Bool) (E : T → Fin n → Fin n → Module.End ℂ M) (μ : T → Fin n → ℝ) (v : M) : Prop :=
  ∀ τ, IsKHWVec (ε τ) (E τ) (μ τ) v

def InCone (Λ μ : Fin n → ℝ) : Prop :=
  ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b) ∧ μ = Λ + ∑ a, ∑ b, (c a b : ℝ) • root a b

def posP (ε : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun x : Fin n × Fin n => x.1 < x.2 ∧ ε x.1 = true ∧ ε x.2 = false).card

end Unitary

section Form

variable {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

def tupIp (d : ℕ) (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] :
    (Fin d → M) →ₗ⋆[ℂ] (Fin d → M) →ₗ[ℂ] ℂ :=
  ∑ i, ((innerₛₗ ℂ (E := M)) ∘ₛₗ LinearMap.proj i).compl₂ (LinearMap.proj i)

end Form

theorem isAlgLow_zero {T : Type} [Fintype T] [DecidableEq T] (n : ℕ) :
    IsAlgLow (T := T) (n := n) (d := 1) (fun _ _ _ => 0) (fun _ _ => 0) := by
  refine ⟨⟨fun τ a b c d => by simp, fun _ _ _ _ _ _ _ => by simp⟩, fun _ _ _ => by simp, fun _ => 1, ?_, by simp, by simp, ?_⟩
  · intro h
    simpa using congrFun h 0
  · intro S hS _
    refine eq_top_iff.2 fun w _ => ?_
    have : w = w 0 • fun _ => (1 : ℂ) := by
      funext i
      fin_cases i
      simp
    rw [this]
    exact S.smul_mem _ hS

section Basic₂

example {T : Type} [Fintype T] [DecidableEq T] {n : ℕ} {ε : T → Fin n → Bool} {M : Type} [AddCommGroup M] [Module ℂ M]
    (E : T → Fin n → Fin n → Module.End ℂ M) (ξ : T → Fin n → Fin n → Matrix (Fin 1) (Fin 1) ℂ) (x : NC ε)
    (v : Fin 1 → M) :
    codOp E ξ x v 0 = ξ x.1.1 x.1.2.2 x.1.2.1 0 0 • v 0 - E x.1.1 x.1.2.2 x.1.2.1 (v 0) := by
  simp [codOp, trOp, famA, famB, onEach, onIdx]

example {P M J : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup M] [Module ℂ M] [Fintype J] (e : J → P)
    (H : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (f g : P [⋀^Fin 2]→ₗ[ℂ] M) :
    coIpStd e H f g = (1 / 2 : ℂ) * coIp e H f g := by
  simp [coIpStd, Nat.factorial]

end Basic₂

end GlobalTheory.Kg

end
