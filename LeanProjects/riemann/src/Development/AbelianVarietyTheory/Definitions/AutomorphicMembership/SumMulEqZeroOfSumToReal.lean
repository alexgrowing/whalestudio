import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqZeroOfApplySelf

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM

namespace GlobalTheory.PolFan

section Forms

variable {O : Type} [CommRing O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X]
  {X₁ : Type} [AddCommGroup X₁] [Module O X₁]

def balForms : Submodule ℤ (LinearMap.BilinForm ℤ X) where
  carrier := {β | (∀ y z, β y z = β z y) ∧ ∀ (a : O) y z, β (a • y) z = β y (bar a • z)}
  add_mem' := by
    rintro β γ ⟨h1, h2⟩ ⟨k1, k2⟩
    exact ⟨fun y z => by simp only [LinearMap.add_apply, h1 y z, k1 y z],
      fun a y z => by simp only [LinearMap.add_apply, h2 a y z, k2 a y z]⟩
  zero_mem' := by simp
  smul_mem' := by
    rintro n β ⟨h1, h2⟩
    exact ⟨fun y z => by simp only [LinearMap.smul_apply, h1 y z],
      fun a y z => by simp only [LinearMap.smul_apply, h2 a y z]⟩

def realForms : Submodule ℝ (X →ₗ[ℤ] X →ₗ[ℤ] ℝ) where
  carrier := {B | (∀ y z, B y z = B z y) ∧ ∀ (a : O) y z, B (a • y) z = B y (bar a • z)}
  add_mem' := by
    rintro β γ ⟨h1, h2⟩ ⟨k1, k2⟩
    exact ⟨fun y z => by simp only [LinearMap.add_apply, h1 y z, k1 y z],
      fun a y z => by simp only [LinearMap.add_apply, h2 a y z, k2 a y z]⟩
  zero_mem' := by simp
  smul_mem' := by
    rintro n β ⟨h1, h2⟩
    exact ⟨fun y z => by simp only [LinearMap.smul_apply, h1 y z],
      fun a y z => by simp only [LinearMap.smul_apply, h2 a y z]⟩

variable {bar X}

theorem mem_balForms {β : LinearMap.BilinForm ℤ X} : β ∈ balForms bar X ↔
    (∀ y z, β y z = β z y) ∧ ∀ (a : O) y z, β (a • y) z = β y (bar a • z) := Iff.rfl

theorem mem_realForms {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} : B ∈ realForms bar X ↔
    (∀ y z, B y z = B z y) ∧ ∀ (a : O) y z, B (a • y) z = B y (bar a • z) := Iff.rfl

theorem balForms_eq_levelForms {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type)
    [AddCommGroup X] [Module (𝓞 E) X] : balForms H.bar X = levelForms H 1 X := by
  ext β
  simp [mem_balForms, mem_levelForms]

theorem mem_realForms_iff_symB {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X : Type}
    [AddCommGroup X] [Module (𝓞 E) X] {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} :
    B ∈ realForms H.bar X ↔ B ∈ Formalism.MainNotions.ModuliIntegralCharts.SymB (fun x : E => IsCMField.complexConj E x) X :=
  and_congr_right' ⟨fun h c c' hc a b => by
    rw [show c' = H.bar c from RingOfIntegers.ext (hc.trans (H.bar_eq c).symm)]; exact h c a b,
    fun h c a b => h c _ (H.bar_eq c) a b⟩

theorem mem_balForms_int {X : Type} [AddCommGroup X] {β : LinearMap.BilinForm ℤ X} :
    β ∈ balForms (id : ℤ → ℤ) X ↔ ∀ y z, β y z = β z y :=
  ⟨fun h => h.1, fun h => ⟨h, fun a y z => by simp⟩⟩

def pull (r : X →ₗ[O] X₁) (β : LinearMap.BilinForm ℤ X₁) : LinearMap.BilinForm ℤ X :=
  β.compl₁₂ r.toAddMonoidHom.toIntLinearMap r.toAddMonoidHom.toIntLinearMap

@[simp] theorem pull_apply (r : X →ₗ[O] X₁) (β : LinearMap.BilinForm ℤ X₁) (a b : X) : pull r β a b = β (r a) (r b) := rfl

theorem pull_mem (r : X →ₗ[O] X₁) {β : LinearMap.BilinForm ℤ X₁} (h : β ∈ balForms bar X₁) : pull r β ∈ balForms bar X :=
  ⟨fun y z => h.1 _ _, fun a y z => by simp only [pull_apply, map_smul, h.2 a]⟩

variable (bar) in

def pullBal (r : X →ₗ[O] X₁) : balForms bar X₁ →ₗ[ℤ] balForms bar X where
  toFun β := ⟨pull r β, pull_mem r β.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (bar) in

def pullBalEquiv (e : X ≃ₗ[O] X₁) : balForms bar X₁ ≃ₗ[ℤ] balForms bar X :=
  LinearEquiv.ofLinear (pullBal bar e.toLinearMap) (pullBal bar e.symm.toLinearMap)
    (by ext β a b; exact congrArg₂ (fun y z => β.1 y z) (e.symm_apply_apply a) (e.symm_apply_apply b))
    (by ext β a b; exact congrArg₂ (fun y z => β.1 y z) (e.apply_symm_apply a) (e.apply_symm_apply b))

def toReal (β : LinearMap.BilinForm ℤ X) : X →ₗ[ℤ] X →ₗ[ℤ] ℝ := β.compr₂ (Algebra.linearMap ℤ ℝ)

@[simp] theorem toReal_apply (β : LinearMap.BilinForm ℤ X) (a b : X) : toReal β a b = (β a b : ℝ) := by simp [toReal]

theorem toReal_mem {β : LinearMap.BilinForm ℤ X} (h : β ∈ balForms bar X) : toReal β ∈ realForms bar X :=
  ⟨fun y z => by simp only [toReal_apply, h.1 y z], fun a y z => by simp only [toReal_apply, h.2 a y z]⟩

theorem sum_mul_eq_zero_of_sum_toReal {L ι : Type} [AddCommGroup L] [Fintype ι] {j : L →ₗ[ℤ] LinearMap.BilinForm ℤ X}
    (hj : Function.Injective j) (ℓ : L →ₗ[ℤ] ℤ) {β : ι → L} {c : ι → ℝ} (h : ∑ i, c i • toReal (j (β i)) = 0) :
    ∑ i, c i * (ℓ (β i) : ℝ) = 0 := by
  have key : ∀ (f : Module.Dual ℚ ℝ) (z : ι → ℤ), f (∑ i, c i * (z i : ℝ)) = ∑ i, f (c i) * z i := fun f z => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  refine (Module.forall_dual_apply_eq_zero_iff ℚ _).1 fun f => ?_
  obtain ⟨⟨D, hD⟩, hn⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) fun i => f (c i)
  choose n hn using hn
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hD
  have hn' : ∀ z : ι → ℤ, ((∑ i, n i * z i : ℤ) : ℚ) = D * ∑ i, f (c i) * z i := fun z => by
    rw [Finset.mul_sum, Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (n i : ℚ) = D * f (c i) := by simpa [Submonoid.smul_def] using hn i
    rw [Int.cast_mul, this, mul_assoc]
  have h0 : ∑ i, n i • β i = 0 := hj (LinearMap.ext₂ fun a b => by
    have h1 : ∑ i, c i * (j (β i) a b : ℝ) = 0 := by simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ h a b
    have h2 := hn' fun i => j (β i) a b
    rw [← key, h1, map_zero, mul_zero] at h2
    simpa [LinearMap.sum_apply] using (by exact_mod_cast h2 : ∑ i, n i * j (β i) a b = 0))
  have h3 := hn' fun i => ℓ (β i)
  rw [show ∑ i, n i * ℓ (β i) = 0 by simpa using congrArg ℓ h0] at h3
  rw [key]
  exact (mul_eq_zero.1 (h3.symm.trans Int.cast_zero)).resolve_left hD'

def pullR (r : X →ₗ[O] X₁) (B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) : X →ₗ[ℤ] X →ₗ[ℤ] ℝ :=
  B.compl₁₂ r.toAddMonoidHom.toIntLinearMap r.toAddMonoidHom.toIntLinearMap

@[simp] theorem pullR_apply (r : X →ₗ[O] X₁) (B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (a b : X) : pullR r B a b = B (r a) (r b) := rfl

def IsPosDef (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → X), LinearIndependent ℤ x → ∀ c : Fin n → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * B (x i) (x j)

theorem IsPosDef.nonneg {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : IsPosDef B) (y : X) : 0 ≤ B y y := by
  by_cases hy : LinearIndependent ℤ ![y]
  · simpa using (h 1 _ hy ![1] (by simp)).le
  · obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hy
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have h0 : g 0 • y = 0 := by simpa using hg
    have h1 : (g 0 : ℝ) * B y y = 0 := by
      rw [← zsmul_eq_mul, ← map_smul, h0, map_zero]
    exact ((mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hi)).ge

theorem isPosDef_iff_basis {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    IsPosDef B ↔ ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * B (b i) (b j) := by
  constructor
  · intro h c hc
    let e := (Fintype.equivFin ι).symm
    have := h _ (b ∘ e) (b.linearIndependent.comp e e.injective) (c ∘ e) fun h0 => hc (by
      ext i; simpa using congrFun h0 (e.symm i))
    simp only [Function.comp] at this
    rw [← e.sum_comp]
    simpa only [← e.sum_comp (fun j => _ * c j * B _ (b j))] using this
  · intro h n x hx c hc
    have h1 : LinearIndependent ℤ fun i => b.equivFun (x i) := hx.map' b.equivFun.toLinearMap b.equivFun.ker
    have h2 := (linearIndependent_algebraMap_comp_iff (S := ℝ)).2 h1
    have h3 : (fun k => ∑ i, c i * (b.repr (x i) k : ℝ)) ≠ 0 := fun h0 => hc (by
      ext i
      refine Fintype.linearIndependent_iff.1 h2 c ?_ i
      ext k
      simpa using congrFun h0 k)
    refine (h _ h3).trans_eq ?_
    have hx' : ∀ i j, B (x i) (x j) = ∑ k, ∑ l, (b.repr (x i) k : ℝ) * (b.repr (x j) l : ℝ) * B (b k) (b l) := fun i j => by
      conv_lhs => rw [← b.sum_repr (x i), ← b.sum_repr (x j)]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    simp only [hx', Finset.mul_sum, Finset.sum_mul]
    calc _ = ∑ k, ∑ l, ∑ i, ∑ j, c i * c j * ((b.repr (x i) k : ℝ) * (b.repr (x j) l : ℝ) * B (b k) (b l)) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ k, ∑ i, ∑ j, ∑ l, c i * c j * ((b.repr (x i) k : ℝ) * (b.repr (x j) l : ℝ) * B (b k) (b l)) :=
          Finset.sum_congr rfl fun k _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

variable (bar X) in

def psdCone : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :=
  {B | ∃ (X₁ : Type) (_ : AddCommGroup X₁) (_ : Module O X₁) (_ : Module.Projective O X₁) (r : X →ₗ[O] X₁)
    (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ), Function.Surjective r ∧ B₁ ∈ realForms bar X₁ ∧ IsPosDef B₁ ∧
    ∀ a b, B a b = B₁ (r a) (r b)}

theorem mem_realForms_of_mem_psdCone {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : B ∈ psdCone bar X) : B ∈ realForms bar X := by
  obtain ⟨X₁, _, _, _, r, B₁, -, h1, -, h2⟩ := h
  exact ⟨fun y z => by rw [h2, h2, h1.1], fun a y z => by rw [h2, h2, r.map_smul, r.map_smul, h1.2]⟩

theorem nonneg_of_mem_psdCone {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : B ∈ psdCone bar X) (y : X) : 0 ≤ B y y := by
  obtain ⟨X₁, _, _, _, r, B₁, -, -, h1, h2⟩ := h
  exact h2 y y ▸ h1.nonneg _

theorem IsPosDef.mem_psdCone [Module.Projective O X] {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : IsPosDef B) (hB : B ∈ realForms bar X) :
    B ∈ psdCone bar X := ⟨X, _, _, inferInstance, LinearMap.id, B, Function.surjective_id, hB, h, fun _ _ => rfl⟩

theorem mem_psdCone_of_comp {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ}
    (h : B₁ ∈ psdCone bar X₁) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : ∀ a b, B a b = B₁ (r a) (r b)) : B ∈ psdCone bar X := by
  obtain ⟨X₂, _, _, _, s, B₂, hs, h1, h2, h3⟩ := h
  exact ⟨X₂, _, _, inferInstance, s ∘ₗ r, B₂, hs.comp hr, h1, h2, fun a b => by rw [hB, h3]; rfl⟩

theorem pullR_mem_psdCone {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ}
    (h : B₁ ∈ psdCone bar X₁) : pullR r B₁ ∈ psdCone bar X := mem_psdCone_of_comp hr h fun _ _ => rfl

theorem zero_mem_psdCone : (0 : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) ∈ psdCone bar X :=
  ⟨PUnit, _, _, inferInstance, 0, 0, fun _ => ⟨0, rfl⟩, zero_mem _, fun n x hx c hc => by
    obtain ⟨i, -⟩ := Function.ne_iff.1 hc
    exact (hx.ne_zero i rfl).elim, fun _ _ => rfl⟩

theorem smul_mem_psdCone {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : B ∈ psdCone bar X) {t : ℝ} (ht : 0 ≤ t) : t • B ∈ psdCone bar X := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [zero_smul]; exact zero_mem_psdCone
  obtain ⟨X₁, _, _, _, r, B₁, hr, h1, h2, h3⟩ := h
  refine ⟨X₁, _, _, inferInstance, r, t • B₁, hr, Submodule.smul_mem _ _ h1, fun n x hx c hc => ?_,
    fun a b => by simp [h3]⟩
  refine (mul_pos ht (h2 n x hx c hc)).trans_eq ?_
  simp only [Finset.mul_sum, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Forms

section Part

variable {L L' : Type} [AddCommGroup L] [AddCommGroup L'] {m m' : ℕ}

theorem isPartOfBasis_map {v : Fin m → L} (h : IsPartOfBasis v) (e : L ≃ₗ[ℤ] L') : IsPartOfBasis fun i => e (v i) := by
  obtain ⟨n, b, hb⟩ := h
  exact ⟨n, b.map e, fun i => by simp [hb]⟩

theorem isPartOfBasis_comp {v : Fin m → L} (h : IsPartOfBasis v) (s : Fin m' ↪ Fin m) : IsPartOfBasis fun i => v (s i) := by
  classical
  obtain ⟨n, b, hb⟩ := h
  let f : Fin m' ↪ Fin m ⊕ Fin n := s.trans ⟨Sum.inl, Sum.inl_injective⟩
  let e : Fin m' ⊕ Fin _ ≃ Fin m ⊕ Fin n :=
    ((Equiv.ofInjective f f.injective).sumCongr (Fintype.equivFin _).symm).trans (Equiv.Set.sumCompl (Set.range f))
  exact ⟨_, b.reindex e.symm, fun i => by simp [e, f, hb]⟩

end Part

section Cones

variable {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
  {X₁ : Type} [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] {m m' : ℕ}

def evalR (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : ℝ := φ.eval X fun a b => B a b

@[simp] theorem evalR_toReal (β : LinearMap.BilinForm ℤ X) : evalR φ (toReal β) = φ.evalZ β := by
  simp [evalR, InvFun.evalZ]

theorem evalR_pullR {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) :
    evalR φ (pullR r B) = evalR φ B := φ.eval_comp hr fun a b => B a b

theorem evalZ_pull {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (β : LinearMap.BilinForm ℤ X₁) :
    φ.evalZ (pull r β) = φ.evalZ β := φ.eval_comp hr fun a b => (β a b : ℝ)

@[simp] theorem evalR_zero : evalR φ (0 : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) = 0 :=
  (φ.eval_comp (X₁ := PUnit) (r := 0) (fun _ => ⟨0, rfl⟩) fun _ _ => 0).trans (φ.eval_of_subsingleton _)

theorem linearOn_iff (γ : Fin m → LinearMap.BilinForm ℤ X) : φ.LinearOn γ ↔
    ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → evalR φ (∑ i, c i • toReal (γ i)) = ∑ i, c i * φ.evalZ (γ i) := by
  simp [InvFun.LinearOn, evalR, LinearMap.sum_apply]

variable {φ} in

theorem linearOn_comp {γ : Fin m → LinearMap.BilinForm ℤ X} (h : φ.LinearOn γ) (s : Fin m' ↪ Fin m) :
    φ.LinearOn fun i => γ (s i) := by
  intro c hc
  have key : ∀ f : Fin m → ℝ, ∑ j, Function.extend s c 0 j * f j = ∑ i, c i * f (s i) := fun f => by
    symm
    refine Fintype.sum_of_injective s s.injective _ _ (fun j hj => ?_) fun i => by rw [s.injective.extend_apply]
    rw [Function.extend_apply' _ _ _ hj]; simp
  have := h (Function.extend s c 0) fun j => by
    by_cases hj : ∃ i, s i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [s.injective.extend_apply]; exact hc i
    · rw [Function.extend_apply' _ _ _ hj]; rfl
  simpa only [key] using this

variable {φ} in

theorem linearOn_pull_iff {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {γ : Fin m → LinearMap.BilinForm ℤ X₁} :
    (φ.LinearOn fun i => pull r (γ i)) ↔ φ.LinearOn γ := by
  refine forall₂_congr fun c _ => ?_
  simp only [evalZ_pull φ hr, pull_apply]
  rw [φ.eval_comp hr fun a b => ∑ i, c i * (γ i a b : ℝ)]

def IsStrict (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ (∀ i, (ℓ (γ i) : ℝ) = N * φ.evalZ (γ i)) ∧
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β ≤ ℓ β) ∧
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β = ℓ β →
      ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • γ i

theorem isStrict_iff_isStrictAt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E))
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (γ : Fin m → LinearMap.BilinForm ℤ X) :
    IsStrict H.bar φ γ ↔ IsStrictAt H φ γ := by
  simp only [IsStrict, IsStrictAt, IsPiece, balForms_eq_levelForms, and_assoc]

structure IsCone (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop where

  mem : ∀ i, γ i ∈ balForms bar X

  nonneg : ∀ i y, 0 ≤ γ i y y

  basis : IsPartOfBasis fun i => (⟨γ i, mem i⟩ : balForms bar X)

  linear : φ.LinearOn γ

  strict : IsStrict bar φ γ

variable {bar φ}

theorem IsStrict.reindex {γ : Fin m → LinearMap.BilinForm ℤ X} (h : IsStrict bar φ γ) (s : Fin m' ≃ Fin m) :
    IsStrict bar φ fun i => γ (s i) := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := h
  refine ⟨N, ℓ, hN, fun i => h1 _, h2, fun β hβ hp he => ?_⟩
  obtain ⟨k, c, hk, hc⟩ := h3 β hβ hp he
  exact ⟨k, c ∘ s, hk, hc.trans (s.sum_comp fun i => c i • γ i).symm⟩

theorem IsStrict.of_pull {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {γ : Fin m → LinearMap.BilinForm ℤ X₁}
    (h : IsStrict bar φ fun i => pull r (γ i)) : IsStrict bar φ γ := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := h
  let P : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X :=
    { toFun := pull r, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  refine ⟨N, ℓ ∘ₗ P, hN, fun i => (h1 i).trans (by rw [evalZ_pull φ hr]), fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · rw [← evalZ_pull φ hr]
    exact h2 _ (pull_mem r hβ) fun y => hp _
  · rw [← evalZ_pull φ hr] at he
    obtain ⟨k, c, hk, hc⟩ := h3 _ (pull_mem r hβ) (fun y => hp _) he
    refine ⟨k, c, hk, LinearMap.ext₂ fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hc a b

omit [Module.Finite O X] [Module.Finite O X₁] in

@[simp] theorem pull_symm_pull (e : X ≃ₗ[O] X₁) (β : LinearMap.BilinForm ℤ X₁) :
    pull e.symm.toLinearMap (pull e.toLinearMap β) = β := LinearMap.ext₂ fun a b => by simp

omit [Module.Finite O X] [Module.Finite O X₁] in

@[simp] theorem pull_pull_symm (e : X ≃ₗ[O] X₁) (β : LinearMap.BilinForm ℤ X) :
    pull e.toLinearMap (pull e.symm.toLinearMap β) = β := LinearMap.ext₂ fun a b => by simp

namespace IsCone

variable {γ : Fin m → LinearMap.BilinForm ℤ X}

theorem linearIndependent (h : IsCone bar φ γ) : LinearIndependent ℤ γ :=
  h.basis.linearIndependent.map' (balForms bar X).subtype (Submodule.ker_subtype _)

theorem injective (h : IsCone bar φ γ) : Function.Injective γ := h.linearIndependent.injective

theorem comp (h : IsCone bar φ γ) (s : Fin m' ↪ Fin m) (hs : IsStrict bar φ fun i => γ (s i)) :
    IsCone bar φ fun i => γ (s i) :=
  ⟨fun _ => h.mem _, fun _ => h.nonneg _, isPartOfBasis_comp h.basis s, linearOn_comp h.linear s, hs⟩

theorem reindex (h : IsCone bar φ γ) (s : Fin m' ≃ Fin m) : IsCone bar φ fun i => γ (s i) :=
  h.comp s.toEmbedding (h.strict.reindex s)

theorem pull_equiv {γ : Fin m → LinearMap.BilinForm ℤ X₁} (h : IsCone bar φ γ) (e : X ≃ₗ[O] X₁) :
    IsCone bar φ fun i => pull e.toLinearMap (γ i) :=
  ⟨fun i => pull_mem _ (h.mem i), fun i _ => h.nonneg i _, isPartOfBasis_map h.basis (pullBalEquiv bar e),
    (linearOn_pull_iff e.surjective).2 h.linear,
    IsStrict.of_pull (r := e.symm.toLinearMap) e.symm.surjective (by simpa using h.strict)⟩

theorem evalZ_smul (h : IsCone bar φ γ) (M : ℕ) (i : Fin m) : φ.evalZ ((M : ℤ) • γ i) = M * φ.evalZ (γ i) := by
  have h1 : φ.LinearOn fun _ : Fin 1 => γ i :=
    linearOn_comp h.linear ⟨fun _ : Fin 1 => i, fun _ _ _ => Subsingleton.elim _ _⟩
  simpa [InvFun.evalZ] using h1 ![M] (by simp)

theorem linearOn_smul (h : IsCone bar φ γ) (M : ℕ) : φ.LinearOn fun i => (M : ℤ) • γ i := by
  intro c hc
  have := h.linear (fun i => c i * M) fun i => mul_nonneg (hc i) M.cast_nonneg
  simp only [h.evalZ_smul]
  simpa [mul_assoc] using this

theorem isStrict_smul (h : IsCone bar φ γ) {M : ℕ} (hM : M ≠ 0) : IsStrict bar φ fun i => (M : ℤ) • γ i := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := h.strict
  refine ⟨N, ℓ, hN, fun i => ?_, h2, fun β hβ hp he => ?_⟩
  · rw [h.evalZ_smul, map_smul, smul_eq_mul, Int.cast_mul, h1]; push_cast; ring
  · obtain ⟨k, c, hk, hc⟩ := h3 β hβ hp he
    refine ⟨M * k, c, by positivity, ?_⟩
    rw [mul_smul, hc, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [natCast_zsmul]; rw [smul_comm]

end IsCone

theorem IsCone.isPartOfBasis_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {φ : InvFun (𝓞 E)}
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] {γ : Fin m → LinearMap.BilinForm ℤ X}
    (h : IsCone H.bar φ γ) {M : ℕ} (hM : M ≠ 0) {δ : Fin m → levelForms H M X}
    (hδ : ∀ i, (δ i : LinearMap.BilinForm ℤ X) = (M : ℤ) • γ i) : IsPartOfBasis δ := by
  let f : balForms H.bar X →ₗ[ℤ] levelForms H M X :=
    ((M : ℤ) • (balForms H.bar X).subtype).codRestrict _ fun β =>
      (mem_levelForms_iff_smul hM).2 ⟨β, balForms_eq_levelForms H X ▸ β.2, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun β β' e => Subtype.ext (LinearMap.ext₂ fun a b => ?_), fun β => ?_⟩
    · have := LinearMap.congr_fun₂ (congrArg Subtype.val e) a b
      exact mul_left_cancel₀ (show (M : ℤ) ≠ 0 by exact_mod_cast hM) this
    · obtain ⟨β', h1, h2⟩ := (mem_levelForms_iff_smul hM).1 β.2
      exact ⟨⟨β', (balForms_eq_levelForms H X).symm ▸ h1⟩, Subtype.ext h2.symm⟩
  convert isPartOfBasis_map h.basis (LinearEquiv.ofBijective f hf) with i
  exact Subtype.ext (hδ i)

end Cones

section Fan

variable {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X]
  {X₁ : Type} [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] {m : ℕ}

structure IsPolFanOn : Prop where

  homog : ∀ B ∈ psdCone bar X, ∀ t : ℝ, 0 ≤ t → evalR φ (t • B) = t * evalR φ B

  superadd : ∀ B ∈ psdCone bar X, ∀ B' ∈ psdCone bar X, evalR φ B + evalR φ B' ≤ evalR φ (B + B')

  integral : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, φ.evalZ β = n

  pos : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < φ.evalZ β

  face : ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m), IsCone bar φ γ →
    IsCone bar φ fun i => γ (s i)

  cover : ∀ B ∈ psdCone bar X, ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCone bar φ γ ∧
    (∀ i, 0 ≤ c i) ∧ B = ∑ i, c i • toReal (γ i)

  finite : ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X),
    IsCone bar φ γ → ∃ e : X ≃ₗ[O] X, ∀ i, pull e.toLinearMap (γ i) ∈ S

def IsPolFan (bar : O → O) (q : ℕ) (φ : InvFun O) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    IsPolFanOn bar φ X

variable (O) {X} in

def NoEquivRays (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∀ (e : X ≃ₗ[O] X) (i j : Fin m), pull e.toLinearMap (γ i) = γ j → i = j

def NoSelfInt (bar : O → O) (q : ℕ) (φ : InvFun O) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone bar φ γ → NoEquivRays O γ

variable {bar φ X}

theorem IsPolFan.mono {q q' : ℕ} (h : IsPolFan bar q φ) (hq : q' ≤ q) : IsPolFan bar q' φ :=
  fun X _ _ _ _ hX => h X (hX.trans hq)

theorem NoSelfInt.mono {q q' : ℕ} (h : NoSelfInt bar q φ) (hq : q' ≤ q) : NoSelfInt bar q' φ :=
  fun X _ _ _ _ hX => h X (hX.trans hq)

theorem IsPolFanOn.evalZ_nonneg (h : IsPolFanOn bar φ X) {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X)
    (hp : ∀ y, 0 ≤ β y y) : 0 ≤ φ.evalZ β := by
  rcases eq_or_ne β 0 with rfl | h0
  · rw [← evalR_toReal, show toReal (0 : LinearMap.BilinForm ℤ X) = 0 from LinearMap.ext₂ fun _ _ => by simp, evalR_zero]
  · exact (h.pos β hβ hp h0).le

theorem IsPolFanOn.exists_nat (h : IsPolFanOn bar φ X) {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X)
    (hp : ∀ y, 0 ≤ β y y) : ∃ n : ℕ, φ.evalZ β = n := by
  obtain ⟨n, hn⟩ := h.integral β hβ hp
  have : (0 : ℝ) ≤ n := hn ▸ h.evalZ_nonneg hβ hp
  lift n to ℕ using by exact_mod_cast this
  exact ⟨n, by simpa using hn⟩

theorem IsPolFanOn.evalR_nonneg (h : IsPolFanOn bar φ X) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone bar X) :
    0 ≤ evalR φ B := by
  obtain ⟨m, γ, c, hγ, hc, rfl⟩ := h.cover B hB
  rw [(linearOn_iff φ γ).1 hγ.linear c hc]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (h.evalZ_nonneg (hγ.mem i) (hγ.nonneg i))

theorem evalR_smul_of_linearOn {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : φ.LinearOn γ) {c : Fin m → ℝ}
    (hc : ∀ i, 0 ≤ c i) {t : ℝ} (ht : 0 ≤ t) :
    evalR φ (t • ∑ i, c i • toReal (γ i)) = t * evalR φ (∑ i, c i • toReal (γ i)) := by
  rw [(linearOn_iff φ γ).1 hγ c hc, Finset.smul_sum, Finset.mul_sum]
  simp only [smul_smul, ← mul_assoc]
  exact (linearOn_iff φ γ).1 hγ _ fun i => mul_nonneg ht (hc i)

theorem IsPolFanOn.of_equiv (h : IsPolFanOn bar φ X) (e : X ≃ₗ[O] X₁) : IsPolFanOn bar φ X₁ where
  homog B hB t ht := by
    rw [← evalR_pullR φ (r := e.toLinearMap) e.surjective, ← evalR_pullR φ (r := e.toLinearMap) e.surjective B]
    exact h.homog _ (pullR_mem_psdCone e.surjective hB) t ht
  superadd B hB B' hB' := by
    simp only [← evalR_pullR φ (r := e.toLinearMap) e.surjective]
    exact h.superadd _ (pullR_mem_psdCone e.surjective hB) _ (pullR_mem_psdCone e.surjective hB')
  integral β hβ hp := by
    rw [← evalZ_pull φ (r := e.toLinearMap) e.surjective]
    exact h.integral _ (pull_mem _ hβ) fun y => hp _
  pos β hβ hp h0 := by
    rw [← evalZ_pull φ (r := e.toLinearMap) e.surjective]
    refine h.pos _ (pull_mem _ hβ) (fun y => hp _) fun h1 => h0 ?_
    rw [← pull_symm_pull e β, h1]; rfl
  face m m' γ s hγ := by simpa using (h.face _ _ _ s (hγ.pull_equiv e)).pull_equiv e.symm
  cover B hB := by
    obtain ⟨m, γ, c, hγ, hc, hs⟩ := h.cover _ (pullR_mem_psdCone (r := e.toLinearMap) e.surjective hB)
    refine ⟨m, _, c, hγ.pull_equiv e.symm, hc, LinearMap.ext₂ fun a b => ?_⟩
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hs (e.symm a) (e.symm b)
  finite := by
    obtain ⟨S, hS, h1⟩ := h.finite
    refine ⟨_, hS.image (pull e.symm.toLinearMap), fun m γ hγ => ?_⟩
    obtain ⟨g, hg⟩ := h1 m _ (hγ.pull_equiv e)
    exact ⟨e.symm.trans (g.trans e), fun i => ⟨_, hg i, rfl⟩⟩

omit [Module.Finite O X] [Module.Finite O X₁] in

theorem NoEquivRays.of_pull_equiv {γ : Fin m → LinearMap.BilinForm ℤ X₁} (e : X ≃ₗ[O] X₁)
    (h : NoEquivRays O fun i => pull e.toLinearMap (γ i)) : NoEquivRays O γ := fun g i j hg =>
  h (e.trans (g.trans e.symm)) i j (LinearMap.ext₂ fun a b => by simpa using LinearMap.congr_fun₂ hg (e a) (e b))

theorem isPolFanOn_of_subsingleton [Subsingleton X] : IsPolFanOn bar φ X := by
  have h0 : ∀ β : LinearMap.BilinForm ℤ X, β = 0 := fun β => Subsingleton.elim _ _
  have hc : ∀ (m : ℕ) [IsEmpty (Fin m)] (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone bar φ γ := fun m _ γ =>
    ⟨isEmptyElim, isEmptyElim, ⟨0, Module.Basis.empty _, isEmptyElim⟩,
      fun c _ => by simp [φ.eval_of_subsingleton],
      ⟨1, 0, one_pos, isEmptyElim, fun β _ _ => by simp [InvFun.evalZ, φ.eval_of_subsingleton],
        fun β _ _ _ => ⟨1, 0, one_pos, Subsingleton.elim _ _⟩⟩⟩
  refine ⟨fun B _ t _ => by simp [evalR, φ.eval_of_subsingleton], fun B _ B' _ => by simp [evalR, φ.eval_of_subsingleton],
    fun β _ _ => ⟨0, by simp [InvFun.evalZ, φ.eval_of_subsingleton]⟩, fun β _ _ h => (h (h0 β)).elim,
    fun m m' γ s hγ => ?_, fun B _ => ⟨0, ![], ![], hc 0 _, isEmptyElim, Subsingleton.elim _ _⟩,
    ⟨{0}, Set.finite_singleton _, fun m γ _ => ⟨LinearEquiv.refl _ _, fun i => h0 _⟩⟩⟩
  have : IsEmpty (Fin m') := ⟨fun i => hγ.linearIndependent.ne_zero (s i) (h0 _)⟩
  exact hc _ _

theorem isPolFan_zero [IsDomain O] : IsPolFan bar 0 φ := fun X _ _ _ _ hX =>
  haveI : Subsingleton X := Module.finrank_zero_iff.1 (Nat.le_zero.1 hX)
  isPolFanOn_of_subsingleton

theorem noSelfInt_zero [IsDomain O] : NoSelfInt bar 0 φ := fun X _ _ _ _ hX _ _ hγ _ i _ _ =>
  haveI : Subsingleton X := Module.finrank_zero_iff.1 (Nat.le_zero.1 hX)
  (hγ.linearIndependent.ne_zero i (Subsingleton.elim _ _)).elim

end Fan

section Fine

variable {X X₁ : Type} [AddCommGroup X] [AddCommGroup X₁] {m m' : ℕ}

def IsFine (N : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∀ y : X, ∃ μ₀ : X, ∀ i μ, γ i (y + N • μ₀) (y + N • μ₀) ≤ γ i (y + N • μ) (y + N • μ)

variable {N : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}

theorem IsFine.comp (h : IsFine N γ) (s : Fin m' → Fin m) : IsFine N fun i => γ (s i) :=
  fun y => (h y).imp fun _ h i => h (s i)

theorem IsFine.exists_min (h : IsFine N γ) (y : X) : ∃ μ₀ : X, ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → ∀ μ,
    ∑ i, c i * (γ i (y + N • μ₀) (y + N • μ₀) : ℝ) ≤ ∑ i, c i * (γ i (y + N • μ) (y + N • μ) : ℝ) :=
  (h y).imp fun _ h c hc μ => Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by exact_mod_cast h i μ) (hc i)

theorem IsFine.sum (h : IsFine N γ) (a : Fin m' → Fin m → ℕ) : IsFine N fun j => ∑ i, a j i • γ i :=
  fun y => (h y).imp fun _ h j μ => by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    exact Finset.sum_le_sum fun i _ => nsmul_le_nsmul_right (h i μ) _

theorem IsFine.smul (h : IsFine N γ) (M : ℕ) : IsFine N fun i => (M : ℤ) • γ i :=
  fun y => (h y).imp fun _ h i μ => mul_le_mul_of_nonneg_left (h i μ) (Int.natCast_nonneg M)

theorem isFine_pull_iff {O : Type} [CommRing O] [Module O X] [Module O X₁] {r : X →ₗ[O] X₁} (hr : Function.Surjective r)
    {γ : Fin m → LinearMap.BilinForm ℤ X₁} : (IsFine N fun i => pull r (γ i)) ↔ IsFine N γ := by
  constructor
  · intro h y
    obtain ⟨y, rfl⟩ := hr y
    obtain ⟨μ₀, h⟩ := h y
    refine ⟨r μ₀, fun i μ => ?_⟩
    obtain ⟨μ, rfl⟩ := hr μ
    simpa only [pull_apply, r.map_add, map_nsmul r] using h i μ
  · intro h y
    obtain ⟨μ₀, h⟩ := h (r y)
    obtain ⟨μ₀, rfl⟩ := hr μ₀
    exact ⟨μ₀, fun i μ => by simpa only [pull_apply, r.map_add, map_nsmul r] using h i (r μ)⟩

theorem isFine_one (h : ∀ i y, 0 ≤ γ i y y) : IsFine 1 γ := fun y => ⟨-y, fun i μ => by simpa using h i (y + μ)⟩

theorem isFine_single {β : LinearMap.BilinForm ℤ X} (h : ∀ y, 0 ≤ β y y) (N : ℕ) : IsFine N ![β] := fun y => by
  obtain ⟨μ₀, -, h0⟩ := (measure fun μ : X => (β (y + N • μ) (y + N • μ)).toNat).wf.has_min Set.univ ⟨0, trivial⟩
  refine ⟨μ₀, fun i μ => ?_⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have h1 : ¬ (β (y + N • μ) (y + N • μ)).toNat < (β (y + N • μ₀) (y + N • μ₀)).toNat := h0 μ trivial
  have := h (y + N • μ)
  have := h (y + N • μ₀)
  simp only [Matrix.cons_val_zero]
  omega

def sqForm (l : X →ₗ[ℤ] ℤ) : LinearMap.BilinForm ℤ X := (LinearMap.mul ℤ ℤ).compl₁₂ l l

@[simp] theorem sqForm_apply (l : X →ₗ[ℤ] ℤ) (a b : X) : sqForm l a b = l a * l b := rfl

example : ¬ IsFine 2 ![sqForm (LinearMap.fst ℤ ℤ ℤ + LinearMap.snd ℤ ℤ ℤ),
    sqForm (LinearMap.fst ℤ ℤ ℤ - LinearMap.snd ℤ ℤ ℤ)] := fun h => by
  obtain ⟨⟨a, b⟩, h⟩ := h (1, 1)
  have h0 := h 0 (0, -1)
  have h1 := h 1 (0, 0)
  simp at h0 h1
  have e0 : 1 + 2 * a + (1 + 2 * b) = 0 := by nlinarith
  have e1 : 1 + 2 * a - (1 + 2 * b) = 0 := by nlinarith
  omega

example : ¬ NoEquivRays ℤ ![sqForm (LinearMap.fst ℤ ℤ ℤ), sqForm (LinearMap.snd ℤ ℤ ℤ)] := fun h =>
  absurd (h (LinearEquiv.prodComm ℤ ℤ ℤ) 0 1 rfl) (by decide)

end Fine

section RankOne

def mulForm : LinearMap.BilinForm ℤ ℤ := LinearMap.mul ℤ ℤ

@[simp] theorem mulForm_apply (a b : ℤ) : mulForm a b = a * b := rfl

theorem real_apply_int (B : ℤ →ₗ[ℤ] ℤ →ₗ[ℤ] ℝ) (a b : ℤ) : B a b = B 1 1 * (a * b) := by
  conv_lhs => rw [← mul_one a, ← mul_one b, ← smul_eq_mul, ← smul_eq_mul, map_smul, map_smul]
  simp only [LinearMap.smul_apply, zsmul_eq_mul]; ring

theorem eq_smul_mulForm (β : LinearMap.BilinForm ℤ ℤ) : β = β 1 1 • mulForm := LinearMap.ext₂ fun a b => by
  have := real_apply_int (toReal β) a b
  simp only [toReal_apply] at this
  exact_mod_cast this

theorem evalR_minVal_int {B : ℤ →ₗ[ℤ] ℤ →ₗ[ℤ] ℝ} (h : 0 ≤ B 1 1) : evalR (InvFun.minVal ℤ) B = B 1 1 := by
  rw [evalR, TorCheck.minVal_eval]
  rcases h.eq_or_lt with h | h
  · rw [← h]
    convert Real.sInf_empty
    exact Set.eq_empty_of_forall_notMem fun x ⟨⟨y, e⟩, h'⟩ => h' (by rw [← e, real_apply_int, ← h]; simp)
  · refine IsLeast.csInf_eq ⟨⟨⟨1, rfl⟩, by simpa using h.ne'⟩, ?_⟩
    rintro x ⟨⟨y, rfl⟩, hy⟩
    have h0 : y ≠ 0 := fun e => hy (by rw [e])
    have : (1 : ℝ) ≤ (y : ℝ) * y := by exact_mod_cast (show 1 ≤ y * y from mul_self_pos.2 h0)
    rw [real_apply_int B y y]
    nlinarith

theorem evalZ_minVal_int {β : LinearMap.BilinForm ℤ ℤ} (h : 0 ≤ β 1 1) : (InvFun.minVal ℤ).evalZ β = β 1 1 := by
  rw [← evalR_toReal, evalR_minVal_int (by simpa using h), toReal_apply]

theorem isCone_mulForm : IsCone id (InvFun.minVal ℤ) ![mulForm] := by
  have hm : mulForm ∈ balForms (id : ℤ → ℤ) ℤ := mem_balForms_int.2 mul_comm
  let ev : LinearMap.BilinForm ℤ ℤ →ₗ[ℤ] ℤ := LinearMap.applyₗ 1 ∘ₗ LinearMap.applyₗ 1
  let e : balForms (id : ℤ → ℤ) ℤ ≃ₗ[ℤ] ℤ := LinearEquiv.ofLinear (ev ∘ₗ Submodule.subtype _)
    (LinearMap.toSpanSingleton ℤ _ ⟨mulForm, hm⟩) (by ext; simp [ev])
    (LinearMap.ext fun β => Subtype.ext (eq_smul_mulForm β.1).symm)
  refine ⟨fun i => by simpa using hm, fun i y => by simpa using mul_self_nonneg y,
    ⟨0, ((Module.Basis.singleton (Fin 1) ℤ).map e.symm).reindex (Equiv.sumEmpty _ _).symm, fun i => ?_⟩,
    TorCheck.minVal_linearOn _, 1, ev, one_pos, fun i => ?_, fun β _ hp => ?_, fun β _ hp _ => ?_⟩
  · apply Subtype.ext
    simp [e]
  · simp [ev, evalZ_minVal_int]
  · simp [ev, evalZ_minVal_int (hp 1)]
  · refine ⟨1, ![(β 1 1).toNat], one_pos, ?_⟩
    rw [one_smul, Fin.sum_univ_one, ← natCast_zsmul]
    simpa [Int.toNat_of_nonneg (hp 1), hp 1] using eq_smul_mulForm β

theorem isCone_empty_int {m : ℕ} [IsEmpty (Fin m)] (γ : Fin m → LinearMap.BilinForm ℤ ℤ) :
    IsCone id (InvFun.minVal ℤ) γ := by
  have hs : IsStrict id (InvFun.minVal ℤ) γ := by
    refine ⟨1, (2 : ℤ) • LinearMap.applyₗ 1 ∘ₗ LinearMap.applyₗ 1, one_pos, isEmptyElim, fun β _ hp => ?_,
      fun β _ hp he => ⟨1, 0, one_pos, ?_⟩⟩
    · have : (0 : ℝ) ≤ β 1 1 := by exact_mod_cast hp 1
      simp [evalZ_minVal_int (hp 1)]
      linarith
    · have : (β 1 1 : ℝ) = 0 := by
        simp [evalZ_minVal_int (hp 1)] at he
        linarith
      rw [eq_smul_mulForm β, show β 1 1 = 0 by exact_mod_cast this]
      simp
  have e : γ = fun i => ![mulForm] ((Function.Embedding.ofIsEmpty : Fin m ↪ Fin 1) i) := Subsingleton.elim _ _
  rw [e] at hs ⊢
  exact isCone_mulForm.comp _ hs

theorem IsCone.eq_mulForm {φ : InvFun ℤ} {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ ℤ} (h : IsCone id φ γ) (i : Fin m) :
    γ i = mulForm := by
  have hu : IsUnit (γ i 1 1) := h.basis.isUnit_of_smul (i := i) (w := ⟨mulForm, mem_balForms_int.2 mul_comm⟩)
    (Subtype.ext (eq_smul_mulForm _).symm)
  have := h.nonneg i 1
  rw [eq_smul_mulForm (γ i), show γ i 1 1 = 1 by rcases Int.isUnit_iff.1 hu with h | h <;> omega, one_smul]

theorem toReal_mulForm_mem_psdCone : toReal mulForm ∈ psdCone (id : ℤ → ℤ) ℤ :=
  ((isPosDef_iff_basis (Module.Basis.singleton Unit ℤ) _).2 fun c hc => by
    have : c () ≠ 0 := fun h => hc (funext fun _ => h)
    simpa using mul_self_pos.2 this).mem_psdCone (toReal_mem (mem_balForms_int.2 mul_comm))

theorem isPolFanOn_minVal_int : IsPolFanOn id (InvFun.minVal ℤ) ℤ where
  homog B hB t ht := by
    have := nonneg_of_mem_psdCone hB 1
    rw [evalR_minVal_int this, evalR_minVal_int (mul_nonneg ht this)]; rfl
  superadd B hB B' hB' := by
    have h := nonneg_of_mem_psdCone hB 1
    have h' := nonneg_of_mem_psdCone hB' 1
    rw [evalR_minVal_int h, evalR_minVal_int h', evalR_minVal_int (add_nonneg h h')]; rfl
  integral β _ hp := ⟨_, evalZ_minVal_int (hp 1)⟩
  pos β _ hp h0 := by
    rw [evalZ_minVal_int (hp 1)]
    exact_mod_cast (hp 1).lt_of_ne fun h => h0 (by rw [eq_smul_mulForm β, ← h, zero_smul])
  face m m' γ s hγ := by
    rcases isEmpty_or_nonempty (Fin m') with h | ⟨⟨i⟩⟩
    · exact isCone_empty_int _
    · let e : Fin m' ≃ Fin 1 := ⟨fun _ => 0, fun _ => i, fun j => s.injective (hγ.injective
        ((hγ.eq_mulForm _).trans (hγ.eq_mulForm _).symm)), fun _ => Subsingleton.elim _ _⟩
      convert isCone_mulForm.reindex e with j
      exact hγ.eq_mulForm _
  cover B hB := ⟨1, ![mulForm], ![B 1 1], isCone_mulForm, fun i => by simpa using nonneg_of_mem_psdCone hB 1,
    LinearMap.ext₂ fun a b => by simpa using real_apply_int B a b⟩
  finite := ⟨{mulForm}, Set.finite_singleton _, fun m γ hγ => ⟨LinearEquiv.refl _ _, fun i => hγ.eq_mulForm i⟩⟩

theorem subsingleton_or_equiv_int (X : Type) [AddCommGroup X] [Module ℤ X] [Module.Finite ℤ X] [Module.Projective ℤ X]
    (h : Module.finrank ℤ X ≤ 1) : Subsingleton X ∨ Nonempty (ℤ ≃ₗ[ℤ] X) := by
  have : Module.Free ℤ X := Module.free_of_finite_type_torsion_free'
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with h | h
  · exact Or.inl (Module.finrank_zero_iff.1 h)
  · exact Or.inr (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (by rw [h, Module.finrank_self]))

theorem isPolFan_minVal_one : IsPolFan id 1 (InvFun.minVal ℤ) := fun X _ _ _ _ hX => by
  rcases subsingleton_or_equiv_int X hX with h | ⟨⟨e⟩⟩
  · exact isPolFanOn_of_subsingleton
  · exact isPolFanOn_minVal_int.of_equiv e

theorem noSelfInt_int_one (φ : InvFun ℤ) : NoSelfInt id 1 φ := fun X _ _ _ _ hX m γ hγ _ i j _ => by
  rcases subsingleton_or_equiv_int X hX with h | ⟨⟨e⟩⟩
  · exact (hγ.linearIndependent.ne_zero i (Subsingleton.elim _ _)).elim
  · have h := hγ.pull_equiv e
    exact h.injective ((h.eq_mulForm i).trans (h.eq_mulForm j).symm)

example (φ : InvFun ℤ) : ¬ IsCone id φ ![(2 : ℤ) • mulForm] := fun h => by
  simpa using LinearMap.congr_fun₂ (h.eq_mulForm 0) 1 1

example : (InvFun.minVal ℤ).evalZ mulForm = 1 := by simp [evalZ_minVal_int]

end RankOne

end GlobalTheory.PolFan
