import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega

set_option autoImplicit false

noncomputable section

open MvPowerSeries TensorProduct

namespace GlobalTheory

namespace Katz

section Law

variable {R : Type} [CommRing R] {d e : ℕ} {τ : Type}

def inL (f : MvPowerSeries (Fin d) R) : MvPowerSeries (Fin d ⊕ Fin d) R :=
  subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) f

def inR (f : MvPowerSeries (Fin d) R) : MvPowerSeries (Fin d ⊕ Fin d) R :=
  subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) f

def at2 (c : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R) :
    MvPowerSeries τ R := subst (Sum.elim u v) c

def op (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R) :
    Fin d → MvPowerSeries τ R := fun i => at2 (μ i) u v

def x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R := fun i => X (Sum.inl i)

def x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R := fun i => X (Sum.inr (Sum.inl i))

def x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R := fun i => X (Sum.inr (Sum.inr i))

def cob1 (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (f : MvPowerSeries (Fin d) R) :
    MvPowerSeries (Fin d ⊕ Fin d) R := subst μ f - inL f - inR f

def cob2 (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R :=
  at2 c x2 x3 - at2 c (op μ x1 x2) x3 + at2 c x1 (op μ x2 x3) - at2 c x1 x2

def swap (c : MvPowerSeries (Fin d ⊕ Fin d) R) : MvPowerSeries (Fin d ⊕ Fin d) R :=
  at2 c (fun i => X (Sum.inr i)) (fun i => X (Sum.inl i))

def lin (f : MvPowerSeries (Fin d) R) : Fin d → R := fun i => coeff (Finsupp.single i 1) f

def pull2 (φ : Fin e → MvPowerSeries (Fin d) R) (c : MvPowerSeries (Fin e ⊕ Fin e) R) :
    MvPowerSeries (Fin d ⊕ Fin d) R := at2 c (fun j => inL (φ j)) (fun j => inR (φ j))

def pullLin (φ : Fin e → MvPowerSeries (Fin d) R) (w : Fin e → R) : Fin d → R :=
  fun i => ∑ j, w j * lin (φ j) i

def addLaw (R : Type) [CommRing R] (d : ℕ) : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R :=
  fun i => X (Sum.inl i) + X (Sum.inr i)

structure IsLaw (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) : Prop where
  const : ∀ i, constantCoeff (μ i) = 0
  unit : op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = fun i => X i
  comm : ∀ i, swap (μ i) = μ i
  assoc : op μ (op μ x1 x2) x3 = op μ x1 (op μ x2 x3)

structure IsHom (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) R) (φ : Fin e → MvPowerSeries (Fin d) R) : Prop where
  const : ∀ j, constantCoeff (φ j) = 0
  hom : ∀ j, subst μ (φ j) = pull2 φ (ν j)

def IsCoc (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    Prop := cob2 μ c = 0 ∧ swap c = c

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R : Type} [CommRing R] {d e : ℕ} {τ : Type} in
theorem _root_.GlobalTheory.Katz.formalCoboundary_add {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (h : ∀ i, constantCoeff (μ i) = 0)
    (f g : MvPowerSeries (Fin d) R) :
    _root_.GlobalTheory.Katz.cob1 μ (f + g) =
      _root_.GlobalTheory.Katz.cob1 μ f + _root_.GlobalTheory.Katz.cob1 μ g := by
  have hμ : HasSubst μ := hasSubst_of_constantCoeff_zero h
  have hL : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun i => by simp
  have hR : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun i => by simp
  simp only [_root_.GlobalTheory.Katz.cob1, _root_.GlobalTheory.Katz.inL,
    _root_.GlobalTheory.Katz.inR, subst_add hμ, subst_add hL, subst_add hR]
  abel

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R : Type} [CommRing R] {d e : ℕ} {τ : Type} in
theorem _root_.GlobalTheory.Katz.formalCoboundary_smul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (h : ∀ i, constantCoeff (μ i) = 0)
    (r : R) (f : MvPowerSeries (Fin d) R) :
    _root_.GlobalTheory.Katz.cob1 μ (r • f) = r • _root_.GlobalTheory.Katz.cob1 μ f := by
  have hμ : HasSubst μ := hasSubst_of_constantCoeff_zero h
  have hL : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun i => by simp
  have hR : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun i => by simp
  simp only [_root_.GlobalTheory.Katz.cob1, _root_.GlobalTheory.Katz.inL,
    _root_.GlobalTheory.Katz.inR, subst_smul hμ, subst_smul hL, subst_smul hR, smul_sub]

end Law

section Witt

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ : Type} {d : ℕ}

variable (k) in

abbrev Fr : Type := FractionRing (WittVector p k)

def lift (f : MvPowerSeries σ k) : MvPowerSeries σ (Fr p k) :=
  fun α => algebraMap (WittVector p k) (Fr p k) (WittVector.teichmuller p (coeff α f))

theorem coeff_lift (f : MvPowerSeries σ k) (α : σ →₀ ℕ) : coeff α (lift p f) =
    algebraMap (WittVector p k) (Fr p k) (WittVector.teichmuller p (coeff α f)) := rfl

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ : Type} {d : ℕ} in
theorem _root_.GlobalTheory.Katz.constantCoeff_lift {f : MvPowerSeries σ k}
    (h : constantCoeff f = 0) :
    constantCoeff (_root_.GlobalTheory.Katz.lift p f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, _root_.GlobalTheory.Katz.coeff_lift,
    coeff_zero_eq_constantCoeff_apply, h, WittVector.teichmuller_zero, map_zero]

variable (k σ) in

def intBy (c : WittVector p k) : Submodule (WittVector p k) (MvPowerSeries σ (Fr p k)) where
  carrier := {f | ∀ α, ∃ w : WittVector p k, coeff α f = algebraMap _ (Fr p k) (c * w)}
  zero_mem' _ := ⟨0, by simp⟩
  add_mem' {f g} hf hg α := by
    obtain ⟨v, hv⟩ := hf α
    obtain ⟨w, hw⟩ := hg α
    exact ⟨v + w, by rw [map_add, hv, hw, mul_add, map_add]⟩
  smul_mem' r f hf α := by
    obtain ⟨w, hw⟩ := hf α
    refine ⟨r * w, ?_⟩
    change r • coeff α f = _
    rw [hw, Algebra.smul_def, ← map_mul, mul_left_comm]

variable (k σ) in

def quasiInt : Submodule (WittVector p k) (MvPowerSeries σ (Fr p k)) where
  carrier := {f | ∀ α i, ∃ w : WittVector p k, (α i : Fr p k) * coeff α f = algebraMap _ (Fr p k) w}
  zero_mem' _ _ := ⟨0, by simp⟩
  add_mem' {f g} hf hg α i := by
    obtain ⟨v, hv⟩ := hf α i
    obtain ⟨w, hw⟩ := hg α i
    exact ⟨v + w, by rw [map_add, mul_add, hv, hw, map_add]⟩
  smul_mem' r f hf α i := by
    obtain ⟨w, hw⟩ := hf α i
    refine ⟨r * w, ?_⟩
    change _ * (r • coeff α f) = _
    rw [Algebra.smul_def, mul_left_comm, hw, ← map_mul]

def Red (f : MvPowerSeries σ (Fr p k)) (g : MvPowerSeries σ k) : Prop :=
  ∀ α, ∃ w : WittVector p k, coeff α f = algebraMap _ (Fr p k) w ∧
    WittVector.constantCoeff w = coeff α g

def RedV (v : Fin d → Fr p k) (w : Fin d → k) : Prop :=
  ∀ i, ∃ a : WittVector p k, v i = algebraMap _ (Fr p k) a ∧ WittVector.constantCoeff a = w i

def quasiLog {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (h : IsLaw μ) :
    Submodule (WittVector p k) (MvPowerSeries (Fin d) (Fr p k)) where
  carrier := {f | f ∈ quasiInt p k (Fin d) ∧ cob1 (fun i => lift p (μ i)) f ∈ intBy p k _ 1}
  zero_mem' := ⟨zero_mem _, by
    have := formalCoboundary_smul (fun i => constantCoeff_lift p (h.const i)) 0 0
    rw [zero_smul, zero_smul] at this
    rw [this]; exact zero_mem _⟩
  add_mem' hf hg := ⟨add_mem hf.1 hg.1, by
    rw [formalCoboundary_add fun i => constantCoeff_lift p (h.const i)]; exact add_mem hf.2 hg.2⟩
  smul_mem' r f hf := ⟨Submodule.smul_mem _ r hf.1, by
    rw [← algebraMap_smul (Fr p k) r f, formalCoboundary_smul fun i => constantCoeff_lift p (h.const i),
      algebraMap_smul]
    exact Submodule.smul_mem _ r hf.2⟩

abbrev Mod {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (h : IsLaw μ) : Type :=
  quasiLog p h ⧸ (intBy p k (Fin d) 1).submoduleOf (quasiLog p h)

end Witt

section Chart

variable {k : Type} [CommRing k] {σ : Type} [Finite σ]

variable (k) in

def evA {A : Type} [CommRing A] [Algebra k A] (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) :
    MvPowerSeries σ k →ₐ[k] A :=
  { (constantCoeff : MvPowerSeries Empty A →+* A).comp
      (substAlgHom (R := k) (a := fun i => (C (x i) : MvPowerSeries Empty A))
        (hasSubst_of_constantCoeff_nilpotent fun i => by simpa using hx i)).toRingHom with
    commutes' := fun r => by
      refine (congrArg (constantCoeff : MvPowerSeries Empty A →+* A) (AlgHom.commutes
        (substAlgHom (R := k) (a := fun i => (C (x i) : MvPowerSeries Empty A))
        (hasSubst_of_constantCoeff_nilpotent fun i => by simpa using hx i)) r)).trans ?_
      rw [MvPowerSeries.algebraMap_apply, constantCoeff_C] }

variable (k) in

def Presents {B : ℕ → Type} [∀ n, CommRing (B n)] [∀ n, Algebra k (B n)] (y : ∀ n, σ → B n)
    (hy : ∀ n i, IsNilpotent (y n i)) : Prop :=
  (∀ n, Function.Surjective (evA k (y n) (hy n))) ∧
    ∀ N : ℕ, ∃ n, ∀ f, evA k (y n) (hy n) f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0

structure Chart {p : ℕ} (G : PDivGroup p k) (d : ℕ) where

  x : ∀ n, Fin d → G.A n
  nil : ∀ n i, IsNilpotent (x n i)
  res : ∀ n i, G.res n (x (n + 1) i) = x n i
  aug : ∀ n i, Coalgebra.counit (R := k) (x n i) = 0
  presents : Presents k x nil

namespace Chart

variable {p d e : ℕ} {G H : PDivGroup p k} (c : Chart G d)

def ev (n : ℕ) : MvPowerSeries (Fin d) k →ₐ[k] G.A n := evA k (c.x n) (c.nil n)

def x₂ (n : ℕ) : Fin d ⊕ Fin d → G.A n ⊗[k] G.A n :=
  Sum.elim (fun i => c.x n i ⊗ₜ 1) (fun i => 1 ⊗ₜ c.x n i)

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {k : Type} [CommRing k] {σ : Type} [Finite σ] in
variable {p d e : ℕ} {G H : _root_.GlobalTheory.PDivGroup p k} (c : _root_.GlobalTheory.Katz.Chart G d) in
theorem _root_.GlobalTheory.Katz.Chart.nil₂ (n : ℕ) (i : Fin d ⊕ Fin d) :
    IsNilpotent (c.x₂ n i) := by
  rcases i with i | i
  · obtain ⟨m, hm⟩ := c.nil n i
    exact ⟨m, by
      simp only [_root_.GlobalTheory.Katz.Chart.x₂, Sum.elim_inl]
      rw [Algebra.TensorProduct.tmul_pow, hm, one_pow, TensorProduct.zero_tmul]⟩
  · obtain ⟨m, hm⟩ := c.nil n i
    exact ⟨m, by
      simp only [_root_.GlobalTheory.Katz.Chart.x₂, Sum.elim_inr]
      rw [Algebra.TensorProduct.tmul_pow, hm, one_pow, TensorProduct.tmul_zero]⟩

def ev₂ (n : ℕ) : MvPowerSeries (Fin d ⊕ Fin d) k →ₐ[k] G.A n ⊗[k] G.A n :=
  evA k (c.x₂ n) (c.nil₂ n)

def IsLawOf (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) : Prop :=
  ∀ n i, c.ev₂ n (μ i) = Coalgebra.comul (R := k) (c.x n i)

def IsMapOf (c' : Chart H e) (f : G ⟶ H) (φ : Fin e → MvPowerSeries (Fin d) k) : Prop :=
  ∀ n j, c.ev n (φ j) = f.app n (c'.x n j)

end Chart

end Chart

structure IsRigOf {k : Type} [CommRing k] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k)
    {V : Type} [AddCommGroup V] [Module k V]
    (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] V) : Prop where
  surj : ∀ v, ∃ c w, IsCoc μ c ∧ ρ (c, w) = v
  ker : ∀ c w, IsCoc μ c → (ρ (c, w) = 0 ↔ ∃ b, c = cob1 μ b ∧ w = lin b)

end Katz

end GlobalTheory
