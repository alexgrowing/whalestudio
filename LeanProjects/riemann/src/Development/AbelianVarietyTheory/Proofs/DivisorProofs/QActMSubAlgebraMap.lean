import Mathlib

noncomputable section

namespace GlobalTheory.HTRho

variable {k H O C : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O]

def mSub (σ : O →+* Module.End k H) (χ : C →+* k) (X : Submodule k H) : Submodule k H :=
  Submodule.span k {z | ∃ c : C, ∃ x ∈ X, z = σ (algebraMap C O c) x - χ c • x}

def jSub {ι : Type*} (σ : O →+* Module.End k H) (χ : ι → C →+* k) (X : Submodule k H) : Submodule k H :=
  Submodule.span k {z | ∃ (r : ℕ) (lam : Fin r → k) (c : Fin r → C) (x : H), x ∈ X ∧
    (∀ i, ∑ l, lam l * χ i (c l) = 0) ∧ z = ∑ l, lam l • σ (algebraMap C O (c l)) x}

def homO {X Y : Type*} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (σX : O →+* Module.End k X) (σY : O →+* Module.End k Y) : Submodule k (X →ₗ[k] Y) where
  carrier := {T | ∀ a, T ∘ₗ σX a = σY a ∘ₗ T}
  zero_mem' a := by simp
  add_mem' {S T} hS hT a := by rw [LinearMap.add_comp, LinearMap.comp_add, hS a, hT a]
  smul_mem' c T hT a := by rw [LinearMap.smul_comp, LinearMap.comp_smul, hT a]

theorem mem_homO {X Y : Type*} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (σX : O →+* Module.End k X) (σY : O →+* Module.End k Y) (T : X →ₗ[k] Y) :
    T ∈ homO σX σY ↔ ∀ a x, T (σX a x) = σY a (T x) := by
  simp only [homO, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    LinearMap.ext_iff, LinearMap.comp_apply]

def rAct (σ : O →+* Module.End k H) (X : Submodule k H) (h : ∀ a, ∀ x ∈ X, σ a x ∈ X) :
    O →+* Module.End k X where
  toFun a := (σ a).restrict (h a)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

@[simp] theorem rAct_apply (σ : O →+* Module.End k H) (X : Submodule k H) (h : ∀ a, ∀ x ∈ X, σ a x ∈ X)
    (a : O) (x : X) : ((rAct σ X h a x : X) : H) = σ a x := rfl

def qAct (σ : O →+* Module.End k H) (X : Submodule k H) (h : ∀ a, ∀ x ∈ X, σ a x ∈ X) :
    O →+* Module.End k (H ⧸ X) where
  toFun a := X.mapQ X (σ a) (fun x hx => h a x hx)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

@[simp] theorem qAct_mk (σ : O →+* Module.End k H) (X : Submodule k H) (h : ∀ a, ∀ x ∈ X, σ a x ∈ X)
    (a : O) (x : H) : qAct σ X h a (X.mkQ x) = X.mkQ (σ a x) := rfl

theorem mSub_stable (σ : O →+* Module.End k H) (χ : C →+* k) (X : Submodule k H)
    (hX : ∀ a, ∀ x ∈ X, σ a x ∈ X) : ∀ a, ∀ x ∈ mSub σ χ X, σ a x ∈ mSub σ χ X := by
  intro a x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, y, hy, rfl⟩ := hz
    refine Submodule.subset_span ⟨c, σ a y, hX a y hy, ?_⟩
    rw [map_sub, map_smul, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      Algebra.commutes]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem jSub_stable {ι : Type*} (σ : O →+* Module.End k H) (χ : ι → C →+* k) (X : Submodule k H)
    (hX : ∀ a, ∀ x ∈ X, σ a x ∈ X) : ∀ a, ∀ x ∈ jSub σ χ X, σ a x ∈ jSub σ χ X := by
  intro a x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, lam, c, y, hy, hc, rfl⟩ := hz
    refine Submodule.subset_span ⟨r, lam, c, σ a y, hX a y hy, hc, ?_⟩
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Algebra.commutes]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem qAct_mSub_algebraMap (σ : O →+* Module.End k H) (χ : C →+* k) (c : C) :
    qAct σ (mSub σ χ ⊤) (mSub_stable σ χ ⊤ (fun _ _ _ => trivial)) (algebraMap C O c) = χ c • 1 := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  change (mSub σ χ ⊤).mkQ (σ (algebraMap C O c) x) = χ c • (mSub σ χ ⊤).mkQ x
  rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨c, x, trivial, rfl⟩

end GlobalTheory.HTRho
