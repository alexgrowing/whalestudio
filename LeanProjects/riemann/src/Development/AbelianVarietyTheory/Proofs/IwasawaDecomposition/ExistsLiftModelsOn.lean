import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies

noncomputable section

open Formalism.IndefR.Links
open scoped InnerProductSpace

namespace GlobalTheory.HilbertModel

def Syn {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) : Type := V

instance {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) : AddCommGroup (Syn V) :=
  inferInstanceAs (AddCommGroup V)

instance {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) : Module ℂ (Syn V) :=
  inferInstanceAs (Module ℂ V)

def Syn.incl {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) : Syn V →ₗ[ℂ] X := V.subtype

theorem Syn.incl_mem {X : Type} [AddCommGroup X] [Module ℂ X] {V : Submodule ℂ X} (x : Syn V) : Syn.incl V x ∈ V :=
  (show V from x).2

theorem Syn.incl_injective {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) :
    Function.Injective (Syn.incl V) := Subtype.val_injective

theorem Syn.range_incl {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) :
    LinearMap.range (Syn.incl V) = V := V.range_subtype

@[reducible] def core {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) (ip : X → X → ℂ)
    (h : ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, ∀ c : ℂ, ip x (y + c • z) = ip x y + c * ip x z ∧ ip y x = star (ip x y))
    (hp : ∀ x ∈ V, x ≠ 0 → 0 < (ip x x).re) : InnerProductSpace.Core ℂ (Syn V) :=
  have hs : ∀ x ∈ V, ∀ y ∈ V, ip y x = star (ip x y) := fun x hx y hy => (h x hx y hy 0 V.zero_mem 0).2
  have h0 : ∀ x ∈ V, ip x 0 = 0 := fun x hx => by
    have := (h x hx 0 V.zero_mem 0 V.zero_mem 1).1
    simpa using this
  { inner := fun x y => ip (Syn.incl V x) (Syn.incl V y)
    conj_inner_symm := fun x y => (hs _ (Syn.incl_mem y) _ (Syn.incl_mem x)).symm
    re_inner_nonneg := fun x => by
      show 0 ≤ (ip (Syn.incl V x) (Syn.incl V x)).re
      by_cases hx : Syn.incl V x = 0
      · rw [hx, h0 0 V.zero_mem]; simp
      · exact (hp _ (Syn.incl_mem x) hx).le
    add_left := fun x y z => by
      show ip (Syn.incl V (x + y)) (Syn.incl V z) = ip (Syn.incl V x) (Syn.incl V z) + ip (Syn.incl V y) (Syn.incl V z)
      have h1 := (h _ (Syn.incl_mem z) _ (Syn.incl_mem x) _ (Syn.incl_mem y) 1).1
      rw [one_smul, one_mul] at h1
      rw [hs _ (Syn.incl_mem z) _ (Syn.incl_mem (x + y)), map_add, h1, star_add,
        ← hs _ (Syn.incl_mem z) _ (Syn.incl_mem x), ← hs _ (Syn.incl_mem z) _ (Syn.incl_mem y)]
    smul_left := fun x y r => by
      show ip (Syn.incl V (r • x)) (Syn.incl V y) = starRingEnd ℂ r * ip (Syn.incl V x) (Syn.incl V y)
      have h1 := (h _ (Syn.incl_mem y) _ V.zero_mem _ (Syn.incl_mem x) r).1
      rw [zero_add, h0 _ (Syn.incl_mem y), zero_add] at h1
      rw [hs _ (Syn.incl_mem y) _ (Syn.incl_mem (r • x)), map_smul, h1, star_mul',
        ← hs _ (Syn.incl_mem y) _ (Syn.incl_mem x)]
      rfl
    definite := fun x hx => by
      have hx' : ip (Syn.incl V x) (Syn.incl V x) = 0 := hx
      by_contra hne
      have h1 : Syn.incl V x ≠ 0 := fun h2 => hne (Syn.incl_injective V (by rw [h2, map_zero]))
      have := hp _ (Syn.incl_mem x) h1
      rw [hx'] at this
      simp at this }

theorem exists_hmod : ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) (ip : X → X → ℂ), FiniteDimensional ℂ V → (∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, ∀ c : ℂ, ip x (y + c • z) = ip x y + c * ip x z ∧ ip y x = star (ip x y)) → (∀ x ∈ V, x ≠ 0 → 0 < (ip x x).re) → ∃ M : HMod X, M.Is V ip := by
  intro X _ _ V ip hf h hp
  let cd : InnerProductSpace.Core ℂ (Syn V) := core V ip h hp
  let nH : NormedAddCommGroup (Syn V) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (cd := cd)
  let iH : InnerProductSpace ℂ (Syn V) := InnerProductSpace.ofCore cd.toCore
  exact ⟨@Formalism.IndefR.Links.HMod.mk X _ _ (Syn V) nH iH hf (Syn.incl V), Syn.incl_injective V, Syn.range_incl V, fun _ _ => rfl⟩

section Lift

variable {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V : Submodule ℂ X} {ip : X → X → ℂ}

theorem e_mem (hM : M.Is V ip) (x : M.H) : M.e x ∈ V := hM.2.1 ▸ LinearMap.mem_range_self M.e x

theorem exists_e_eq (hM : M.Is V ip) {v : X} (hv : v ∈ V) : ∃ x : M.H, M.e x = v := by
  rw [← hM.2.1] at hv; exact hv

def equivSub (hM : M.Is V ip) : M.H ≃ₗ[ℂ] V :=
  (LinearEquiv.ofInjective M.e hM.1).trans (LinearEquiv.ofEq _ _ hM.2.1)

@[simp] theorem coe_equivSub (hM : M.Is V ip) (x : M.H) : (equivSub hM x : X) = M.e x := rfl

@[simp] theorem e_equivSub_symm (hM : M.Is V ip) (v : V) : M.e ((equivSub hM).symm v) = v := by
  rw [← coe_equivSub hM, LinearEquiv.apply_symm_apply]

theorem exists_lift_fun {R A : Type*} [Semiring R] [AddCommMonoid A] [Module R A] (σ : R →+* ℂ) (hM : M.Is V ip)
    (f : A → X) (hadd : ∀ a b, f (a + b) = f a + f b) (hsmul : ∀ (c : R) a, f (c • a) = σ c • f a) (hf : ∀ a, f a ∈ V) :
    ∃ g : A →ₛₗ[σ] M.H, ∀ a, M.e (g a) = f a :=
  ⟨{ toFun := fun a => (equivSub hM).symm ⟨f a, hf a⟩
     map_add' := fun a b => hM.1 (by simp [hadd])
     map_smul' := fun c a => hM.1 (by simp [hsmul]) }, fun a => e_equivSub_symm hM _⟩

theorem exists_lift {R A : Type*} [Semiring R] [AddCommMonoid A] [Module R A] {σ : R →+* ℂ} (hM : M.Is V ip)
    (f : A →ₛₗ[σ] X) (hf : ∀ a, f a ∈ V) : ∃ g : A →ₛₗ[σ] M.H, ∀ a, M.e (g a) = f a :=
  exists_lift_fun σ hM f f.map_add f.map_smulₛₗ hf

theorem lift_unique {A : Type*} (hM : M.Is V ip) {g g' : A → M.H} {f : A → X}
    (hg : ∀ a, M.e (g a) = f a) (hg' : ∀ a, M.e (g' a) = f a) : g = g' :=
  funext fun a => hM.1 ((hg a).trans (hg' a).symm)

variable {X' : Type} [AddCommGroup X'] [Module ℂ X'] {M' : HMod X'} {V' : Submodule ℂ X'} {ip' : X' → X' → ℂ}

theorem exists_lift_range {σ : ℂ →+* ℂ} (M : HMod X) (M' : HMod X') (hinj : Function.Injective M'.e) (f : X →ₛₗ[σ] X')
    (hf : ∀ x ∈ LinearMap.range M.e, f x ∈ LinearMap.range M'.e) :
    ∃ g : M.H →ₛₗ[σ] M'.H, ∀ x, M'.e (g x) = f (M.e x) := by
  choose s hs using fun x : M.H => LinearMap.mem_range.1 (hf _ (LinearMap.mem_range_self M.e x))
  exact ⟨{ toFun := s
           map_add' := fun a b => hinj (by simp [hs])
           map_smul' := fun c a => hinj (by simp [hs, LinearMap.map_smulₛₗ]) }, hs⟩

theorem exists_lift_models {σ : ℂ →+* ℂ} (hM : M.Is V ip) (hM' : M'.Is V' ip') (f : X →ₛₗ[σ] X')
    (hf : ∀ x ∈ V, f x ∈ V') : ∃ g : M.H →ₛₗ[σ] M'.H, ∀ x, M'.e (g x) = f (M.e x) :=
  exists_lift_range M M' hM'.1 f (by rw [hM.2.1, hM'.2.1]; exact hf)

theorem exists_lift_models_on {σ : ℂ →+* ℂ} (hM : M.Is V ip) (hM' : M'.Is V' ip') (f : X → X')
    (hadd : ∀ x ∈ V, ∀ y ∈ V, f (x + y) = f x + f y) (hsmul : ∀ (c : ℂ), ∀ x ∈ V, f (c • x) = σ c • f x)
    (hf : ∀ x ∈ V, f x ∈ V') : ∃ g : M.H →ₛₗ[σ] M'.H, ∀ x, M'.e (g x) = f (M.e x) :=
  exists_lift_fun σ hM' (fun x => f (M.e x))
    (fun a b => by rw [map_add, hadd _ (e_mem hM a) _ (e_mem hM b)])
    (fun c a => by rw [map_smul, hsmul c _ (e_mem hM a)]) (fun a => hf _ (e_mem hM a))

end Lift

end GlobalTheory.HilbertModel
