import Mathlib

noncomputable section

namespace PI.Dv

section Abstract

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

def laG (G : Type) [Fintype G] : ℝ := Real.log (Fintype.card G : ℝ)

structure GoodSet (K : Type) [Field K] (G : Type) [Group G] where
  S : Type
  [finS : Fintype S]
  [decS : DecidableEq S]
  W : S → Type
  [acgW : ∀ s, AddCommGroup (W s)]
  [modW : ∀ s, Module K (W s)]
  [fdW : ∀ s, FiniteDimensional K (W s)]
  [ntW : ∀ s, Nontrivial (W s)]
  tau : ∀ s, Representation K G (W s)

  irr : ∀ s, Function.Surjective (tau s).asAlgebraHom

  inj : Function.Injective fun s g => LinearMap.trace K (W s) (tau s g)

attribute [instance] GoodSet.finS GoodSet.decS GoodSet.acgW GoodSet.modW GoodSet.fdW GoodSet.ntW

structure Pair (K : Type) [Field K] (G : Type) [Group G] where
  H : Subgroup G
  chi : H →* Kˣ

def eS (T : GoodSet K G) (s : T.S) : MonoidAlgebra K G :=
  ∑ x : G, (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
    LinearMap.trace K (T.W s) (T.tau s x⁻¹)) • MonoidAlgebra.of K G x

def eG (T : GoodSet K G) : MonoidAlgebra K G := ∑ s, eS T s

open Classical in

def eps (P : Pair K G) : MonoidAlgebra K G :=
  ((Nat.card P.H : ℕ) : K)⁻¹ • ∑ x : G, if h : x ∈ P.H then
    (((P.chi ⟨x, h⟩)⁻¹ : Kˣ) : K) • MonoidAlgebra.of K G x else 0

def nS (T : GoodSet K G) (P : Pair K G) (s : T.S) : ℕ :=
  Module.finrank K (LinearMap.range ((T.tau s).asAlgebraHom (eps P)))

def M1 (T : GoodSet K G) (P0 : Pair K G) : Prop := ∀ s, nS T P0 s = 1
end Abstract

section Lemma8

def eigP {K : Type} [Field K] (σ : K →+* ℂ) {G : Type} [Group G] (P : Pair K G)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) : Submodule ℂ V :=
  ⨅ h : P.H, LinearMap.ker (ρ (h : G) - (σ ((P.chi h : Kˣ) : K)) • LinearMap.id)

structure GMap (K : Type) [Field K] (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (T : GoodSet K G)
    (EE : Type) [AddCommGroup EE] [Module ℂ EE] (ρE : Representation ℂ G EE) where
  VK : Type
  [acgK : AddCommGroup VK]
  [modK : Module K VK]
  [fdK : FiniteDimensional K VK]
  rhoK : Representation K G VK
  V : Type
  [acgV : AddCommGroup V]
  [modV : Module ℂ V]
  rho : Representation ℂ G V

  j : VK →ₛₗ[σ] V
  j_indep : ∀ (n : ℕ) (b : Fin n → VK), LinearIndependent K b → LinearIndependent ℂ (fun i => j (b i))
  j_span : Submodule.span ℂ (Set.range j) = ⊤
  j_eq : ∀ g x, j (rhoK g x) = rho g (j x)

  good : rhoK.asAlgebraHom (eG T) = 1
  io : V →ₗ[ℂ] EE
  io_eq : ∀ g x, io (rho g x) = ρE g (io x)

attribute [instance] GMap.acgK GMap.modK GMap.fdK GMap.acgV GMap.modV

namespace GMap

variable {K : Type} [Field K] {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G] {T : GoodSet K G}
  {EE : Type} [AddCommGroup EE] [Module ℂ EE] {ρE : Representation ℂ G EE} (M : GMap K σ G T EE ρE)

def IsRat (U : Submodule ℂ M.V) : Prop := Submodule.span ℂ (M.j '' {x | M.j x ∈ U}) = U

def form (a : MonoidAlgebra K G) : Set EE := Set.range fun x : M.VK => M.io (M.j (M.rhoK.asAlgebraHom a x))

end GMap

def Conclusion8 : Prop :=
  ∀ (K : Type) [Field K] (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 : Pair K G),
    M1 T P0 → ∀ (EE : Type) [AddCommGroup EE] [Module ℂ EE] (ρE : Representation ℂ G EE)
      (M : GMap K σ G T EE ρE),
      M.IsRat (LinearMap.ker M.io ⊓ eigP σ P0 M.rho) →
      M.IsRat (LinearMap.ker M.io) ∧
      M.form 1 = (AddSubgroup.closure {z | ∃ g, ∃ y ∈ M.form (eps P0), z = ρE g y} : Set EE)

def SameFormAllLevels : Prop :=
  ∀ (K : Type) [Field K] (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 : Pair K G),
    M1 T P0 → ∀ (EE : Type) [AddCommGroup EE] [Module ℂ EE] (ρE : Representation ℂ G EE)
      (M M' : GMap K σ G T EE ρE), M.form (eps P0) = M'.form (eps P0) →
      M.form 1 = M'.form 1 ∧ ∀ P : Pair K G, M.form (eps P) = M'.form (eps P)

end Lemma8

end PI.Dv
