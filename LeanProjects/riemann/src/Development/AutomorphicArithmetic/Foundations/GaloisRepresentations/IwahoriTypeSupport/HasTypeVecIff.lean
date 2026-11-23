import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.GIface

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.Gal.TypesAndIwahori

section Defs

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]

def leviChar {R : Type} [CommRing R] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (θ : α → Rˣ →* ℂˣ) : Levi R m →* ℂˣ :=
  ∏ a, (detChar (m a) (θ a)).comp (Pi.evalMonoidHom (fun a => GL (m a) R) a)

omit [LinearOrder α] in
theorem leviChar_apply {R : Type} [CommRing R] (θ : α → Rˣ →* ℂˣ) (x : Levi R m) :
    leviChar m θ x = ∏ a, θ a (GeneralLinearGroup.det (x a)) := by
  simp [leviChar, MonoidHom.finsetProd_apply]

def typeChar (e : (Σ a, m a) ≃ n) (θ : α → 𝓀[k]ˣ →* ℂˣ) : parahoric k e →* ℂˣ :=
  (leviChar m θ).comp (parahoricProj k e)

theorem typeChar_apply (e : (Σ a, m a) ≃ n) (θ : α → 𝓀[k]ˣ →* ℂˣ) (g : parahoric k e) :
    typeChar e θ g = ∏ a, θ a (GeneralLinearGroup.det (parahoricProj k e g a)) :=
  leviChar_apply θ _

def typeSp (π : Representation ℂ (GL n k) V) (e : (Σ a, m a) ≃ n) (θ : α → 𝓀[k]ˣ →* ℂˣ) : Submodule ℂ V where
  carrier := {v | ∀ g : parahoric k e, π g v = (typeChar e θ g : ℂ) • v}
  add_mem' := fun {a b} ha hb g => by rw [map_add, ha g, hb g, smul_add]
  zero_mem' := fun g => by simp
  smul_mem' := fun c v hv g => by rw [map_smul, hv g, smul_comm]

theorem mem_typeSp {π : Representation ℂ (GL n k) V} {e : (Σ a, m a) ≃ n} {θ : α → 𝓀[k]ˣ →* ℂˣ} {v : V} :
    v ∈ typeSp π e θ ↔ ∀ g : parahoric k e, π g v = (typeChar e θ g : ℂ) • v := Iff.rfl

def HasTypeVec (π : Representation ℂ (GL n k) V) (e : (Σ a, m a) ≃ n) (θ : α → 𝓀[k]ˣ →* ℂˣ) : Prop :=
  ∃ v : V, v ≠ 0 ∧ ∀ g : parahoric k e, π g v = (typeChar e θ g : ℂ) • v

variable (k) in

def blockDet (e : (Σ a, m a) ≃ n) : parahoric k e →* (α → 𝓀[k]ˣ) :=
  MonoidHom.pi fun a => GeneralLinearGroup.det.comp
    ((Pi.evalMonoidHom (fun a => GL (m a) 𝓀[k]) a).comp (parahoricProj k e))

variable (k) in

def typeKer (e : (Σ a, m a) ≃ n) : Subgroup (GL n k) := (blockDet k e).ker.map (parahoric k e).subtype

abbrev iwBlocks (N : ℕ) : (Σ _ : Fin N, Fin 1) ≃ Fin N := stdBlocks (fun _ : Fin N => 1) (by simp)

abbrev blockOf {s N : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = N) (i : Fin N) : Fin s := ((stdBlocks d hd).symm i).1

def HasTameSupp {N : ℕ} (π : Representation ℂ (GL (Fin N) k) V) (ω : Fin N → 𝓀[k]ˣ →* ℂˣ) : Prop :=
  ∃ μ : Fin N → kˣ →* ℂˣ, (∀ i, IsTameLift (μ i) (ω i)) ∧
    IsCuspSupport π (fun _ : Fin N => 1) (fun i => detRep (Fin 1) (μ i))

def IsTameSphProd {N s : ℕ} (π : Representation ℂ (GL (Fin N) k) V) (d : Fin s → ℕ) (hd : ∑ a, d a = N)
    (θ : Fin s → 𝓀[k]ˣ →* ℂˣ) : Prop :=
  ∃ η : Fin s → kˣ →* ℂˣ, (∀ a, IsSmoothChar (η a) ∧ IsTameLift (η a) (θ a)) ∧ UpperTheory.TNZ.IsTwSphProd π d hd η

end Defs

def IwIff : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
    ∀ ω : Fin N → 𝓀[k]ˣ →* ℂˣ, HasTypeVec π (iwBlocks N) ω ↔ HasTameSupp π ω

def IwEntries : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ),
    parahoric k (iwBlocks N) = iwahori k (Fin N) ∧ typeKer k (iwBlocks N) = proRad k (iwBlocks N) ∧
    ∀ g : parahoric k (iwBlocks N), ∃ u : Fin N → 𝒪[k]ˣ,
      (∀ i, ((g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i i = algebraMap 𝒪[k] k (u i)) ∧
      ∀ i, blockDet k (iwBlocks N) g i = unitRes k (u i)

def SuppOfType : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = N) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
    ∀ θ : Fin s → 𝓀[k]ˣ →* ℂˣ, HasTypeVec π (stdBlocks d hd) θ → HasTameSupp π fun i => θ (blockOf d hd i)

def TypeOfSph : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = N) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (θ : Fin s → 𝓀[k]ˣ →* ℂˣ),
    IsTameSphProd π d hd θ → HasTypeVec π (stdBlocks d hd) θ

def TopA : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (a r s : ℕ) (t : Fin s → ℕ) (ht : ∑ j, t j = a) (hd : ∑ j, Fin.append t (fun _ : Fin r => 1) j = a + r)
    (χ : Fin s → 𝓀[k]ˣ →* ℂˣ) (ω : Fin r → 𝓀[k]ˣ →* ℂˣ)
    (X Y V : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup V] [Module ℂ V]
    (A : Representation ℂ (GL (Fin a) k) X) (B : Representation ℂ (GL (Fin r) k) Y)
    (π : Representation ℂ (GL (Fin (a + r)) k) V),
    IsTameSphProd A t ht χ → HasTameSupp B ω → Nonempty (π.Equiv (prod₂ A B)) →
    HasTypeVec π (stdBlocks (Fin.append t fun _ : Fin r => 1) hd) (Fin.append χ ω)

def TopB : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
    ∀ θ : Fin s → 𝓀[k]ˣ →* ℂˣ, Function.Injective θ → HasTypeVec π (stdBlocks d hd) θ → IsTameSphProd π d hd θ

def TameSuppUnique : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (ω ω' : Fin N → 𝓀[k]ˣ →* ℂˣ), HasTameSupp π ω → HasTameSupp π ω' →
    Finset.univ.val.map ω = Finset.univ.val.map ω'

def TypeSpan : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin N) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), fixed π (typeKer k e) = ⨆ θ : Fin s → 𝓀[k]ˣ →* ℂˣ, typeSp π e θ

def TopC : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N s s' : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = N) (d' : Fin s' → ℕ) (hd' : ∑ a, d' a = N)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
    ∀ (θ : Fin s → 𝓀[k]ˣ →* ℂˣ) (θ' : Fin s' → 𝓀[k]ˣ →* ℂˣ),
    HasTypeVec π (stdBlocks d hd) θ → HasTypeVec π (stdBlocks d' hd') θ' →
    (∑ a, Multiset.replicate (d a) (θ a)) = ∑ a, Multiset.replicate (d' a) (θ' a)

end UpperTheory.Gal.TypesAndIwahori
