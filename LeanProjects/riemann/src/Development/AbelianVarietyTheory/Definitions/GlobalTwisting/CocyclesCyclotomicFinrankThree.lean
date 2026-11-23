import Mathlib

noncomputable section

namespace GlobalTheory.OrdLoc

variable {G : Type} [Group G] [TopologicalSpace G] (E : Type) [NontriviallyNormedField E]

def WCont {X M : Type} [TopologicalSpace X] [AddCommGroup M] [Module E M] (f : X → M) : Prop :=
  ∀ ℓ : M →ₗ[E] E, Continuous fun x => ℓ (f x)

variable {E}

def Z1 (γ : G →* Eˣ) : Submodule E (G → E) where
  carrier := {c | Continuous c ∧ ∀ g h, c (g * h) = c g + (γ g : E) * c h}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨ha.add hb, fun g h => by simp only [Pi.add_apply, ha', hb']; ring⟩
  zero_mem' := ⟨continuous_const, fun g h => by simp⟩
  smul_mem' := by
    rintro t a ⟨ha, ha'⟩
    exact ⟨continuous_const.mul ha, fun g h => by simp only [Pi.smul_apply, smul_eq_mul, ha']; ring⟩

def IsCoc2 (γ : G →* Eˣ) (c : G × G → E) : Prop :=
  Continuous c ∧ ∀ g h k, (γ g : E) * c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) = 0

def IsCob2 (γ : G →* Eˣ) (c : G × G → E) : Prop :=
  ∃ b : G → E, Continuous b ∧ ∀ g h, c (g, h) = (γ g : E) * b h - b (g * h) + b g

structure TateChar (ε : G →* Eˣ) : Prop where
  h2_vanish_nontrivial : ∀ γ : G →* Eˣ, Continuous (fun g => (γ g : E)) → γ ≠ ε → ∀ c, IsCoc2 γ c → IsCob2 γ c
  h2_one_dimensional_cyclotomic : ∀ c c', IsCoc2 ε c → IsCoc2 ε c' → ∃ a b : E, (a ≠ 0 ∨ b ≠ 0) ∧ IsCob2 ε (a • c + b • c')
  cocycles_finrank_two : ∀ γ : G →* Eˣ, Continuous (fun g => (γ g : E)) → γ ≠ ε → Module.finrank E (Z1 γ) = 2
  cocycles_cyclotomic_finrank_three : Module.finrank E (Z1 ε) = 3

def IsCocOn (I : Subgroup G) (ε : G →* Eˣ) (c : G → E) : Prop :=
  ContinuousOn c I ∧ ∀ s ∈ I, ∀ t ∈ I, c (s * t) = c s + (ε s : E) * c t

structure IsKummerVal (I : Subgroup G) (ε : G →* Eˣ) (val : (G → E) →ₗ[E] E) (κ : G → E) : Prop where
  congr : ∀ c c' : G → E, (∀ s ∈ I, c s = c' s) → val c = val c'
  cob : val (fun s => (ε s : E) - 1) = 0
  conj : ∀ c, IsCocOn I ε c → ∀ g : G, val (fun s => (ε g : E) * c (g⁻¹ * s * g)) = val c
  kap_mem : κ ∈ Z1 ε
  kap_val : val κ = 1

structure IsFrobData [IsTopologicalGroup G] (I : Subgroup G) (φ : G) (ν : G → E) : Prop where
  dense : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤
  nu_cont : Continuous ν
  nu_add : ∀ g h, ν (g * h) = ν g + ν h
  nu_I : ∀ s ∈ I, ν s = 0
  nu_phi : ν φ = 1

variable (G E) in

structure LocD [IsTopologicalGroup G] where
  I : Subgroup G
  Gv : Subgroup G
  ε : G →* Eˣ
  ψ : G →* Eˣ
  φ : G
  ν : G → E
  val : (G → E) →ₗ[E] E
  κ : G → E
  s0 : G
  I_normal : I.Normal
  I_le : I ≤ Gv
  Gv_open : IsOpen (Gv : Set G)
  Gv_two : ∀ g h, g ∉ Gv → h ∉ Gv → g * h ∈ Gv
  eps_cont : Continuous fun g => (ε g : E)
  psi_cont : Continuous fun g => (ψ g : E)
  tate : TateChar ε
  kum : IsKummerVal I ε val κ
  frob : IsFrobData I φ ν
  decompSigma_mem : s0 ∈ I
  char_sq_ne_one : ψ s0 ^ 2 ≠ 1
  eps_ne : ∃ s ∈ I, ε s ≠ 1
  sq_ne : ∃ s ∈ I, ψ s ^ 2 ≠ ε s

end GlobalTheory.OrdLoc
