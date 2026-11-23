import Mathlib

open scoped InnerProductSpace

noncomputable section

namespace Formalism.IndefR.U2

variable {I : Type*} {A B : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup B] [InnerProductSpace ℂ B]

def eigPart (op : I → Module.End ℂ A) (c : I → ℂ) : Submodule ℂ A :=
  ⨅ i, LinearMap.ker (op i - c i • (1 : Module.End ℂ A))

theorem mem_eigPart {op : I → Module.End ℂ A} {c : I → ℂ} {x : A} :
    x ∈ eigPart op c ↔ ∀ i, op i x = c i • x := by
  simp only [eigPart, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]

structure OrthDecomp (op : I → Module.End ℂ A) (good : Submodule ℂ A) (Ix : Set (I → ℂ)) : Prop where

  span : good ≤ ⨆ c ∈ Ix, eigPart op c ⊓ good

  orth : ∀ c ∈ Ix, ∀ c' ∈ Ix, c ≠ c' → ∀ x ∈ eigPart op c ⊓ good, ∀ y ∈ eigPart op c' ⊓ good, ⟪x, y⟫_ℂ = 0

def Intw (θ : A →ₗ[ℂ] B) (op : I → Module.End ℂ A) (opB : I → Module.End ℂ B) : Prop :=
  ∀ i x, θ (op i x) = opB i (θ x)

def GoodIn (θ : A →ₗ[ℂ] B) (good : Submodule ℂ A) (goodB : Submodule ℂ B) : Prop :=
  ∀ x ∈ good, θ x ∈ goodB

def IsAdj (θ : A →ₗ[ℂ] B) (θa : B →ₗ[ℂ] A) : Prop :=
  ∀ x y, ⟪θ x, y⟫_ℂ = ⟪x, θa y⟫_ℂ

def Lifted (opB : I → Module.End ℂ B) (goodB : Submodule ℂ B) (Ix : Set (I → ℂ)) : Set (I → ℂ) :=
  {c | c ∈ Ix ∧ eigPart opB c ⊓ goodB ≠ ⊥}

def OntoParts (θa : B →ₗ[ℂ] A) (op : I → Module.End ℂ A) (opB : I → Module.End ℂ B) (good : Submodule ℂ A)
    (goodB : Submodule ℂ B) (Ix : Set (I → ℂ)) : Prop :=
  ∀ c ∈ Lifted opB goodB Ix, eigPart op c ⊓ good ≤ LinearMap.range θa

def LiftsFull (θ : A →ₗ[ℂ] B) (op : I → Module.End ℂ A) (opB : I → Module.End ℂ B) (good : Submodule ℂ A)
    (goodB : Submodule ℂ B) (Ix : Set (I → ℂ)) : Prop :=
  (LinearMap.ker θ)ᗮ ⊓ good = ⨆ c ∈ Lifted opB goodB Ix, eigPart op c ⊓ good

def LiftsTyp (opB : I → Module.End ℂ B) (goodB : Submodule ℂ B) (Ix : Set (I → ℂ)) (Ty : (I → ℂ) → Prop) : Prop :=
  ∀ c ∈ Lifted opB goodB Ix, Ty c

def OccTyp (opB : I → Module.End ℂ B) (goodB : Submodule ℂ B) (Ty : (I → ℂ) → Prop) : Prop :=
  ∀ c, eigPart opB c ⊓ goodB ≠ ⊥ → Ty c

variable {θ : A →ₗ[ℂ] B} {θa : B →ₗ[ℂ] A} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
  {good : Submodule ℂ A} {goodB : Submodule ℂ B} {Ix : Set (I → ℂ)}

theorem map_eigPart (hI : Intw θ op opB) {c : I → ℂ} {x : A} (hx : x ∈ eigPart op c) : θ x ∈ eigPart opB c := by
  rw [mem_eigPart] at hx ⊢
  intro i
  rw [← hI, hx i, map_smul]

theorem notLifted_le_ker (hI : Intw θ op opB) (hG : GoodIn θ good goodB) {c : I → ℂ} (hc : c ∈ Ix)
    (hn : c ∉ Lifted opB goodB Ix) : eigPart op c ⊓ good ≤ LinearMap.ker θ := by
  intro x hx
  have h0 : eigPart opB c ⊓ goodB = ⊥ := by
    by_contra h
    exact hn ⟨hc, h⟩
  have hm : θ x ∈ eigPart opB c ⊓ goodB := ⟨map_eigPart hI hx.1, hG x hx.2⟩
  rw [h0, Submodule.mem_bot] at hm
  exact hm

theorem range_adj_le (hA : IsAdj θ θa) : LinearMap.range θa ≤ (LinearMap.ker θ)ᗮ := by
  rintro _ ⟨y, rfl⟩
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [← hA, LinearMap.mem_ker.mp hu, inner_zero_left]

theorem liftsFull_of (hD : OrthDecomp op good Ix) (hI : Intw θ op opB) (hG : GoodIn θ good goodB)
    (hA : IsAdj θ θa) (hO : OntoParts θa op opB good goodB Ix) : LiftsFull θ op opB good goodB Ix := by
  set L : Submodule ℂ A := ⨆ c ∈ Lifted opB goodB Ix, eigPart op c ⊓ good with hL
  set M : Submodule ℂ A := ⨆ c ∈ {c | c ∈ Ix ∧ c ∉ Lifted opB goodB Ix}, eigPart op c ⊓ good with hM
  have hMker : M ≤ LinearMap.ker θ := iSup₂_le fun c hc => notLifted_le_ker hI hG hc.1 hc.2
  have hgood : good ≤ L ⊔ M := by
    refine hD.span.trans (iSup₂_le fun c hc => ?_)
    by_cases h : c ∈ Lifted opB goodB Ix
    · exact le_sup_of_le_left
        (le_iSup₂_of_le (f := fun c (_ : c ∈ Lifted opB goodB Ix) => eigPart op c ⊓ good) c h le_rfl)
    · exact le_sup_of_le_right
        (le_iSup₂_of_le (f := fun c (_ : c ∈ {c | c ∈ Ix ∧ c ∉ Lifted opB goodB Ix}) => eigPart op c ⊓ good)
          c ⟨hc, h⟩ le_rfl)
  have hOrth : M ⟂ L := by
    rw [hM, Submodule.isOrtho_iSup_left]
    intro c
    rw [Submodule.isOrtho_iSup_left]
    intro hc
    rw [hL, Submodule.isOrtho_iSup_right]
    intro c'
    rw [Submodule.isOrtho_iSup_right]
    intro hc'
    rw [Submodule.isOrtho_iff_inner_eq]
    intro u hu v hv
    have hne : c ≠ c' := fun h => hc.2 (h ▸ hc')
    exact hD.orth c hc.1 c' hc'.1 hne u hu v hv
  apply le_antisymm
  · rintro x ⟨hxk, hxg⟩
    obtain ⟨l, hl, m, hm, rfl⟩ := Submodule.mem_sup.mp (hgood hxg)
    have h1 : ⟪m, l + m⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).mp hxk m (hMker hm)
    have h2 : ⟪m, l⟫_ℂ = 0 := Submodule.isOrtho_iff_inner_eq.mp hOrth m hm l hl
    have h3 : ⟪m, m⟫_ℂ = 0 := by rw [inner_add_right, h2, zero_add] at h1; exact h1
    rw [inner_self_eq_zero] at h3
    rw [h3, add_zero]
    exact hl
  · exact iSup₂_le fun c hc => le_inf ((hO c hc).trans (range_adj_le hA)) inf_le_right

section FD

variable [FiniteDimensional ℂ A] [FiniteDimensional ℂ B]

theorem isAdj_adjoint (θ : A →ₗ[ℂ] B) : IsAdj θ (LinearMap.adjoint θ) :=
  fun x y => (LinearMap.adjoint_inner_right θ x y).symm

def AdjClosed (op : I → Module.End ℂ A) : Prop := ∀ i, ∃ i', op i' = LinearMap.adjoint (op i)

def PairCommF (op : I → Module.End ℂ A) : Prop := ∀ i j, Commute (op i) (op j)

def Occ (op : I → Module.End ℂ A) (good : Submodule ℂ A) : Set (I → ℂ) := {c | eigPart op c ⊓ good ≠ ⊥}

theorem liftsFull_adj {θ : A →ₗ[ℂ] B} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
    {good : Submodule ℂ A} {goodB : Submodule ℂ B} {Ix : Set (I → ℂ)}
    (hD : OrthDecomp op good Ix) (hI : Intw θ op opB) (hG : GoodIn θ good goodB)
    (hO : OntoParts (LinearMap.adjoint θ) op opB good goodB Ix) : LiftsFull θ op opB good goodB Ix :=
  liftsFull_of hD hI hG (isAdj_adjoint θ) hO

end FD

def DecompOfNormalStatement : Prop :=
  ∀ (I A : Type) [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
    (op : I → Module.End ℂ A) (good : Submodule ℂ A),
    PairCommF op → AdjClosed op → (∀ i, ∀ x ∈ good, op i x ∈ good) → OrthDecomp op good (Occ op good)

end Formalism.IndefR.U2
