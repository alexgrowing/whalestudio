import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.InPow

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def KC (n r : ℕ) : Set (GL (Fin n) k) :=
  {g | g ∈ KO k (Fin n) ∧ ∀ i j, InPow r ((g : Matrix (Fin n) (Fin n) k) i j - if i = j then 1 else 0)}

variable (k) in

def KCg (n r : ℕ) : Subgroup (GL (Fin n) k) := Subgroup.closure (KC k n r)

namespace Grp

variable {n : ℕ} (G : Grp k n)

def JSet : Set (GL (Fin n) k) :=
  {g | g ∈ KO k (Fin n) ∧ ∀ i j, G.bl j < G.bl i → InPow (cc G.μ (G.bl j) (G.bl i)) ((g : Matrix (Fin n) (Fin n) k) i j)}

def Jg : Subgroup (GL (Fin n) k) := Subgroup.closure G.JSet

def chk (μ : kˣ →* ℂˣ) (x : k) : ℂ := if h : x = 0 then 1 else ((μ (Units.mk0 x h) : ℂˣ) : ℂ)

def μnext (a : Fin G.s) : kˣ →* ℂˣ := if h : (a : ℕ) + 1 < G.s then G.μ ⟨a + 1, h⟩ else 1

def Δ (a : Fin G.s) (g : GL (Fin n) k) : k :=
  ((g : Matrix (Fin n) (Fin n) k).submatrix (Subtype.val : {i : Fin n // G.bl i ≤ a} → Fin n) Subtype.val).det

def lam (g : GL (Fin n) k) : ℂ := ∏ a : Fin G.s, chk (G.μ a / G.μnext a) (G.Δ a g)

def lev : ℕ := 1 + ∑ a, cond (res (G.μ a))

def PO : Set (GL (Fin n) k) := {g | g ∈ KO k (Fin n) ∧ g ∈ parab k G.e}

def V0sp : Submodule ℂ (↥(KO k (Fin n)) → ℂ) where
  carrier := {f | (∀ p : ↥(KO k (Fin n)), (p : GL (Fin n) k) ∈ G.PO → ∀ g, f (p * g) = G.lam (p : GL (Fin n) k) * f g) ∧
    ∀ g (u : ↥(KO k (Fin n))), (u : GL (Fin n) k) ∈ KC k n G.lev → f (g * u) = f g}
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun p hp g => ?_, fun g u hu => ?_⟩
    · simp only [Pi.add_apply, h1 p hp g, h1' p hp g, mul_add]
    · simp only [Pi.add_apply, h2 g u hu, h2' g u hu]
  zero_mem' := ⟨fun p _ g => by simp, fun g u _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨fun p hp g => ?_, fun g u hu => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, h1 p hp g]; ring
    · simp only [Pi.smul_apply, h2 g u hu]

abbrev Rreg : Representation ℂ ↥(KO k (Fin n)) (↥(KO k (Fin n)) → ℂ) := rightReg ℂ ↥(KO k (Fin n)) ℂ

def v0 : ↥(KO k (Fin n)) → ℂ := fun g => if (g : GL (Fin n) k) ∈ G.JSet then G.lam g else 0

end Grp

end UpperTheory.TNZ
