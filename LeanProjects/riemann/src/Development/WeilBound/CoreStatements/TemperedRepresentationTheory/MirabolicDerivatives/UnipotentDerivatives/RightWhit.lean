import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.BZMir

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def rightUnip (n t : ℕ) : Subgroup (GL (Fin n) k × GL (Fin t) k) := Subgroup.prod ⊥ (unipB k (Fin t))

variable (k) in

def rightWhit (ψ : AddChar k Circle) (n t : ℕ) : rightUnip k n t →* ℂˣ :=
  (whitChar ψ t).comp
    { toFun := fun x => ⟨(x : GL (Fin n) k × GL (Fin t) k).2, (Subgroup.mem_prod.1 x.2).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem inl_stab (ψ : AddChar k Circle) (n t : ℕ) (m : GL (Fin n) k) (u : rightUnip k n t) :
    ∃ h : MonoidHom.inl (GL (Fin n) k) (GL (Fin t) k) m * (u : GL (Fin n) k × GL (Fin t) k) *
        (MonoidHom.inl (GL (Fin n) k) (GL (Fin t) k) m)⁻¹ ∈ rightUnip k n t,
      rightWhit k ψ n t ⟨_, h⟩ = rightWhit k ψ n t u := by
  have h1 : (u : GL (Fin n) k × GL (Fin t) k).1 = 1 := Subgroup.mem_bot.1 (Subgroup.mem_prod.1 u.2).1
  have hconj : MonoidHom.inl (GL (Fin n) k) (GL (Fin t) k) m * (u : GL (Fin n) k × GL (Fin t) k) *
      (MonoidHom.inl (GL (Fin n) k) (GL (Fin t) k) m)⁻¹ = (u : GL (Fin n) k × GL (Fin t) k) := by
    refine Prod.ext ?_ ?_ <;> simp [h1]
  refine ⟨by rw [hconj]; exact u.2, ?_⟩
  congr 1
  exact Subtype.ext hconj

variable (k) in

def derRep (ψ : AddChar k Circle) {n t N : ℕ} (h : n + t = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) :
    Representation ℂ (GL (Fin n) k) (TwJacquet (jacU₂ (stdSum h) π) (rightUnip k n t) (rightWhit k ψ n t)) :=
  twAct (jacU₂ (stdSum h) π) (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _) (inl_stab ψ n t)

end GlobalTheory.BZMir

end
