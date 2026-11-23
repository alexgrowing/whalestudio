import Mathlib
import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace MassDataIdxCore

open Matrix

variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K)

def t1 : T →+* K := (RingHom.fst K K).comp θ.toAlgHom.toRingHom

def t2 : T →+* K := (RingHom.snd K K).comp θ.toAlgHom.toRingHom

theorem firstSplit_apply (t : T) : t1 θ t = (θ t).1 := rfl
theorem secondSplit_apply (t : T) : t2 θ t = (θ t).2 := rfl

variable {θ} {s : T →+* T} (hs : ∀ t, θ (s t) = (θ t).swap)
include hs

theorem firstSplit_conj (t : T) : t1 θ (s t) = t2 θ t := by
  rw [firstSplit_apply, secondSplit_apply, hs]
  rfl
theorem secondSplit_conj (t : T) : t2 θ (s t) = t1 θ t := by
  rw [firstSplit_apply, secondSplit_apply, hs]
  rfl

variable {n : Type} [Fintype n] [DecidableEq n]

theorem unit_1 (J : Matrix n n T) (g : GL n T) (hg : g ∈ Formalism.UG.UJ s J) :
    ((g : Matrix n n T).map (t2 θ))ᵀ * J.map (t1 θ) * (g : Matrix n n T).map (t1 θ) = J.map (t1 θ) := by
  have hg' : Formalism.UG.cT s (g : Matrix n n T) * J * (g : Matrix n n T) = J := hg
  have e : ((g : Matrix n n T).map (t2 θ))ᵀ = (Formalism.UG.cT s (g : Matrix n n T)).map (t1 θ) := by
    ext i j
    simp [Formalism.UG.cT, firstSplit_conj hs]
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul]
  exact congrArg (fun M : Matrix n n T => M.map (t1 θ)) hg'

theorem unit_2 (J : Matrix n n T) (g : GL n T) (hg : g ∈ Formalism.UG.UJ s J) :
    ((g : Matrix n n T).map (t1 θ))ᵀ * J.map (t2 θ) * (g : Matrix n n T).map (t2 θ) = J.map (t2 θ) := by
  have hg' : Formalism.UG.cT s (g : Matrix n n T) * J * (g : Matrix n n T) = J := hg
  have e : ((g : Matrix n n T).map (t1 θ))ᵀ = (Formalism.UG.cT s (g : Matrix n n T)).map (t2 θ) := by
    ext i j
    simp [Formalism.UG.cT, secondSplit_conj hs]
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul]
  exact congrArg (fun M : Matrix n n T => M.map (t2 θ)) hg'

theorem group_law_jacobian_eq (J : Matrix n n T) (hJ : Formalism.UG.cT s J = J) : J.map (t2 θ) = (J.map (t1 θ))ᵀ := by
  ext i j
  have hij := congrFun (congrFun hJ i) j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at hij
  simp only [Matrix.map_apply, Matrix.transpose_apply]
  rw [← hij, secondSplit_conj hs]

end MassDataIdxCore
