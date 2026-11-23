import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZNuPair

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def firstEmb (d : Fin 2 → ℕ) : GL (Fin (d 0)) k →* Levi k (fun a => Fin (d a)) :=
  MonoidHom.mulSingle (fun a => GL (Fin (d a)) k) 0

def secondEmb (d : Fin 2 → ℕ) : GL (Fin (d 1)) k →* Levi k (fun a => Fin (d a)) :=
  MonoidHom.mulSingle (fun a => GL (Fin (d a)) k) 1

theorem firstEmb_comm (d : Fin 2 → ℕ) (g : GL (Fin (d 0)) k) (h : GL (Fin (d 1)) k) :
    firstEmb d g * secondEmb d h = secondEmb d h * firstEmb d g :=
  Pi.mulSingle_commute (f := fun a => GL (Fin (d a)) k) (by decide : (0 : Fin 2) ≠ 1) g h

variable {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

abbrev whitKer (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X) :
    Submodule ℂ X :=
  twKer (J.comp (secondEmb d)) (unipB k (Fin (d 1))) (whitChar ψ (d 1))

theorem whitKer_le_comap (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    (g : GL (Fin (d 0)) k) : whitKer ψ d J ≤ (whitKer ψ d J).comap (J (firstEmb d g)) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, v, rfl⟩
  refine Submodule.subset_span ⟨u, J (firstEmb d g) v, ?_⟩
  simp only [map_sub, map_smul, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, firstEmb_comm]

def whit2 (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X) :
    Representation ℂ (GL (Fin (d 0)) k) (X ⧸ whitKer ψ d J) where
  toFun g := (whitKer ψ d J).mapQ (whitKer ψ d J) (J (firstEmb d g)) (whitKer_le_comap ψ d J g)
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp

theorem whit2_mk (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    (g : GL (Fin (d 0)) k) (v : X) :
    whit2 ψ d J g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (J (firstEmb d g) v) := rfl

theorem whitKer_le_comap_map (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {J : Representation ℂ (Levi k fun a => Fin (d a)) X}
    {J' : Representation ℂ (Levi k fun a => Fin (d a)) Y} (f : J.IntertwiningMap J') :
    whitKer ψ d J ≤ (whitKer ψ d J').comap f.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, v, rfl⟩
  refine Submodule.subset_span ⟨u, f v, ?_⟩
  simp [f.isIntertwining]

def whitMap (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {J : Representation ℂ (Levi k fun a => Fin (d a)) X}
    {J' : Representation ℂ (Levi k fun a => Fin (d a)) Y} (f : J.IntertwiningMap J') :
    (whit2 ψ d J).IntertwiningMap (whit2 ψ d J') :=
  .mk ((whitKer ψ d J).mapQ (whitKer ψ d J') f.toLinearMap (whitKer_le_comap_map ψ d f)) (fun g => by
    ext v
    simp [whit2_mk, f.isIntertwining])

end

end GlobalTheory.CompanionTheory.BZNuPair

end
