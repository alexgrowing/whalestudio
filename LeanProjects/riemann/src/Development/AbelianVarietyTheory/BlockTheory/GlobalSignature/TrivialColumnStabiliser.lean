import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open scoped TensorProduct

def GAf (D : D7) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

def GRat (D : D7) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  ratPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

def colU (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  ColLevel.U (Lv u)

def stabGroup (D : D7) (Lv : LevelData D) (u : D.what₂.Word)
    (y : GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  GRat D ⊓ (colU D Lv u).map (MulAut.conj y).toMonoidHom

def ColumnStabilisersTrivial : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word),
    GBig D → (∀ i : Fin 2, SplitsF D (D.host.g i)) →
      ∀ y ∈ GAf D, stabGroup D Lv u y = ⊥

theorem mem_stabGroup (D : D7) (Lv : LevelData D) (u : D.what₂.Word)
    (y γ : GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    γ ∈ stabGroup D Lv u y ↔ γ ∈ GRat D ∧ y⁻¹ * γ * y ∈ colU D Lv u := by
  unfold stabGroup
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨_, h, ?_⟩⟩
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · simp [mul_assoc]

end GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser

end
