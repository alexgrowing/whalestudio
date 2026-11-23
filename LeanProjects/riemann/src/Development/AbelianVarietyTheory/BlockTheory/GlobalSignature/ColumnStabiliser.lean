import Mathlib
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open scoped TensorProduct

def colStab (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    letI := D.host.cmStar
    UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →
      Subgroup (GL (Fin D.R.k) D.host.E) :=
  letI := D.host.cmStar
  fun y =>
    UJ (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 ⊓
      ((Lv u).U.comap (MulAut.conj (y : GL (Fin D.R.k)
          (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))⁻¹).toMonoidHom).comap
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))

theorem mem_colStab (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    letI := D.host.cmStar
    ∀ (y : UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (γ : GL (Fin D.R.k) D.host.E),
      γ ∈ colStab D Lv u y ↔
        γ ∈ UJ (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 ∧
          (y : GL (Fin D.R.k) _)⁻¹ *
            bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ *
            (y : GL (Fin D.R.k) _) ∈ (Lv u).U := by
  intro y γ
  simp [colStab, Subgroup.mem_inf, Subgroup.mem_comap]

def ColStabTrivialAt (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  letI := D.host.cmStar
  GBig D → (∀ i : Fin 2, SplitsF D (D.host.g i)) →
    ∀ y : UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      colStab D Lv u y = ⊥

def ColStabTrivial : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), ColStabTrivialAt D Lv u

example (D : D7) : GBig D ↔ ∃ i : Fin 2, 2 * D.R.f * D.R.k + 1 < D.host.g i := by
  unfold GBig
  exact exists_congr fun i => by omega

example (h : ColStabTrivial) (D : D7) (Lv : LevelData D) (u : D.what₂.Word) (hg : GBig D)
    (hs : ∀ i : Fin 2, SplitsF D (D.host.g i)) (c : (D.mem u).C.cls 0)
    (γ : (D.mem u).C.stab 0 c) : γ = 1 := by
  let _ := D.host.cmStar
  have hb := h D Lv u hg hs ((Lv u).y c)
  have hr := ((Lv u).stabI_range c ((Lv u).stabI c γ).1 ((Lv u).stabI c γ).2).1 ⟨γ, rfl⟩
  have hm : ((Lv u).stabI c γ).1 ∈ colStab D Lv u ((Lv u).y c) := by
    rw [mem_colStab]
    refine ⟨((Lv u).stabI c γ).2, ?_⟩
    obtain ⟨x, hx, hx'⟩ := hr
    rw [← hx']
    simpa [mul_assoc] using hx
  rw [hb, Subgroup.mem_bot] at hm
  apply (Lv u).stabI_inj c
  rw [map_one]
  exact Subtype.ext hm

theorem map_colStab (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    letI := D.host.cmStar
    ∀ y : UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      (colStab D Lv u y).map (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) =
        ratPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊓
          (Lv u).U.map (MulAut.conj (y : GL (Fin D.R.k) _)).toMonoidHom := by
  intro y
  ext x
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_colStab D Lv u y γ).1 hγ
    exact ⟨⟨γ, h1, rfl⟩, ⟨_, h2, by simp [mul_assoc]⟩⟩
  · rintro ⟨⟨γ, h1, rfl⟩, z, hz, hz'⟩
    refine ⟨γ, (mem_colStab D Lv u y γ).2 ⟨h1, ?_⟩, rfl⟩
    rw [← hz']
    simpa [mul_assoc] using hz

end GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser
