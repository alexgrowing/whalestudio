import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardMulConjEqLeOfFractionalIdeal
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCOfOcc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.NGCut.NormalIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

instance instCM (D : D7) : IsCMField D.host.E := D.host.isCMField_hostE

theorem star_eq_conj (x : D.host.E) : star x = IsCMField.complexConj D.host.E x := rfl

def Jsub (Λ : Submodule (𝓞 D.host.E) (VS D).V) (X : Submodule D.host.E (VS D).V) (y0 : (VS D).V) :
    Submodule (𝓞 D.host.E) D.host.E where
  carrier := {l | l • y0 ∈ Λ ⊔ X.restrictScalars (𝓞 D.host.E)}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, add_smul] at *
    exact Submodule.add_mem _ ha hb
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at *
    rw [smul_assoc]
    exact Submodule.smul_mem _ c ha

section Hyp

variable (Λ : Submodule (𝓞 D.host.E) (VS D).V) (X : Submodule D.host.E (VS D).V) (y0 : (VS D).V)

theorem pair_int (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    (hiso : ∀ x ∈ X, ∀ x' ∈ X, brS (VS D) x x' = 0) (horth : ∀ x ∈ X, brS (VS D) y0 x = 0)
    {l m : D.host.E} (hl : l ∈ Jsub Λ X y0) (hm : m ∈ Jsub Λ X y0) :
    ∃ c : 𝓞 D.host.E, (c : D.host.E) = brS (VS D) (l • y0) (m • y0) := by
  have hl0 : l • y0 ∈ Λ ⊔ X.restrictScalars (𝓞 D.host.E) := hl
  have hm0 : m • y0 ∈ Λ ⊔ X.restrictScalars (𝓞 D.host.E) := hm
  obtain ⟨a1, ha1, x1, hx1, e1⟩ := Submodule.mem_sup.mp hl0
  obtain ⟨a2, ha2, x2, hx2, e2⟩ := Submodule.mem_sup.mp hm0
  have hx1' : x1 ∈ X := by simpa using hx1
  have hx2' : x2 ∈ X := by simpa using hx2

  have hy1 : ∀ x ∈ X, (VS D).hT x y0 = 0 := fun x hx => horth x hx
  have hxx : (VS D).hT x2 x1 = 0 := hiso x1 hx1' x2 hx2'
  have hsym : starRingEnd D.host.E ((VS D).hT x1 y0) = (VS D).hT y0 x1 := by
    first
      | exact (VS D).herm x1 y0
      | exact (VS D).herm.eq x1 y0
  have hy2 : (VS D).hT y0 x1 = 0 := by
    rw [← hsym, hy1 x1 hx1', map_zero]
  have ea1 : a1 = l • y0 - x1 := by rw [← e1]; abel
  have ea2 : a2 = m • y0 - x2 := by rw [← e2]; abel
  have c1 : (VS D).hT x2 a1 = 0 := by
    rw [ea1, map_sub, map_smul, hy1 x2 hx2', hxx]
    simp
  have c2 : (VS D).hT a2 x1 = 0 := by
    rw [ea2, map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy2, hxx]
    simp
  have e : brS (VS D) (l • y0) (m • y0) = (VS D).hT a2 a1 := by
    show (VS D).hT (m • y0) (l • y0) = _
    rw [← e1, ← e2]
    simp only [map_add, LinearMap.add_apply]
    rw [c1, c2, hxx]
    simp

  have ha1d : a1 ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by
    rw [show Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ from hun]
    exact ha1
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at ha1d
  have h2 := (Submodule.mem_iInf _).mp ha1d a2
  have h3 := (Submodule.mem_iInf _).mp h2 ha2
  have h4 := Submodule.mem_comap.mp h3
  obtain ⟨c, hc⟩ := Submodule.mem_one.mp h4
  refine ⟨c, ?_⟩
  rw [e]
  exact hc

end Hyp

end Formalism.L2.SG.NGCut.NormalIntegrality
