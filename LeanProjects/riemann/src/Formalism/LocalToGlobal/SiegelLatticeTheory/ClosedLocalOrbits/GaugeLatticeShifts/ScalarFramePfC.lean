import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfB

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

section Quot

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem perp_map (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h21 : ∀ y ∈ X2, e.symm y ∈ X1) {x : V} (hx : x ∈ H.perp X1) : e x ∈ H.perp X2 := by
  intro y hy
  rw [show y = e (e.symm y) from (e.apply_symm_apply y).symm, hiso]
  exact hx _ (h21 y hy)

theorem perp_map_symm (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h12 : ∀ x ∈ X1, e x ∈ X2) {y : V} (hy : y ∈ H.perp X2) : e.symm y ∈ H.perp X1 := by
  intro x hx
  rw [← hiso, e.apply_symm_apply]
  exact hy _ (h12 x hx)

def perpEquiv (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h12 : ∀ x ∈ X1, e x ∈ X2) (h21 : ∀ y ∈ X2, e.symm y ∈ X1) : ↥(H.perp X1) ≃ₗ[E] ↥(H.perp X2) :=
  e.ofSubmodules (H.perp X1) (H.perp X2) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact perp_map H e hiso X1 X2 h21 hx
    · intro hy
      exact ⟨e.symm y, perp_map_symm H e hiso X1 X2 h12 hy, e.apply_symm_apply y⟩)

theorem perpEquiv_coe (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h12 : ∀ x ∈ X1, e x ∈ X2) (h21 : ∀ y ∈ X2, e.symm y ∈ X1) (x : ↥(H.perp X1)) :
    ((perpEquiv H e hiso X1 X2 h12 h21 x : ↥(H.perp X2)) : V) = e x := rfl

def qEquiv (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h12 : ∀ x ∈ X1, e x ∈ X2) (h21 : ∀ y ∈ X2, e.symm y ∈ X1) :
    (↥(H.perp X1) ⧸ X1.comap (H.perp X1).subtype) ≃ₗ[E] (↥(H.perp X2) ⧸ X2.comap (H.perp X2).subtype) :=
  Submodule.Quotient.equiv _ _ (perpEquiv H e hiso X1 X2 h12 h21) (by
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨⟨x, hx⟩, hx1, hxy⟩
      have h' : e x = y := congrArg Subtype.val hxy
      rw [← h']
      exact h12 x hx1
    · intro hy2
      refine ⟨⟨e.symm y, perp_map_symm H e hiso X1 X2 h12 hy⟩, h21 y hy2, ?_⟩
      apply Subtype.ext
      show e (e.symm y) = y
      exact e.apply_symm_apply y)

theorem qEquiv_mk (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h12 : ∀ x ∈ X1, e x ∈ X2) (h21 : ∀ y ∈ X2, e.symm y ∈ X1) (x : ↥(H.perp X1)) :
    qEquiv H e hiso X1 X2 h12 h21 (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (perpEquiv H e hiso X1 X2 h12 h21 x) := rfl

theorem mk_eq_iff (X : Submodule E V) (x y : ↥(H.perp X)) :
    (Submodule.Quotient.mk x : ↥(H.perp X) ⧸ X.comap (H.perp X).subtype) = Submodule.Quotient.mk y ↔
      (x : V) - y ∈ X := by
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub]

theorem smul_mk_eq (X : Submodule E V) (c₁ c₂ : E) (x y : ↥(H.perp X)) (h : c₁ • (x : V) - c₂ • (y : V) ∈ X) :
    c₁ • (Submodule.Quotient.mk x : ↥(H.perp X) ⧸ X.comap (H.perp X).subtype) = c₂ • Submodule.Quotient.mk y := by
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, mk_eq_iff]
  simpa using h

theorem iso_span {ι : Type} (w : ι → V) (hw : ∀ i j, H.h (w i) (w j) = 0) :
    ∀ a ∈ Submodule.span E (Set.range w), ∀ b ∈ Submodule.span E (Set.range w), H.h a b = 0 := by
  have hle : Submodule.span E (Set.range w) ≤ H.perp (Submodule.span E (Set.range w)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_perp_span]
    rintro _ ⟨j, rfl⟩
    exact hw i j
  intro a ha b hb
  exact hle ha b hb

end Quot

end Formalism.L2.SG.Pf.ScalarFramePf
