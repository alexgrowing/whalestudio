import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.KaSmallNonpos

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SupremumLattice

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

section Ambient

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
  [IsScalarTower (𝓞 K) K R] (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
  (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)

def supIn : Submodule (𝓞 K) R := (latOf C Vs hV).map (C.subtype.restrictScalars (𝓞 K))

theorem supIn_full_iff :
    ((supIn C Vs hV).FG ∧ Submodule.span K (supIn C Vs hV : Set R) = C) ↔
      Submodule.IsLattice K (latOf C Vs hV) := by
  have h1 : (supIn C Vs hV).FG ↔ (latOf C Vs hV).FG :=
    ⟨Submodule.fg_of_fg_map_injective (C.subtype.restrictScalars (𝓞 K)) C.injective_subtype, fun h => h.map _⟩
  have h2 : Submodule.span K (supIn C Vs hV : Set R) =
      (Submodule.span K (latOf C Vs hV : Set C)).map C.subtype := by
    rw [← Submodule.span_image]; rfl
  rw [h1, h2]
  constructor
  · rintro ⟨a, b⟩
    refine ⟨a, Submodule.map_injective_of_injective C.injective_subtype ?_⟩
    rw [b, Submodule.map_subtype_top]
  · intro h
    exact ⟨h.fg, by rw [h.span_eq_top, Submodule.map_subtype_top]⟩

end Ambient

variable {D : D7}

def supLattice (T : Core D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule (𝓞 T.Q.c.F) (T.R j) :=
  supIn (T.cuspA j a n) (valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)) fun la => isVal_valSet la

def SupLatticeFullAt (T : Core D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  (supLattice T j a n).FG ∧ Submodule.span T.Q.c.F (supLattice T j a n : Set (T.R j)) = T.cuspA j a n

def kappaExp (D : D7) (hK : DV.KapDef D) (hn : Even D.R.nV) (j : ℕ) : (D.host.E →+* ℂ) × ℕ → ℕ :=
  wtA (DIV.Cons.kaWt D hK hn j)

def IntegralCuspFormsFullLattice : Prop :=
  ∀ (D : D7) (hK : DV.KapDef D) (hn : Even D.R.nV) (T : Core D), LawsM T → ∀ j, InR D j →
    SupLatticeFullAt T j (kappaExp D hK hn j) D.R.nV

example (T : Core D) (h : LawsM T) (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) :
    Nonempty (T.PtM j la) := by
  obtain ⟨V, io, e, ho, y, hy⟩ := h.ptNe j hj la
  exact ⟨⟨_, PtV.mk la ho y hy () trivial, rfl⟩⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SupremumLattice
