import Formalism.LocalToGlobal.Columns.RecChainCUnfPol
import Formalism.LocalToGlobal.Columns.RefXi1Above

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Vec

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}

def VecAt (E : Type) [Field E] [NumberField E] (n : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 E))) (all : Prop) : Type :=
  {v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal // all ∨ v = 0}

instance (all : Prop) : Finite (VecAt E n SG all) := Subtype.finite

instance vecAct (Λ : LevFam E K n SG) (all : Prop) : MulAction ↥Λ.grp (VecAt E n SG all) where
  smul h v := ⟨fun w => ((h.1 w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec (v.1 w), by
    rcases v.2 with h1 | h1
    · exact Or.inl h1
    · right
      funext w
      rw [h1]
      exact Matrix.mulVec_zero _⟩
  one_smul v := Subtype.ext (funext fun w => Matrix.one_mulVec _)
  mul_smul g h v := Subtype.ext (funext fun w => by
    show ((((g * h : ↥Λ.grp) : GLG E n SG) w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec (v.1 w) =
      ((g.1 w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec
        (((h.1 w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec (v.1 w))
    rw [Matrix.mulVec_mulVec]
    rfl)

abbrev yIdx (Λ : LevFam E K n SG) (all : Prop) : Type := MulAction.orbitRel.Quotient ↥Λ.grp (VecAt E n SG all)

def yIdx.vec {Λ : LevFam E K n SG} {all : Prop} (o : yIdx Λ all) : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal := (Quotient.out o).1

def stabLev (Λ : LevFam E K n SG) (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) : LevFam E K n SG := fun w =>
  { H := (Λ w).H ⊓
      { carrier := {h | (h : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec (v w) = v w}
        one_mem' := Matrix.one_mulVec _
        mul_mem' := fun {a b} ha hb => by
          show ((a * b : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec (v w) = v w
          rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb, ha]
        inv_mem' := fun {a} ha => by
          show ((a⁻¹ : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec (v w) = v w
          conv_lhs => rw [← show (a : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec (v w) = v w from ha]
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] }
    lam := (Λ w).lam.comp (Subgroup.inclusion inf_le_left) }

end Vec

section Ref

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

open Classical in

def refLevCh (m2 : ℕ) : LevCh X Pr R where
  β j := Σ b : L.β j, yIdx (L.levG j b) (j = m2 + 1)
  finβ _ := Fintype.ofFinite _
  decβ _ := Classical.decEq _
  lev j b := stabLev (L.levG j b.1) b.2.vec

def refXi (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (m2 : ℕ) (u : Pr.Word) : XiFamC (refLevCh sel mu L m2) u :=
  fun i b b' p p' x =>
    if i < m2 then XiEntry Ch sel mu cst L i b.1 b'.1 (liftQ hQ p) (liftQ hQ p') x
    else if i = m2 then XiCpl1 Ch sel mu cst L i b.1 (liftQ hQ p) (liftQ hQ p') (p'.1.yOf b'.2.vec) x
    else if i = m2 + 1 then XiTop Ch sel mu cst i (liftQ hQ p) (p.1.yOf b.2.vec) (liftQ hQ p') x
    else 0

end Ref

end Formalism.L2.Col
