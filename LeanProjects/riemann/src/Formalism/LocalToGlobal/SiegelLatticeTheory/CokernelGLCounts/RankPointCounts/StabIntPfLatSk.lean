import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfEx

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

def hgt (q : FreeE w) : ℕ := q.1.2.val - q.1.1.val

theorem qbar_prop (q : FreeE w) :
    pinv w q.1.2 < pinv w q.1.1 ∧ blkOf w.1 (pinv w q.1.2).val = blkOf w.1 (pinv w q.1.1).val :=
  ⟨(pinv_lt_iff w q.1.1 q.1.2 q.2.2).1 q.2.1, by rw [blkOf_pinv, blkOf_pinv]; exact q.2.2.symm⟩

def qbar (q : FreeE w) : FreeE w := ⟨(pinv w q.1.2, pinv w q.1.1), qbar_prop w q⟩

def selfP (q : FreeE w) : Prop := qbar w q = q

def upperM (q : FreeE w) : Prop := (qbar w q).1.1 < q.1.1

def hpr (q : FreeE w) : ℕ := 2 * hgt w q + if upperM w q then 1 else 0

def sgq (q : FreeE w) : D.host.E := (-1) ^ (D.R.rS - q.1.1.val) * (-1) ^ (D.R.rS - q.1.2.val)

def Xmat (y : FreeE w → D.host.E) : MatR D := fun a c =>
  if a = c then 1 else if h : a < c ∧ blkOf w.1 a.val = blkOf w.1 c.val then y ⟨(a, c), h⟩ else 0

def trunc (y : FreeE w → D.host.E) (n : ℕ) : FreeE w → D.host.E := fun q => if hgt w q < n then y q else 0

def cf (y : FreeE w → D.host.E) (q : FreeE w) : D.host.E := ((Xmat w (trunc w y (hgt w q)))⁻¹) q.1.1 q.1.2

variable (D) in

def mOdd : ℕ := (gS D + 1) / 2

def τA (q : FreeE w) (y : FreeE w → D.host.E) : D.host.E :=
  if selfP w q then (mOdd D : D.host.E) * cf w y q
  else if upperM w q then sgq w (qbar w q) * D.conjF (-(y (qbar w q)) + cf w y (qbar w q))
  else 0

variable (D) in

def sLat (h : ℕ) (s : D.host.E) (_hs : D.conjF s = s) : AddSubgroup D.host.E where
  carrier := {z | z ∈ ddPow D h ∧ z + s * D.conjF z ∈ qdPow D h}
  zero_mem' := by
    refine ⟨FractionalIdeal.zero_mem _, ?_⟩
    simp only [map_zero, mul_zero, add_zero]; exact FractionalIdeal.zero_mem _
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨(ddPow D h : Submodule (𝓞 D.host.E) D.host.E).add_mem ha1 hb1, ?_⟩
    rw [map_add, show a + b + s * (D.conjF a + D.conjF b) = (a + s * D.conjF a) + (b + s * D.conjF b) by ring]
    exact (qdPow D h : Submodule (𝓞 D.host.E) D.host.E).add_mem ha2 hb2
  neg_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨(ddPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem ha1, ?_⟩
    rw [map_neg, show -a + s * -D.conjF a = -(a + s * D.conjF a) by ring]
    exact (qdPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem ha2

theorem sgq_conj (q : FreeE w) : D.conjF (sgq w q) = sgq w q := by
  simp [sgq, map_pow, map_neg, map_one]

def Iq (q : FreeE w) : FI D := if selfP w q ∨ ¬ upperM w q then ddPow D (hgt w q) else qdPow D (hgt w q)

def Λq (q : FreeE w) : AddSubgroup D.host.E :=
  if selfP w q then sLat D (hgt w q) (sgq w q) (sgq_conj w q)
  else ((Iq w q : FI D) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup

variable (D) in

def TwistC : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → Odd (gS D) → ∀ (w : Point D.host.E (D.R.rS + 1)) (y : FreeE w → D.host.E),
      CondX w (Xmat w y) ↔ ∀ q, y q - τA w q y ∈ Λq w q

variable (D) in

def SelfIdxC : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (q : FreeE w), selfP w q →
    (Λq w q).relIndex ((Iq w q : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup) ≠ 0

variable (D) in

def OddC : Prop := Odd (gS D)

end Formalism.L2.SG.Pf.StabIntLat
