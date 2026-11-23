import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

def cPl (w : Pl E) : Pl E := conjSrc (IsCMField.complexConj E).toRingEquiv w

def orb (w : Pl E) : Finset (Pl E) := {w, cPl E w}

def idem (T : Finset (Pl E)) : FiniteAdeleRing (𝓞 E) E :=
  ⟨fun w => if w ∈ T then 1 else 0, by
    filter_upwards [T.finite_toSet.compl_mem_cofinite] with w hw
    rw [if_neg (by simpa using hw)]
    exact zero_mem _⟩

theorem idem_mul_self (T : Finset (Pl E)) : idem E T * idem E T = idem E T := by
  refine Subtype.ext (funext fun w => ?_)
  show (if w ∈ T then (1 : w.adicCompletion E) else 0) * (if w ∈ T then 1 else 0) = if w ∈ T then 1 else 0
  split_ifs <;> simp

def prjM (T : Finset (Pl E)) :
    Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) →* Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) where
  toFun M := idem E T • M + (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))
  map_one' := by rw [← add_smul, add_sub_cancel, one_smul]
  map_mul' M N := by
    have h1 : idem E T * (1 - idem E T) = 0 := by rw [mul_sub, mul_one, idem_mul_self, sub_self]
    have h2 : (1 - idem E T) * idem E T = 0 := by rw [sub_mul, one_mul, idem_mul_self, sub_self]
    have h3 : (1 - idem E T) * (1 - idem E T) = 1 - idem E T := by rw [sub_mul, one_mul, h1, sub_zero]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
      idem_mul_self, h1, h2, h3, zero_smul, add_zero, zero_add]

def prjG (T : Finset (Pl E)) : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) →* GL (Fin n) (FiniteAdeleRing (𝓞 E) E) :=
  Units.map (prjM E n T)

def Gam (w : Pl E) : Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) := (prjG E n (orb E w)).range

def pfU (w : Pl E) : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) →* Gam E n w := (prjG E n (orb E w)).rangeRestrict

def thU (w : Pl E) : Gam E n w →* Gam E n w := (pfU E n w).comp ((thF E n).comp (Gam E n w).subtype)

def Kglob : Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :=
  ⨅ w : Pl E, (GlobalTheory.LFun.KGL w n).comap (GeneralLinearGroup.map (pLoc E w))

def KU (w : Pl E) : Subgroup (Gam E n w) := (Kglob E n).subgroupOf (Gam E n w)

def FU (S : Set (Pl E)) (φ : ∀ w : Pl E, GLw n w → ℂ) (w : Pl E) (y : Gam E n w) : ℂ :=
  (∏ᶠ u ∈ S ∩ ↑(orb E w), φ u (GeneralLinearGroup.map (pLoc E u) y.1)) *
    ∏ᶠ u ∈ Sᶜ ∩ ↑(orb E w), (GlobalTheory.LFun.KGL u n : Set (GLw n u)).indicator 1 (GeneralLinearGroup.map (pLoc E u) y.1)

instance t2Space_finiteAdeleRing : T2Space (FiniteAdeleRing (𝓞 E) E) :=
  T2Space.of_injective_continuous (f := fun x : FiniteAdeleRing (𝓞 E) E => (x : ∀ v : Pl E, v.adicCompletion E))
    Subtype.val_injective RestrictedProduct.continuous_coe

end GlobalTheory.EulerTw
