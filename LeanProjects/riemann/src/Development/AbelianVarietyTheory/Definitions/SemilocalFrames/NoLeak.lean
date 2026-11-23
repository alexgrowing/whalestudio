import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.IdxInt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Frames

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

def Ysp (J : ℕ) : Submodule E S.V := S.spanTo S.f J ⊔ S.spanTo S.f' J

def refB (J : ℕ) (Λ : Submodule L.O S.V) : AddSubgroup (S.V × S.V) :=
  ((S.spanTo S.f J).toAddSubgroup.prod (S.spanTo S.f' J).toAddSubgroup) ⊓
    (Λ.toAddSubgroup.map (algebraMap F E S.th • (LinearMap.id : S.V →ₗ[E] S.V)).toAddMonoidHom).comap
      (AddMonoidHom.fst S.V S.V + AddMonoidHom.snd S.V S.V)

def refU (J : ℕ) (Λ : Submodule L.O S.V) : AddSubgroup S.V :=
  Λ.toAddSubgroup ⊓ (perp L S.Hm (S.Ysp J)).toAddSubgroup

def refT : AddSubgroup E :=
  (AddMonoidHom.id E + (L.cj : E →+* E).toAddMonoidHom).ker ⊓
    L.O.toAddSubgroup.map (AddMonoidHom.mulLeft (algebraMap F E ((S.ϖ : F) ^ S.a)))

abbrev MW : Type := (S.V × S.V) × S.V × E

def refA (J : ℕ) (Λ : Submodule L.O S.V) : AddSubgroup S.MW :=
  (S.refB J Λ).prod ((S.refU J Λ).prod S.refT)

def sOf (w : S.MW) : E := algebraMap F E 2⁻¹ * S.h w.2.1 w.2.1 + w.2.2

def Mv (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V) (w : S.MW) : Prop :=
  S.IsMove J d Λ w.1.1 w.1.2 w.2.1 (S.sOf w)

def MvTo (J : ℕ) (d : S.Datum) (Λ Λ₁ : Submodule L.O S.V) (w : S.MW) : Prop :=
  S.Mv J d Λ w ∧ (Λ₁ : Set S.V) = S.moved Λ w.1.1 w.2.1 (S.sOf w)

def NoLeak (Λ : Submodule L.O S.V) (u : S.V) : Prop := ∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1

def InZ (u : S.V) : Prop := ∃ c : 𝒪[F], S.h u u = algebraMap F E ((S.ϖ : F) ^ S.a * c)

def chiM (j : Fin r) (d : S.Datum) (Λ : Submodule L.O S.V) (b : S.V × S.V) (u : S.V) : ℂ :=
  L.psi0 (-(algebraMap F E S.th⁻¹ *
    S.h (S.h b.1 (S.es j) • S.fr d Λ j.succ + S.h b.2 (S.es' j) • S.fr' d Λ j.succ) u))

def cK (β βJ : ℕ) : ℝ := (S.q : ℝ) ^ S.a * β / βJ

def kern (β J βJ : ℕ) (d : S.Datum) (Λ Λ₁ : Submodule L.O S.V) : ℝ :=
  S.cK β βJ * (cint (S.refA J Λ) (ind (S.MvTo J d Λ Λ₁))).re

end GlobalTheory.HL.Frames
