import Mathlib
import GroundTheory.PAdicHodge.BStPeriod
import GroundTheory.PAdicHodge.ACrisPhi
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OfNatTrans

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

variable (l : ℕ) [Fact l.Prime]

abbrev OC : Type := ↥(normInteger ℂ_[l])

abbrev Ob : Type := PreTilt (OC l) l

def xi0 : AInf ℂ_[l] l := (l : AInf ℂ_[l] l) - WittVector.teichmuller l (pFlat l)

structure PAlg : Type 1 where
  A : Type
  [ring : CommRing A]
  s : Ob l →+* A
  perf : PerfectRing A l
  compl : IsAdicComplete (Ideal.span {s (pFlat l)}) A
  tf : s (pFlat l) ∈ nonZeroDivisors A

attribute [instance] PAlg.ring PAlg.perf

variable {l}

namespace PAlg

@[ext] structure Hom (A B : PAlg l) where
  f : A.A →+* B.A
  comm : f.comp A.s = B.s

instance : Category (PAlg l) where
  Hom := Hom
  id A := ⟨RingHom.id _, RingHom.id_comp _⟩
  comp f g := ⟨g.f.comp f.f, by rw [RingHom.comp_assoc, f.comm, g.comm]⟩

variable (A : PAlg l)

def pi : A.A := A.s (pFlat l)

def AIC : Prop := ∀ P : Polynomial A.A, P.Monic → 0 < P.natDegree → ∃ x, P.IsRoot x

def VAL : Prop := ∀ f g : A.A, (∃ N : ℕ, A.pi ^ N ∈ Ideal.span {f, g}) →
  ∃ e : A.A, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f}

def IsTest : Prop := A.AIC ∧ A.VAL

abbrev W : Type := WittVector l A.A

def sW : AInf ℂ_[l] l →+* A.W := WittVector.map A.s

def xi : A.W := A.sW (xi0 l)

def U : Type := A.W ⧸ Ideal.span {A.xi}

instance : CommRing A.U := inferInstanceAs (CommRing (A.W ⧸ Ideal.span {A.xi}))

def th : A.W →+* A.U := Ideal.Quotient.mk _

abbrev Ug : Type := Localization.Away (l : A.U)

def Acr0 : Subalgebra A.W (Localization.Away (l : A.W)) :=
  Algebra.adjoin A.W (Set.range fun k : ℕ =>
    Ring.inverse (k.factorial : Localization.Away (l : A.W)) * algebraMap A.W (Localization.Away (l : A.W)) A.xi ^ k)

def Acr (n : ℕ) : Type := A.Acr0 ⧸ Ideal.span {(l : A.Acr0) ^ n}

instance (n : ℕ) : CommRing (A.Acr n) := inferInstanceAs (CommRing (A.Acr0 ⧸ Ideal.span {(l : A.Acr0) ^ n}))

def toAcr (n : ℕ) : A.W →+* A.Acr n := (Ideal.Quotient.mk _).comp (algebraMap A.W A.Acr0)

variable {A} {B : PAlg l}

def mapW (f : A ⟶ B) : A.W →+* B.W := WittVector.map (Hom.f f)

theorem mapW_xi (f : A ⟶ B) : mapW f A.xi = B.xi := by
  have h : (mapW f).comp A.sW = B.sW := by
    ext x i
    simp only [mapW, sW, RingHom.comp_apply, WittVector.map_coeff]
    exact RingHom.congr_fun (Hom.comm f) _
  exact RingHom.congr_fun h _

def mapU (f : A ⟶ B) : A.U →+* B.U :=
  Ideal.quotientMap _ (mapW f) (by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show mapW f A.xi ∈ Ideal.span {B.xi}
    rw [mapW_xi]; exact Ideal.mem_span_singleton_self _)

end PAlg

variable (l) in

def IsBase (A : PAlg l) : Prop := Function.Bijective A.s

variable (l) in

abbrev Test : Type 1 := ObjectProperty.FullSubcategory fun A : PAlg l => A.IsTest

end CrystallineSemistableComparison
