import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.Algebra.Category.Ring.FilteredColimits

noncomputable section
open CategoryTheory Limits Polynomial

namespace LateralTheory.CohomologicalPurity.Hz

def Univ {A S : Type} [CommRing A] [CommRing S] (φ : A →+* S) (I : Ideal A) : Prop :=
  ∀ (B : Type) [CommRing B] (J : Ideal B), HenselianRing B J → ∀ ψ : A →+* B, I ≤ J.comap ψ →
    ∃! χ : S →+* B, χ.comp φ = ψ

structure Good {A S : Type} [CommRing A] [CommRing S] (φ : A →+* S) (I : Ideal A) : Prop where
  etale : φ.Etale
  retr : ∃ r : S →+* A ⧸ I, r.comp φ = Ideal.Quotient.mk I
  surj : ∀ s : S, ∃ a : A, s - φ a ∈ I.map φ
  univ : Univ φ I

structure Diag (A : Type) [CommRing A] (I : Ideal A) where
  J : Type
  [cat : SmallCategory J]
  [filt : IsFiltered J]
  D : J ⥤ CommRingCat.{0}
  s : ∀ j, A →+* D.obj j
  nat : ∀ {j k} (e : j ⟶ k), (D.map e).hom.comp (s j) = s k
  good : ∀ j, Good (s j) I
  exh : ∀ (j) (S : Type) [CommRing S] (ψ : D.obj j →+* S), Good ψ (I.map (s j)) →
    ∃ (k : J) (e : j ⟶ k) (ρ : S →+* D.obj k), ρ.comp ψ = (D.map e).hom

attribute [instance] Diag.cat Diag.filt

def Diag.leg {A : Type} [CommRing A] {I : Ideal A} (Δ : Diag A I) (c : Cocone Δ.D) (j : Δ.J) : Δ.D.obj j →+* c.pt :=
  (c.ι.app j).hom

def LeafComp : Prop :=
  (∀ (A S : Type) [CommRing A] [CommRing S] (e : A ≃+* S) (I : Ideal A), Good (e : A →+* S) I) ∧
  ∀ (A S T : Type) [CommRing A] [CommRing S] [CommRing T] (φ : A →+* S) (ψ : S →+* T) (I : Ideal A),
    Good φ I → Good ψ (I.map φ) → Good (ψ.comp φ) I

def LeafInv : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) (i : A), i ∈ I →
  ∃ (S : Type) (_ : CommRing S) (φ : A →+* S), Good φ I ∧ IsUnit (φ (1 + i))

def LeafRoot : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) (f : A[X]) (a : A), f.Monic → f.eval a ∈ I →
  IsUnit (Ideal.Quotient.mk I (f.derivative.eval a)) →
  ∃ (S : Type) (_ : CommRing S) (φ : A →+* S) (b : S), Good φ I ∧ (f.map φ).IsRoot b ∧ b - φ a ∈ I.map φ

def LeafSup : Prop := ∀ (A S S' : Type) [CommRing A] [CommRing S] [CommRing S'] (φ : A →+* S) (φ' : A →+* S') (I : Ideal A),
  Good φ I → Good φ' I → ∃ (T : Type) (_ : CommRing T) (u : S →+* T) (u' : S' →+* T),
    u.comp φ = u'.comp φ' ∧ Good (u.comp φ) I

def LeafCoeq : Prop := ∀ (A S S' : Type) [CommRing A] [CommRing S] [CommRing S'] (φ : A →+* S) (φ' : A →+* S') (I : Ideal A)
  (u v : S →+* S'), Good φ I → Good φ' I → u.comp φ = φ' → v.comp φ = φ' →
  ∃ (T : Type) (_ : CommRing T) (w : S' →+* T), w.comp u = w.comp v ∧ Good (w.comp φ') I

def LeafDiag : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A), Nonempty (Diag A I)

def LeafStage : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) (Δ : Diag A I) (c : Cocone Δ.D), IsColimit c →
  ∀ η : A →+* c.pt, (∀ j, (Δ.leg c j).comp (Δ.s j) = η) →
  (∀ T : Finset c.pt, ∃ j, ∀ t ∈ T, t ∈ (Δ.leg c j).range) ∧
  ∀ j (x : Δ.D.obj j), Δ.leg c j x ∈ I.map η → x ∈ I.map (Δ.s j)

def LeafColHens : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) (Δ : Diag A I) (c : Cocone Δ.D), IsColimit c →
  ∀ η : A →+* c.pt, (∀ j, (Δ.leg c j).comp (Δ.s j) = η) → HenselianRing c.pt (I.map η)

def LeafColUniv : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) (Δ : Diag A I) (c : Cocone Δ.D), IsColimit c →
  ∀ η : A →+* c.pt, (∀ j, (Δ.leg c j).comp (Δ.s j) = η) → Univ η I

end LateralTheory.CohomologicalPurity.Hz
