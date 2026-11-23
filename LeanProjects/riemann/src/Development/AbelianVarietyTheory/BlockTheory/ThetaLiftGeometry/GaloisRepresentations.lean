import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GaloisRepresentations

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

abbrev Rep (i : N.Loc) (a : ℕ) : Type := G H.E N.Om →* GL (Fin a) (Qbar (N.l i))

def IsCont (i : N.Loc) {a : ℕ} (r : Rep N i a) : Prop :=
  Continuous fun g => ((r g : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))

def cycPow (i : N.Loc) (k : ℤ) (g : G H.E N.Om) : Qbar (N.l i) :=
  algebraMap ℚ_[N.l i] (Qbar (N.l i))
    ((((cycZ (F := H.E) (Ω := N.Om) (N.l i) g) ^ k : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) : ℚ_[N.l i])

def IsPolarized (i : N.Loc) {a : ℕ} (r : Rep N i a) : Prop :=
  ∀ c : N.Om ≃+* N.Om, (∀ x : H.E, c (algebraMap H.E N.Om x) = algebraMap H.E N.Om (H.conj x)) →
    ∃ P : GL (Fin a) (Qbar (N.l i)), ∀ g g' : G H.E N.Om, (∀ y, g' y = c (g (c.symm y))) →
      ((r g' : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) *
          (P : Matrix (Fin a) (Fin a) (Qbar (N.l i))) =
        (P : Matrix (Fin a) (Fin a) (Qbar (N.l i))) *
          (cycPow N i (1 - (a : ℤ)) g •
            (((r g)⁻¹ : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i))).transpose)

def IsGalRep (i : N.Loc) {a : ℕ} (π : A.CG a) (r : Rep N i a) : Prop :=
  IsCont N i r ∧ IsSSRep r ∧
  (∀ w : PlE H, A.wdOf i r w = A.lpTw (A.locG π w) ((1 - (a : ℝ)) / 2)) ∧
  (∀ w ∈ placesOver H.E (N.l i), A.IsdRW i r w) ∧
  ∀ τ : H.E →+* Qbar (N.l i), (A.jumpsW i r τ).map (fun n : ℤ => (n : ℂ)) =
    (A.infG π ((A.iotaQC i).toRingHom.comp τ)).map (fun α => ((a : ℂ) - 1) / 2 - α)

def GalRep (i : N.Loc) : Prop :=
  ∀ (a : ℕ) (π : A.CG a), 1 ≤ a → A.csd π → A.ralg π →
    (∃ r : Rep N i a, IsGalRep N A i π r) ∧
    ∀ w : PlE H, w ∉ placesOver H.E (N.l i) → A.tempered (A.locG π w)

def GalRepFull (i : N.Loc) : Prop :=
  ∀ (a : ℕ) (π : A.CG a), 1 ≤ a → A.csd π → A.ralg π →
    (∃ r : Rep N i a, IsGalRep N A i π r ∧ IsPolarized N i r ∧
      ∀ w ∈ placesOver H.E (N.l i), A.unr (A.locG π w) → A.IsCrysW i r w) ∧
    ∀ w : PlE H, A.tempered (A.locG π w)

def IsAlg {a : ℕ} (π : A.CG a) : Prop :=
  ∀ τ : H.E →+* ℂ, ∀ z ∈ A.infG π τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2

def ClozelPurity : Prop :=
  ∀ (a : ℕ) (π : A.CG a), 1 ≤ a → IsAlg N A π →
    ∃ u : ℤ, (∀ τ : H.E →+* ℂ,
        A.infG π ((starRingEnd ℂ).comp τ) = (A.infG π τ).map (fun z => (u : ℂ) - z)) ∧
      (A.csd π → u = 0)

def ExistsGaloisRepresentationOfHeckeCharacter (i : N.Loc) : Prop :=
  ∀ (χ : A.CG 1) (s : ℝ) (n : (H.E →+* ℂ) → ℤ),
    (∀ τ, (A.infG χ τ).map (fun z => z + (s : ℂ)) = {(n τ : ℂ)}) →
    ∃ r : Rep N i 1, IsCont N i r ∧
      (∀ w : PlE H, A.wdOf i r w = A.lpTw (A.locG χ w) s) ∧
      (∀ w ∈ placesOver H.E (N.l i), A.IsdRW i r w) ∧
      ∀ τ : H.E →+* Qbar (N.l i), A.jumpsW i r τ = {-n ((A.iotaQC i).toRingHom.comp τ)}

def Gal : Prop :=
  ∀ i : N.Loc, GalRep N A i ∧ ClozelPurity N A ∧ ExistsGaloisRepresentationOfHeckeCharacter N A i

def GalFull : Prop :=
  ∀ i : N.Loc, GalRepFull N A i ∧ ClozelPurity N A ∧ ExistsGaloisRepresentationOfHeckeCharacter N A i

theorem GalFull.gal (h : GalFull N A) : Gal N A := fun i =>
  ⟨fun a π ha hc hr =>
    let ⟨⟨r, h₁, _⟩, h₂⟩ := (h i).1 a π ha hc hr
    ⟨⟨r, h₁⟩, fun w _ => h₂ w⟩, (h i).2⟩

theorem IsGalRep.crys {i : N.Loc} {a : ℕ} {π : A.CG a} {r : Rep N i a} (h : IsGalRep N A i π r)
    (w : PlE H) (hw : w ∈ placesOver H.E (N.l i)) (hu : A.unr (A.locG π w)) : A.IsCrysW i r w := by
  refine (A.wdOf_unrL i r w hw h.1 (h.2.2.2.1 w hw)).1 ?_
  rw [h.2.2.1 w]
  exact (A.unr_tw _ _).2 hu

end GlobalTheory.IndefiniteRowSideFullHecke.GaloisRepresentations
