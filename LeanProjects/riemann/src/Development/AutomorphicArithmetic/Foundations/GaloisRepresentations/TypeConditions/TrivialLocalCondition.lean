import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.HeckeCharacterEqualityOfRealisation
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition

noncomputable section

namespace UpperTheory.GalS

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain Formalism.MainNotions.SumRepresentations Formalism.MainNotions.SumRepresentations.At
open UpperTheory.GalN (RelA)

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

structure RelU {w : PlE H} (x y : A.LP w) : Prop where
  rel : RelW N A x y
  nice : Nc N A y

variable {N A}
theorem RelU.dim {w : PlE H} {x y : A.LP w} (h : RelU N A x y) : A.lpDim x = A.lpDim y := h.rel.dim
theorem RelU.ine {w : PlE H} {x y : A.LP w} (h : RelU N A x y) :
    ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol x σ = A.inePol y σ := h.rel.ine h.nice
theorem RelU.mono {w : PlE H} {x y : A.LP w} (h : RelU N A x y) : A.mono0 x := h.rel.mono h.nice
variable (N)

def LGCatN {i : N.Loc} (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) (A : NAut N) (w : PlE H) : Prop :=
  ∀ x, ∃ P, A.ptV i P = some x ∧
    RelU N A (A.wdOf i (mapRep (iotaOQ N A i) (r x)) w) (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2))

variable (A)

def AwayRepN (i : N.Loc) (m : ℕ) (L : ∀ w, A.LP w) : Prop :=
  ∃ r : G H.E N.Om →* GL (Fin m) (Qbar (N.l i)), ContQ N i r ∧ IsSSRep r ∧
    ∀ w, w ∉ placesOver H.E (N.l i) → A.unr (L w) → A.wdOf i r w = L w

def GalIsoN (i : N.Loc) : Prop := ∀ (P : A.AV i) (Pa : List (Part A.CG)), IsBCV N A i P Pa →
  ∃ r : G H.E N.Om →* GL (Fin R.nV) (Qbar (N.l i)),
    Continuous (fun g => ((r g : GL (Fin R.nV) (Qbar (N.l i))) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))) ∧
    IsSSRep r ∧ ∀ w, w ∉ placesOver H.E (N.l i) →
      RelW N A (A.wdOf i r w) (A.lpTw (isoLoc N A Pa w) ((1 - (R.nV : ℝ)) / 2))

def Gd (i : N.Loc) (x : N.X i) (w : PlE H) : Prop := (N.l i ≠ H.g 0 ∧ N.l i ≠ H.g 1) ∨ NcPt N A i x w
end

def LGCN (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ w : PlE D.host, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → LGCatN D.nd r D.naut w

def RowRepAtGN (D : D7) : Prop := ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ →
  ∃ (Sig : List (Part D.naut.CG)) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)),
    HasParamW D.nd D.naut i σ Sig ∧ IsRepOfSig D.nd D.naut i Sig ρ ∧
    ∀ k v, D.nd.l i ≠ D.host.g k →
      RelW D.nd D.naut (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) ρ) (D.naut.plGw k v))
        (D.naut.lpTw (D.naut.locW i σ (D.naut.plGw k v)) ((1 - (D.R.r : ℝ)) / 2))

def IsoRepB (D : D7) : Prop := ∀ (i : D.nd.Loc) (P : D.naut.AV i) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)), IsBCV D.nd D.naut i P Pa →
  ∃ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      RelW D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2))) ∧
    ∀ w ∈ placesOver D.host.E (D.nd.l i), Nc D.nd D.naut (isoLoc D.nd D.naut Pa w) → D.naut.IsdRW i ρ w ∧
      RelA D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧
      ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ

def GalAwayN (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (a : ℕ), 1 ≤ a → ∀ π : D.naut.CG a, D.naut.csd π → D.naut.ralg π →
    ∃ r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)),
      Continuous (fun g => ((r g : GL (Fin a) (Qbar (D.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i)))) ∧
      ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
        RelW D.nd D.naut (D.naut.wdOf i r w) (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))

def IsStringRepN (D : D7) (i : D.nd.Loc) (p : Part D.naut.CG)
    (R : G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i))) : Prop :=
  Continuous (fun g => ((R g : GL _ _) : Matrix (Fin p.a) (Fin p.a) (Qbar (D.nd.l i)))) ∧ IsSSRep R ∧
    ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → RelW D.nd D.naut
      (D.naut.wdOf i R w) (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2))

theorem strN' {D : D7} {i : D.nd.Loc} {p : Part D.naut.CG} {R : G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i))}
    (h : IsStringRepN D i p R) : IsStringRepN D i p R := h

def G2a {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)
    (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∀ w ∈ placesOver H.E (N.l i), N.l i ≠ H.g 0 → N.l i ≠ H.g 1 → ∀ x, A.IsCrysW i (mapRep (iotaOQ N A i) (r x)) w ∧
    ∀ τ, InducesW N i τ w → A.jumpsW i (mapRep (iotaOQ N A i) (r x)) τ = A.locAutHodgeTateWeightsLevelZero i τ

theorem g2a' {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} {i : N.Loc}
    {r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))} (h : G2a N A i r) : G2a N A i r := h

def UnusedSlot55 {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (_ : NAut N) (_ : N.Loc) : Prop := True
def NoCondition (_ : D7) : Prop := True

end UpperTheory.GalS
