import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistedRepresentations

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

section Twist

variable {Γ : Type} [Group Γ] {O : Type} [CommRing O] {a : ℕ}

def twistRep (ρ : Γ →* GL (Fin a) O) (ξ : Γ →* Oˣ) : Γ →* GL (Fin a) O where
  toFun g := Units.map (Matrix.scalar (Fin a) : O →+* Matrix (Fin a) (Fin a) O).toMonoidHom (ξ g) * ρ g
  map_one' := by simp
  map_mul' g h := by
    ext1
    simp only [map_mul, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    have hc : ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O) * Matrix.scalar (Fin a) (ξ h : O) =
        Matrix.scalar (Fin a) (ξ h : O) * ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O) :=
      ((Matrix.scalar_commute (ξ h : O) (fun r => Commute.all _ r) _).eq).symm
    rw [mul_assoc, mul_assoc, ← mul_assoc (Matrix.scalar (Fin a) (ξ h : O)), ← hc, mul_assoc]

theorem twistRep_val (ρ : Γ →* GL (Fin a) O) (ξ : Γ →* Oˣ) (g : Γ) :
    ((twistRep ρ ξ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O) =
      (ξ g : O) • ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O) := by
  change Matrix.scalar (Fin a) (ξ g : O) * _ = _
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

end Twist

section Local

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def UnramOverTypePrimes (i : N.Loc) (ξ : G H.E N.Om →* (N.O i)ˣ) : Prop :=
  ∀ k : Fin 2, N.l i ≠ H.g k → ∀ w ∈ placesOver H.E (H.g k), ∀ B : ValuationSubring N.Om,
    IsPlaceOver (F := H.E) B w → ∀ σ ∈ Ine (F := H.E) B, ξ σ = 1

def IsRankPart (i : N.Loc) (x : N.X i) (ρ' : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  Continuous (fun g => ((ρ' g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))) ∧
  IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ') ∧
  ∀ w, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
    ((ρ' σ : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)).charpoly *
        ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)) =
      heckePol N i x w

theorem IsRankPart.charpoly_frob {i : N.Loc} {x : N.X i} {ρ' : G H.E N.Om →* GL (Fin R.r) (N.O i)}
    (h : IsRankPart N i x ρ') {r : G H.E N.Om →* GL (Fin R.nV) (N.O i)} (hr : IsHeckeGalois N i x r)
    {w : PlE H} (hw : SplitOut N i w) {B : ValuationSubring N.Om} {σ : G H.E N.Om}
    (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) :
    ((r σ : GL (Fin R.nV) (N.O i)) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).charpoly =
      ((ρ' σ : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)).charpoly *
        ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)) := by
  rw [hr.2.2 w hw B σ hB hσ, h.2.2 w hw B σ hB hσ]

theorem mem_ZgoodN_of_param (A : NAut N) {i : N.Loc} {x : N.X i} {Sig : List (Part A.CG)}
    (hx : HasParamX N A i x Sig) (hg : goodSig N A Sig) : x ∈ ZgoodN N A i := by
  obtain ⟨P, hP, hBC⟩ := hx
  refine ⟨⟨P, hP, _, hBC, ?_⟩, Sig, ⟨P, hP, hBC⟩, hg⟩
  simp [twistIso, muPart]

end Local

def RhoOfGoodPoint (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (Sig : List (Part D.naut.CG)),
    x ∈ ZN D.nd D.naut i → HasParamX D.nd D.naut i x Sig → goodSig D.nd D.naut Sig →
    ∃ (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) (ξ : G D.host.E D.nd.Om →* (D.nd.O i)ˣ),
      IsRepOfSig D.nd D.naut i Sig ρ ∧
      Continuous (fun g => ((ξ g : (D.nd.O i)ˣ) : D.nd.O i)) ∧
      UnramOverTypePrimes D.nd i ξ ∧
      IsRankPart D.nd i x (twistRep ρ ξ)

end GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistedRepresentations

end
