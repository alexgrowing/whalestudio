import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreJoin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime)

noncomputable section

section Objects

variable {K : Type} [Fintype K] (ι : K → Type)

abbrev segreIdx : Unit ⊕ K → Type := Sum.elim (fun _ : Unit => ∀ k, ι k) ι

variable (R : Type*) [CommRing R]

def segreIncl : MRing ι R →ₐ[R] MRing (segreIdx ι) R :=
  rename fun v => (⟨Sum.inr v.1, v.2⟩ : Σ k, segreIdx ι k)

variable {ι R}

def segreY (c : ∀ k, ι k) : MRing (segreIdx ι) R :=
  X (⟨Sum.inl (), c⟩ : Σ k, segreIdx ι k)

def segreMon (c : ∀ k, ι k) : MRing (segreIdx ι) R :=
  ∏ k, X (⟨Sum.inr k, c k⟩ : Σ k, segreIdx ι k)

variable (ι R)

def segreRels : Set (MRing (segreIdx ι) R) :=
  {g | ∃ c d : ∀ k, ι k, g = segreY c * segreMon d - segreY d * segreMon c}

def segreLiftVal (W : Ideal (MRing ι R)) : (Σ k, segreIdx ι k) → Polynomial (MRing ι R ⧸ W)
  | ⟨Sum.inl _, c⟩ => Polynomial.X * Polynomial.C (Ideal.Quotient.mk W (∏ k, X ⟨k, c k⟩))
  | ⟨Sum.inr k, i⟩ => Polynomial.C (Ideal.Quotient.mk W (X ⟨k, i⟩))

def segreLiftMap (W : Ideal (MRing ι R)) :
    MRing (segreIdx ι) R →ₐ[R] Polynomial (MRing ι R ⧸ W) :=
  aeval (segreLiftVal ι R W)

def segreLift (W : Ideal (MRing ι R)) : Ideal (MRing (segreIdx ι) R) :=
  RingHom.ker (segreLiftMap ι R W)

end Objects

section Examples

example (W : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) :
    segreY (R := ℚ) (fun _ => (0 : Fin 2)) * segreMon (fun _ => 1) -
        segreY (fun _ => 1) * segreMon (fun _ => 0) ∈ segreLift _ ℚ W := by
  simp only [segreLift, RingHom.mem_ker, segreY, segreMon, map_sub, map_mul, map_prod,
    segreLiftMap, aeval_X, segreLiftVal]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  ring

example : (X ⟨Sum.inr (), (0 : Fin 2)⟩ : MRing (segreIdx (fun _ : Unit => Fin 2)) ℚ) ∉
    segreLift _ ℚ ⊥ := by
  simp only [segreLift, RingHom.mem_ker, segreLiftMap, aeval_X, segreLiftVal]
  rw [Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
  exact X_ne_zero _

end Examples

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
