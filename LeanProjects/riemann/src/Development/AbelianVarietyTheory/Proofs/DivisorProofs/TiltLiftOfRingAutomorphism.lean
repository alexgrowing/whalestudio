import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineThetaNatural
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

noncomputable section
namespace GlobalTheory.DetInv

theorem span_p_map_ringEquiv (p : ℕ) {O : Type} [CommRing O] (γ : O ≃+* O) :
    Ideal.span {(p : O)} = Ideal.map (γ : O →+* O) (Ideal.span {(p : O)}) := by
  rw [Ideal.map_span, Set.image_singleton]
  simp

def modPEquiv (p : ℕ) {O : Type} [CommRing O] (γ : O ≃+* O) : ModP O p ≃+* ModP O p :=
  Ideal.quotientEquiv _ _ γ (span_p_map_ringEquiv p γ)

def perfectionEquiv (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] (e : R ≃+* R) :
    Perfection R p ≃+* Perfection R p :=
  RingEquiv.ofRingHom (Perfection.map p (e : R →+* R)) (Perfection.map p (e.symm : R →+* R))
    (RingHom.ext fun x => Perfection.ext (R := R) (p := p) fun n => by simp [Perfection.coeff_map])
    (RingHom.ext fun x => Perfection.ext (R := R) (p := p) fun n => by simp [Perfection.coeff_map])

theorem perfectionEquiv_coeff (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    (e : R ≃+* R) (x : Perfection R p) (n : ℕ) :
    Perfection.coeff R p n (perfectionEquiv p e x) = e (Perfection.coeff R p n x) :=
  Perfection.coeff_map p (e : R →+* R) x n

def tiltEquiv (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    (γ : O ≃+* O) : PreTilt O p ≃+* PreTilt O p :=
  perfectionEquiv p (modPEquiv p γ)

theorem tiltEquiv_coeff (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    (γ : O ≃+* O) (x : PreTilt O p) (n : ℕ) (y : O)
    (hy : PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {(p : O)}) y) :
    PreTilt.coeff n (tiltEquiv p γ x) = Ideal.Quotient.mk (Ideal.span {(p : O)}) (γ y) := by
  have : PreTilt.coeff n (tiltEquiv p γ x) = modPEquiv p γ (PreTilt.coeff n x) :=
    perfectionEquiv_coeff p (modPEquiv p γ) x n
  rw [this, hy]
  exact Ideal.quotientEquiv_mk _ _ γ _ y

theorem ringEquiv_tilt_theta : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (γ : O ≃+* O), ∃ Γ : PreTilt O p ≃+* PreTilt O p,
    (∀ x, (Γ x).untilt = γ x.untilt) ∧ ∀ a : Ainf p O, WittVector.fontaineTheta O p
      (WittVector.map (Γ : PreTilt O p →+* PreTilt O p) a) = γ (WittVector.fontaineTheta O p a) := by
  intro p _ O _ _ _ γ
  refine ⟨tiltEquiv p γ, fun x => ?_, fun a => ?_⟩
  · exact GlobalTheory.Per.untilt_natural (γ : O →+* O) (tiltEquiv p γ : PreTilt O p →+* PreTilt O p)
      (fun x n y hy => tiltEquiv_coeff p γ x n y hy) x
  · exact GlobalTheory.Per.fontaineTheta_natural (γ : O →+* O) (tiltEquiv p γ : PreTilt O p →+* PreTilt O p)
      (fun x n y hy => tiltEquiv_coeff p γ x n y hy) a

end GlobalTheory.DetInv
