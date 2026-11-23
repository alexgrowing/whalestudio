import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

private theorem upts_ext {C : Type} [Ring C] [Algebra ℚ C] [Nontrivial C] {star : C →+* Cᵐᵒᵖ} {R : Type} [CommRing R] [Algebra ℚ R]
    (x y : UPts star R) (h : (((x : (R ⊗[ℚ] C)ˣ × Rˣ).1 : (R ⊗[ℚ] C)ˣ) : R ⊗[ℚ] C) = ((y : (R ⊗[ℚ] C)ˣ × Rˣ).1 : (R ⊗[ℚ] C)ˣ)) :
    x = y := by
  obtain ⟨⟨g, c⟩, hx⟩ := x
  obtain ⟨⟨g', c'⟩, hy⟩ := y
  have hx' : (g : R ⊗[ℚ] C) * (starT star R g).unop = algebraMap R (R ⊗[ℚ] C) c := hx
  have hy' : (g' : R ⊗[ℚ] C) * (starT star R g').unop = algebraMap R (R ⊗[ℚ] C) c' := hy
  have hg : g = g' := Units.ext h
  subst hg
  have hinj : Function.Injective (algebraMap R (R ⊗[ℚ] C)) := fun a b hab =>
    Algebra.TensorProduct.includeLeft_injective (R := ℚ) (S := ℚ) (A := R) (B := C) (algebraMap ℚ C).injective hab
  have hc : c = c' := Units.ext (hinj (hx'.symm.trans hy'))
  subst hc
  rfl

theorem UpperTheory.Gal.W2.Seed.pTrEx :
    AdTEx → MuEx → IsoEx' → JEx → JEq → JSurj → TrEx := by
  intro hT hM hI hJ hQ hS E _ _ _ A n p _ S hn
  obtain ⟨T⟩ := hT p E
  obtain ⟨μ, hμ⟩ := hM (AfP p) E n
  obtain ⟨a, ha⟩ := hI E A n hn
  obtain ⟨j, hj1, hj2⟩ := hJ E A n p S T μ hμ a ha
  obtain ⟨hc, he⟩ := hQ E A n p S T μ hμ a j hj1
  choose sec hs1 hs2 using hS E A n p S T μ hμ a ha
  have hjs : ∀ h, j (sec h) = h := fun h =>
    upts_ext _ _ (μ.injective ((hj1 (sec h)).trans (hs1 h).symm))
  have hmul : ∀ h h', sec (h * h') = sec h * sec h' := by
    intro h h'
    apply hc
    intro w
    by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
    · rw [map_mul, hs2 _ w hw, hs2 _ w hw, hs2 _ w hw, one_mul]
    · exact (he _ _).1 (by rw [map_mul, hjs, hjs, hjs]) w hw
  exact ⟨{ T with
    μ := μ, mu := hμ, a := a, iso := ha, j := j, j_mx := hj1, j_sim := hj2
    sec := MonoidHom.mk' sec hmul, j_sec := hjs, sec_p := hs2, j_eq := he }⟩
