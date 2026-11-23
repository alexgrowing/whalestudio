import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.JacquetShalikaLocal

def lift_levelP_alt₂ : Prop := ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)),
  qF (w.adicCompletion E) = Ideal.absNorm w.asIdeal ∧ ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (v : V) (z : Fin n → ℂˣ),
    IsSatVecGL w ρ v (Finset.univ.val.map z) → Heig ρ v z

def G1 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a),
  (CG.mk π).IsUnitary → ∀ w : HeightOneSpectrum (𝓞 E), ∃ B, Unit' (π.locRep w) B

def G2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
  (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), HasSatGL w (π.locRep w) B → ∀ l : π.V →ₗ[ℂ] ℂ, l ≠ 0 →
    ∃ v g, IsSatVecGL w (π.locRep w) v B ∧ l (π.locRep w g v) ≠ 0

def G3 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
  (w : HeightOneSpectrum (𝓞 E)), Smooth (π.locRep w)

def G4 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a)
  (w : HeightOneSpectrum (𝓞 E)), ∃ ψ, PsiOK ψ ∧ ∃ l : π.V →ₗ[ℂ] ℂ, l ≠ 0 ∧ Whit (π.locRep w) ψ l

end PositivityTheory.JacquetShalikaLocal

end
