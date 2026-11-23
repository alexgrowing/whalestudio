import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp

noncomputable section

open NumberField IsDedekindDomain

namespace PositivityTheory.NCmp

open GlobalTheory.CuspRep

def SatFlip : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π π' : CuspSub L a) (T : π.V ≃ₗ[ℂ] π'.V),
    (∀ o φ, T (π.op (thetaOp o) φ) = π'.op o (T φ)) →
    ∀ (w : HeightOneSpectrum (𝓞 L)) (B : Multiset ℂˣ), (CG.mk π).HasSat w B →
      (CG.mk π').HasSat (conjSrc (IsCMField.complexConj L).toRingEquiv w) (B.map (·⁻¹))

def ThetaTw : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a),
    ∃ (π' : CuspSub L a) (T : π.V ≃ₗ[ℂ] π'.V), ∀ o φ, T (π.op (thetaOp o) φ) = π'.op o (T φ)

end PositivityTheory.NCmp
