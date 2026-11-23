import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBasisDiagonalTwistedCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerLocalUnitaryCommOfSeparable

noncomputable section

open Matrix PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.LocalTorus

theorem comm (n : ℕ) (d : GL (Fin n) ℂ) (hs : (d * thC n d).val.charpoly.Separable)
    (s : GL (Fin n) ℂ) (hs' : s ∈ twCent (thC n) d) (t : GL (Fin n) ℂ) (ht : t ∈ twCent (thC n) d) :
    s * t = t * s := by
  have hθθ : ∀ g : GL (Fin n) ℂ, thC n (thC n g) = g := by
    intro g
    apply Units.ext
    show ((((thC n g)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ = (g : Matrix (Fin n) (Fin n) ℂ)
    have e : (((thC n g)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        ((g : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ := rfl
    rw [e]
    ext i j
    simp [Matrix.map_apply, Matrix.transpose_apply]
  have key : ∀ x ∈ twCent (thC n) d,
      Commute ((d * thC n d : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (x : Matrix (Fin n) (Fin n) ℂ) := by
    intro x hx
    have h1 : x⁻¹ * d * thC n x = d := hx
    have h2 : d * thC n x = x * d := by
      calc d * thC n x = x * (x⁻¹ * d * thC n x) := by group
        _ = x * d := by rw [h1]
    have h3 : thC n d * x = thC n x * thC n d := by
      have h4 := congrArg (thC n) h2
      rw [map_mul, map_mul, hθθ] at h4
      exact h4
    apply Commute.units_val
    show (d * thC n d) * x = x * (d * thC n d)
    rw [mul_assoc, h3, ← mul_assoc, h2, mul_assoc]
  have hc := GlobalTheory.BCT.CentComm.commute_of_commute_separable hs (key s hs') (key t ht)
  exact Units.ext (by simpa using hc.eq)

end PositivityTheory.Rg.BcB.CV.LocalTorus

theorem PositivityTheory.Rg.BcB.CV.pf_LocTor : PositivityTheory.Rg.BcB.CV.LocTor := by
  intro n d hs
  exact ⟨GlobalTheory.CompanionTheory.LocVan.isClosed_twCent d, PositivityTheory.Rg.BcB.CV.LocalTorus.comm n d hs,
    GlobalTheory.CompanionTheory.LocVan.continuous_thC, GlobalTheory.CompanionTheory.LocVan.locallyCompact_GL n, GlobalTheory.CompanionTheory.LocVan.secondCountable_GL n⟩

end
