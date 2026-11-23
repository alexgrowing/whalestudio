import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.flagMove_of :
    FlagMove := by
  intro Γ k _ _ d ρ W P W' hW' hJH
  have hPP : ∀ w : Fin d → k, (↑P : Matrix (Fin d) (Fin d) k).mulVec
      ((↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hPP' : ∀ w : Fin d → k, (↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec
      ((↑P : Matrix (Fin d) (Fin d) k).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hc : ∀ g v, (↑P : Matrix (Fin d) (Fin d) k).mulVec ((↑(cj P ρ g) : Matrix (Fin d) (Fin d) k).mulVec v) =
      (↑(ρ g) : Matrix (Fin d) (Fin d) k).mulVec ((↑P : Matrix (Fin d) (Fin d) k).mulVec v) := by
    intro g v
    rw [cj_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPP]
  refine ⟨fun i g v hv => ?_, fun i U hU h1 h2 => ?_⟩
  · rw [hW', hc]
    exact hJH.1 i g _ ((hW' i v).1 hv)
  · let U0 : Submodule k (Fin d → k) := U.map (Matrix.mulVecLin (↑P : Matrix (Fin d) (Fin d) k))
    have hmem : ∀ v, v ∈ U ↔ (↑P : Matrix (Fin d) (Fin d) k).mulVec v ∈ U0 := by
      intro v
      constructor
      · intro hv
        exact ⟨v, hv, rfl⟩
      · rintro ⟨u, hu, he⟩
        have huv : u = v := by
          have := congrArg (fun w => (↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec w) he
          simpa [Matrix.mulVecLin_apply, hPP'] using this
        exact huv ▸ hu
    have hinv : IsInv ρ U0 := by
      rintro g w ⟨u, hu, rfl⟩
      refine ⟨(↑(cj P ρ g) : Matrix (Fin d) (Fin d) k).mulVec u, hU g u hu, ?_⟩
      simp only [Matrix.mulVecLin_apply]
      exact hc g u
    have hlo : W i ≤ U0 := by
      intro w hw
      refine ⟨(↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec w, h1 ((hW' i _).2 (by rw [hPP]; exact hw)), ?_⟩
      simp only [Matrix.mulVecLin_apply]
      exact hPP w
    have hhi : U0 ≤ W (i + 1) := by
      rintro w ⟨u, hu, rfl⟩
      exact (hW' (i + 1) u).1 (h2 hu)
    rcases hJH.2 i U0 hinv hlo hhi with h | h
    · left
      ext v
      rw [hmem, h, hW']
    · right
      ext v
      rw [hmem, h, hW']
