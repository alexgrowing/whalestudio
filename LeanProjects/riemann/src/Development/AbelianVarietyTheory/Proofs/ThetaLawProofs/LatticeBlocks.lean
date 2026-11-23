import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaCharBlockDiagonal
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatuStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KeyPow

theorem det_blocks {j g G : ℕ} {R : Type*} [CommRing R] (e : Fin j × Fin g ≃ Fin G)
    (M : Matrix (Fin g) (Fin g) R) :
    (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) R).det = M.det ^ j := by
  have h : (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) R) =
      Matrix.reindex ((Equiv.prodComm _ _).trans e) ((Equiv.prodComm _ _).trans e)
        (Matrix.blockDiagonal fun _ : Fin j => M) := by
    ext p q
    simp [Matrix.blockDiagonal_apply]
  rw [h, Matrix.det_reindex_self, Matrix.det_blockDiagonal]
  simp

theorem lattice_blocks {j g G : ℕ} (e : Fin j × Fin g ≃ Fin G) (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin G → ℂ) :
    (∀ i, ∃ m n : Fin g → ℤ, (fun k => z (e (i, k))) = (fun k => (m k : ℂ)) + τ.mulVec (fun k => (n k : ℂ))) ↔
      ∃ m n : Fin G → ℤ, z = (fun p => (m p : ℂ)) +
        (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
          τ (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) ℂ).mulVec (fun p => (n p : ℂ)) := by
  constructor
  · intro h
    choose m n h using h
    refine ⟨fun p => m (e.symm p).1 (e.symm p).2, fun p => n (e.symm p).1 (e.symm p).2, ?_⟩
    funext p
    obtain ⟨⟨i, k⟩, rfl⟩ := e.surjective p
    have h₁ := congrFun (ThetaPow.mulVec_blocks e τ (fun p => (n (e.symm p).1 (e.symm p).2 : ℂ)) i) k
    have h₂ := congrFun (h i) k
    simp only [Equiv.symm_apply_apply, Pi.add_apply] at h₁ h₂ ⊢
    rw [h₁, h₂]
  · rintro ⟨m, n, rfl⟩ i
    refine ⟨fun k => m (e (i, k)), fun k => n (e (i, k)), ?_⟩
    rw [← ThetaPow.mulVec_blocks e τ (fun p => (n p : ℂ)) i]
    rfl

theorem normalAt_pow : ∀ (x y : KeyIn ℂ) (j : ℕ) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℝ) (c : ℂ), GlobalTheory.KeyPow.IsKeyPow y x j → GlobalTheory.KeyPow.NormalAt x τ M (fun k => (a k : ℂ)) (fun k => (b k : ℂ)) c → ∃ (e : Fin j × Fin x.P.g ≃ Fin y.P.g) (τ' M' : Matrix (Fin y.P.g) (Fin y.P.g) ℂ), M'.det = M.det ^ j ∧ GlobalTheory.KeyPow.NormalAt y τ' M' (fun p => (a (e.symm p).2 : ℂ)) (fun p => (b (e.symm p).2 : ℂ)) (c ^ j) := by
  rintro x y j τ M a b c hp ⟨u, hs, hd, hΛ, hr, hf, hv⟩
  obtain ⟨e, u', hΛ', hr', hf', hv'⟩ := GlobalTheory.T.exists_holomorphicUniformisation_powerThetaKeyDatum x y j u _
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M) hp hr hf hv
  obtain ⟨hs', hd', hθ⟩ := thetaChar_blockDiagonal j _ τ a b _ e hs hd
  refine ⟨e, _, _, det_blocks e M, u', hs', hd', fun z => ?_, hr', ?_, fun p => ?_⟩
  · rw [hΛ', ← lattice_blocks]
    exact forall_congr' fun i => hΛ _
  · convert hf' using 2 with z
    rw [hθ, Finset.prod_mul_distrib]
    simp
  · convert hv' p using 1
    funext q
    simp only [Pi.smul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp

end GlobalTheory.KeyPow
end
