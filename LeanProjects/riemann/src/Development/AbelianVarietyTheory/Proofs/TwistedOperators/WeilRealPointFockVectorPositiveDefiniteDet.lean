import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSource
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdeleAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilMaximalCompactFockSubstitutionCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealFockPos

variable {D : D7}

theorem det_ne_zero_of_frame {n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * G * B = 1) :
    G.det ≠ 0 ∧ B.det ≠ 0 := by
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h2
  exact ⟨right_ne_zero_of_mul (left_ne_zero_of_mul_eq_one h2), right_ne_zero_of_mul_eq_one h2⟩

theorem mul_eq_mul_conj {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.det ≠ 0) :
    A * B = B * (B⁻¹ * A * B) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hB), Matrix.one_mul]

theorem scalar_identity (G H : ℂ) (hG : G ≠ 0) (hH : H ≠ 0) (e₁ e₂ : ℤ) (nS nT : ℕ) :
    (G ^ (-e₂ - (nT : ℤ)))⁻¹ * H ^ (e₁ - (nS : ℤ)) * (H ^ nS * G⁻¹ ^ nT) = G ^ e₂ * H ^ e₁ := by
  rw [inv_pow, ← zpow_natCast H, ← zpow_natCast G, ← zpow_neg G, ← zpow_neg G]
  calc G ^ (-(-e₂ - (nT : ℤ))) * H ^ (e₁ - (nS : ℤ)) * (H ^ (nS : ℤ) * G ^ (-(nT : ℤ)))
      = G ^ (-(-e₂ - (nT : ℤ))) * G ^ (-(nT : ℤ)) * (H ^ (e₁ - (nS : ℤ)) * H ^ (nS : ℤ)) := by ring
    _ = G ^ (-(-e₂ - (nT : ℤ)) + -(nT : ℤ)) * H ^ (e₁ - (nS : ℤ) + (nS : ℤ)) := by
      rw [← zpow_add₀ hG, ← zpow_add₀ hH]
    _ = G ^ e₂ * H ^ e₁ := by congr 2 <;> ring

theorem om_pureTensorO_pos : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → (∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = 1) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (e₂ τ : ℚ) = -(b τ + (T.rank : ℚ) / 2)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f P) = (∏ τ, (compAt θ τ (Formalism.L2.Theta.mt S g)).det ^ e₂ τ * (compAt θ τ (Formalism.L2.Theta.mt T h)).det ^ e₁ τ) • pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f (GlobalTheory.CompactHowe.substF (fun τ => (BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) (fun τ => (((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ)⁻¹)ᵀ) P) := by
  intro D ψ θ S T χS χT om hom hθ BS BT hBS hBT a b ha hb e₁ e₂ he₁ he₂ f hf hv g hg h hh P
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hψ := hom.std
  have dS : ∀ τ, (gramAt D S τ).det ≠ 0 ∧ (BS τ).det ≠ 0 := fun τ => det_ne_zero_of_frame (hBS τ)
  have dT : ∀ τ, (gramAt D T τ).det ≠ 0 ∧ (BT τ).det ≠ 0 := fun τ => det_ne_zero_of_frame (hBT τ)
  have cS : ∀ τ, IsCartanInv (gramAt D S τ) 1 := fun τ => GlobalTheory.FockCompactAction.isCartanInv_one (hBS τ)
  have cT : ∀ τ, IsCartanInv (gramAt D T τ) 1 := fun τ => GlobalTheory.FockCompactAction.isCartanInv_one (hBT τ)
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ S (fun τ => (dS τ).1) g hg
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ T (fun τ => (dT τ).1) h hh
  have hvac := GlobalTheory.WeilVacChar.vacuum_character D ψ hψ S T θ hθ χS χT om η hη hom (fun _ => 1) (fun _ => 1)
    cS cT g hg h hh (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) x y hx hy f hf hv
  have expT : ∀ τ, HasInfExp D (χT * (η ^ T.rank)⁻¹) τ ((-e₂ τ - T.rank : ℤ) : ℚ) := fun τ => by
    have h1 := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (hb τ) (hη.2.2.2 τ) T.rank
    convert h1 using 1
    push_cast; rw [he₂]; ring
  have expS : ∀ τ, HasInfExp D (χS * (η ^ S.rank)⁻¹) τ ((e₁ τ - S.rank : ℤ) : ℚ) := fun τ => by
    have h1 := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (ha τ) (hη.2.2.2 τ) S.rank
    convert h1 using 1
    push_cast; rw [he₁]; ring
  have vx := hxv _ (fun τ => -e₂ τ - T.rank) expT
  have vy := hyv _ (fun τ => e₁ τ - S.rank) expS
  have hmain := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ (fun _ => 1) (fun _ => 1) BS
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) (fun _ => 1) (fun _ => 1) BT
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) g h (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => rfl) (fun τ => rfl) f hf P).2
  have fS : (fun τ => compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) =
      fun τ => BS τ * ((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) :=
    funext fun τ => mul_eq_mul_conj _ _ (dS τ).2
  have fT : (fun τ => compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) =
      fun τ => BT τ * ((BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) :=
    funext fun τ => mul_eq_mul_conj _ _ (dT τ).2
  rw [hmain, hvac, GlobalTheory.FiniteFock.pureTensorO_smul, fS, fT,
    GlobalTheory.FockBaseChange.pureTensorO_subst D ψ θ S T hψ hθ BS _ BT _ f hf P]
  congr 1
  rw [Circle.coe_mul, Circle.coe_inv, vx, vy, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have inv := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ g)
  rw [Matrix.det_mul, Matrix.det_one] at inv
  have g0 := left_ne_zero_of_mul_eq_one inv
  have inv' := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ h)
  rw [Matrix.det_mul, Matrix.det_one] at inv'
  have h0 := left_ne_zero_of_mul_eq_one inv'
  rw [GlobalTheory.KJReal.detPlus_one_one, eq_inv_of_mul_eq_one_right inv]
  exact scalar_identity _ _ g0 h0 (e₁ τ) (e₂ τ) S.rank T.rank

end GlobalTheory.RealFockPos

end
