import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorChangeOrthonormalBasesSubstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSourceStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompactAction

theorem trace_Jm {n p q : ℕ} (h : p + q = n) (ε : Fin n → Bool) (hε : ∀ a, ε a = decide ((a : ℕ) < p)) :
    (Formalism.REAL.Jm ε).trace = (p : ℂ) - q := by
  subst h
  unfold Formalism.REAL.Jm
  rw [Matrix.trace_diagonal, Fin.sum_univ_add]
  simp [hε, sub_eq_add_neg]

theorem isCartanInv_one {n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * G * B = 1) : IsCartanInv G 1 := by
  have hB : B * (Bᴴ * G) = 1 := mul_eq_one_comm.1 h
  have hi : B⁻¹ = Bᴴ * G := Matrix.inv_eq_right_inv hB
  have hu : IsUnit B := IsUnit.of_mul_eq_one _ hB
  have hG : G = (B⁻¹)ᴴ * B⁻¹ := by
    have h1 : (B⁻¹)ᴴ * Bᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hi, hB, Matrix.conjTranspose_one]
    calc G = ((B⁻¹)ᴴ * Bᴴ) * G := by rw [h1, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, ← hi]
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  refine Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit ?_)
  exact (Matrix.isUnit_nonsing_inv_iff).2 hu

theorem conj_unitary {n : ℕ} {G B g : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * G * B = 1) (hg : gᴴ * G * g = G) :
    B⁻¹ * g * B ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hB : B * (Bᴴ * G) = 1 := mul_eq_one_comm.1 h
  have hi : B⁻¹ = Bᴴ * G := Matrix.inv_eq_right_inv hB
  have h0 : B * B⁻¹ = 1 := by rw [hi, hB]
  have h1 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h0, Matrix.conjTranspose_one]
  have hG : (B⁻¹)ᴴ * B⁻¹ = G := by
    calc _ = (B⁻¹)ᴴ * (Bᴴ * G) := by rw [← hi]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc _ = Bᴴ * (gᴴ * ((B⁻¹)ᴴ * B⁻¹) * g) * B := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hG, hg, h]

theorem det_conj {n : ℕ} {F F' : Matrix (Fin n) (Fin n) ℂ} (h : F' * F = 1) (A C x : Matrix (Fin n) (Fin n) ℂ) :
    (A * (F * x * F') + C).det = (F' * A * F * x + F' * C * F).det := by
  have e : F' * A * F * x + F' * C * F = F' * (A * (F * x * F') + C) * F := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h, Matrix.mul_one]
  have hd : F'.det * F.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  rw [e, Matrix.det_mul, Matrix.det_mul]
  linear_combination (-(A * (F * x * F') + C).det) * hd

theorem pureTensorO_smul {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (c : ℂ) (f : WO S T → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (c • f) P = c • pureTensorO ψ θ S T sS sT BS BT f P := by
  have hd : ∀ τ z (f : WO S T → ℂ), dRho (heisO ψ S T) θ τ z (c • f) = c • dRho (heisO ψ S T) θ τ z f := by
    intro τ z f
    funext x
    simp only [Formalism.IndefR.Datum.dRho, heisO, Pi.smul_apply, smul_eq_mul]
    rw [← deriv_const_mul_field]
    congr 1
    funext t
    ring
  refine (GlobalTheory.OrientedHeis.pureTensorL_intertwine (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) _ _ (c • (1 : Module.End ℂ (WO S T → ℂ))) (fun k f _ => ⟨trivial, ?_⟩) f trivial P).2.symm
  simp only [aPlusAll, Formalism.IndefR.Datum.aPlus, crea, LinearMap.smul_apply, Module.End.one_apply, hd]
  rw [smul_comm Complex.I c, ← smul_sub, smul_comm]

theorem om_pureTensorO_eq_fact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → ∀ (p q : D.what₂.Tau → ℕ), (∀ τ, p τ + q τ = T.rank) → (∀ τ a, M.ε τ a = decide ((a : ℕ) < p τ)) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (x₁ x₂ x₃ : D.what₂.Tau → ℤ), (∀ τ, (x₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (x₂ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (x₃ τ : ℚ) = -(((p τ : ℚ) - q τ) / 2 + b τ)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, M.fr τ * compAt θ τ (Formalism.L2.Theta.mt T h) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ, (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) ∧ ∀ P : PolF D T.rank S.rank, om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f P) = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (fact M.ε x₁ x₂ x₃ (fun τ => M.fr τ * compAt θ τ (Formalism.L2.Theta.mt T h) * (M.fr τ)⁻¹) (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) P) := by
  intro D ψ θ S T χS χT om Sp M BS hom hθ hS hT hBS p q hpq hε a b ha hb x₁ x₂ x₃ h₁ h₂ h₃ f hf hv g hg h hh hk
  have hu : ∀ τ, (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ :=
    fun τ => conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S g τ)
  refine ⟨hu, fun P => ?_⟩
  have f1 : ∀ τ, M.fr τ * (M.fr τ)⁻¹ = 1 := fun τ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have f2 : ∀ τ, (M.fr τ)⁻¹ * M.fr τ = 1 := fun τ => mul_eq_one_comm.1 (f1 τ)
  have b1 : ∀ τ, BS τ * (BS τ)⁻¹ = 1 := fun τ => by
    have hB : BS τ * ((BS τ)ᴴ * gramAt D S τ) = 1 := mul_eq_one_comm.1 (hBS τ)
    rw [Matrix.inv_eq_right_inv hB, hB]
  have hc : ∀ τ, cart M τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * cart M τ := fun τ => by
    have e := congrArg (fun X => (M.fr τ)⁻¹ * X * M.fr τ) (hk τ).2
    simp only [Matrix.mul_assoc, f2, Matrix.mul_one] at e
    rw [← Matrix.mul_assoc (M.fr τ)⁻¹ (M.fr τ), f2, Matrix.one_mul] at e
    unfold cart
    simp only [Matrix.mul_assoc]
    exact e.symm
  have htr : ∀ τ, (cart M τ).trace = (p τ : ℂ) - q τ := fun τ => by
    unfold cart
    rw [Matrix.trace_mul_cycle, f1, Matrix.one_mul, trace_Jm (hpq τ) _ (hε τ)]
  have hvac := GlobalTheory.T.vacuum_character_positive_definite_source D ψ θ S T χS χT om hom hθ hS hT (cart M) (fun τ => isCartanInv_one (hBS τ))
    (GlobalTheory.Chain.VacVec.cart_isCartanInv M) a b ha hb x₁ x₂ x₃ h₁ h₂ (fun τ => by
      rw [htr]
      have := congrArg (fun x : ℚ => (x : ℂ)) (h₃ τ)
      push_cast at this
      exact this) f hf hv g hg h hh hc
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ (fun _ => 1) (fun _ => 1) BS
    (fun τ => BS τ * ((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ)) (cart M) (cart M) (onb M)
    (fun τ => onb M τ * (M.fr τ * compAt θ τ (Formalism.L2.Theta.mt T h) * (M.fr τ)⁻¹)) g h
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) hc
    (fun τ => by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, b1, Matrix.one_mul])
    (fun τ => by unfold onb; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, f2, Matrix.one_mul]) f hf P).2,
    GlobalTheory.T.fockPolynomialVector_change_orthonormalBases_subst D ψ θ S T Sp M BS hom.std hθ hBS _ _ hk hu _ (hom.om_pres _ _ hf), hvac, pureTensorO_smul]
  unfold fact
  rw [LinearMap.smul_apply, map_smul]
  congr 1
  unfold fchar
  refine Finset.prod_congr rfl fun τ _ => ?_
  have eP : (M.fr τ)⁻¹ * ((1 / 2 : ℂ) • (1 + Formalism.REAL.Jm (M.ε τ))) * M.fr τ = (1 / 2 : ℂ) • (1 + cart M τ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, f2]; rfl
  have eM : (M.fr τ)⁻¹ * ((1 / 2 : ℂ) • (1 - Formalism.REAL.Jm (M.ε τ))) * M.fr τ = (1 / 2 : ℂ) • (1 - cart M τ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, f2]; rfl
  have eU : ((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ).det = (compAt θ τ (Formalism.L2.Theta.mt S g)).det := by
    rw [Matrix.det_mul_comm, ← Matrix.mul_assoc, b1, Matrix.one_mul]
  unfold detP detM
  rw [det_conj (f2 τ), det_conj (f2 τ), eP, eM, eU]

end GlobalTheory.FockCompactAction

end
