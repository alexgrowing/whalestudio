import Formalism.HermitianCurvature.HermitianCurvatureProofs.RhsInt

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

def psiInt {ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (B1 : B.RealPlaceData k (ρ + 1) Wp Wq) (f1 : B.Mat k (ρ + 1) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (γ : B.Mat k ρ) (b b' : B.Mat k (1 + ρ)) : Wq →L[ℂ] Wp :=
  (psi k (ρ + 1) B1.z cStd (D.castM (Nat.add_comm 1 ρ) b) *
      star (psi k (ρ + 1) B1.z' cStd (D.castM (Nat.add_comm 1 ρ) b'))) •
    f1 ((D.castM (Nat.add_comm 1 ρ) b)⁻¹ * D.castM (Nat.add_comm 1 ρ) (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) *
      D.castM (Nat.add_comm 1 ρ) b')

theorem levA_inv (ρ : ℕ) {h : B.Mat k ρ} (hh : IsUnit h.det) :
    (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ h))⁻¹ = D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ h⁻¹) := by
  rw [← castM_inv', LongWeylElement.lev_inv _ hh]

theorem pt_eq {ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (B1 : B.RealPlaceData k (ρ + 1) Wp Wq) (B0 : B.RealPlaceData k ρ Wp Wq)
    (hz : B1.z = D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ B0.z))
    (hz' : B1.z' = D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ B0.z'))
    (hπ : ∀ y : B.Mat k ρ, B0.π y = B1.π (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ y)))
    (hπ' : ∀ y : B.Mat k ρ, B0.π' y = B1.π' (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ y)))
    (f1 : B.Mat k (ρ + 1) → (Wq →L[ℂ] Wp)) (c : ℂ) (γ : B.Mat k ρ)
    (h0 y h0' y' : Mt k ρ) (a a' : Mt k (1 + ρ))
    (hh0 : Matrix.of h0 ∈ UWset k ρ B0.z) (hy : Matrix.of y ∈ Nset k ρ)
    (hh0' : Matrix.of h0' ∈ UWset k ρ B0.z') (hy' : Matrix.of y' ∈ Nset k ρ)
    (ha : Matrix.of a ∈ Nset k (1 + ρ)) (ha' : Matrix.of a' ∈ Nset k (1 + ρ)) :
    JF.integrand B1 f1 (D.castM (Nat.add_comm 1 ρ) (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ))
        ((levA ρ h0, Qm ρ (a, y)), (levA ρ h0', Qm ρ (a', y'))) =
      (psi k ρ B0.z cStd (Matrix.of y) * star (psi k ρ B0.z' cStd (Matrix.of y'))) •
        (B0.π (Matrix.of h0)).comp
          ((psiInt B1 f1 c ((Matrix.of y * Matrix.of h0)⁻¹ * γ * (Matrix.of y' * Matrix.of h0'))
              (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) a))
              (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) a'))).comp
            (B0.π' (Matrix.of h0')⁻¹)) := by
  set κ : 1 + ρ = ρ + 1 := Nat.add_comm 1 ρ with hκ
  have hH := Ux3.hpk_det k ρ
  have hu0 : IsUnit (Matrix.of h0).det := HermitianFormFactor.UH_unit hH hh0.1
  have hu0' : IsUnit (Matrix.of h0').det := HermitianFormFactor.UH_unit hH hh0'.1
  have huy : IsUnit (Matrix.of y).det := HermitianFormFactor.UH_unit hH hy.1
  have huy' : IsUnit (Matrix.of y').det := HermitianFormFactor.UH_unit hH hy'.1
  have hg : IsUnit (ιLev k 1 ρ (Matrix.of y * Matrix.of h0)).det :=
    LongWeylElement.lev_unit _ (by rw [Matrix.det_mul]; exact huy.mul hu0)
  have hg' : IsUnit (ιLev k 1 ρ (Matrix.of y' * Matrix.of h0')).det :=
    LongWeylElement.lev_unit _ (by rw [Matrix.det_mul]; exact huy'.mul hu0')

  have hconj : ∀ (g : B.Mat k (1 + ρ)) (hg : IsUnit g.det) (x : Mt k (1 + ρ)),
      (Matrix.of (conjM g⁻¹ x) : B.Mat k (1 + ρ)) = g⁻¹ * Matrix.of x * g := by
    intro g hg x
    show g⁻¹ * Matrix.of x * g⁻¹⁻¹ = _
    rw [Matrix.nonsing_inv_nonsing_inv _ hg]

  have hψ1 : psi k (ρ + 1) B1.z cStd (Matrix.of (Qm ρ (a, y))) =
      psi k (ρ + 1) B1.z cStd (D.castM κ (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) a))) *
        psi k ρ B0.z cStd (Matrix.of y) := by
    rw [hz, psi_Qm ρ B0.z_mem ha hy, psi_castM, psi_castM, hconj _ hg, psi_conjLev ρ B0.z_mem ha hy hh0]
  have hψ2 : psi k (ρ + 1) B1.z' cStd (Matrix.of (Qm ρ (a', y'))) =
      psi k (ρ + 1) B1.z' cStd (D.castM κ (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) a'))) *
        psi k ρ B0.z' cStd (Matrix.of y') := by
    rw [hz', psi_Qm ρ B0.z'_mem ha' hy', psi_castM, psi_castM, hconj _ hg', psi_conjLev ρ B0.z'_mem ha' hy' hh0']

  have hπa : B1.π (Matrix.of (levA ρ h0)) = B0.π (Matrix.of h0) := (hπ _).symm
  have hπb : B1.π' (Matrix.of (levA ρ h0'))⁻¹ = B0.π' (Matrix.of h0')⁻¹ := by
    rw [levA_apply, levA_inv ρ hu0', ← hπ']

  have hpt : (Matrix.of (levA ρ h0))⁻¹ * (Matrix.of (Qm ρ (a, y)))⁻¹ *
        D.castM κ (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) * Matrix.of (Qm ρ (a', y')) * Matrix.of (levA ρ h0') =
      (D.castM κ (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) a)))⁻¹ *
        D.castM κ (U.mMap k 1 ρ (Matrix.of fun _ _ => c)
          ((Matrix.of y * Matrix.of h0)⁻¹ * γ * (Matrix.of y' * Matrix.of h0'))) *
        D.castM κ (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) a')) := by
    rw [hconj _ hg, hconj _ hg']
    show (D.castM κ (ιLev k 1 ρ (Matrix.of h0)))⁻¹ * (D.castM κ (Matrix.of a * ιLev k 1 ρ (Matrix.of y)))⁻¹ *
        D.castM κ (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) * D.castM κ (Matrix.of a' * ιLev k 1 ρ (Matrix.of y')) *
        D.castM κ (ιLev k 1 ρ (Matrix.of h0')) = _
    rw [← castM_inv', ← castM_inv', ← castM_inv', ← Dx2.Tower.castM_mul, ← Dx2.Tower.castM_mul,
      ← Dx2.Tower.castM_mul, ← Dx2.Tower.castM_mul, ← Dx2.Tower.castM_mul, ← Dx2.Tower.castM_mul,
      sgs_alg ρ _ _ _ _ hu0 huy hu0' huy']
  unfold JF.integrand JF.xiP B.rho B.sgs psiInt
  rw [hψ1, hψ2, hπa, hπb, hpt]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
  congr 1
  rw [star_mul']
  ring

end Formalism.FourierDecayAlt.P.PBH
