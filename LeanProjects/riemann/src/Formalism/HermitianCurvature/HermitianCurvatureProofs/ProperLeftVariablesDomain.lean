import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceIntegralJacobianFactor
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbWords
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowVLift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalUnipotentFirstBasisEqOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AsmCastMCastM
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Tower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VLetZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniOfCore
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.LeftFubiniLemmas

def ProperLeftVariablesDomain : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (Cs : Set (B.Mat P.k P.r)), IsCompact Cs →
    PartialBesselProperness.Proper (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) Cs (PBQ.domP P.k P.r j p.T.base.z p.T.base.z')

section gen

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jfSliceIntN (e : p + ρ = n) (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq)
    (hz : D.castV e (liftVec k p ρ Bj.z) = B0.z) (hz' : D.castV e (liftVec k p ρ Bj.z') = B0.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (D.castM e (ιLev k p ρ y)))
    (hW' : Bj.μW' Set.univ = 1) (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ e))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k n)
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k n → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k n ∧ Dmin k n B0.z B0.z' x ⟨p, by omega⟩ ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k n, H x ≠ 0 → B.gN x ≤ R) :
    B.JF Bj (U.PhiFun (s := 0) k ρ σ d (D.castV e.symm B0.z) (D.castV e.symm B0.z') (D.castF e H)
        (fun a => a.elim0)) g =
      ∫ v : U.LW σ → ℂ, psiH σ v • PBQ.pbF Bj B0 e H (D.castM e (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g)) := by
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl] at hz hz'
  have hπ'' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y) := fun y => by
    rw [hπ' y, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
  have hset : {x | x ∈ B.GV k (p + ρ) ∧ Dmin k (p + ρ) B0.z B0.z' x ⟨p, by omega⟩ ≠ 0} =
      {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0} := by
    ext x
    show _ ∧ _ ↔ _ ∧ _
    rw [Formalism.FourierDecayAlt.P.hat_z_minimum_degree k p ρ B0.z B0.z' x]
  have hHc' : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0} := hset ▸ hHc
  have h := (Formalism.FourierDecayAlt.P.slice_integral_jacobian_factor hp σ d hd Bj B0 hz'.symm hπ'' hW' hW0' hNj hN0 g hg H hHc' R hR).2
  have hF : D.castF (rfl : p + ρ = p + ρ) H = H := funext fun y => by
    simp only [D.castF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  have hV : ∀ v : Fin (2 * (p + ρ) + k + 1) → ℂ, D.castV (rfl : p + ρ = p + ρ).symm v = v :=
    fun v => Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl v
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, hF, hV, ← hz, ← hz']
  exact h

end gen

section pt

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem slice_eq {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (H : B.Mat k r → E) (a : C.LPt) (hle : D.ptSize a ≤ r)
    (h2 : r - D.ptSize a = r - D.ptSize a) (e : D.ptSize a + (r - D.ptSize a) = r) :
    D.castF h2 (D.sliceAt k r z z' H a) =
      U.PhiFun (s := 0) k (r - D.ptSize a) (D.ptPerm a) (D.ptDiag a) (D.castV e.symm z) (D.castV e.symm z')
        (D.castF e H) (fun a => a.elim0) := by
  funext y
  unfold D.castF
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, D.sliceAt, dif_pos hle]
  rfl

theorem mMap_castM {k j a b : ℕ} (h : a = b) (Z : Matrix (Fin j) (Fin j) ℂ) (g : B.Mat k a) :
    U.mMap k j b Z (D.castM h g) = D.castM (by omega : j + a = j + b) (U.mMap k j a Z g) := by
  subst h
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

theorem pt_eq {k r j : ℕ} (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (hZ : IsUnit Z.det) (τ : ℂ) (hτ : τ ≠ 0)
    (γ : B.Mat k (r - (j + 1))) (e0 : j + (r - j) = r) (h1 : 1 + (r - (j + 1)) = r - j) :
    D.castM e0 (U.mMap k j (r - j) Z (D.castM h1 (U.mMap k 1 (r - (j + 1)) (Matrix.of fun _ _ => τ) γ))) =
      LevelPointCoordinates.x0 k r j hj Z τ γ := by
  rw [mMap_castM, Formalism.FourierDecayAlt.P.PBH.asm_castM_castM]
  unfold LevelPointCoordinates.x0 LevelPointCoordinates.zfull
  have hM : D.castM (Formalism.FourierDecayAlt.P.PBH.hs' k j (r - (j + 1)))
      (U.mMap k j (1 + (r - (j + 1))) Z (U.mMap k 1 (r - (j + 1)) (Matrix.of fun _ _ => τ) γ)) =
      U.mMap k (j + 1) (r - (j + 1)) (U.blk2 Z 0 0 (Matrix.of fun _ _ => τ)) γ :=
    Formalism.FourierDecayAlt.P.PBH.M2 (k := k) (ρ := r - (j + 1)) Z hZ τ hτ γ
  rw [← hM, Formalism.FourierDecayAlt.P.PBH.asm_castM_castM]

end pt

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
