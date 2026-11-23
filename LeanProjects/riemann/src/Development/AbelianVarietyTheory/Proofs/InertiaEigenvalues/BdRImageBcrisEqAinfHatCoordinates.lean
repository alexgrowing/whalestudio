import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusActionMulOneStatement
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisInclIBEqDeRhamInclID
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrysLatticeBdRPlusActionCompat
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.PhiModCoefficientsEqSumOfInverseMatrix
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open GlobalTheory.BKGal.HatVal in
private theorem gen {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O)
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) {W : Type} [AddCommGroup W] (Y : TW (OB l O) T →+ W)
    (act : OD l O →+ (W →+ W)) (hmul : ∀ x y w, act (x * y) w = act x (act y w)) (C : GlobalTheory.MemLoc.Core l)
    (hact : ∀ (b : OB l O) (y : OD l O), iotaO O C b = dRO l O y → ∀ z : TW (OB l O) T, Y (b • z) = act y (Y z))
    (n : ℕ) (s : Fin n → ZMod a → Ahat O K l e) (m : Fin n → P.MMl) (c : ZMod a → ι → Ahat O K l e)
    (hc : ∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) =
      ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) :
    ∑ k, act (ϖ.iD t K (s k)) (Y (jB (toBcris t ϖ P (m k)))) =
      ∑ j, act (ϖ.iD t K (fun τ => c τ j)) (Y (jB (Pi.single j 1))) := by
  have hco := UpperTheory.KN.phiMod_coefficients_eq_sum_of_inverse_matrix l a e O K t ϖ ι P n s m c hc
  have h1 : ∀ k, Y (jB (toBcris t ϖ P (m k))) = ∑ j, act (ϖ.iD t K
      (fun τ => GlobalTheory.GalStep.hatR O (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧)))
      (Y (jB (Pi.single j 1))) := by
    intro k
    have h2 : toBcris t ϖ P (m k) = ∑ j, ϖ.iB t K
        (coordL P (invL l (S O K e)) (m k) j) • (Pi.single j 1 : ι → OB l O) := by
      funext i
      rw [toBcris_apply, Finset.sum_apply, Finset.sum_eq_single i]
      · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      · intro j _ hj
        rw [Pi.smul_apply, Pi.single_eq_of_ne hj.symm, smul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [jB.map_smul]
    exact hact _ _ (UpperTheory.KN.crisIncl_iB_eq_deRhamIncl_iD l a e O K t ϖ C _) _
  simp only [h1, hco, map_sum, map_mul, AddMonoidHom.finset_sum_apply, hmul]
  exact Finset.sum_comm

theorem _root_.GlobalTheory.T.bdR_image_bcris_eq_ainfHat_coordinates : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl) (c : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (c τ j) = ∑ i, hat ↥(OL LL) l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) → ∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (s k)) (X (jB (toBcris (thetaW a LL) ϖ P (m k)))) = ∑ j, A (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => c τ j)) (X (jB (Pi.single j 1))) := by
  intro _ l _ a e _ _ ϖ LL _ _ _ ι _ _ P T jB Pl AI Td Y hY act hA n s m c hc
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  exact gen (thetaW a LL) ϖ P T jB Y act (GlobalTheory.T.coeffDeRhamPlusAction_mul_one l LL T Pl AI Td act hA).1 C
    (UpperTheory.KN.crysLattice_bdRPlus_action_compat l LL T Pl AI Td Y hY act hA C) n s m c hc
