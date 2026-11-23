import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LamCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ContinuousThetaInf

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

theorem hasFDerivAt_conj_exp {ι : Type} [Fintype ι] {n : ℕ}
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    ∃ D : EuclideanSpace ℝ ι →L[ℝ] (Fin n → ℂ),
      HasFDerivAt (fun y => (A * NormedSpace.exp (L y) * B) *ᵥ w) D 0 ∧ ∀ y, D y = (A * L y * B) *ᵥ w := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  let Lc : EuclideanSpace ℝ ι →L[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap L
  let h : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin n → ℂ) :=
    { toFun := fun M => (A * M * B) *ᵥ w
      map_add' := fun M N => by simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec]
      map_smul' := fun r M => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
        ext i
        simp [Matrix.mulVec, dotProduct, Finset.smul_sum, mul_assoc] }
  let hc : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap h
  have hexp : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (Lc 0) := by
    rw [map_zero]; exact hasFDerivAt_exp_zero
  have h1 := hc.hasFDerivAt.comp (0 : EuclideanSpace ℝ ι) (hexp.comp (0 : EuclideanSpace ℝ ι) Lc.hasFDerivAt)
  refine ⟨hc.comp ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ).comp Lc), h1, fun y => rfl⟩

theorem dKForm_holds : DKForm := by
  intro D X u' ψ hT μinf νinf fibInf hP hb c S ι _ L hc hL x v
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  let Φ : TupI X →+ (InfinitePlace X.B.I.F → Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → ℂ) :=
    { toFun := fun Y v b i => PI.AprimeInfU.thetaInf X v (Y b i)
      map_zero' := by funext v b i; exact map_zero _
      map_add' := by intro Y Z; funext v b i; exact map_add _ _ _ }
  have hsa : ∀ z z', (tupCoord X).symm (z + z') = (tupCoord X).symm z + (tupCoord X).symm z' := by
    intro z z'; apply (tupCoord X).injective; rw [tupCoord_add]; simp
  let T0 : EuclideanSpace ℝ (KapI X) →+ TupI X :=
    { toFun := (tupCoord X).symm
      map_zero' := by
        have h := hsa 0 0
        rw [add_zero] at h
        simpa using h
      map_add' := hsa }
  let Ψ0 := Φ.comp T0
  have hc0 : Continuous Ψ0 := by
    refine continuous_pi fun v => continuous_pi fun b => continuous_pi fun i => ?_
    exact (continuous_thetaInf X v).comp ((continuous_apply i).comp ((continuous_apply b).comp
      (tupCoord X).symm.continuous))
  let Ψ := Ψ0.toRealLinearMap hc0
  have hΨ : ∀ z v b i, Ψ z v b i = PI.AprimeInfU.thetaInf X v ((tupCoord X).symm z b i) := fun _ _ _ _ => rfl
  have hinj : Function.Injective Ψ := by
    intro z z' h
    apply (tupCoord X).symm.injective
    funext b i
    have key : ∀ v, PI.AprimeInfU.thetaInf X v ((tupCoord X).symm z b i) =
        PI.AprimeInfU.thetaInf X v ((tupCoord X).symm z' b i) := by
      intro v
      rw [← hΨ, ← hΨ, h]
    exact sub_eq_zero.1 (thetaInf_inj X _ fun v => by rw [map_sub, key v, sub_self])
  have hcbi : Fintype.card (Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex,
      Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (Ainf X.B.I.F)
        (Module.finBasisOfFinrankEq X.B.I.F X.B.I.E X.B.I.cm.deg2)), Fintype.card_fin]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (KapI X)) =
      Module.finrank ℝ (InfinitePlace X.B.I.F → Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → ℂ) := by
    simp only [finrank_euclideanSpace, Fintype.card_prod, hcbi, Module.finrank_pi_fintype,
      Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin]
    ring
  let Ψe := LinearMap.linearEquivOfInjective (Ψ : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] _) hinj hdim
  have hΨe : ∀ Z : TupI X, tupCoord X Z = Ψe.symm (Φ Z) := by
    intro Z
    apply Ψe.injective
    rw [LinearEquiv.apply_symm_apply, LinearMap.linearEquivOfInjective_apply]
    show Φ (T0 (tupCoord X Z)) = Φ Z
    simp [T0]
  have hG : ∀ x v b, (fun i => Φ (kap0 X hb c L x • Y0 X u') v b i) =
      ((X.B.I.P v * uMat (c v)) * NormedSpace.exp (L x v) * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) *ᵥ
        fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
    intro x v b
    funext i
    show PI.AprimeInfU.thetaInf X v ((X.toInf hb (c * (fun w => expU (X.B.I.ε w) (L x w)) * c⁻¹) • Y0 X u') b i) = _
    rw [theta_act]
    have hu : uMat ((c * (fun w => expU (X.B.I.ε w) (L x w)) * c⁻¹) v) =
        uMat (c v) * NormedSpace.exp (L x v) * uMat (c v)⁻¹ := by
      have e := expU_val (X.B.I.ε v) (L x v) (hL.1 x v).1
      simp only [uMat, Pi.mul_apply, Pi.inv_apply, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul] at e ⊢
      rw [e]
    rw [hu]
    simp only [Matrix.mul_assoc]

  have hD : ∀ v b, ∃ Dvb : EuclideanSpace ℝ ι →L[ℝ] (Fin X.B.I.n → ℂ),
      HasFDerivAt (fun x => Φ (kap0 X hb c L x • Y0 X u') v b) Dvb 0 ∧
        ∀ y, Dvb y = ((X.B.I.P v * uMat (c v)) * L y v * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) *ᵥ
          fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
    intro v b
    obtain ⟨Dvb, h1, h2⟩ := hasFDerivAt_conj_exp ((LinearMap.proj v : (InfinitePlace X.B.I.F →
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) →ₗ[ℝ] _) ∘ₗ L) (X.B.I.P v * uMat (c v)) (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)
      (fun j => X.B.I.φ v (tupH (frameOf X u') b j))
    refine ⟨Dvb, ?_, fun y => h2 y⟩
    have e : (fun x => Φ (kap0 X hb c L x • Y0 X u') v b) = fun x =>
        ((X.B.I.P v * uMat (c v)) * NormedSpace.exp (((LinearMap.proj v : (InfinitePlace X.B.I.F →
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) →ₗ[ℝ] _) ∘ₗ L) x) * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) *ᵥ
          fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
      funext x
      exact hG x v b
    rw [e]
    exact h1
  choose Dv hDv1 hDv2 using hD
  let DD : EuclideanSpace ℝ ι →L[ℝ] (InfinitePlace X.B.I.F → Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → ℂ) :=
    ContinuousLinearMap.pi fun v => ContinuousLinearMap.pi fun b => Dv v b
  have hGd : HasFDerivAt (fun x => Φ (kap0 X hb c L x • Y0 X u')) DD 0 :=
    hasFDerivAt_pi.2 fun v => hasFDerivAt_pi.2 fun b => hDv1 v b
  have hK : KapOrb X u' (kap0 X hb c L) = fun x => Ψe.symm (Φ (kap0 X hb c L x • Y0 X u')) := by
    funext x
    exact hΨe _
  have hKd : HasFDerivAt (KapOrb X u' (kap0 X hb c L))
      (Ψe.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp DD) 0 := by
    rw [hK]
    exact Ψe.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp (0 : EuclideanSpace ℝ ι) hGd
  rw [hKd.fderiv]
  have hΦ : Φ ((tupCoord X).symm (Ψe.symm (DD x))) = DD x := by
    have h1 : Ψe (Ψe.symm (DD x)) = DD x := Ψe.apply_symm_apply (DD x)
    rw [LinearMap.linearEquivOfInjective_apply] at h1
    exact h1
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  ext i b
  have e1 : (fun j => PI.AprimeInfU.thetaInf X v ((tupCoord X).symm (Ψe.symm (DD x)) b j)) = DD x v b :=
    funext fun j => congrFun (congrFun (congrFun hΦ v) b) j
  have hY0 : (fun j => PI.AprimeInfU.thetaInf X v (Y0 X u' b j)) = fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
    funext j
    rw [show Y0 X u' b j = inclR (Ainf X.B.I.F) (tupH (frameOf X u') b j) from rfl, thetaInf_inclR]
  show ((X.B.I.P v)⁻¹ *ᵥ fun j => PI.AprimeInfU.thetaInf X v ((tupCoord X).symm (Ψe.symm (DD x)) b j)) i =
    (uMat (c v) * L x v * uMat (c v)⁻¹ * betaV X v (Y0 X u')) i b
  rw [e1, show DD x v b = Dv v b x from rfl, hDv2]
  have eR : (uMat (c v) * L x v * uMat (c v)⁻¹ * betaV X v (Y0 X u')) i b =
      ((uMat (c v) * L x v * uMat (c v)⁻¹) *ᵥ ((X.B.I.P v)⁻¹ *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j))) i := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    show ((X.B.I.P v)⁻¹ *ᵥ fun j => PI.AprimeInfU.thetaInf X v (Y0 X u' b j)) k = _
    rw [hY0]
    rfl
  have hM : (X.B.I.P v)⁻¹ * (X.B.I.P v * uMat (c v) * L x v * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) =
      uMat (c v) * L x v * uMat (c v)⁻¹ * (X.B.I.P v)⁻¹ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu,
      Matrix.one_mul, Matrix.mul_assoc (uMat (c v) * L x v)]
  rw [eR, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]

end PI.AprimeInfW
