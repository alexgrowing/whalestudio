import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimUnitaryKTypeEqDualWeylModule
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorWeylModuleMapsInjectiveOnPureSpan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFockSSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsBranchingMapEquivariantNonzeroCommon
import Formalism.GradedWeylDivisibility.FinalD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.DualWeylTensor

open MvPolynomial

def domOf {n : ℕ} (w : ℕ → ℤ) (h : ∀ a : ℕ, a + 1 < n → w (a + 1) ≤ w a) : Formalism.BasicNotions.DomWeight n where
  w i := w i
  anti := by
    intro i j hij
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    simp only [Fin.mk_le_mk] at hij
    show w j ≤ w i
    have key : ∀ k, i ≤ k → k < n → w k ≤ w i := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ k hik ih => intro hk1; exact (h k hk1).trans (ih (by omega))
    exact key j hij hj

theorem rev_cast {n : ℕ} (i : Fin n) : ((Fin.rev i : ℕ) : ℝ) = (n : ℝ) - 1 - (i : ℕ) := by
  have := i.2
  rw [Fin.val_rev, Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ n)]
  push_cast; ring

theorem lam_eq {n : ℕ} (lamH : Fin n → ℝ) (lam : ℕ → ℤ)
    (hl : ∀ i : Fin n, (lam i : ℝ) = -(Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) lamH) (Fin.rev i)) (i : Fin n) :
    (lam i : ℝ) = -lamH (Fin.rev i) - ((n : ℝ) - 1) / 2 + (i : ℕ) := by
  rw [hl i, GlobalTheory.ConjTypeW.lowK_allPos, rev_cast]; ring

theorem step {n : ℕ} (lamH : Fin n → ℝ) (hH : StrictAnti lamH) (lam : ℕ → ℤ)
    (hl : ∀ i : Fin n, (lam i : ℝ) = -(Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) lamH) (Fin.rev i))
    (a : ℕ) (ha : a + 1 < n) : lam (a + 1) ≤ lam a := by
  have h1 := lam_eq lamH lam hl ⟨a, by omega⟩
  have h2 := lam_eq lamH lam hl ⟨a + 1, ha⟩
  have h3 : lamH (Fin.rev ⟨a, by omega⟩) < lamH (Fin.rev ⟨a + 1, ha⟩) :=
    hH (by rw [Fin.rev_lt_rev]; simp [Fin.lt_def])
  simp only [Fin.val_mk] at h1 h2
  have h4 : ((lam (a + 1) : ℤ) : ℝ) < (lam a : ℝ) + 1 := by rw [h1, h2]; push_cast; linarith
  have h5 : lam (a + 1) < lam a + 1 := by exact_mod_cast h4
  omega

theorem rho_cond {n : ℕ} (lamH : Fin n → ℝ) (hH : StrictAnti lamH) (lam : ℕ → ℤ)
    (hl : ∀ i : Fin n, (lam i : ℝ) = -(Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) lamH) (Fin.rev i)) (i : Fin n) :
    -lamH (Fin.rev i) = ((domOf (n := n) lam (step lamH hH lam hl)).w (Fin.cast rfl i) : ℝ) +
      ((Formalism.BasicNotions.rhoVec n i : ℚ) : ℝ) := by
  show -lamH (Fin.rev i) = ((lam (Fin.cast rfl i : ℕ) : ℤ) : ℝ) + _
  rw [Fin.val_cast, lam_eq lamH lam hl i, Formalism.BasicNotions.rhoVec]
  push_cast; ring

theorem forms_ten_eq {ι : Type} [Fintype ι] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.L2.Forms.ten f = Formalism.L2.DIV.ten f := rfl

theorem polyAction_ten' {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n)
    (h : ι → GL (Fin n) ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.L2.DIV.actP lam h (Formalism.L2.DIV.ten f) = Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.sqAct ℂ n (lam τ) (h τ) (f τ) := by
  have hb := (Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n (fun τ => ((h τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ)).1
  simp only [Formalism.L2.DIV.actP, Formalism.L2.DIV.ten, Formalism.L2.DIV.detTwK, Formalism.L2.DIV.trAct, Formalism.BasicNotions.sqAct, LinearMap.smul_apply,
    AlgHom.toLinearMap_apply, map_prod, hb, map_smul]
  rw [Finset.prod_smul]

theorem sqAct_invTr {n : ℕ} (lam : Formalism.BasicNotions.DomWeight n) (u : Matrix.unitaryGroup (Fin n) ℂ)
    (f : MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.BasicNotions.sqAct ℂ n lam (Formalism.BasicNotions.inside₂ ℂ n (GlobalTheory.Branching.unitaryIncl n u)) f =
      ((u : Matrix (Fin n) (Fin n) ℂ).det ^ (-lam.detShift)) • Formalism.GradedWeylDivisibility.rowAct ℂ (u : Matrix (Fin n) (Fin n) ℂ)ᴴ f := by
  have hm : ((Formalism.BasicNotions.inside₂ ℂ n (GlobalTheory.Branching.unitaryIncl n u) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      ((u : Matrix (Fin n) (Fin n) ℂ)ᴴ)ᵀ := by
    show (((GlobalTheory.Branching.unitaryIncl n u)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ = _
    rw [← map_inv, GlobalTheory.Branching.unitaryIncl_coe]
    rfl
  have hu : (u : Matrix (Fin n) (Fin n) ℂ) * (u : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff).1 u.2
    rwa [Matrix.star_eq_conjTranspose] at this
  have hd : (u : Matrix (Fin n) (Fin n) ℂ)ᴴ.det = ((u : Matrix (Fin n) (Fin n) ℂ).det)⁻¹ := by
    have h1 : (u : Matrix (Fin n) (Fin n) ℂ).det * (u : Matrix (Fin n) (Fin n) ℂ)ᴴ.det = 1 := by
      rw [← Matrix.det_mul, hu, Matrix.det_one]
    exact (eq_inv_of_mul_eq_one_right h1)
  unfold Formalism.BasicNotions.sqAct Formalism.BasicNotions.detPow
  rw [hm, Matrix.transpose_transpose, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, hm,
    Matrix.det_transpose, hd, inv_zpow', zpow_neg]

theorem main : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (H : ι → Type) [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)] [∀ τ, FiniteDimensional ℂ (H τ)] (σ : ∀ τ, Matrix (Fin n) (Fin n) ℂ → (H τ →L[ℂ] H τ)) (lamH : ι → Fin n → ℝ) (lam : ι → ℕ → ℤ), (∀ τ, StrictAnti (lamH τ)) → (∀ τ, Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos n)) (σ τ)) → (∀ τ, Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos n) (σ τ) (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) (lamH τ)) ⊤) → (∀ τ (i : Fin n), (lam τ i : ℝ) = -(Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) (lamH τ)) (Fin.rev i)) → ∃ Φ : Module.Dual ℂ (weylSub n lam) ≃ₗ[ℂ] ⨂[ℂ] τ, H τ, ∀ (u : UG ι n) (φ : Module.Dual ℂ (weylSub n lam)), Φ ((weylRep n lam).dual u φ) = PiTensorProduct.map (fun τ => ((σ τ (u τ) : H τ →L[ℂ] H τ) : H τ →ₗ[ℂ] H τ)) (Φ φ) := by
  intro ι _ _ n H _ _ _ σ lamH lam hH hU hK hl
  classical
  let lam' : ι → Formalism.BasicNotions.DomWeight n := fun τ => domOf (lam τ) (step (lamH τ) (hH τ) (lam τ) (hl τ))
  have hlw : ∀ τ (i : Fin n), (lam' τ).w i = lam τ i := fun _ _ => rfl
  haveI : FiniteDimensional ℂ (Formalism.L2.DIV.VV ℂ lam') := Module.Finite.of_basis (Formalism.L2.DIV.bVV ℂ lam')
  have hj := fun τ => GlobalTheory.DualWeylType.dual_weyl_type n n rfl (lam' τ) (H τ) (σ τ) (lamH τ) (hU τ) (hK τ)
    (rho_cond (lamH τ) (hH τ) (lam τ) (hl τ))
  choose j d b hin hon hortho heq using hj
  obtain ⟨Jt, hinj, hrange, hpure⟩ := GlobalTheory.TenInj.main ι n lam' H j d b hin hon hortho
  have hR : LinearMap.range Jt = Formalism.L2.DIV.VV ℂ lam' := hrange.trans (GlobalTheory.TrueBranch.cSpan_eq_VV lam')
  let E : (⨂[ℂ] τ, H τ) ≃ₗ[ℂ] Formalism.L2.DIV.VV ℂ lam' :=
    (LinearEquiv.ofInjective Jt hinj).trans (LinearEquiv.ofEq _ _ hR)
  have hE : ∀ x, (E x : Formalism.L2.DIV.Pol ℂ ι n) = Jt x := fun _ => rfl
  let U : GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.UG ι n → (ι → GL (Fin n) ℂ) := fun u τ => GlobalTheory.Branching.unitaryIncl n (u τ)
  have hEq : ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.UG ι n) x,
      E (PiTensorProduct.map (fun τ => ((σ τ (u τ) : H τ →L[ℂ] H τ) : H τ →ₗ[ℂ] H τ)) x) =
        Formalism.L2.DIV.rhoK lam' (Formalism.L2.DIV.invTrK (U u)) (E x) := by
    intro u x
    apply Subtype.ext
    rw [hE]
    show Jt _ = Formalism.L2.DIV.actP lam' _ (Jt x)
    have hlin : Jt ∘ₗ PiTensorProduct.map (fun τ => ((σ τ (u τ) : H τ →L[ℂ] H τ) : H τ →ₗ[ℂ] H τ)) =
        Formalism.L2.DIV.actP lam' (Formalism.L2.DIV.invTrK (U u)) ∘ₗ Jt := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro y
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod, hpure]
      rw [forms_ten_eq, forms_ten_eq, polyAction_ten']
      congr 1
      funext τ
      have hs : ((u τ : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.cast rfl) (Fin.cast rfl) =
          (u τ : Matrix (Fin n) (Fin n) ℂ) := by ext; simp
      have h1 := heq τ (u τ) (u τ).2 (y τ)
      rw [hs] at h1
      rw [ContinuousLinearMap.coe_coe, h1]
      exact (sqAct_invTr (lam' τ) (u τ) _).symm
    exact LinearMap.congr_fun hlin x
  obtain ⟨A, hA⟩ := GlobalTheory.CoefPsi.exists_equiv n lam lam' hlw
  refine ⟨(A.symm.dualMap.trans (Module.evalEquiv ℂ (Formalism.L2.DIV.VV ℂ lam')).symm).trans E.symm, fun u φ => ?_⟩
  have hU' : (fun τ => GlobalTheory.Branching.unitaryIncl n ((u⁻¹ : GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.UG ι n) τ)) = (U u)⁻¹ := by
    funext τ
    simp [U, Pi.inv_apply, map_inv]
  have key : ∀ ℓ : Module.Dual ℂ (Formalism.L2.DIV.VV ℂ lam'), weylRep n lam u⁻¹ (A.symm ℓ) =
      A.symm (ℓ ∘ₗ Formalism.L2.DIV.rhoK lam' (Formalism.L2.DIV.invTrK (U u))) := by
    intro ℓ
    apply A.injective
    rw [hA, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hU',
      map_inv (Formalism.L2.DIV.invTrK (K := ℂ) (ι := ι) (n := n)), inv_inv]
  obtain ⟨v, hvv⟩ : ∃ v, (Module.evalEquiv ℂ (Formalism.L2.DIV.VV ℂ lam')).symm (A.symm.dualMap φ) = v := ⟨_, rfl⟩
  have hv : ∀ ℓ : Module.Dual ℂ (Formalism.L2.DIV.VV ℂ lam'), ℓ v = φ (A.symm ℓ) := by
    intro ℓ
    have h2 := congrArg (fun X => X ℓ) ((Module.evalEquiv ℂ (Formalism.L2.DIV.VV ℂ lam')).apply_symm_apply (A.symm.dualMap φ))
    rw [hvv] at h2
    simpa [Module.evalEquiv_apply] using h2
  apply E.injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [hvv, hEq, LinearEquiv.apply_symm_apply]
  apply (Module.evalEquiv ℂ (Formalism.L2.DIV.VV ℂ lam')).injective
  rw [LinearEquiv.apply_symm_apply]
  ext ℓ
  rw [Module.evalEquiv_apply, Module.Dual.eval_apply, LinearEquiv.dualMap_apply, Representation.dual_apply,
    Module.Dual.transpose_apply, LinearMap.comp_apply, key, ← hv]
  rfl

end GlobalTheory.DualWeylTensor
