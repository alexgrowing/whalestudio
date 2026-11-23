import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvRoots
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCentralGroupAlgebraIdempotentUniversal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupEigenspaceEqTopOfAeval
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

section HeckeKill

variable (D : D7) (S : RatDat D.ntw)

theorem actL_mul (j : ℕ) (g h : G0g D.nd) : actL D S j (g * h) = actL D S j g * actL D S j h := by
  unfold actL
  rw [map_mul, map_mul, map_mul, Units.val_mul, mul_inv, smul_mul_smul_comm]

theorem actL_one (j : ℕ) : actL D S j 1 = 1 := by
  unfold actL
  rw [map_one, map_one, map_one, Units.val_one, inv_one, one_smul]

def actLHom (j : ℕ) : G0g D.nd →* Module.End D.what₂.LL (S.WL j) where
  toFun := actL D S j
  map_one' := actL_one D S j
  map_mul' := actL_mul D S j

def actAlg (j : ℕ) : MonoidAlgebra ↥D.LL0 (G0g D.nd) →+* Module.End D.what₂.LL (S.WL j) :=
  (MonoidAlgebra.lift D.what₂.LL (Module.End D.what₂.LL (S.WL j)) (G0g D.nd) (actLHom D S j)).toRingHom.comp
    (MonoidAlgebra.mapRangeRingHom (G0g D.nd) (algebraMap ↥D.LL0 D.what₂.LL))

theorem actAlg_of (j : ℕ) (g : G0g D.nd) : actAlg D S j (MonoidAlgebra.of _ _ g) = actL D S j g := by
  simp [actAlg, MonoidAlgebra.mapRangeRingHom, MonoidAlgebra.of_apply, actLHom]

theorem actAlg_eL (j : ℕ) : actAlg D S j (eL D) = eLop D S j := by
  letI := Fintype.ofFinite (G0g D.nd)
  rw [eLop, finsum_eq_sum_of_fintype]
  simp [actAlg, eL, MonoidAlgebra.mapRangeRingHom, MonoidAlgebra.lift_apply, actLHom]
  rw [Finsupp.sum_fintype _ (fun a (b : D.what₂.LL) => b • actL D S j a) (fun _ => zero_smul _ _)]
  refine Finset.sum_congr rfl fun g _ => ?_
  congr 1

theorem eLop_idem (j : ℕ) : eLop D S j * eLop D S j = eLop D S j := by
  rw [← actAlg_eL, ← map_mul, (eIdem_all D).1]

theorem eLop_comm (j : ℕ) (g : G0g D.nd) : eLop D S j * actL D S j g = actL D S j g * eLop D S j := by
  rw [← actAlg_eL, ← actAlg_of, ← map_mul, (eIdem_all D).2 g, map_mul]

theorem piCoef_shift (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (u w : Formalism.IndefR.NX.U D.nd) :
    piCoef D θ (u⁻¹ * w) = (((psiUOf D.nd (NX.xiRed D) θ u : (↥D.LL0)ˣ) : ↥D.LL0)) * piCoef D θ w := by
  unfold piCoef
  rw [map_mul, map_inv, mul_inv, inv_inv, Units.val_mul]
  ring

theorem actL_piLop (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ)
    (u : Formalism.IndefR.NX.U D.nd) :
    actL D S j u * piLop D S θ j =
      ((((psiUOf D.nd (NX.xiRed D) θ u : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL)) • piLop D S θ j := by
  letI := Fintype.ofFinite (Formalism.IndefR.NX.U D.nd)
  rw [piLop, finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.smul_sum]
  have h1 : ∀ v : Formalism.IndefR.NX.U D.nd,
      actL D S j u * (((piCoef D θ v : ↥D.LL0) : D.what₂.LL) • actL D S j (v : G0g D.nd)) =
        ((piCoef D θ (u⁻¹ * (u * v)) : ↥D.LL0) : D.what₂.LL) • actL D S j ((u * v : Formalism.IndefR.NX.U D.nd) : G0g D.nd) := by
    intro v
    rw [inv_mul_cancel_left, mul_smul_comm, Subgroup.coe_mul, actL_mul]
  simp_rw [h1]
  rw [Fintype.sum_equiv (Equiv.mulLeft u)
    (fun v => ((piCoef D θ (u⁻¹ * (u * v)) : ↥D.LL0) : D.what₂.LL) • actL D S j ((u * v : Formalism.IndefR.NX.U D.nd) : G0g D.nd))
    (fun w => ((piCoef D θ (u⁻¹ * w) : ↥D.LL0) : D.what₂.LL) • actL D S j (w : G0g D.nd)) (fun v => rfl)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [piCoef_shift, IntermediateField.coe_mul, mul_smul]

theorem eig_le_ker (In : RatIn D S) (j k : ℕ) (P : PlE D.host) (r : ↥D.LL0) (hr : r ∈ evRoots D S In j k P) :
    Module.End.eigenspace (In.hL j k P) ((r : ↥D.LL0) : D.what₂.LL) ≤ LinearMap.ker (phiLop D S In j k P) := by
  intro x hx
  rw [LinearMap.mem_ker]
  by_cases h0 : x = 0
  · rw [h0, map_zero]
  have hev : (In.hL j k P).HasEigenvector ((r : ↥D.LL0) : D.what₂.LL) x := Module.End.hasEigenvector_iff.mpr ⟨hx, h0⟩
  unfold phiLop
  rw [Module.End.aeval_apply_of_hasEigenvector hev, eval_map,
    show ((r : ↥D.LL0) : D.what₂.LL) = algebraMap ↥D.LL0 D.what₂.LL r from rfl, eval₂_at_apply]
  have he : (evPol D S In j k P).eval r = 0 := by
    unfold evPol
    rw [eval_prod]
    exact Finset.prod_eq_zero hr (by simp)
  rw [he, map_zero, zero_smul]

end HeckeKill

theorem phiLop_eLop_piLop : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (j k : ℕ) (P : PlE D.host), 1 ≤ j → j ≤ D.R.m → 1 ≤ k → k ≤ D.R.r →
    IsSplitPl D.host P → P ∉ In.Sb → phiLop D S In j k P * eLop D S j * piLop D S In.θ j = 0 := by
  intro D S In j k P hj1 hj2 hk1 hk2 hsp hP
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.zero_apply, Module.End.mul_apply, Module.End.mul_apply]
  have hg : eLop D S j (piLop D S In.θ j y) ∈ goodL D S In.θ j := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · change eLop D S j (piLop D S In.θ j y) ∈ Module.End.eigenspace (eLop D S j) 1
      rw [Module.End.mem_eigenspace_iff, one_smul, ← Module.End.mul_apply, eLop_idem]
    · refine Submodule.mem_iInf _ |>.mpr fun u => ?_
      rw [Module.End.mem_eigenspace_iff, ← Module.End.mul_apply, ← eLop_comm, Module.End.mul_apply,
        ← Module.End.mul_apply (actL D S j u), actL_piLop, LinearMap.smul_apply, map_smul]
  have hs := In.span j hj1 hj2 hg
  have hle : (⨆ σ ∈ {σ | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}, goodL D S In.θ j ⊓ ⨅ (k : ℕ) (P : PlE D.host)
      (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ In.Sb),
        Module.End.eigenspace (In.hL j k P) ((In.eig j σ k P : ↥D.LL0) : D.what₂.LL)) ≤
      LinearMap.ker (phiLop D S In j k P) := by
    refine iSup₂_le fun σ hσ => inf_le_right.trans ?_
    refine (iInf_le _ k).trans ((iInf_le _ P).trans ((iInf_le _ ⟨hk1, hk2, hsp, hP⟩).trans ?_))
    classical
    exact eig_le_ker D S In j k P _ (Finset.mem_image.mpr ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩, rfl⟩)
  exact LinearMap.mem_ker.mp (hle hs)

end GlobalTheory.HeightCounting.FormsStep
