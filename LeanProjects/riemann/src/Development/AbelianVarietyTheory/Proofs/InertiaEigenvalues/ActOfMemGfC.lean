import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFockVacuumProperties
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ConjTwist
open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefActIo

variable {D : D7}

section Gen

variable {S T : HSp D}

theorem om_fock_of_vac {B : Base S T} {ψ : Twist D Circle} {ω : PairRep S T} (hB : B.Good) (hψ : ψ.Good)
    (hω : B.IsWeil ψ.chi ω) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO B.F.ψ S T) B.F.θ τ (cplxO 1 (B.F.sT τ)) f) {u : GA D S} (hu : u ∈ GinfC S)
    (P : PolF D T.rank S.rank) : ω (u, 1) (B.F.fock f P) = B.F.fock f (B.act u P) := by
  have hθ := hB.frame.vac.2.inf
  have hBS := fun τ => GlobalTheory.RealFockAction.onb_posDef (hB.frame.onbS τ)
  have one : ∀ τ, compAt B.F.θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have eu : ∀ τ, (inBasis B.F.BS (realGL B.F.θ S u) τ).val =
      (B.F.BS τ).val⁻¹ * compAt B.F.θ τ (Formalism.L2.Theta.mt S u) * (B.F.BS τ).val := fun τ => by
    rw [← Matrix.coe_units_inv]
    rfl
  have hle : ∀ τ, B.w.p τ ≤ T.rank := fun τ => by
    obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at e
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  unfold Frame.fock
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D _ _ S T _ _ ω hω hθ (fun _ => 1) (fun _ => 1) (fun τ => (B.F.BS τ).val)
    (fun τ => (B.F.BS τ).val * (inBasis B.F.BS (realGL B.F.θ S u) τ).val) B.F.sT B.F.sT B.F.BT B.F.BT u 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, one_mul, mul_one])
    (fun τ => by rw [eu, ← Matrix.coe_units_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul])
    (fun τ => by rw [one, one_mul]) _ hf P).2, GlobalTheory.RealFockAction.om_vac hB hψ hω hf hv hu,
    GlobalTheory.FiniteFock.pureTensorO_smul,
    GlobalTheory.RealFockAction.pureTensorO_subst (p := B.w.p) hB.frame.vac.1 hθ
      (fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBS τ)) hB.frame.cartT
      (fun τ => (GlobalTheory.RealFockAction.onb_laws (by have := hB.frame.onbT τ; rwa [← hB.sig τ] at this) (hle τ)).1) _ _
      (fun τ => by rw [eu]; exact GlobalTheory.RealFockAction.conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S u τ)) hf,
    Base.act, MonoidHom.comp_apply, fockGL_apply, LinearMap.map_smul]

theorem act_of_mem_GfC (B : Base S T) {k : GA D S} (hk : k ∈ GfC S) : B.act k = 1 := by
  have e : realGL B.F.θ S k = 1 := by
    funext τ
    change (Formalism.UG.bc (B.F.θ τ)) (infHom S k) = 1
    rw [show infHom S k = 1 from hk, map_one]
  rw [Base.act, MonoidHom.comp_apply, e, map_one]

end Gen

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {i : Fin D.R.m}

theorem thetaVector_laws (hC : GlobalTheory.Hk3.Core R F) (t : T0) :
    IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) ∧
      (∀ ρ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ ρ (cplxO 1 (cart (R.MW i (sg0 D A)) ρ)) (R.vP i t)) ∧
      Function.Injective (R.ptP i t) := by
  have hP := hC.thP
  have hM := hC.models
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have h := hP.pt_theta i t 1
    have e : R.ptP i t 1 = R.vP i t := by
      unfold RealDat.ptP pureTensorO pureTensorL
      rw [show (1 : PolF D (Wc D i).rank (Vc D i).rank) = MvPolynomial.basisMonomials _ ℂ 0 from rfl,
        Module.Basis.constr_basis]
      simp [opPow]
    rwa [e] at h
  have hv := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hP.vP i t) hf
  have hne : R.vP i t ≠ 0 :=
    GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i))
      (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i))
      ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hP.vP i t)
  exact ⟨hf, hv, GlobalTheory.FockIndep.pureTensorO_injective D R.ψ R.θ _ _ _ (R.MW i (sg0 D A)) (R.BV i) _
    (hP.ωP i t).std hM.inf (fun τ => GlobalTheory.OneMapRef.VecP.isCartanInv_one_of_onb (hM.BV i τ)) (hM.BV i) hf hne hv⟩

theorem act_ioP_inf (hC : GlobalTheory.Hk3.Core R F) {B : Base (Vc D i) (Wc D i)} (hB : B.Good) (h : BaseOf R i B)
    {ψ : Twist D Circle} (hψ : ψ.Good) {t : T0} (ht : IsTupOf R B ψ t) :
    ∀ u ∈ GinfC (Vc D i), ∀ x w, B.act u (R.ioP i x w) = R.ioP i x ((R.cV i).ρ u w) := by
  intro u hu x w
  obtain ⟨hf, hv, hinj⟩ := thetaVector_laws (i := i) hC t
  have hω := h.isWeil hC.thP.ωP ht
  have hpt : ∀ P, R.ptP i t P = B.F.fock (R.vP i t) P := fun P => by rw [h.fock_eq]; rfl
  have hf' : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) (R.vP i t) := by rw [h.ψ]; exact hf
  have hv' : ∀ τ, IsFockVacAt (heisO B.F.ψ (Vc D i) (Wc D i)) B.F.θ τ (cplxO 1 (B.F.sT τ)) (R.vP i t) := by
    rw [h.ψ, h.θ, h.sT]; exact hv
  apply hinj
  rw [hpt, hpt, ← om_fock_of_vac hB hψ hω hf' hv' hu, ← hpt, ← hpt]
  exact (hC.thP.ioP i t).1 u hu x w

theorem act_ioP (hC : GlobalTheory.Hk3.Core R F) {B : Base (Vc D i) (Wc D i)} (hB : B.Good) (h : BaseOf R i B)
    {ψ : Twist D Circle} (hψ : ψ.Good) {t : T0} (ht : IsTupOf R B ψ t) :
    (∀ u ∈ GinfC (Vc D i), ∀ x w, B.act u (R.ioP i x w) = R.ioP i x ((R.cV i).ρ u w)) ∧
      ∀ (u : GA D (Vc D i)) x w, B.act u (R.ioP i x w) = R.ioP i x ((R.cV i).ρ u w) := by
  refine ⟨act_ioP_inf hC hB h hψ ht, fun u x w => ?_⟩
  have e := GlobalTheory.AutMult.toInf_mul_toFin u
  set a := GlobalTheory.AutMult.toInf (Vc D i) u
  set k := GlobalTheory.AutMult.toFin (Vc D i) u
  rw [← e, map_mul, map_mul, act_of_mem_GfC B k.2, (hC.models.cV i).1 _ k.2, mul_one, mul_one]
  exact act_ioP_inf hC hB h hψ ht _ a.2 x w

end GlobalTheory.CoefActIo

end
