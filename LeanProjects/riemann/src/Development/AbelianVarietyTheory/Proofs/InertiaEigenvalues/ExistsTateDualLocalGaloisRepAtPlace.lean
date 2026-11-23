import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMulVec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocChiEpsUEqCycLL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousLoc
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.TateDualX

section Mat

variable {G : Type} [Group G] {LL : Type} [Field LL] {k : ℕ} {V : Type} [AddCommGroup V] [Module LL V]

def toMat (b : Basis (Fin k) LL V) (ρ : Representation LL G V) : G →* Matrix (Fin k) (Fin k) LL :=
  (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom.comp ρ

theorem toMat_apply (b : Basis (Fin k) LL V) (ρ : Representation LL G V) (g : G) :
    toMat b ρ g = LinearMap.toMatrix b b (ρ g) := rfl

def dualTw (c : G →* LLˣ) (M : G →* Matrix (Fin k) (Fin k) LL) : G →* Matrix (Fin k) (Fin k) LL where
  toFun g := ((c g : LLˣ) : LL) • (M g⁻¹).transpose
  map_one' := by simp
  map_mul' g h := by
    simp only [mul_inv_rev, map_mul, Units.val_mul, Matrix.transpose_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, mul_comm]

theorem dualTw_apply (c : G →* LLˣ) (M : G →* Matrix (Fin k) (Fin k) LL) (g : G) :
    dualTw c M g = ((c g : LLˣ) : LL) • (M g⁻¹).transpose := rfl

end Mat

section Cont

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] {k : ℕ}

theorem continuous_dualTw (c : G →* LLˣ) (M : G →* Matrix (Fin k) (Fin k) LL)
    (hc : Continuous fun g => ((c g : LLˣ) : LL)) (hM : Continuous fun g => M g) :
    Continuous fun g => dualTw c M g :=
  hc.smul (hM.comp continuous_inv).matrix_transpose

theorem continuous_toMat {V : Type} [AddCommGroup V] [Module LL V] [TopologicalSpace V]
    [IsModuleTopology LL V] (b : Basis (Fin k) LL V)
    (ρ : Representation LL G V) (hρ : ∀ x, Continuous fun g => ρ g x) :
    Continuous fun g => toMat b ρ g := by
  refine continuous_matrix fun a j => ?_
  have h : Continuous (b.coord a) := IsModuleTopology.continuous_of_linearMap _
  refine (h.comp (hρ (b j))).congr fun g => ?_
  simp [toMat_apply, LinearMap.toMatrix_apply]

end Cont

section Transport

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {k : ℕ}

theorem isDual1_basis (b : Basis (Fin k) LL V) (ρ : Representation LL G V)
    (U : G →* Matrix (Fin k) (Fin k) LL)
    (hd : IsDual1 PD (matRep (toMat b ρ)) (matRep U) (dotProductBilin LL LL)) :
    IsDual1 PD ρ (matRep U) ((dotProductBilin LL LL).comp b.equivFun.toLinearMap) := by
  have hM : ∀ g x, b.equivFun (ρ g x) = matRep (toMat b ρ) g (b.equivFun x) := by
    intro g x
    change _ = (toMat b ρ g).mulVec _
    rw [toMat_apply, Basis.equivFun_apply, Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
  refine ⟨fun g x y => ?_, fun x hx => ?_, fun y hy => ?_, ?_⟩
  · change dotProductBilin LL LL (b.equivFun (ρ g x)) (matRep U g y) = _ * dotProductBilin LL LL (b.equivFun x) y
    rw [hM]
    exact hd.1 g (b.equivFun x) y
  · have := hd.2.1 (b.equivFun x) fun y => hx y
    exact b.equivFun.injective (by rw [this, map_zero])
  · refine hd.2.2.1 y fun v => ?_
    have h := hy (b.equivFun.symm v)
    change dotProductBilin LL LL (b.equivFun (b.equivFun.symm v)) y = 0 at h
    rwa [LinearEquiv.apply_symm_apply] at h
  · rw [Module.finrank_fin_fun, Module.finrank_eq_card_basis b, Fintype.card_fin]

end Transport

section Loc

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem continuous_cyc : Continuous fun g : Br.G D.nbr i w hw =>
    ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) :
      Br.LL D.nbr i w hw) := by
  rw [← GlobalTheory.CycBridge.locChi_epsU_eq_cycLL D i w hw]
  have hfc : Continuous (D.nbr i w hw).toLL :=
    continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have hι : Continuous fun g : Br.G D.nbr i w hw => ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) :=
    continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)
  exact hfc.comp ((GlobalTheory.Pass.FamCont.epsU_cont D.nd i).comp hι)

end Loc

theorem exists_tateDual : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)),
    ∃ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
      (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
      IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX := by
  intro D i w hw X
  have hU : Continuous fun g => dualTw (cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw))
      (toMat (Module.finBasis (Br.LL D.nbr i w hw) X.V) X.ρ) g :=
    continuous_dualTw _ _ (continuous_cyc D i w hw) (continuous_toMat _ X.ρ X.cont)
  exact ⟨GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ hU, _,
    isDual1_basis (Br.PD D.loc D.nbr i w hw) (Module.finBasis (Br.LL D.nbr i w hw) X.V) X.ρ _
      (GlobalTheory.PotDual.isDual1_of_eq (Br.PD D.loc D.nbr i w hw) _ _ fun g => dualTw_apply _ _ g)⟩

end GlobalTheory.TateDualX
