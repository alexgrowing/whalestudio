import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearMapTensorOneCommDiagonalAction
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

noncomputable section

namespace GlobalTheory.BaseCoefIner

section Ext

variable {K L : Type} [Field K] [Field L] [Algebra K L] {W : Type} [AddCommGroup W] [Module K W]

theorem extS_mono {S T : Submodule K W} (h : S ≤ T) : CJ.extS L S ≤ CJ.extS L T := by
  have := CJ.extS_inf (L := L) S T
  rw [inf_eq_left.2 h] at this
  rw [this]
  exact inf_le_right

theorem extS_iSup_le {J : Sort*} (S : J → Submodule K W) :
    CJ.extS L (⨆ j, S j) ≤ ⨆ j, CJ.extS L (S j) := by
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | tmul c s =>
    obtain ⟨s, hs⟩ := s
    rw [LinearMap.baseChange_tmul]
    change c ⊗ₜ[K] s ∈ _
    induction hs using Submodule.iSup_induction' with
    | mem j x hx =>
      exact Submodule.mem_iSup_of_mem j ⟨c ⊗ₜ[K] (⟨x, hx⟩ : S j), by simp [LinearMap.baseChange_tmul]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [tmul_add]; exact Submodule.add_mem _ hx hy

end Ext

section Main

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL']

section Tower

variable [Algebra LL LL'] [IsScalarTower Qp LL LL'] {k : ℕ}

theorem comm_act_smul (A : Matrix (Fin k) (Fin k) LL) (β : B →ₗ[Qp] B) (r : LL)
    (x : LL' ⊗[LL] ((Fin k → LL) ⊗[Qp] B)) :
    CJ.EE (Qp := Qp) (LL' := LL') B ((PI.CoefExt.actT A β - r • LinearMap.id).baseChange LL' x)
      = (PI.CoefExt.actT (A.map (algebraMap LL LL')) β - (algebraMap LL LL' r) • LinearMap.id :
        (Fin k → LL') ⊗[Qp] B →ₗ[LL'] (Fin k → LL') ⊗[Qp] B) (CJ.EE B x) := by
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.sub_apply, map_sub,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.id_apply, ← algebraMap_smul LL' r x, map_smul]
  congr 1
  exact PI.CoefExt.coefEquiv_comm A β x

theorem dpcris_ext (M : G →* Matrix (Fin k) (Fin k) LL) :
    (CJ.extS LL' (PC.Dpcris (CJ.rep M))).map ((CJ.EE (Qp := Qp) (LL := LL) (LL' := LL') (k := k) B :
        _ ≃ₗ[LL'] _) : _ →ₗ[LL'] _)
      = PC.Dpcris (CJ.rep (((IsScalarTower.toAlgHom Qp LL LL').mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp M)) := by
  unfold PotCrysData.Dpcris Dcris
  rw [CJ.extS_iInf]
  simp only [CJ.extS_ker]
  exact CJ.map_iInf_ker _ _ _ (fun g x => CJ.comm_act (BdR := B) (M g) _ x)

theorem eig_ext (M : G →* Matrix (Fin k) (Fin k) LL) (I : Subgroup G) (a : I →* LLˣ) :
    (CJ.extS LL' (PC.Eig (CJ.rep M) I a)).map ((CJ.EE (Qp := Qp) (LL := LL) (LL' := LL') (k := k) B :
        _ ≃ₗ[LL'] _) : _ →ₗ[LL'] _)
      = PC.Eig (CJ.rep (((IsScalarTower.toAlgHom Qp LL LL').mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp M)) I
          ((Units.map (algebraMap LL LL' : LL →* LL')).comp a) := by
  unfold PotCrysData.Eig
  rw [CJ.extS_inf, CJ.map_inf_equiv, dpcris_ext, CJ.extS_iInf]
  simp only [CJ.extS_ker]
  congr 1
  exact CJ.map_iInf_ker _ _ _ (fun g x => comm_act_smul (M g) _ _ x)

end Tower

theorem orderOf_comp {I : Type} [Group I] (f : LL →+* LL') (a : I →* LLˣ) :
    orderOf ((Units.map (f : LL →* LL')).comp a) = orderOf a := by
  refine orderOf_eq_orderOf_iff.2 fun n => ?_
  simp only [MonoidHom.ext_iff, MonoidHom.pow_apply, MonoidHom.comp_apply, MonoidHom.one_apply]
  refine forall_congr' fun g => ?_
  rw [← map_pow]
  exact map_eq_one_iff _ (Units.map_injective f.injective)

theorem inertiaThrough_mat (f : LL →ₐ[Qp] LL') {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL)
    (Sig : Finset (PC.Iner →* LLˣ)) (hS : PC.InertiaThrough (CJ.rep M) Sig) :
    PC.InertiaThrough (CJ.rep ((f.mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp M))
      (mapSig f.toRingHom Sig) := by
  classical
  let _ : Algebra LL LL' := f.toRingHom.toAlgebra
  have _ : IsScalarTower Qp LL LL' := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  have hf : IsScalarTower.toAlgHom Qp LL LL' = f := AlgHom.ext fun _ => rfl
  have hm : ∀ c, c ∈ mapSig f.toRingHom Sig ↔
      ∃ a ∈ Sig, (Units.map (f.toRingHom : LL →* LL')).comp a = c := fun c => by
    unfold mapSig
    convert Finset.mem_image
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨fun c hc g hg => ?_, fun c hc => ?_, le_antisymm ?_ ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (hm c).1 hc
    rw [MonoidHom.comp_apply, h1 a ha g hg, map_one]
  · obtain ⟨a, ha, rfl⟩ := (hm c).1 hc
    rw [orderOf_comp]
    exact h2 a ha
  · have hD := dpcris_ext (LL' := LL') PC M
    rw [hf] at hD
    refine hD.symm.le.trans (Submodule.map_le_iff_le_comap.2 ?_)
    refine (extS_mono h3.le).trans ?_
    refine (extS_iSup_le _).trans (iSup_le fun a => (extS_iSup_le _).trans (iSup_le fun ha => ?_))
    refine Submodule.map_le_iff_le_comap.1 ?_
    have hE := eig_ext (LL' := LL') PC M PC.Iner a
    rw [hf] at hE
    refine hE.le.trans ?_
    exact le_iSup₂_of_le ((Units.map (f.toRingHom : LL →* LL')).comp a) ((hm _).2 ⟨a, ha, rfl⟩) le_rfl
  · exact iSup₂_le fun _ _ => inf_le_left

theorem inertiaThrough_basis (f : LL →ₐ[Qp] LL') {k : ℕ}
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (b : Module.Basis (Fin k) LL V)
    (Sig : Finset (PC.Iner →* LLˣ)) (hS : PC.InertiaThrough ρ Sig) :
    PC.InertiaThrough (CJ.rep ((f.mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp
          ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ)))
      (mapSig f.toRingHom Sig) := by
  refine inertiaThrough_mat _ f _ Sig ?_
  refine (GlobalTheory.HTW.Rec.potCrys_inertiaThrough_of_equiv _ b.equivFun.symm ?_).2 Sig hS
  intro g v
  apply b.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  change (LinearMap.toMatrix b b (ρ g)).mulVec v = _
  have := LinearMap.toMatrix_mulVec_repr b b (ρ g) (b.equivFun.symm v)
  rw [← Module.Basis.equivFun_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply] at this
  exact this

end Main

set_option maxHeartbeats 1000000 in

theorem main : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) (Sig : Finset ((pc Pl h hN hF hS).Iner →* (↥LL.1)ˣ)), (pc Pl h hN hF hS).InertiaThrough T.ρ Sig → (pc Pl h hN hF hS).InertiaThrough (extLat hL T b hb).ρ (mapSig (incl hL).toRingHom Sig) := by
  intro l _ Pl K' h hN hF hS LL LL' hL T k b hb Sig hI
  exact inertiaThrough_basis (pc Pl h hN hF hS) (incl hL) T.ρ b Sig hI

end GlobalTheory.BaseCoefIner
