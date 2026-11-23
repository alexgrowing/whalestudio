import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftEquivariance
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MapMemISupIsLinAt
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.ThetaTri
open scoped TensorProduct
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ThetaLoc Formalism.L2.Theta
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}
theorem eW_cast_symm_wt_rho_eq (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h' : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (γ : GA D (Vc D j))
    (hγ : γ ∈ GQ (Vc D j)) (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h' * A.a j)))
    (k : ℕ) (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m) (w : (P.M (D.nd.mu i) k p1 p2).wt.W) :
    (Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (P.M (D.nd.mu i) k p1 p2).wt.W) (fun _ _ => A.eW (D.nd.mu i) hμ j) hk p1 p2).symm
        ((P.M (D.nd.mu i) k p1 p2).wt.ρ h' w) =
      (X.R.cV j).ρ γ ((Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (P.M (D.nd.mu i) k p1 p2).wt.W) (fun _ _ => A.eW (D.nd.mu i) hμ j) hk p1 p2).symm w) := by
  subst hk
  apply (A.eW _ hμ j).injective
  simp only [LinearEquiv.apply_symm_apply]
  rw [A.wt _ hμ j h' γ hγ he]
  simp
theorem eWloc_symm_wt_rho_eq_cV_rho (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h' : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (γ : GA D (Vc D j))
    (hγ : γ ∈ GQ (Vc D j)) (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h' * A.a j)))
    (w : (P.M.loc i).wt.W) :
    (_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm ((P.M.loc i).wt.ρ h' w) = (X.R.cV j).ρ γ ((_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm w) :=
  _root_.GlobalTheory.ThetaTri.eW_cast_symm_wt_rho_eq A i j hμ h' γ hγ he (D.nd.j i) hj _ _ w
theorem formToVectorMap_rt_eq_mul_psi (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (hcv : (X.R.cV j).Is) (h : Formalism.AUTREP.GAf D.host.E D.R.nV)
    (F F' : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    (hF : (F' : Formalism.AUTREP.GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = NG.rt D.host.E D.R.nV h F)
    (x : GA D (Vc D j)) : _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F' x = _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F (x * (A.PV j).ψ h) := by
  show (X.R.cV j).ext _ x = (X.R.cV j).ext _ (x * (A.PV j).ψ h)
  rw [GlobalTheory.DefLiftHecke.ext_mul _ hcv _ ((A.PV j).into h) x]
  show (X.R.cV j).ρ x⁻¹ _ = _
  simp only [LinearMap.coe_mk, AddHom.coe_mk, preF_mul, hF, NG.rt, mul_assoc]
theorem formToVectorMap_mul_of_mem_GQ (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    (γ : GA D (Vc D j)) (hγ : γ ∈ GQ (Vc D j)) (x : GA D (Vc D j)) :
    _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F (γ * x) = _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F x := by
  obtain ⟨y, hy⟩ := fin_frame_surj (A.PV j) ((finHom (Vc D j)).rangeRestrict γ)
  obtain ⟨z, hz⟩ := fin_frame_surj (A.PV j) ((finHom (Vc D j)).rangeRestrict x)
  have hh' : A.a j * y * (A.a j)⁻¹ ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV := by
    refine (A.rat j _).2 ⟨γ, hγ, ?_⟩
    have : (A.a j)⁻¹ * (A.a j * y * (A.a j)⁻¹) * A.a j = y := by group
    rw [this]
    exact (congrArg Subtype.val hy).symm
  have he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ *
      ((⟨_, hh'⟩ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) : Formalism.AUTREP.GAf D.host.E D.R.nV) * A.a j)) := by
    have : (A.a j)⁻¹ * (A.a j * y * (A.a j)⁻¹) * A.a j = y := by group
    simp only [this]
    exact (congrArg Subtype.val hy).symm
  show (X.R.cV j).ρ (γ * x)⁻¹ ((_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm ((F : Formalism.AUTREP.GAf D.host.E D.R.nV → (P.M.loc i).wt.W)
      (A.a j * preF (A.PV j) ((finHom (Vc D j)).rangeRestrict (γ * x))))) =
    (X.R.cV j).ρ x⁻¹ ((_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm ((F : Formalism.AUTREP.GAf D.host.E D.R.nV → (P.M.loc i).wt.W)
      (A.a j * preF (A.PV j) ((finHom (Vc D j)).rangeRestrict x))))
  have hprod : (finHom (Vc D j)).rangeRestrict γ * (finHom (Vc D j)).rangeRestrict x =
      (finHom (Vc D j)).rangeRestrict ((A.PV j).ψ (y * z)) :=
    (congrArg₂ (· * ·) hy.symm hz.symm).trans
      ((map_mul (finHom (Vc D j)).rangeRestrict _ _).symm.trans
        (congrArg (finHom (Vc D j)).rangeRestrict (map_mul (A.PV j).ψ y z).symm))
  have key : preF (A.PV j) ((finHom (Vc D j)).rangeRestrict (γ * x)) = y * z :=
    (congrArg (preF (A.PV j)) ((map_mul (finHom (Vc D j)).rangeRestrict γ x).trans hprod)).trans (preF_frame _ _)
  have hz' : preF (A.PV j) ((finHom (Vc D j)).rangeRestrict x) = z :=
    (congrArg (preF (A.PV j)) hz.symm).trans (preF_frame _ _)
  rw [key, hz']
  have e1 : A.a j * (y * z) = (A.a j * y * (A.a j)⁻¹) * (A.a j * z) := by group
  rw [e1, F.2.1 ⟨_, hh'⟩ (A.a j * z), _root_.GlobalTheory.ThetaTri.eWloc_symm_wt_rho_eq_cV_rho A i j hj hμ ⟨_, hh'⟩ γ hγ he, _root_.mul_inv_rev,
    map_mul, Module.End.mul_apply, ← Module.End.mul_apply ((X.R.cV j).ρ γ⁻¹), ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]
theorem thetaEvaluationMap_apply {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (y : ↥Y.C) (x : GA D (Wc D j)) :
    _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y x = PiTensorProduct.lift (_root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y : Y.A)) (PiTensorProduct.map
      (fun τ => (lowT (X.R.MW j (sg0 D X.A)) τ).subtype) (kUnit (X.R.MW j (sg0 D X.A)))) x := rfl
theorem thetaEvaluationMap_rho_eq_mul_psi {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (g : Formalism.AUTREP.GAf D.host.E D.R.r) (y y' : ↥Y.C) (hy : (y' : Y.A) = Y.ρ g y) (x : GA D (Wc D j)) :
    _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y' x = _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y (x * (X.PW j).ψ g) := by
  have he : _root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y' : Y.A) = Formalism.IndefR.principalLevelFrame.actM (X.PW j) (X.R.MW j (sg0 D X.A)) g (_root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y : Y.A)) := by
    rw [hy]; exact (Classical.choose_spec (Classical.choose_spec hc)).2.2.2.1 g y
  rw [_root_.GlobalTheory.ThetaTri.thetaEvaluationMap_apply, _root_.GlobalTheory.ThetaTri.thetaEvaluationMap_apply, he, lift_actM]
theorem thetaEvaluationMap_mul_of_mem_GQ {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (y : ↥Y.C) (γ : GA D (Wc D j)) (hγ : γ ∈ GQ (Wc D j)) (x : GA D (Wc D j)) :
    _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y (γ * x) = _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y x := by
  have hm : _root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y : Y.A) ∈ LeftInvM (X.R.MW j (sg0 D X.A)) := by
    apply minf_le_leftInv X.R.θ (X.PW j)
    rw [← (Classical.choose_spec (Classical.choose_spec hc)).2.2.1]
    exact Submodule.mem_map_of_mem y.2
  rw [_root_.GlobalTheory.ThetaTri.thetaEvaluationMap_apply, _root_.GlobalTheory.ThetaTri.thetaEvaluationMap_apply]
  exact lift_left _ _ hm _ γ hγ x
theorem lamI_inv_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r) (φ : (X.R.cV j).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) → ℂ)), φ ∈ _root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ → ∀ (F F' : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) (y y' : ↥Y.C), (F' : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = NG.rt D.host.E D.R.nV h F → (y' : Y.A) = Y.ρ g y → _root_.GlobalTheory.ThetaTri.canonicalPairingValue A i j hj hc hμ (GlobalTheory.ThetaTri.valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) (h, g) φ) F' y' = _root_.GlobalTheory.ThetaTri.canonicalPairingValue A i j hj hc hμ φ F y := by
  intro hL D P X A i j hj Y hc hμ h g φ hφ F F' y y' hF hy
  have hcore := X.given.core
  have hW := hcore.thP.ωP j (X.tupT (D.nd.mu i))
  have hcv : (X.R.cV j).Is := hcore.models.cV j
  have hth : ∀ v, IsThetaFunO X.R.ψ (Vc D j) (Wc D j) (φ v) := by
    intro v
    have := (hφ 1).1 v
    simpa [valAct1_apply] using this
  have hV := hcore.models.νV j (X.tupT (D.nd.mu i))
  have hWm := hcore.models.νW j
  haveI : (X.R.νV j (X.tupT (D.nd.mu i))).IsHaarMeasure := hV.1.1
  haveI : (X.R.νV j (X.tupT (D.nd.mu i))).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hV.1.1
  haveI : (X.R.νW j).IsHaarMeasure := hWm.1.1
  haveI : (X.R.νW j).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hWm.1.1
  haveI : Countable (GQ (Vc D j)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Vc D j).gram
  haveI : Countable (GQ (Wc D j)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Wc D j).gram
  have inner : ∀ g₀, thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (X.R.νV j (X.tupT (D.nd.mu i)))
      (X.R.fdV j (X.tupT (D.nd.mu i))) (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) (h, g) φ) F' g₀ =
      thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (X.R.νV j (X.tupT (D.nd.mu i)))
      (X.R.fdV j (X.tupT (D.nd.mu i))) φ F (g₀ * (X.PW j).ψ g) := by
    intro g₀
    unfold thIn
    have e1 : ∀ h₀, thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) h₀ g₀
        (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) (h, g) φ (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F' h₀)) =
        thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) (h₀ * (A.PV j).ψ h) (g₀ * (X.PW j).ψ g)
          (φ (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F (h₀ * (A.PV j).ψ h))) := by
      intro h₀
      rw [valAct1_apply, _root_.GlobalTheory.ThetaTri.formToVectorMap_rt_eq_mul_psi A i j hj hμ hcv h F F' hF h₀]
      exact thetaKO_act _ _ _ _ _
    simp only [e1]
    refine (Formalism.IndefR.Eqv.rightInv_holds _ (GQ (Vc D j)) _ _ hV.2
      (fun h₁ => thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) h₁ (g₀ * (X.PW j).ψ g) (φ (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h₁))) ?_ _).2
    intro γ hγ h₁
    rw [_root_.GlobalTheory.ThetaTri.formToVectorMap_mul_of_mem_GQ A i j hj hμ F γ hγ h₁]
    have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hW _ (hth (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h₁))).1 γ hγ 1
      (one_mem _) h₁ (g₀ * (X.PW j).ψ g)
    rwa [one_mul] at this
  unfold _root_.GlobalTheory.ThetaTri.canonicalPairingValue lamV
  congr 1
  have e2 : ∀ g₀, star (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y' g₀) * thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ)
      (X.R.νV j (X.tupT (D.nd.mu i))) (X.R.fdV j (X.tupT (D.nd.mu i)))
      (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) (h, g) φ) F' g₀ =
      star (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y (g₀ * (X.PW j).ψ g)) * thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ)
      (X.R.νV j (X.tupT (D.nd.mu i))) (X.R.fdV j (X.tupT (D.nd.mu i))) φ F (g₀ * (X.PW j).ψ g) := by
    intro g₀
    rw [inner, _root_.GlobalTheory.ThetaTri.thetaEvaluationMap_rho_eq_mul_psi hc g y y' hy]
  simp only [e2]
  refine (Formalism.IndefR.Eqv.rightInv_holds _ (GQ (Wc D j)) _ _ hWm.2
    (fun g₁ => star (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y g₁) * thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ)
      (X.R.νV j (X.tupT (D.nd.mu i))) (X.R.fdV j (X.tupT (D.nd.mu i))) φ F g₁) ?_ _).2
  intro γ hγ g₁
  rw [_root_.GlobalTheory.ThetaTri.thetaEvaluationMap_mul_of_mem_GQ hc y γ hγ g₁]
  congr 1
  unfold thIn
  congr 1
  funext h₁
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hW _ (hth (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h₁))).1 1 (one_mem _) γ hγ
    h₁ g₁
  rwa [one_mul] at this
end GlobalTheory.ThetaTri
end
end
