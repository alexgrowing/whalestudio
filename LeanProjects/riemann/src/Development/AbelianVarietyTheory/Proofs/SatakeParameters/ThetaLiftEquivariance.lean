import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RightInv
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ThetaTri
open scoped TensorProduct
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ThetaLoc Formalism.L2.Theta

theorem thetaKO_act {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
    (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
    (h' : Formalism.L2.Theta.GA D V) (g' : Formalism.L2.Theta.GA D W) (p : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W)
    (f : WO V W → ℂ) : thetaKO om h' g' (om p f) = thetaKO om (h' * p.1) (g' * p.2) f := by
  simp only [thetaKO]
  rw [← Module.End.mul_apply, ← map_mul]
  rfl

theorem fin_frame_surj {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n)
    (k : ↥(Formalism.IndefR.Bridge.Gf V)) : ∃ y, (Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ y) = k := by
  obtain ⟨g, hg, rfl⟩ := GlobalTheory.SplitHeckeAdj.fin_lift V k
  obtain ⟨y, rfl⟩ := PV.onto g hg
  exact ⟨y, rfl⟩

theorem preF_frame {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n)
    (y : Formalism.AUTREP.GAf D.host.E n) : preF PV ((Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ y)) = y := by
  classical
  have h : ∃ x, (Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ x) = (Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ y) :=
    ⟨y, rfl⟩
  unfold preF
  rw [dif_pos h]
  exact PV.inj (GlobalTheory.SplitHeckeAdj.fin_inj V (PV.into _) (PV.into _) h.choose_spec)

theorem preF_mul {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n)
    (k : ↥(Formalism.IndefR.Bridge.Gf V)) (y : Formalism.AUTREP.GAf D.host.E n) :
    preF PV (k * (Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ y)) = preF PV k * y := by
  obtain ⟨z, rfl⟩ := fin_frame_surj PV k
  rw [← map_mul, ← map_mul, preF_frame, preF_frame]

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}

theorem eW_cast_symm_wt (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m)
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

theorem eWloc_symm_wt (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h' : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (γ : GA D (Vc D j))
    (hγ : γ ∈ GQ (Vc D j)) (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h' * A.a j)))
    (w : (P.M.loc i).wt.W) :
    (eWloc A i j hj hμ).symm ((P.M.loc i).wt.ρ h' w) = (X.R.cV j).ρ γ ((eWloc A i j hj hμ).symm w) :=
  eW_cast_symm_wt A i j hμ h' γ hγ he (D.nd.j i) hj _ _ w

theorem fV_rt (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (hcv : (X.R.cV j).Is) (h : Formalism.AUTREP.GAf D.host.E D.R.nV)
    (F F' : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    (hF : (F' : Formalism.AUTREP.GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = NG.rt D.host.E D.R.nV h F)
    (x : GA D (Vc D j)) : fV A i j hj hμ F' x = fV A i j hj hμ F (x * (A.PV j).ψ h) := by
  show (X.R.cV j).ext _ x = (X.R.cV j).ext _ (x * (A.PV j).ψ h)
  rw [GlobalTheory.DefLiftHecke.ext_mul _ hcv _ ((A.PV j).into h) x]
  show (X.R.cV j).ρ x⁻¹ _ = _
  simp only [LinearMap.coe_mk, AddHom.coe_mk, preF_mul, hF, NG.rt, mul_assoc]

theorem fV_rat (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    (γ : GA D (Vc D j)) (hγ : γ ∈ GQ (Vc D j)) (x : GA D (Vc D j)) :
    fV A i j hj hμ F (γ * x) = fV A i j hj hμ F x := by
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
  show (X.R.cV j).ρ (γ * x)⁻¹ ((eWloc A i j hj hμ).symm ((F : Formalism.AUTREP.GAf D.host.E D.R.nV → (P.M.loc i).wt.W)
      (A.a j * preF (A.PV j) ((finHom (Vc D j)).rangeRestrict (γ * x))))) =
    (X.R.cV j).ρ x⁻¹ ((eWloc A i j hj hμ).symm ((F : Formalism.AUTREP.GAf D.host.E D.R.nV → (P.M.loc i).wt.W)
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
  rw [e1, F.2.1 ⟨_, hh'⟩ (A.a j * z), eWloc_symm_wt A i j hj hμ ⟨_, hh'⟩ γ hγ he, _root_.mul_inv_rev,
    map_mul, Module.End.mul_apply, ← Module.End.mul_apply ((X.R.cV j).ρ γ⁻¹), ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]

theorem lift_actM {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (PW : Formalism.IndefR.principalLevelFrame.RowPsi V n) (M : Formalism.IndefR.Mult.DSModel V Sp) (g : Formalism.AUTREP.GAf D.host.E n)
    (T : Formalism.IndefR.Mult.MMap M) (u : PiTensorProduct ℂ fun τ => ↥(M.sm τ)) (x : GA D V) :
    PiTensorProduct.lift (Formalism.IndefR.principalLevelFrame.actM PW M g T) u x = PiTensorProduct.lift T u (x * PW.ψ g) := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod r f => simp [PiTensorProduct.lift.tprod, Formalism.IndefR.principalLevelFrame.actM_apply]
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

theorem lift_left {V : Formalism.BasicNotions.TH.HSp D} {Sp : D.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (M : Formalism.IndefR.Mult.DSModel V Sp) (T : Formalism.IndefR.Mult.MMap M)
    (hT : ∀ v, ∀ γ ∈ GQ V, ∀ x, T v (γ * x) = T v x) (u : PiTensorProduct ℂ fun τ => ↥(M.sm τ))
    (γ : GA D V) (hγ : γ ∈ GQ V) (x : GA D V) :
    PiTensorProduct.lift T u (γ * x) = PiTensorProduct.lift T u x := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod r f => simp [PiTensorProduct.lift.tprod, hT f γ hγ x]
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

def LeftInvM {V : Formalism.BasicNotions.TH.HSp D} {Sp : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : Formalism.IndefR.Mult.DSModel V Sp) :
    Submodule ℂ (Formalism.IndefR.Mult.MMap M) where
  carrier := {T | ∀ v, ∀ γ ∈ GQ V, ∀ x, T v (γ * x) = T v x}
  add_mem' := by
    intro T T' hT hT' v γ hγ x
    simp only [MultilinearMap.add_apply, Pi.add_apply, hT v γ hγ x, hT' v γ hγ x]
  zero_mem' := by intro v γ hγ x; rfl
  smul_mem' := by
    intro c T hT v γ hγ x
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, hT v γ hγ x]

theorem minf_le_leftInv {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (PW : Formalism.IndefR.principalLevelFrame.RowPsi V n) (M : Formalism.IndefR.Mult.DSModel V Sp) :
    Formalism.IndefR.principalLevelFrame.Minf θ PW M ≤ LeftInvM M := by
  refine iSup_le fun N => Submodule.span_le.2 fun T hT v γ hγ x => ?_
  exact (hT.aut v).left γ hγ x

theorem yv_apply {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (y : ↥Y.C) (x : GA D (Wc D j)) :
    yv hc y x = PiTensorProduct.lift (eC hc (y : Y.A)) (PiTensorProduct.map
      (fun τ => (lowT (X.R.MW j (sg0 D X.A)) τ).subtype) (kUnit (X.R.MW j (sg0 D X.A)))) x := rfl

theorem yv_rt {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (g : Formalism.AUTREP.GAf D.host.E D.R.r) (y y' : ↥Y.C) (hy : (y' : Y.A) = Y.ρ g y) (x : GA D (Wc D j)) :
    yv hc y' x = yv hc y (x * (X.PW j).ψ g) := by
  have he : eC hc (y' : Y.A) = Formalism.IndefR.principalLevelFrame.actM (X.PW j) (X.R.MW j (sg0 D X.A)) g (eC hc (y : Y.A)) := by
    rw [hy]; exact (Classical.choose_spec (Classical.choose_spec hc)).2.2.2.1 g y
  rw [yv_apply, yv_apply, he, lift_actM]

theorem yv_rat {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (y : ↥Y.C) (γ : GA D (Wc D j)) (hγ : γ ∈ GQ (Wc D j)) (x : GA D (Wc D j)) :
    yv hc y (γ * x) = yv hc y x := by
  have hm : eC hc (y : Y.A) ∈ LeftInvM (X.R.MW j (sg0 D X.A)) := by
    apply minf_le_leftInv X.R.θ (X.PW j)
    rw [← (Classical.choose_spec (Classical.choose_spec hc)).2.2.1]
    exact Submodule.mem_map_of_mem y.2
  rw [yv_apply, yv_apply]
  exact lift_left _ _ hm _ γ hγ x

theorem lamI_inv : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r) (φ : (X.R.cV j).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) → ℂ)), φ ∈ GlobalTheory.ThetaTri.OmI A i j hj hc hμ → ∀ (F F' : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) (y y' : ↥Y.C), (F' : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = NG.rt D.host.E D.R.nV h F → (y' : Y.A) = Y.ρ g y → GlobalTheory.ThetaTri.lamI A i j hj hc hμ (GlobalTheory.ThetaTri.valAct1 (GlobalTheory.ThetaTri.omStd A j (X.tupT (D.nd.mu i))) (h, g) φ) F' y' = GlobalTheory.ThetaTri.lamI A i j hj hc hμ φ F y := by
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
  have inner : ∀ g₀, thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (fV A i j hj hμ) (X.R.νV j (X.tupT (D.nd.mu i)))
      (X.R.fdV j (X.tupT (D.nd.mu i))) (valAct1 (omStd A j (X.tupT (D.nd.mu i))) (h, g) φ) F' g₀ =
      thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (fV A i j hj hμ) (X.R.νV j (X.tupT (D.nd.mu i)))
      (X.R.fdV j (X.tupT (D.nd.mu i))) φ F (g₀ * (X.PW j).ψ g) := by
    intro g₀
    unfold thIn
    have e1 : ∀ h₀, thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) h₀ g₀
        (valAct1 (omStd A j (X.tupT (D.nd.mu i))) (h, g) φ (fV A i j hj hμ F' h₀)) =
        thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) (h₀ * (A.PV j).ψ h) (g₀ * (X.PW j).ψ g)
          (φ (fV A i j hj hμ F (h₀ * (A.PV j).ψ h))) := by
      intro h₀
      rw [valAct1_apply, fV_rt A i j hj hμ hcv h F F' hF h₀]
      exact thetaKO_act _ _ _ _ _
    simp only [e1]
    refine (Formalism.IndefR.Eqv.rightInv_holds _ (GQ (Vc D j)) _ _ hV.2
      (fun h₁ => thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) h₁ (g₀ * (X.PW j).ψ g) (φ (fV A i j hj hμ F h₁))) ?_ _).2
    intro γ hγ h₁
    rw [fV_rat A i j hj hμ F γ hγ h₁]
    have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hW _ (hth (fV A i j hj hμ F h₁))).1 γ hγ 1
      (one_mem _) h₁ (g₀ * (X.PW j).ψ g)
    rwa [one_mul] at this
  unfold lamI lamV
  congr 1
  have e2 : ∀ g₀, star (yv hc y' g₀) * thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (fV A i j hj hμ)
      (X.R.νV j (X.tupT (D.nd.mu i))) (X.R.fdV j (X.tupT (D.nd.mu i)))
      (valAct1 (omStd A j (X.tupT (D.nd.mu i))) (h, g) φ) F' g₀ =
      star (yv hc y (g₀ * (X.PW j).ψ g)) * thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (fV A i j hj hμ)
      (X.R.νV j (X.tupT (D.nd.mu i))) (X.R.fdV j (X.tupT (D.nd.mu i))) φ F (g₀ * (X.PW j).ψ g) := by
    intro g₀
    rw [inner, yv_rt hc g y y' hy]
  simp only [e2]
  refine (Formalism.IndefR.Eqv.rightInv_holds _ (GQ (Wc D j)) _ _ hWm.2
    (fun g₁ => star (yv hc y g₁) * thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (fV A i j hj hμ)
      (X.R.νV j (X.tupT (D.nd.mu i))) (X.R.fdV j (X.tupT (D.nd.mu i))) φ F g₁) ?_ _).2
  intro γ hγ g₁
  rw [yv_rat hc y γ hγ g₁]
  congr 1
  unfold thIn
  congr 1
  funext h₁
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hW _ (hth (fV A i j hj hμ F h₁))).1 1 (one_mem _) γ hγ
    h₁ g₁
  rwa [one_mul] at this

end GlobalTheory.ThetaTri

end
