import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalCongruenceLevelContained
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.ThetaFormV

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.ThetaTri
open scoped Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Frame

variable {D : D7} {V : HSp D} {n : ℕ}

theorem fin_preF (PV : principalLevelFrame.RowPsi V n) (k : Bridge.Gf V) :
    (finHom V).rangeRestrict (PV.ψ (preF PV k)) = k := by
  have hex : ∃ κ, (finHom V).rangeRestrict (PV.ψ κ) = k := by
    obtain ⟨κ, hκ, e⟩ := Formalism.IndefR.Eqv.Act.exists_finLift V k
    obtain ⟨h, rfl⟩ := PV.onto κ hκ
    exact ⟨h, Subtype.ext e⟩
  unfold preF
  rw [dif_pos hex]
  exact hex.choose_spec

theorem preF_fin (PV : principalLevelFrame.RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n) :
    preF PV ((finHom V).rangeRestrict (PV.ψ x)) = x := by
  apply PV.inj
  have e1 : finHom V (PV.ψ (preF PV ((finHom V).rangeRestrict (PV.ψ x)))) = finHom V (PV.ψ x) :=
    congrArg Subtype.val (fin_preF PV _)
  refine inv_mul_eq_one.1 (GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V
    ((GfC V).mul_mem ((GfC V).inv_mem (PV.into _)) (PV.into _)) ?_)
  show finHom V _ = 1
  rw [map_mul, map_inv, e1, inv_mul_cancel]

theorem preF_mul (PV : principalLevelFrame.RowPsi V n) (k₁ k₂ : Bridge.Gf V) :
    preF PV (k₁ * k₂) = preF PV k₁ * preF PV k₂ := by
  have h := preF_fin PV (preF PV k₁ * preF PV k₂)
  rwa [map_mul, map_mul, fin_preF, fin_preF] at h

theorem ext_apply (c : CoefA V) (f : Bridge.Gf V → c.W) (h : GA D V) :
    c.ext f h = c.ρ h⁻¹ (f ((finHom V).rangeRestrict h)) := rfl

theorem mem_adForms_one (c : CoefA V) (f : Bridge.Gf V → c.W)
    (hf : ∀ γ ∈ GQ V, ∀ k, f ((finHom V).rangeRestrict γ * k) = c.ρ γ (f k))
    (J : Subgroup (Bridge.Gf V)) (hJ : ∀ q ∈ J, ∀ k, f (k * q) = f k) :
    f ∈ Bridge.AdForms ((finHom V).rangeRestrict.comp (GQ V).subtype) (c.ρ.comp (GQ V).subtype) J 1 := by
  intro γ h k
  have e1 := hJ k k.2 ((finHom V).rangeRestrict (γ : GA D V) * h)
  have e2 := hf γ γ.2 h
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, MonoidHom.comp_apply, Subgroup.coe_subtype]
  exact e1.trans e2

end Frame

section Forms

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}

theorem eW_cast_wt (A : GlobalTheory.NJoin.Agree X P.M P.rep) {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ)
    (j : Fin D.R.m) (k : ℕ) (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m)
    (h : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) {γ : GA D (Vc D j)} (hγ : γ ∈ GQ (Vc D j))
    (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h * A.a j))) (v : (X.R.cV j).W) :
    (Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (P.M μ k p1 p2).wt.W) (fun _ _ => A.eW μ hμ j) hk p1 p2) ((X.R.cV j).ρ γ v) =
      (P.M μ k p1 p2).wt.ρ h ((Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (P.M μ k p1 p2).wt.W) (fun _ _ => A.eW μ hμ j) hk p1 p2) v) := by
  subst hk
  exact A.wt μ hμ j h γ hγ he v

theorem eWloc_wt (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) {γ : GA D (Vc D j)}
    (hγ : γ ∈ GQ (Vc D j))
    (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h * A.a j))) (v : (X.R.cV j).W) :
    eWloc A i j hj hμ ((X.R.cV j).ρ γ v) = (P.M.loc i).wt.ρ h (eWloc A i j hj hμ v) :=
  eW_cast_wt A hμ j _ hj _ _ h hγ he v

end Forms

section Main

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}

def fFin (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) :
    Bridge.Gf (Vc D j) → (X.R.cV j).W :=
  fun k => (eWloc A i j hj hμ).symm ((F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) (A.a j * preF (A.PV j) k))

theorem fFin_apply (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    (k : Bridge.Gf (Vc D j)) : fFin A i j hj hμ F k =
      (eWloc A i j hj hμ).symm ((F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) (A.a j * preF (A.PV j) k)) := rfl

theorem fV_eq_ext (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) :
    fV A i j hj hμ F = (X.R.cV j).ext (fFin A i j hj hμ F) := rfl

theorem fFin_rat (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    {γ : GA D (Vc D j)} (hγ : γ ∈ GQ (Vc D j)) (k : Bridge.Gf (Vc D j)) :
    fFin A i j hj hμ F ((finHom (Vc D j)).rangeRestrict γ * k) = (X.R.cV j).ρ γ (fFin A i j hj hμ F k) := by
  set x := preF (A.PV j) ((finHom (Vc D j)).rangeRestrict γ) with hxdef
  have hx : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ x) :=
    (congrArg Subtype.val (GlobalTheory.ThetaFormV.fin_preF (A.PV j) ((finHom (Vc D j)).rangeRestrict γ))).symm
  have e0 : (A.a j)⁻¹ * (A.a j * x * (A.a j)⁻¹) * A.a j = x := by group
  have hrat : A.a j * x * (A.a j)⁻¹ ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV :=
    (A.rat j _).2 ⟨γ, hγ, by rw [e0]; exact hx⟩
  have he : finHom (Vc D j) γ =
      finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * ((⟨_, hrat⟩ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) : GAf D.host.E D.R.nV) * A.a j)) := by
    rw [e0]; exact hx
  have e1 : A.a j * preF (A.PV j) ((finHom (Vc D j)).rangeRestrict γ * k) =
      (A.a j * x * (A.a j)⁻¹) * (A.a j * preF (A.PV j) k) := by
    rw [GlobalTheory.ThetaFormV.preF_mul, ← hxdef]; group
  have hF := F.2.1 ⟨_, hrat⟩ (A.a j * preF (A.PV j) k)
  unfold fFin
  rw [e1]
  refine (LinearEquiv.symm_apply_eq _).2 ?_
  rw [eWloc_wt A i j hj hμ ⟨_, hrat⟩ hγ he, LinearEquiv.apply_symm_apply]
  exact hF

theorem fV_invariant (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) :
    ∀ γ ∈ GQ (Vc D j), ∀ h, fV A i j hj hμ F (γ * h) = fV A i j hj hμ F h := by
  intro γ hγ h
  rw [fV_eq_ext, GlobalTheory.ThetaFormV.ext_apply, GlobalTheory.ThetaFormV.ext_apply, map_mul, fFin_rat A i j hj hμ F hγ]
  have e : (X.R.cV j).ρ (γ * h)⁻¹ * (X.R.cV j).ρ γ = (X.R.cV j).ρ h⁻¹ := by
    rw [← map_mul]; congr 1; group
  exact congrArg (fun T : Module.End ℂ (X.R.cV j).W => T _) e

end Main

theorem eventually_cong_preF {D : D7} {V : HSp D} {n : ℕ} (PV : principalLevelFrame.RowPsi V n)
    (hF : D.host.F = maximalRealSubfield D.host.E) (hstd : GlobalTheory.NJoin.StdFrame hF PV) {N : ℕ} (hN : 0 < N) :
    ∀ᶠ κ in 𝓝 (1 : GA D V), NG.Cong D.host.E n N (preF PV ((finHom V).rangeRestrict κ)) := by
  obtain ⟨N', hN', himg⟩ := GlobalTheory.LatCongImage.finCong_mem_levN D V n PV hF hstd N hN
  filter_upwards [GlobalTheory.Member.PrincLevel.finCong_mem_nhds V hN'] with κ hκ
  obtain ⟨κ', hκ', e⟩ := Formalism.IndefR.Eqv.Act.exists_finLift V ((finHom V).rangeRestrict κ)
  have hc : GlobalTheory.Member.FinCong V N' κ' := by
    intro z hz
    have e' : finHom V κ' = finHom V κ := e
    rw [e']
    exact hκ z hz
  obtain ⟨x, hx, hxe⟩ := himg κ' hκ' hc
  have e2 : (finHom V).rangeRestrict κ = (finHom V).rangeRestrict (PV.ψ x) := by
    rw [hxe]; exact (Subtype.ext e).symm
  rw [e2, GlobalTheory.ThetaFormV.preF_fin]
  exact hx

section Cont

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}

theorem fV_continuous (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) :
    Continuous (fV A i j hj hμ F) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D (Vc D j)) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Vc D j).gram))
  obtain ⟨N, hN, hlev⟩ := F.2.2
  let J : Subgroup (Bridge.Gf (Vc D j)) :=
    { carrier := {q | ∀ k, fFin A i j hj hμ F (k * q) = fFin A i j hj hμ F k}
      mul_mem' := fun {a b} ha hb k => by simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [← mul_assoc, hb, ha]
      one_mem' := fun k => by rw [mul_one]
      inv_mem' := fun {a} ha k => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [← ha (k * a⁻¹), inv_mul_cancel_right] }
  have hfJ : fFin A i j hj hμ F ∈ Bridge.AdForms ((finHom (Vc D j)).rangeRestrict.comp (GQ (Vc D j)).subtype)
      ((X.R.cV j).ρ.comp (GQ (Vc D j)).subtype) J 1 := by
    exact GlobalTheory.ThetaFormV.mem_adForms_one _ _ (fun γ hγ k => fFin_rat A i j hj hμ F hγ k) J (fun q hq => hq)
  have hJ : ∀ᶠ κ in 𝓝 (1 : GA D (Vc D j)), ∃ h : (finHom (Vc D j)).rangeRestrict κ ∈ J,
      (1 : J →* ℂˣ) ⟨_, h⟩ = 1 := by
    filter_upwards [eventually_cong_preF (A.PV j) A.hF (A.stdV j) hN] with κ hκ
    refine ⟨fun k => ?_, rfl⟩
    show fFin A i j hj hμ F (k * (finHom (Vc D j)).rangeRestrict κ) = fFin A i j hj hμ F k
    rw [fFin_apply, fFin_apply, GlobalTheory.ThetaFormV.preF_mul, ← mul_assoc, hlev _ hκ]
  exact (GlobalTheory.ThetaIntegrand.form_continuous (finHom (Vc D j)).rangeRestrict (GQ (Vc D j)) (X.R.cV j).ρ
    ((X.given.core.models.cV j).2.2.1) hJ hfJ).congr fun g => (GlobalTheory.ThetaFormV.ext_apply _ _ _).symm

end Cont

theorem fV_continuous_invariant : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp)
    (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)),
    Continuous (GlobalTheory.ThetaTri.fV A i j hj hμ F) ∧
      ∀ γ ∈ GQ (Vc D j), ∀ h, GlobalTheory.ThetaTri.fV A i j hj hμ F (γ * h) = GlobalTheory.ThetaTri.fV A i j hj hμ F h :=
  fun _ _ _ _ A i j hj hμ F => ⟨fV_continuous A i j hj hμ F, fV_invariant A i j hj hμ F⟩

end GlobalTheory.ThetaFormV

end
