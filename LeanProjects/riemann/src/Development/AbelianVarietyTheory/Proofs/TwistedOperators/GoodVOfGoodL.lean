import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActEqTranslateLiftV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointIntertwines
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelFormOrthogonalKilledByThetaMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
open Formalism.IndefR.CxPass Formalism.IndefR.CxPass.LevelOperators

namespace GlobalTheory.GoodModelVec

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 4000000 in

theorem actL_coord (R : RealDat D A Ks) (hr : R.grp_red_L) (hj : R.models_jV) (i : Fin D.R.m) (hc : (R.cV i).Is) (t : T0)
    (g : G) (x : (A.fam.L i t).S.Forms) (ℓ : (R.cV i).W →ₗ[ℂ] ℂ) :
    actL (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (fun h => ℓ (R.extV i t (R.jV i t x) h)) =
      fun h => ℓ (R.extV i t (R.jV i t ((A.fam.L i t).r g x)) h) := by
  have hT := GlobalTheory.RationalFormsAction.isTranslate_act_V R hr hj i t g x
  have hk : ∃ κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ := by
    obtain ⟨κ, h1, -⟩ := GlobalTheory.LiftEquivariance.exists_adelic_lift hT
    exact ⟨κ, h1⟩
  funext h
  refine (GlobalTheory.SecLift.actL_apply hk _ h).trans ?_
  have hs := hk.choose_spec
  have e1 := finE_eq (Vc D i) hk.choose
  have hq : (finHom (Vc D i)).rangeRestrict hk.choose ∈ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := by
    show Formalism.UG.bc (swapAE D) (finHom (Vc D i) hk.choose) ∈ lev _ _ _ _
    rw [← e1]
    exact ⟨hs.2.1, Subgroup.mem_top _⟩
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.LiftsTo (Vc D i) (R.βV i) (R.datVt i t) ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩ (R.eG g) := by
    show rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) (finHom (Vc D i) hk.choose)) = R.eG g
    rw [← e1]; exact hs.2.2
  have hT2 : ∀ u, (R.HV i t).e ((R.jV i t) (((A.fam.L i t).r g) x)) u =
      ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩)⁻¹ : ℂˣ) : ℂ) •
        (R.HV i t).e ((R.jV i t) x) (u * (finHom (Vc D i)).rangeRestrict hk.choose) := hT.2 _ hl
  have h2 := GlobalTheory.SecLift.coord_translate (R.cV i) hc hs.1 _ hT2 ℓ h
  have ec := GlobalTheory.LiftEquivariance.ch_eq (V := Vc D i) (β := R.βV i) (L := R.datVt i t) ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩
  have e2 : levFn (R.βV i) (flagL (R.datVt i t)) (Formalism.UG.bc (swapAE D) ((finHom (Vc D i)) hk.choose)) =
      levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) hk.choose) := by rw [e1]
  have hc' : ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩ : ℂˣ)) : ℂ) =
      levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) hk.choose := congrArg Units.val (ec.trans e2)
  rw [Units.val_inv_eq_inv_val, hc'] at h2
  exact h2.symm

set_option maxHeartbeats 4000000 in

theorem goodV_of_fix (R : RealDat D A Ks) (hr : R.grp_red_L) (hj : R.models_jV) (i : Fin D.R.m) (hc : (R.cV i).Is)
    (x : (A.fam.L i A.μ0).S.Forms) (hx : opF (A.fam.L i A.μ0).r (idemOf A.X) x = x) :
    GlobalTheory.LiftRows.GoodV R i (R.jV i A.μ0 x) := by
  intro ℓ
  let Φ : (R.HV i A.μ0).H →ₗ[ℂ] (GA D (Vc D i) → ℂ) := ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i A.μ0
  have hΦ : ∀ y, Φ y = fun h => ℓ (R.extV i A.μ0 y h) := fun _ => rfl
  have key : ∀ g, Φ (R.jV i A.μ0 ((A.fam.L i A.μ0).r g x)) =
      actL (Vc D i) (R.βV i) (R.datVt i A.μ0) (R.eG g) (Φ (R.jV i A.μ0 x)) := fun g =>
    (actL_coord R hr hj i hc A.μ0 g x ℓ).symm
  have hs : ∀ a, RealDat.eC (A := A) (sg0 D A) a = D.what₂.embLL ((idemOf A.X).coeff a) := fun a => by
    show sg0 D A _ = _
    rw [sg0, sgAt_mk D.what₂.embLL R.hv0]
  have e1 : Φ (R.jV i A.μ0 (opF (A.fam.L i A.μ0).r (idemOf A.X) x)) =
      gaL (Vc D i) (R.βV i) (R.datVt i A.μ0) R.eG (RealDat.eC (A := A) (sg0 D A)) (Φ (R.jV i A.μ0 x)) := by
    simp only [opF, gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, LinearMap.map_smulₛₗ, key, hs, RingHom.id_apply]
    rfl
  rw [← hΦ, ← e1, hx]

noncomputable def goodSub (R : RealDat D A Ks) (i : Fin D.R.m) : Submodule ℂ (R.HV i A.μ0).H :=
  ⨅ ℓ : (R.cV i).W →ₗ[ℂ] ℂ, LinearMap.ker
    (gaL (Vc D i) (R.βV i) (R.datVt i A.μ0) R.eG (RealDat.eC (A := A) (sg0 D A)) ∘ₗ (ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i A.μ0) -
      ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i A.μ0)

theorem mem_goodSub (R : RealDat D A Ks) (i : Fin D.R.m) (y : (R.HV i A.μ0).H) :
    y ∈ goodSub R i ↔ GlobalTheory.LiftRows.GoodV R i y := by
  simp only [goodSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

end GlobalTheory.GoodModelVec

open GlobalTheory.GoodModelVec in
set_option maxHeartbeats 4000000 in

theorem GlobalTheory.goodV_of_goodL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ (j : Fin D.R.m) (y : (R.toCx3 F).FLC j A3.A.fam.μ0), y ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j → GoodV R.toRealDat j (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hC _ _ _ j y hy
  have hM := hC.base.models
  have hr := hC.base.grp.red_L
  have hfix : ∀ x ∈ BlockGood.goodR (A3.fam3.F.L j A3.A.fam.μ0) (A3.fam3.F.lvlA F.P0 F.ψ0),
      opF (A3.A.fam.L j A3.A.fam.μ0).r (idemOf A3.A.X) x = x := by
    intro x hx
    rw [goodR_eq] at hx
    obtain ⟨z, rfl⟩ := hx
    have hid := opF_goodAt_idem (A3.A.fam.L j A3.A.fam.μ0).r A3.A.X hok.ok2.irr ⊥ 1
    rw [goodAt_bot] at hid
    show opF _ (idemOf A3.A.X) (opF _ (idemOf A3.A.X * lvlIdem F.P0 F.ψ0⁻¹) z) = opF _ (idemOf A3.A.X * lvlIdem F.P0 F.ψ0⁻¹) z
    rw [opF_mul, LinearMap.comp_apply]
    exact LinearMap.congr_fun hid _
  have hy' : y ∈ Submodule.span ℂ ((R.toCx3 F).jL j A3.A.fam.μ0 ''
      (BlockGood.goodR (A3.fam3.F.L j A3.A.fam.μ0) (A3.fam3.F.lvlA F.P0 F.ψ0) : Set _)) := hy
  rw [← mem_goodSub]
  clear hy
  induction hy' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    exact (mem_goodSub _ _ _).2 (goodV_of_fix R.toRealDat hr hM.jV j (hM.cV j) x (hfix x hx))
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ (Links.cj (twAt D.what₂.embLL A3.A.v0) c) ha
