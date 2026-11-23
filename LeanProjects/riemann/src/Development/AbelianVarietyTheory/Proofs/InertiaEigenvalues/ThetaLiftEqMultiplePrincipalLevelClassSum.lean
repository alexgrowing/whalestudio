import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThFEqIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEqClassSumThetaKernelsLowestKType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVectorEqUnitMulCentralTranslateLiftVectorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVecExistsUnique
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorTorusAction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LiftClassSumPrinc

theorem isReps_mul_central {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) (J : Subgroup G) {I : Type} (y : I → G)
    {z : G} (hz : z ∈ Subgroup.center G) (hy : Bridge.IsReps ι J y) : Bridge.IsReps ι J fun i => y i * z := by
  have hc : ∀ a : G, a * z = z * a := fun a => ((Subgroup.mem_center_iff.1 hz) a)
  intro h
  obtain ⟨i, ⟨γ, k, hk⟩, hu⟩ := hy (h * z⁻¹)
  refine ⟨i, ⟨γ, k, ?_⟩, fun i' ⟨γ', k', hk'⟩ => hu i' ⟨γ', k', ?_⟩⟩
  · calc h = h * z⁻¹ * z := by group
      _ = ι γ * y i * k * z := by rw [hk]
      _ = ι γ * y i * (z * k) := by rw [mul_assoc _ (k : G) z, hc (k : G)]
      _ = ι γ * (y i * z) * k := by simp only [mul_assoc]
  · have hc' : ∀ a : G, a * z⁻¹ = z⁻¹ * a := fun a => ((Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hz)) a)
    rw [hk', mul_assoc _ (k' : G) z⁻¹, hc' (k' : G)]
    group

theorem stab_mul_central {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) (J : Subgroup G) (y : G) {z : G}
    (hz : z ∈ Subgroup.center G) : Bridge.stab ι J (y * z) = Bridge.stab ι J y := by
  have hc : ∀ a : G, a * z = z * a := fun a => ((Subgroup.mem_center_iff.1 hz) a)
  ext γ
  rw [Bridge.mem_stab, Bridge.mem_stab]
  have e : (y * z)⁻¹ * ι γ * (y * z) = y⁻¹ * ι γ * y :=
    calc (y * z)⁻¹ * ι γ * (y * z) = z⁻¹ * ((y⁻¹ * ι γ * y) * z) := by group
      _ = z⁻¹ * (z * (y⁻¹ * ι γ * y)) := by rw [hc (y⁻¹ * ι γ * y)]
      _ = y⁻¹ * ι γ * y := by group
  rw [e]

theorem map_mem_center {G H : Type} [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f) {z : G}
    (hz : z ∈ Subgroup.center G) : f z ∈ Subgroup.center H := by
  rw [Subgroup.mem_center_iff]
  intro a
  obtain ⟨a', rfl⟩ := hf a
  rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz) a']

theorem twist_good_of {D : D7} (ψ : Twist D Circle) (hQ : ψ.Q = ∅) (hc : ψ.chi = 1) : ψ.Good := by
  obtain ⟨Q, chi, res⟩ := ψ
  dsimp only at hQ hc
  subst hQ hc
  exact ⟨by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ, fun _ => rfl, fun _ => rfl, splitSet_empty, fun _ _ _ _ _ => rfl,
    fun _ h => absurd h (Finset.notMem_empty _)⟩

theorem lev_eq_of {F E LL : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [CommRing LL] {n : ℕ} (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Af F))
    (L L' : LevDat E LL n) (hr : L.r = L'.r) (ht : L.t = L'.t) (hP : L.Pg = L'.Pg) (hQ : L.Q = L'.Q)
    (hH : L.P.H = ⊥) (hH' : L'.P.H = ⊥) : lev hc J β L = lev hc J β L' := by
  obtain ⟨r, hr0, t, s, Pg, Q, P, cg, xq⟩ := L
  obtain ⟨r', hr0', t', s', Pg', Q', P', cg', xq'⟩ := L'
  dsimp only at hr ht hP hQ hH hH'
  subst hr ht hP hQ
  ext x
  rw [mem_lev, mem_lev, hH, hH', Subgroup.mem_bot, Subgroup.mem_bot]
  rfl

open GlobalTheory.ConjTwist in

theorem ser_transl {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)
    {χS χT : (AE D)ˣ →* Circle} (hom : IsWeilDatumO R.ψ (Vc D i) (Wc D i) χS χT (R.ωP i t)) (hθ : IsInfFam R.θ)
    (hv : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t)) {k : GA D (Vc D i)} (hk : k ∈ GfC (Vc D i)) (c : ℂ)
    (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (w : (R.cV i).W) (g : GA D (Wc D i)) :
    ser R i t (c • R.ωP i t (k, 1) (R.vP i t)) u h w g = c * ser R i t (R.vP i t) u (h * k) w g := by
  simp only [ser, thetaKO]
  rw [GlobalTheory.FiniteFock.pureTensorO_smul, ← GlobalTheory.OrientedHeis.om_fin_pureTensorO R.ψ _ _ _ _ (R.ωP i t) hom R.θ hθ k hk 1
    (one_mem _) _ _ _ _ (R.vP i t) _ hv, map_smul, Pi.smul_apply, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one,
    smul_eq_mul]

open GlobalTheory.ConjTwist GlobalTheory.FlatVecSum in

theorem sum_eq_classSum {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (j : Fin D.R.m) (t : T0)
    {B : Base (Vc D j) (Wc D j)} (hB : BaseOf R j B) (ψ : Twist D Circle) {c0 : ℂ} (hc0 : c0 ≠ 0) {z' : GA D (Vc D j)}
    (hz' : z' ∈ GfC (Vc D j)) (hzc : Formalism.IndefR.FWT.fin (Vc D j) z' ∈ Subgroup.center (Bridge.Gf (Vc D j)))
    (hflat : c0 • R.ωP j t (z', 1) (R.vP j t) = (princ B).vecFlat ψ)
    {χS χT : (AE D)ˣ →* Circle} (hom : IsWeilDatumO R.ψ (Vc D j) (Wc D j) χS χT (R.ωP j t)) (hθ : IsInfFam R.θ)
    (hv : IsThetaFunO R.ψ (Vc D j) (Wc D j) (R.vP j t)) {m : ℕ} (h₀ : Fin m → GA D (Vc D j))
    (J : Subgroup (Bridge.Gf (Vc D j))) (hrel : ((princ B).levJ ψ).relIndex J = 1) (Ef : Bridge.Gf (Vc D j) → (R.cV j).W)
    (u : ∀ ρ, lowT (R.MW j (sg0 D A)) ρ) (g : GA D (Wc D j)) :
    ∑ k, ((((princ B).levJ ψ).relIndex J : ℕ) : ℂ)⁻¹ *
        ((Nat.card (Bridge.stab (Bridge.ratF (Vc D j)) ((princ B).levJ ψ) (Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z'))) : ℕ) : ℂ)⁻¹ *
        thetaKO (R.ωP j t) (h₀ k * z') g
          ((pureTensorO R.ψ R.θ (Vc D j) (Wc D j) (fun _ => 1) (cart (R.MW j (sg0 D A))) (R.BV j) (onb (R.MW j (sg0 D A)))
            (R.vP j t) ∘ₗ R.ioP j (PiTensorProduct.tprod ℂ u)) (Ef (Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z')))) =
      (c0⁻¹ • (princ B).classSum (R.ωP j t) ψ h₀
        (fun h => R.ioP j (PiTensorProduct.tprod ℂ u) (Ef (h * Formalism.IndefR.FWT.fin (Vc D j) z')))) g := by
  rw [Pi.smul_apply, Base.classSum_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hfin1 : Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z') = finPt (Vc D j) (h₀ k) * Formalism.IndefR.FWT.fin (Vc D j) z' :=
    map_mul _ _ _
  rw [Pi.smul_apply, smul_eq_mul, hrel, Nat.cast_one, inv_one, one_mul, hfin1, stab_mul_central _ _ _ hzc,
    show (princ B).F = B.F from rfl, hB.series_eq_ser, ← hflat, ser_transl R j t hom hθ hv hz', mul_left_comm _ c0,
    ← mul_assoc c0⁻¹ c0, inv_mul_cancel₀ hc0, one_mul]
  rfl

open Classical GlobalTheory.ConjTwist GlobalTheory.FlatVecSum in

theorem thF_eq_classSum_princ : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ (y : (X.R.HV j t).H) (u : ∀ ρ, lowT (X.R.MW j (sg0 D X.A3.A)) ρ),
    ∃ (m : ℕ) (h₀ : Fin m → GA D (Vc D j)) (c : ℂ) (z : Bridge.Gf (Vc D j)),
      IsClassSystem (Vc D j) ((GlobalTheory.FlatVecSum.princ (Y.Z.ρ.B i j b)).levJ (Y.Z.ρ.tw i b 0 ∅ 1)) h₀ ∧ z ∈ Subgroup.center (Bridge.Gf (Vc D j)) ∧
      X.R.thF j t y (fun ρ => (u ρ : ↥((X.R.MW j (sg0 D X.A3.A)).sm ρ))) =
        c • (GlobalTheory.FlatVecSum.princ (Y.Z.ρ.B i j b)).classSum (X.R.ωP j t) (Y.Z.ρ.tw i b 0 ∅ 1) h₀
          (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * z))) := by
  intro D X E Y i j b t hxi hQ y u
  have hB : BaseOf X.R.toRealDat j (Y.Z.ρ.B i j b) := GlobalTheory.PinBase.baseOf_of_pin D X Y.Z.ρ Y.Z.good Y.Z.pin i j b
  have hG : (Y.Z.ρ.B i j b).Good := Y.Z.good.base i j b
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 :=
    ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.chain, X.char.thP⟩
  have he : (Y.Z.ρ.tw i b 0 ∅ 1).Q = ∅ := half_empty _
  have hone : (Y.Z.ρ.tw i b 0 ∅ 1).chi = 1 := charOf_one _ _
  have hψ : (Y.Z.ρ.tw i b 0 ∅ 1).Good := twist_good_of _ he hone
  have hadm : (Y.Z.ρ.B i j b).admitted (Y.Z.ρ.tw i b 0 ∅ 1).Q := by rw [he]; exact Base.admissible_empty_of_good hG
  have htup : IsTupOf X.R.toRealDat (Y.Z.ρ.B i j b) (Y.Z.ρ.tw i b 0 ∅ 1) t :=
    ⟨by rw [hxi, hone, mul_one], by rw [hQ, he, Finset.union_empty]⟩
  obtain ⟨⟨f, hf⟩, -⟩ := GlobalTheory.FlatVecExist.flatVec_existsUnique D X.Γ X.Pl0 X.T X.A3.A _ X.R.toRealDat X.F.lv2 hC X.guard j t
  obtain ⟨z', c0, hz', hc0, hfz⟩ :=
    GlobalTheory.T.flatVector_eq_unit_mul_centralTranslate_liftVector D X.Γ X.Pl0 X.T X.A3.A _ X.R.toRealDat X.F.lv2 hC X.guard j t (X.std j) f hf
  have hflat : f = (princ (Y.Z.ρ.B i j b)).vecFlat (Y.Z.ρ.tw i b 0 ∅ 1) :=
    eq_vecFlat_princ hB htup hC.lev hG hψ hadm hf

  have hβ : (princ (Y.Z.ρ.B i j b)).F.βS = X.R.βV j := hB.βS
  have hrW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  have hrV : (Vc D j).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have hJ : (princ (Y.Z.ρ.B i j b)).levJ (Y.Z.ρ.tw i b 0 ∅ 1) =
      (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J := by
    unfold Base.levJ
    rw [hβ, GlobalTheory.LiftClassSumPrinc.lev_eq_of _ _ _ ((princ (Y.Z.ρ.B i j b)).levS (Y.Z.ρ.tw i b 0 ∅ 1))
      (Formalism.IndefR.Lev.flag1L (X.R.datVt j t)) (by show (Wc D j).rank = D.R.r; exact hrW)
      (by show (Vc D j).rank - (Wc D j).rank = D.R.t; omega) (by show (Y.Z.ρ.B i j b).G.Pg = X.R.Pg; exact hB.Pg)
      (by show (Y.Z.ρ.B i j b).de.Q ∪ (Y.Z.ρ.tw i b 0 ∅ 1).Q = X.R.Q t; rw [he, Finset.union_empty, hQ]) rfl rfl]
    rfl
  have hrel : ((princ (Y.Z.ρ.B i j b)).levJ (Y.Z.ρ.tw i b 0 ∅ 1)).relIndex
      (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J = 1 := Subgroup.relIndex_eq_one.2 hJ.ge
  refine (exists_isClassSystem (princ (Y.Z.ρ.B i j b)) (princ_good hG).frame (Y.Z.ρ.tw i b 0 ∅ 1)).elim fun m hm =>
    hm.elim fun h₀ hcs => ?_
  have hzc : Formalism.IndefR.FWT.fin (Vc D j) z' ∈ Subgroup.center (Bridge.Gf (Vc D j)) :=
    GlobalTheory.LiftClassSumPrinc.map_mem_center (finHom (Vc D j)).rangeRestrict (MonoidHom.rangeRestrict_surjective _) hz'.1
  refine ⟨m, h₀, c0⁻¹, Formalism.IndefR.FWT.fin (Vc D j) z', hcs, hzc, ?_⟩
  have hfin1 : ∀ k, Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z') = finPt (Vc D j) (h₀ k) * Formalism.IndefR.FWT.fin (Vc D j) z' :=
    fun k => map_mul _ _ _
  have hy : Bridge.IsReps (Bridge.ratF (Vc D j)) ((princ (Y.Z.ρ.B i j b)).levJ (Y.Z.ρ.tw i b 0 ∅ 1))
      (fun k => Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z')) := by
    rw [show (fun k => Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z')) = fun k => finPt (Vc D j) (h₀ k) * Formalism.IndefR.FWT.fin (Vc D j) z'
      from funext hfin1]
    exact GlobalTheory.LiftClassSumPrinc.isReps_mul_central _ _ _ hzc hcs.reps
  have hh : ∀ k, h₀ k * z' ∈ GfC (Vc D j) := fun k => mul_mem (hcs.fin k) hz'.2.1
  have hθ : IsInfFam X.R.θ := hC.models.inf
  have hvθ : IsThetaFunO X.R.ψ (Vc D j) (Wc D j) (X.R.vP j t) :=
    GlobalTheory.AdTh.MinorWeight.pure_one _ (X.R.vP j t) ▸ hC.thP.pt_theta j t 1
  funext g
  refine (hC.thP.thF j t).elim fun thP hPF => ?_
  have hx : (X.R.HV j t).e y ∈ Bridge.AdForms (Bridge.ratF (Vc D j)) (X.R.cV j).coef.ρ
      (levEnv _ (X.R.βV j) (X.R.datVt j t)).J (levEnv _ (X.R.βV j) (X.R.datVt j t)).χ :=
    (hC.models.HV j t).2.1.le (LinearMap.mem_range_self _ y)
  have hfin : ∀ k ∈ GfC (Vc D j), ∀ hk : Formalism.IndefR.FWT.fin (Vc D j) k ∈ Formalism.IndefR.FWT.levJ X.R.toRealDat j t, ∀ P,
      X.R.ωP j t (k, 1) (X.R.ptP j t P) =
      (((levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).χ ⟨Formalism.IndefR.FWT.fin (Vc D j) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • X.R.ptP j t P :=
    fun k hk hk' =>
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite X.R.ψ X.R.θ (Vc D j) (Wc D j) _ _ (X.R.ωP j t) hC.models.inf
      (hC.thP.ωP j t) _ _ _ _ _ (hC.thP.pt_theta j t) k hk 1 (one_mem _) _
      (GlobalTheory.AdTh.LevelLawCore.omega_level_vP_core D X.Γ X.Pl0 X.T X.A3.A _ X.R.toRealDat X.F.lv2 hC j t k (X.std j) hk hk')
  have key := GlobalTheory.LiftUnfold.integral_theta (hC.thP.ωP j t) (D.sp.V_sig _) (hC.models.vpos j) (X.R.cV j) (hC.models.cV j)
    (X.R.βV j) (X.R.datVt j t) (fun _ => Iff.rfl) hx
    (pureTensorO X.R.ψ X.R.θ (Vc D j) (Wc D j) (fun _ => 1) (cart (X.R.MW j (sg0 D X.A3.A))) (X.R.BV j)
      (onb (X.R.MW j (sg0 D X.A3.A))) (X.R.vP j t) ∘ₗ X.R.ioP j (PiTensorProduct.tprod ℂ u)) (fun w => hC.thP.pt_theta j t _)
    (fun a ha w => (hC.thP.ioP j t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _)
    (hC.models.νV j t) _ (Fin m) (fun k => h₀ k * z') hJ.le (by rw [hrel]; exact one_ne_zero) hy hh g
  have h1 := congrFun (hPF.2 y u) g
  have h2 := hPF.1.eq ((X.R.extV j t).rangeRestrict y) (PiTensorProduct.tprod ℂ u) g
  refine h1.trans (h2.trans (Eq.trans ?_ (key.trans ?_)))
  · rfl
  exact sum_eq_classSum X.R.toRealDat j t hB (Y.Z.ρ.tw i b 0 ∅ 1) hc0.1 hz'.2.1 hzc (hfz.symm.trans hflat) (hC.thP.ωP j t) hθ
    hvθ h₀ _ hrel ((X.R.HV j t).e y) u g

end GlobalTheory.LiftClassSumPrinc

end
