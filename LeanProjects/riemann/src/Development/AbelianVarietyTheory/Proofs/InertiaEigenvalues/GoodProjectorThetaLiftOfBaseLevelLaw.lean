import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLevelActionEqInvSmulTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProjectionIntertwinesLevelLifts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseOfOfPin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups GlobalTheory.ThetaProjEquiv GlobalTheory.ThetaCommutation Formalism.IndefR.Lev Formalism.IndefR.Mult

namespace GlobalTheory.ProjLiftLaw

theorem reductionGroupAction_mul {G W : Type} [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {Q : Subgroup G} (ch : Q →* ℂˣ)
    (q q' : Q) (f : G → W) : Bridge.g0Act ch q (Bridge.g0Act ch q' f) = Bridge.g0Act ch (q * q') f := by
  funext h
  simp only [Bridge.g0Act, smul_smul, Subgroup.coe_mul, mul_assoc, map_mul, mul_inv, Units.val_mul, mul_comm]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem liftV_exists_core (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (g : G) : ∃ κ, IsLiftV R i t g κ := by
  obtain ⟨κ, hκ⟩ := (R.B.L i t).act_tie.red_surj g
  have e := hC.grp.red_L i t κ
  exact ⟨κ, e.symm.trans (congrArg R.eG hκ)⟩

theorem exists_act_core (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (g : G) (κ : (levV R i t).Q)
    (hκ : IsLiftV R i t g κ) (x : (R.HV i t).H) :
    ∃ y : (R.HV i t).H, (R.HV i t).e y = Bridge.g0Act (levV R i t).ch κ ((R.HV i t).e x) := by
  refine (exists_adelic_lift (Vc D i) (R.βV i) (R.datVt i t) κ (R.eG g) hκ (R.cV i).W).elim fun k hk => ?_
  refine (GlobalTheory.translate_unitary_lifts R hC.lev hC.models.HV hC.models.cV i t (R.eG g) k hk.1 x).elim fun y hy => ?_
  exact ⟨y, funext fun h => (hy.1 h).trans (hk.2 _ h).symm⟩

theorem thF_act_core (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (g : G) (κ : (levV R i t).Q) (hκ : IsLiftV R i t g κ)
    (x y : (R.HV i t).H) (hy : (R.HV i t).e y = Bridge.g0Act (levV R i t).ch κ ((R.HV i t).e x)) :
    R.thF i t y = FWT.actW R i (sg0 D A) g (R.thF i t x) := by
  refine (exists_adelic_lift (Vc D i) (R.βV i) (R.datVt i t) κ (R.eG g) hκ (R.cV i).W).elim fun k hk => ?_
  have hk' := hk.1
  refine ((GlobalTheory.StepLifts.lifts_exist R hC.lev i).2 (R.eG g)).elim fun k' hk'' => ?_
  refine (hC.thP.ioP i t).2.2.elim fun v hv0 => hv0.elim fun _ hw => ?_
  have hv := hw.1
  refine ((hC.models.HW i (sg0 D A)).2.1.ge (hC.thP.thF_mem i t x)).elim fun a ha => ?_
  refine ((hC.models.HW i (sg0 D A)).2.1.ge (hC.thP.thF_mem i t y)).elim fun b hb => ?_
  have hg : (R.HW i (sg0 D A)).e (R.gW i (sg0 D A) g a) = FWT.actW R i (sg0 D A) g (R.thF i t x) :=
    (hC.models.gW i (sg0 D A) g a).trans (congrArg (FWT.actW R i (sg0 D A) g) ha)
  have hinj := GlobalTheory.EvalAtUnitVector.eval_injective (R.MW i (sg0 D A)) (R.HW i (sg0 D A)).H (R.HW i (sg0 D A)).e _
    (R.νW i) (R.fdW i) (hC.models.HW i (sg0 D A)).2.2 (fun ρ => v ρ) hv
  have h1 : R.thF i t y (fun ρ => v ρ) = FWT.actW R i (sg0 D A) g (R.thF i t x) (fun ρ => v ρ) := funext fun z =>
    (thF_shift_core R F hC i t (R.eG g) k k' hk' hk''.1 x y (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) k)
      (levChi_ne_zero (V := Vc D i) (β := R.βV i) (flagL (R.datVt i t)) k)
      (GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hC.lev hC.models.inf hC.thP.ωP hC.thP.vP i t (R.eG g) k k' hk' hk'')
      (fun h => (congrFun hy h).trans (hk.2 _ h)) v z).trans
    (finiteGroup_acts_by_lift_translation_principalType R i (R.eG g) k' hk'' _ (thF_type R hC.thP.thF_mem i t x _) z).symm
  have h2 : b = R.gW i (sg0 D A) g a := hinj
    ((congrArg (fun U : MMap (R.MW i (sg0 D A)) => U fun ρ => v ρ) hb).trans
      (h1.trans (congrArg (fun U : MMap (R.MW i (sg0 D A)) => U fun ρ => v ρ) hg).symm))
  exact hb.symm.trans ((congrArg (R.HW i (sg0 D A)).e h2).trans hg)

theorem thF_alg_core (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (c : G → ℂ) (κ : G → (levV R i t).Q)
    (hκ : ∀ g, IsLiftV R i t g (κ g)) (x y : (R.HV i t).H) (hy : IsAlgV R i t c κ x y) :
    R.thF i t y = algW R i c (R.thF i t x) :=
  (map_comb (R.HV i t).e (hC.models.HV i t).1 (R.thF i t) c _ _ y hy (fun g => exists_act_core hC i t g (κ g) (hκ g) x)
    fun g z hz => thF_act_core hC i t g (κ g) (hκ g) x z hz).trans (algW_apply i c _).symm

theorem exists_alg_core (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (c : G → ℂ) (κ : G → (levV R i t).Q)
    (hκ : ∀ g, IsLiftV R i t g (κ g)) (x : (R.HV i t).H) : ∃ y, IsAlgV R i t c κ x y := by
  have hm : ∑ g, c g • Bridge.g0Act (levV R i t).ch (κ g) ((R.HV i t).e x) ∈ LinearMap.range (R.HV i t).e :=
    Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ ((exists_act_core hC i t g (κ g) (hκ g) x).elim fun z hz => ⟨z, hz⟩)
  obtain ⟨y, hy⟩ := hm
  exact ⟨y, hy⟩

end GlobalTheory.ProjLiftLaw

namespace GlobalTheory.ProjLiftLaw
open Formalism.IndefR.Links GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups

theorem parLev_congr {F' E' LL : Type} [Field F'] [NumberField F'] [Field E'] [NumberField E'] [StarRing E'] [Algebra F' E']
    [CommRing LL] {n : ℕ} (hc : CMData F' E') (J : Matrix (Fin n) (Fin n) E') (β : GL (Fin n) (E' ⊗[F'] Af F'))
    (L L' : LevDat E' LL n) (hr : L.r = L'.r) (ht : L.t = L'.t) (hP : L.Pg = L'.Pg) (hQ : L.Q = L'.Q) :
    parLev hc J β L = parLev hc J β L' := by
  unfold parLev
  rw [hr, ht, hP, hQ]

open Classical in

theorem levJ_le_Q (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (t : X.T) (hQ : X.R.Q t = (Y.Z.ρ.B i j b).de.Q) (k : Bridge.Gf (Vc D j))
    (hk : k ∈ (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)) : k ∈ (levV X.R.toRealDat j t).Q := by
  have hB := GlobalTheory.PinBase.baseOf_of_pin D X Y.Z.ρ Y.Z.good Y.Z.pin i j b
  have h1 := hk.1
  have hrW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  have hrV : (Vc D j).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have he : (Y.Z.ρ.tw i b 0 ∅ 1).Q = ∅ := half_empty _
  rw [hB.βS] at h1
  refine ⟨?_, ?_⟩
  · refine (parLev_congr _ _ _ _ _ ?_ ?_ ?_ ?_).le h1
    · show (Wc D j).rank = D.R.r
      exact hrW
    · show (Vc D j).rank - (Wc D j).rank = D.R.t
      omega
    · exact hB.Pg
    · show (Y.Z.ρ.B i j b).de.Q ∪ (Y.Z.ρ.tw i b 0 ∅ 1).Q = X.R.Q t
      rw [he, Finset.union_empty, hQ]
  · exact Subgroup.mem_top _

end GlobalTheory.ProjLiftLaw

namespace GlobalTheory.ProjLiftLaw
open Formalism.IndefR.Links GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups

theorem flagLevelTwistedTranslation_finsetSum {G W ι : Type} [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {Q : Subgroup G} (ch : Q →* ℂˣ)
    (q : Q) (s : Finset ι) (a : ι → ℂ) (f : ι → G → W) :
    Bridge.g0Act ch q (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i • Bridge.g0Act ch q (f i) := by
  funext h
  simp only [Bridge.g0Act, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem flagLevelTwistedTranslation_smul {G W : Type} [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {Q : Subgroup G} (ch : Q →* ℂˣ)
    (q : Q) (a : ℂ) (f : G → W) : Bridge.g0Act ch q (a • f) = a • Bridge.g0Act ch q f := by
  funext h
  simp only [Bridge.g0Act, Pi.smul_apply]
  exact smul_comm _ _ _

theorem twistedTranslation_classCombination_eigen {H W G : Type} [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Group G] [Fintype G]
    {Q : Subgroup H} (ch : Q →* ℂˣ) (red : Q →* G) (f : H → W)
    (hker : ∀ j : Q, red j = 1 → Bridge.g0Act ch j f = f)
    (c : G → ℂ) (hc : ∀ u g, c (u * g * u⁻¹) = c g) (κ : G → Q) (hκ : ∀ g, red (κ g) = g)
    (k : Q) (a : ℂ) (hk : Bridge.g0Act ch k f = a • f) :
    Bridge.g0Act ch k (∑ g, c g • Bridge.g0Act ch (κ g) f) = a • ∑ g, c g • Bridge.g0Act ch (κ g) f := by
  rw [flagLevelTwistedTranslation_finsetSum]
  have step : ∀ g, Bridge.g0Act ch k (Bridge.g0Act ch (κ g) f) =
      a • Bridge.g0Act ch (κ (red k * g * (red k)⁻¹)) f := by
    intro g
    have hj : red ((κ (red k * g * (red k)⁻¹) * k)⁻¹ * (k * κ g)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hκ, hκ]
      group
    have e : k * κ g = κ (red k * g * (red k)⁻¹) * (k * ((κ (red k * g * (red k)⁻¹) * k)⁻¹ * (k * κ g))) := by group
    rw [reductionGroupAction_mul, e, ← reductionGroupAction_mul, ← reductionGroupAction_mul, hker _ hj, hk, flagLevelTwistedTranslation_smul]
  simp only [step, smul_comm (c _) a, ← Finset.smul_sum]
  congr 1
  exact Fintype.sum_equiv (MulAut.conj (red k)).toEquiv _ _ (fun g => by simp [hc])

theorem law_of_comb {H W G : Type} [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Group G] [Fintype G]
    {Q : Subgroup H} (ch : Q →* ℂˣ) (red : Q →* G) (f f' : H → W)
    (hker : ∀ j : Q, red j = 1 → Bridge.g0Act ch j f = f)
    (c : G → ℂ) (hc : ∀ u g, c (u * g * u⁻¹) = c g) (κ : G → Q) (hκ : ∀ g, red (κ g) = g)
    (hf' : f' = ∑ g, c g • Bridge.g0Act ch (κ g) f) (k : H) (hkQ : k ∈ Q) (lam : ℂ)
    (hlaw : ∀ h, f (h * k) = lam • f h) (h : H) : f' (h * k) = lam • f' h := by
  have hk : Bridge.g0Act ch ⟨k, hkQ⟩ f = ((((ch ⟨k, hkQ⟩)⁻¹ : ℂˣ) : ℂ) * lam) • f := by
    funext h'
    simp only [Bridge.g0Act, Pi.smul_apply]
    rw [hlaw h', smul_smul]
  have hcomb := twistedTranslation_classCombination_eigen ch red f hker c hc κ hκ ⟨k, hkQ⟩ _ hk
  rw [← hf'] at hcomb
  have e3 := congrFun hcomb h
  simp only [Bridge.g0Act, Pi.smul_apply] at e3
  rw [mul_smul] at e3
  exact smul_right_injective _ (Units.ne_zero _) e3

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem eC_conj (hC : GlobalTheory.Hk3.Core R F) (u g : G) :
    RealDat.eC (A := A) (sg0 D A) (u * g * u⁻¹) = RealDat.eC (A := A) (sg0 D A) g := by
  obtain ⟨eR, _, _, h, _⟩ := hC.grp.record
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have key : ∀ x, RealDat.eC (A := A) (sg0 D A) x = D.ntypes.e0.coeff (eR x) := fun x => by
    rw [← h x, RealDat.eC, hs]
  rw [key, key, map_mul eR, map_mul eR, map_inv eR]
  have hc := (Subalgebra.mem_center_iff.1 (GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D).1) (MonoidAlgebra.single (eR u) 1)
  have := congrArg (fun z => z.coeff (eR u * eR g)) hc
  simp only [MonoidAlgebra.single_mul_apply, MonoidAlgebra.mul_single_apply, one_mul, mul_one, inv_mul_cancel_left] at this
  exact this.symm

end GlobalTheory.ProjLiftLaw

namespace GlobalTheory.ProjLiftLaw
open Formalism.IndefR.Links GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups

theorem twistedTranslation_fixes_adelicForm_of_mem_level {G Γ W : Type} [Group G] [Group Γ] {ι : Γ →* G} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : Γ →* Module.End ℂ W} {Q J : Subgroup G} (ch : Q →* ℂˣ) (χ : J →* ℂˣ) (hJ : J ≤ Q)
    (hch : ∀ k : J, ch ⟨k, hJ k.2⟩ = χ k) {f : G → W} (hf : f ∈ Bridge.AdForms ι ρ J χ) (q : Q) (hq : (q : G) ∈ J) :
    Bridge.g0Act ch q f = f := by
  funext h
  have e1 := hf 1 h ⟨q, hq⟩
  rw [map_one, one_mul, map_one, Module.End.one_apply] at e1
  have e2 := hch ⟨q, hq⟩
  simp only [Bridge.g0Act]
  rw [e1, ← e2, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem twistedTranslation_fixes_formV_of_reduction_one (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (jq : (levV R i t).Q)
    (hjq : (R.B.L i t).act_tie.red jq = 1) :
    Bridge.g0Act (levV R i t).ch jq ((R.HV i t).e y) = (R.HV i t).e y :=
  twistedTranslation_fixes_adelicForm_of_mem_level (levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch (levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ
    (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J_le (levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch_J
    ((hC.models.HV i t).2.1.le (LinearMap.mem_range_self _ y)) jq (((R.B.L i t).act_tie.red_ker jq).1 hjq)

theorem red_of_lift (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (g : G) (κ : (levV R i t).Q) (hκ : IsLiftV R i t g κ) :
    (R.B.L i t).act_tie.red κ = g :=
  R.eG.injective ((hC.grp.red_L i t κ).trans hκ)

theorem law_keep (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (κ : G → (levV R i t).Q) (hκ : ∀ g, IsLiftV R i t g (κ g))
    (y y' : (R.HV i t).H) (hy' : IsAlgV R i t (RealDat.eC (A := A) (sg0 D A)) κ y y') (k : Bridge.Gf (Vc D i))
    (hkQ : k ∈ (levV R i t).Q) (lam : ℂ) (hlaw : ∀ h, (R.HV i t).e y (h * k) = lam • (R.HV i t).e y h)
    (h : Bridge.Gf (Vc D i)) : (R.HV i t).e y' (h * k) = lam • (R.HV i t).e y' h :=
  law_of_comb (levV R i t).ch (R.B.L i t).act_tie.red ((R.HV i t).e y) ((R.HV i t).e y') (twistedTranslation_fixes_formV_of_reduction_one hC i t y) _
    (eC_conj hC) κ (fun g => red_of_lift hC i t g (κ g) (hκ g)) hy' k hkQ lam hlaw h

theorem thG_apply_eq (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (κ : G → (levV R i t).Q)
    (hκ : ∀ g, IsLiftV R i t g (κ g)) (y y' : (R.HV i t).H) (hy' : IsAlgV R i t (RealDat.eC (A := A) (sg0 D A)) κ y y')
    (v : (R.MW i (sg0 D A)).Vec) : (R.HW i (sg0 D A)).e (R.thG i t y) v = R.thF i t y' v := by
  have h1 : R.thF i t y' = postOn _ (R.eWf i (sg0 D A)) (R.thF i t y) :=
    (thF_alg_core hC i t _ κ hκ y y' hy').trans (algW_eC R i ▸ rfl)
  rw [hC.thP.thG i t y, h1]

end GlobalTheory.ProjLiftLaw

namespace GlobalTheory.ProjLiftLaw
open Formalism.IndefR.Links GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups

theorem projLift_law : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y : (X.R.HV j t).H,
    (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) →
    ∃ y' : (X.R.HV j t).H, (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y' (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y' h) ∧
      (X.R.HW j (sg0 D X.A3.A)).e (X.R.thG j t y) (X.geo.v₀ j _) = X.R.thF j t y' (X.geo.v₀ j _) := by
  intro D X E Y i j b t hxi hQ y hy
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 :=
    ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.chain, X.char.thP⟩
  choose κ hκ using liftV_exists_core hC j t
  obtain ⟨y', hy'⟩ := exists_alg_core hC j t (RealDat.eC (A := X.A3.A) (sg0 D X.A3.A)) κ hκ y
  refine ⟨y', fun h k => ?_, ?_⟩
  · exact law_keep hC j t κ hκ y y' hy' (k : Bridge.Gf (Vc D j)) (levJ_le_Q D X E Y i j b t hQ k k.2) _
      (fun h' => hy h' k) h
  · exact thG_apply_eq hC j t κ hκ y y' hy' _

end GlobalTheory.ProjLiftLaw
