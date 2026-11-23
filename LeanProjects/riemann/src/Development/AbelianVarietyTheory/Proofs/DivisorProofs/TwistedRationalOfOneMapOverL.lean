import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotOntoOfCharAlone
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapOfOfPtIdent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IpMSelfEqZero
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameConstantsOfCharacterisationCoreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormClassSumNormalisedDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicLiftEqGeometricClassSumAllTuplesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNormalisedTupleDataOverCoefficientFieldStatement

set_option autoImplicit false

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.TwistedClassSum

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.OneMapTuples GlobalTheory.OnTies GlobalTheory.TwistField GlobalTheory.RealIndexBound GlobalTheory.AdTh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem exists_linear {K X X' Y M : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup X'] [Module K X']
    [AddCommGroup Y] [Module K Y] [AddCommGroup M] [Module ℂ M] (σ : K →+* ℂ) (j : Y → M) (hj : Function.Injective j)
    (j1 : ∀ x y, j (x + y) = j x + j y) (j2 : ∀ (a : K) x, j (a • x) = σ a • j x) (L : X → M)
    (L1 : ∀ x y, L (x + y) = L x + L y) (L2 : ∀ (a : K) x, L (a • x) = σ a • L x) (c : ℂ) (h : ∀ x, ∃ y, j y = c • L x)
    (s : X' →ₗ[K] X) : ∃ θ : X' →ₗ[K] Y, ∀ x, j (θ x) = c • L (s x) := by
  choose θ hθ using fun x => h (s x)
  refine ⟨{ toFun := θ, map_add' := fun x y => hj ?_, map_smul' := fun a x => hj ?_ }, hθ⟩
  · rw [j1, hθ, hθ, hθ, map_add, L1, smul_add]
  · rw [RingHom.id_apply, j2, hθ, hθ, map_smul, L2, smul_comm]

section Linear

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem base_embedding_apply (R : RealDat D A Ks) (a : D.what₂.LL) : sg0 D A a = D.what₂.embLL a :=
  DFunLike.congr_fun (sgAt_mk _ R.hv0) a

theorem adForm_add (x y : Fin (R.nW i) → D.what₂.LL) : adForm R i (x + y) = adForm R i x + adForm R i y := by
  unfold adForm
  rw [map_add, map_add]

theorem adForm_smul (a : D.what₂.LL) (x : Fin (R.nW i) → D.what₂.LL) :
    adForm R i (a • x) = D.what₂.embLL a • adForm R i x := by
  unfold adForm
  rw [map_smulₛₗ, map_smul, base_embedding_apply R]

theorem classSumRational_of_forall (hHW : R.models_HW) (hU : R.LUnif) {t : T0} {ph : ℂ}
    (h : ∀ x : A.fam.amb.FL i t, ∃ y, adForm R i y = ph • R.thF i t (jVx R i t x)) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) :
    ClassSumRational R i t U ψ ph := by
  have hinj : Function.Injective (adForm R i) := (hHW i _).1.comp (j_injective hU i)
  let L : (A.MtCSD i t).Forms → MMap (R.MW i (sg0 D A)) := fun x => R.thF i t (R.jV i t x)
  have h1 : ∀ x y, L (x + y) = L x + L y := fun x y =>
    (congrArg (R.thF i t) ((R.jV i t).map_add x y)).trans ((R.thF i t).map_add _ _)
  have h2 : ∀ (a : D.what₂.LL) x, L (a • x) = D.what₂.embLL a • L x := fun a x =>
    (congrArg (R.thF i t) ((R.jV i t).map_smulₛₗ a x)).trans ((R.thF i t).map_smul _ _)
  exact exists_linear D.what₂.embLL (adForm R i) hinj adForm_add adForm_smul L h1 h2 ph h (srcForm A i t U ψ)

theorem left_of_mem {σ : D.what₂.LL →+* ℂ} {Θ : MMap (R.MW i σ)} (h : Θ ∈ R.Wall i σ) (v : (R.MW i σ).Vec) :
    ∀ γ ∈ GQ (Wc D i), ∀ g, Θ v (γ * g) = Θ v g := by
  intro γ hγ g
  induction h using Submodule.span_induction with
  | mem F hF => exact (hF.aut v).left γ hγ g
  | zero => rfl
  | add F F' _ _ h h' => simp only [MultilinearMap.add_apply, Pi.add_apply, h, h']
  | smul s F _ h => simp only [MultilinearMap.smul_apply, Pi.smul_apply, h]

theorem ratio_of_j (hU : R.LUnif) {y y' : Fin (R.nW i) → D.what₂.LL} {ρ : ℂ}
    (h : (R.FW i).j (sg0 D A) y = ρ • (R.FW i).j (sg0 D A) y') (h0 : (R.FW i).j (sg0 D A) y ≠ 0) : ∃ a, D.what₂.embLL a = ρ :=
  ratio_mem ((R.FW i).j (sg0 D A)) (hU i _).1 D.what₂.embLL.toRatAlgHom.fieldRange (fun a => ⟨a, (base_embedding_apply R a).symm⟩)
    (fun _ : Fin 1 => 1) (fun _ => y) (fun _ : Fin 1 => 1) (fun _ => y') (fun _ => one_mem _)
    (fun _ => one_mem _) ρ (by simpa using h) (by simpa using h0)

variable (R) in

def AllRational (ph : Fin D.R.m → ℂ) : Prop :=
  ∀ (i : Fin D.R.m) (t : T0) (x₀ : A.fam.amb.FL i t), ∃ y, adForm R i y = ph i • R.thF i t (jVx R i t x₀)

theorem exists_base_lift {F : Face D A} (hU : R.LUnif) (h5 : R.LTheta F) (hr : R.LRatTh F)
    (hRk : Formalism.L2.Indef.Tree.RankRows ((R.toCx F).data F.cr false)) (i : Fin D.R.m) :
    ∃ (x₀ : A.fam.amb.FL i A.μ0) (y : Fin (R.nW i) → D.what₂.LL),
      (R.FW i).j (sg0 D A) y = R.thG i A.μ0 (R.jV i A.μ0 x₀) ∧ (R.FW i).j (sg0 D A) y ≠ 0 := by
  refine Classical.byContradiction fun hn => ?_
  have hd : 0 < Module.finrank D.what₂.LL (R.WL F false i) := hRk.1.trans_eq (hRk.2 i).symm
  obtain ⟨y, hy⟩ : ∃ y, (GlobalTheory.OntoChain.thetaMat R F i A.μ0).mulVec y = fun _ => 1 :=
    ((R.toCx F).liftMat_bij F.cr false (RealDat.kForm hU false) (RealDat.ewNorm false) (RealDat.nP_pos false) (h5 false)
      (hr false) i A.μ0).2 _
  have h1 := GlobalTheory.OntoChain.j_thetaMat h5 hr i A.μ0 y
  refine hn ⟨(A.fam.L i A.μ0).toF (GlobalTheory.OntoChain.liftLvl F) (GlobalTheory.OntoChain.liftSub R F i A.μ0) y,
    GlobalTheory.OntoChain.coordMap R F i ((GlobalTheory.OntoChain.thetaMat R F i A.μ0).mulVec y), h1, fun h0 => ?_⟩
  have h2 : GlobalTheory.OntoChain.coordMap R F i ((GlobalTheory.OntoChain.thetaMat R F i A.μ0).mulVec y) = 0 :=
    (injective_iff_map_eq_zero _).1 (j_injective hU i) _ h0
  have h3 := (injective_iff_map_eq_zero _).1 (GlobalTheory.OntoChain.coordMap_injective (R := R) (F := F) i) _ h2
  exact one_ne_zero (congrFun (hy.symm.trans h3) ⟨0, hd⟩)

end Linear

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m}

theorem AllRational.twisted {F : Face D A} {ph : Fin D.R.m → ℂ} (h : AllRational R ph) (hHW : R.models_HW) (hU : R.LUnif) :
    TwistedRational R F ph := fun w _ i => classSumRational_of_forall hHW hU (h i (R.mu w)) _ _

theorem evaluates (fw : FWTie T R κ v₀) (hU : R.LUnif) : fw.Evaluates := by
  intro i σ hσ hV
  refine fw.ev i σ hσ hV (by_contra fun hn => hn ⟨0, fun f => ?_⟩)
  have h0 := fw.ev0 i σ hσ hV hn
  have h1 : f = 0 := by
    by_contra hf
    have h2 : ((fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) ≠ 0 := fun h =>
      hf ((fw.e i).injective ((Subtype.ext h).trans (map_zero _).symm))
    exact ((hU i σ).1 1 _ (linearIndependent_unique_iff.2 h2 : LinearIndependent _ fun _ : Fin 1 => _)).ne_zero 0
      (by rw [h0]; rfl)
  have key : ∀ (σ' : T.Q.c.F →+* ℂ) (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ' = W),
      phiC T hV (wtA (κ i)) (0 : T.R ((i : ℕ) + 1)) = 0 := by
    rintro σ' W rfl
    show (_ : ℂ) • adel _ _ _ (rdU _ 0) = 0
    rw [map_zero, map_zero, smul_zero]
  subst h1
  refine Eq.trans ?_ (key _ _ hV).symm
  rw [LinearMap.zero_apply, map_zero]
  rfl

theorem adForm_e (fw : FWTie T R κ v₀) (hU : R.LUnif) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i) (f : Cu T κ i) :
    adForm R i (fw.e i f) (v₀ i (sg0 D A)) =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) • psi T _ hV (f : T.R ((i : ℕ) + 1)) := by
  have e : res T (sg0 D A) = T.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T fw.alg_eq fw.laws.pins.2.2.1]
  have key : ∀ (σ' : T.Q.c.F →+* ℂ) (_ : σ' = T.σ₀) (W : HSp D) (h' : T.V ((i : ℕ) + 1) σ' = W)
      (h : T.V ((i : ℕ) + 1) T.σ₀ = W), phiC T h' (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) =
        (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) • psi T _ h (f : T.R ((i : ℕ) + 1)) := by
    rintro σ' rfl W rfl h
    rfl
  have hV' : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := e ▸ hV
  exact (evaluates fw hU i _ (e ▸ T.good_σ₀) hV' f).trans (key _ e _ hV' hV)

theorem exists_adForm (fw : FWTie T R κ v₀) (hHW : R.models_HW) (hU : R.LUnif) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i)
    {Θ : MMap (R.MW i (sg0 D A))} (hΘ : Θ ∈ R.Wall i (sg0 D A)) {m : ℕ} (b : Fin m → D.what₂.LL) (f : Fin m → Cu T κ i) (c : ℂ)
    (h : ∀ q : AutQ (Wc D i), Θ (v₀ i (sg0 D A)) q.out = c * ∑ l, D.what₂.embLL (b l) *
      ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * psi T _ hV (f l : T.R ((i : ℕ) + 1)) q.out)) :
    ∃ y, Θ = c • adForm R i y := by
  obtain ⟨w, rfl⟩ := (hHW i _).2.1.ge hΘ
  have hg := base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1
  let y : Fin m → Fin (R.nW i) → D.what₂.LL := fun l => fw.e i (f l)
  have e : adForm R i (∑ l, b l • y l) = ∑ l, D.what₂.embLL (b l) • adForm R i (y l) := by
    unfold adForm
    rw [map_sum, map_sum]
    exact Finset.sum_congr rfl fun l _ => adForm_smul _ _
  have e' : (R.HW i (sg0 D A)).e (c • (R.FW i).j (sg0 D A) (∑ l, b l • y l)) = c • adForm R i (∑ l, b l • y l) :=
    (R.HW i (sg0 D A)).e.map_smul c _
  have key : evAt R i _ (v₀ i (sg0 D A)) w = evAt R i _ (v₀ i (sg0 D A)) (c • (R.FW i).j (sg0 D A) (∑ l, b l • y l)) := by
    refine sub_eq_zero.1 (eq_zero_of_out _ (fun γ hγ g => ?_) 1 fun q => ?_)
    · simp only [Pi.sub_apply, evAt, left_of_mem ((hHW i _).2.1.le (LinearMap.mem_range_self _ _)) _ γ hγ g]
    · rw [mul_one, Pi.sub_apply, sub_eq_zero]
      refine (h q).trans ?_
      rw [evAt, e', e, MultilinearMap.smul_apply, MultilinearMap.sum_apply, Pi.smul_apply, Finset.sum_apply]
      refine congrArg (c * ·) (Finset.sum_congr rfl fun l _ => ?_)
      rw [MultilinearMap.smul_apply, adForm_e fw hU hV]
      rfl
  exact ⟨_, (congrArg _ (GlobalTheory.EvalAtUnitVector.evInj T R v₀ hHW fw.hv₀ i _ hg key)).trans e'⟩

section Data

variable {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup)

def rdAd (f : Rul (T.Q.Xo ((i : ℕ) + 1)) O.c') (g : GA D (Wc D i)) : ℂ :=
  T.cE ((i : ℕ) + 1) O.s0 (O.dict g).1 *
    (O.mu g * rdU (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) f (O.dict g).1 (O.dict g).2)

abbrev cuspOf (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) : Submodule O.c'.F (Rul (T.Q.Xo ((i : ℕ) + 1)) O.c') :=
  cusp (T.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (T.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank

variable {O}

theorem rdAd_of_isBC (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i) {m : ℕ} {f : Rul (T.Q.Xo ((i : ℕ) + 1)) O.c'} {as : Fin m → O.c'.F}
    {fs : Fin m → T.R ((i : ℕ) + 1)} (h : IsBC O.hle f as fs) (g : GA D (Wc D i)) :
    rdAd O f g = ∑ l, (as l : ℂ) * psi T _ hV (fs l) g := by
  rw [rdAd, rdU_unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c') h]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  show _ = (as l : ℂ) * (T.cE ((i : ℕ) + 1) O.s0 (O.dict g).1 * O.mu g *
    rdU (T.U ((i : ℕ) + 1) O.s0) (fs l) (O.dict g).1 (O.dict g).2)
  show _ * (_ * ((as l : ℂ) * _)) = _
  ring

theorem weight_eq (fw : FWTie T R κ v₀) (i : Fin D.R.m) : (κ i).n = (Vc D i).rank :=
  (fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm

theorem exists_translate (fw : FWTie T R κ v₀) {ph : ℂ}
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0))
    (hrow : O.OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O.s0) ph) :
    ∃ z k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG z) k ∧ ∀ t, ∃ ze : D.what₂.LL, ∀ x, O.Plc t x →
      ∃ f ∈ cuspOf O (κ i), IsCls O t x f ∧ ∀ q, ph * O.thAd t x q = D.what₂.embLL ze *
        ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (chiG R i z * rdAd O f (q.out * k))) := by
  obtain ⟨hE, ⟨-, hC, hA, -, -, z, -, h1⟩, -⟩ := hrow
  obtain ⟨k, hk, -⟩ := hP.lift.lev z
  have hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i := O.hV
  refine ⟨z, k, hk, fun t => ?_⟩
  obtain ⟨s, ⟨ze, rfl⟩, -, h1⟩ := h1 t
  refine ⟨ze, fun x hx => ?_⟩
  obtain ⟨⟨f, hf, hf'⟩, h2⟩ := h1 x hx
  have hs := ((mem_cusp _ _ _ _ _ _).1 hf).1
  refine ⟨f, hf, hf', fun q => ?_⟩
  obtain ⟨m, as, fs, hfs, hBC⟩ := hC _ _ f hf
  have h3 := rdAd_of_isBC hV (hA _ _ z m as fs f hs (fun l => ((mem_cusp _ _ _ _ _ _).1 (hfs l)).1) hBC) q.out
  have h4 : ∀ l, psi T _ hV (actLev T.Q.c O.lev2 z (fs l)) q.out = chiG R i z * psi T _ hV (fs l) (q.out * k) := fun l =>
    (hE z k hk (fs l) (by rw [weight_eq fw]; exact hfs l)).2 q.out
  have h5 : ph * O.thAd t x q = D.what₂.embLL ze * T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 *
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (O.mu q.out * rdU (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c'))
        (actLev O.c' O.lev2 z f) (O.dict q.out).1 (O.dict q.out).2) := h2 f hs hf' q
  have h6 : rdAd O (actLev O.c' O.lev2 z f) q.out = chiG R i z * rdAd O f (q.out * k) := by
    rw [h3, rdAd_of_isBC hV hBC, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [h4]; ring
  rw [← h6, h5, rdAd]
  ring

theorem exists_adForm_of_translate (fw : FWTie T R κ v₀) (hHW : R.models_HW) (hU : R.LUnif)
    (hE : O.EquivAt (κ i) (T.cE ((i : ℕ) + 1) O.s0)) {z : G} {k : GA D (Wc D i)}
    (hk : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG z) k)
    {Tp' : Type} {tup' : Tp' → T0} {O' : OMDat T.toCore R i Tp' tup'} (hF : O'.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange)
    {f : Rul (T.Q.Xo ((i : ℕ) + 1)) O'.c'} (hf : f ∈ cuspOf O' (κ i))
    {Θ : MMap (R.MW i (sg0 D A))} (hΘ : Θ ∈ R.Wall i (sg0 D A)) (c : ℂ)
    (h : ∀ q : AutQ (Wc D i), Θ (v₀ i (sg0 D A)) q.out = c *
      ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (chiG R i z * rdAd O' f (q.out * k)))) :
    ∃ y, Θ = c • adForm R i y := by
  have hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i := O.hV
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O'.hle).2 _ (T.U ((i : ℕ) + 1)) _ _ f hf
  have hb : ∀ l, ∃ b : D.what₂.LL, D.what₂.embLL b = (as l : ℂ) := fun l =>
    (hF ▸ (as l).2 : (as l : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange)
  choose b hb using hb
  have h4 := fun l => hE z k hk (fs l) (by rw [weight_eq fw]; exact hfs l)
  refine exists_adForm fw hHW hU hV hΘ b (fun l => ⟨_, (h4 l).1⟩) c fun q => ?_
  rw [h q, rdAd_of_isBC hV hBC, Finset.mul_sum, Finset.mul_sum]
  refine congrArg (c * ·) (Finset.sum_congr rfl fun l _ => ?_)
  have h5 : psi T _ hV (actLev T.Q.c O.lev2 z (fs l)) q.out = chiG R i z * psi T _ hV (fs l) (q.out * k) := (h4 l).2 q.out
  rw [hb]
  show _ = _ * (_ * psi T _ hV (actLev T.Q.c O.lev2 z (fs l)) q.out)
  rw [h5]
  ring

end Data

section Descent

theorem ennreal_volume_ratio_step_cancel {u u' c l m a a' : ℂ} (h0 : u * c ≠ 0) (hl : l ≠ 0) (h : u * c * l * m * a = u' * c * l * m * a') (e : ℂ) :
    e * (m * a) = u' / u * (e * (m * a')) := by
  have hu := left_ne_zero_of_mul h0
  refine mul_left_cancel₀ (mul_ne_zero h0 hl) ?_
  have h1 : u' / u * u = u' := div_mul_cancel₀ _ hu
  linear_combination e * h - c * l * e * m * a' * h1

variable {Tp : Type} {tup : Tp → T0} {O O' : OMDat T.toCore R i Tp tup}

theorem rational_upTo (fw : FWTie T R κ v₀) (hHW : R.models_HW) (hmem : R.thP_thF_mem) (hU : R.LUnif) {ph : ℂ}
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0))
    (hrow : O.OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O.s0) ph)
    (hF : O'.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange)
    (hP' : O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0))
    {cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ} {u u' : ℂ} (hS : SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1)
    (hS' : SerOf O' (κ i) (v₀ i (sg0 D A)) (u' • cc) 1) (hex : ∀ t x, ∃ f ∈ cuspOf O' (κ i), IsCls O' t x f)
    (t : Tp) (x₀ : A.fam.amb.FL i (tup t)) :
    ∃ y, ph • R.thF i (tup t) (jVx R i (tup t) x₀) = (u' / u) • adForm R i y := by
  refine Classical.byContradiction fun hn => ?_
  obtain ⟨z, k, hk, h⟩ := exists_translate (O := O) fw hP hrow
  obtain ⟨ze, h⟩ := h t
  obtain ⟨r, J, hr, h2, h3, h4⟩ := (hP.tuple t).reps
  obtain ⟨r', J', hr', h2', -, -⟩ := (hP'.tuple t).reps
  obtain ⟨x, hx⟩ := h2 x₀
  obtain ⟨x', hx'⟩ := h2' x₀
  obtain ⟨f, hf, hc, h⟩ := h x ((h4 x).2 ⟨x₀, hx⟩)
  obtain ⟨f', hf', hc'⟩ := hex t x'
  have hl : ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  have e : ∀ g, rdAd O f g = u' / u * rdAd O' f' g := fun g => by
    have e1 := hS.2.2 t r J hr _ x hx f ((mem_cusp _ _ _ _ _ _).1 hf).1 hc g
    have e2 := hS'.2.2 t r' J' hr' _ x' hx' f' ((mem_cusp _ _ _ _ _ _).1 hf').1 hc' g
    have h0 : u * cc (O.dict g).1 ≠ 0 := norm_ne_zero_iff.1 ((hS.1 (O.dict g).1).trans_ne one_ne_zero)
    have e3 : u * cc (O.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * O.mu g *
        rdU (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) f (O.dict g).1 (O.dict g).2 =
        u' * cc (O.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * O.mu g *
        rdU (unfBC O'.hle (T.U ((i : ℕ) + 1)) (inC O'.c')) f' (O'.dict g).1 (O'.dict g).2 := e1.symm.trans e2
    exact ennreal_volume_ratio_step_cancel h0 hl e3 _
  have hm : ph • R.thF i (tup t) (jVx R i (tup t) x₀) ∈ R.Wall i (sg0 D A) := (R.Wall i (sg0 D A)).smul_mem ph (hmem i _ _)
  obtain ⟨y, hy⟩ := exists_adForm_of_translate (O := O) (O' := O') fw hHW hU hrow.1 hk hF hf' hm (u' / u * D.what₂.embLL ze)
    fun q => ((congrArg (ph * ·) (congrFun (h3 _ x hx) q).symm).trans (h q)).trans (by rw [e]; ring)
  exact hn ⟨ze • y, hy.trans ((mul_smul _ _ _).trans (congrArg ((u' / u) • ·) (adForm_smul ze y).symm))⟩

theorem ratio_rational (fw : FWTie T R κ v₀) (hHW : R.models_HW) (hU : R.LUnif) (hG : R.thP_thG) {ph ρ : ℂ}
    (hph : ph ≠ 0) (hrat : O.PhRat (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O.s0) ph)
    (h : ∀ x₀ : A.fam.amb.FL i A.μ0, ∃ y, ph • R.thF i A.μ0 (jVx R i A.μ0 x₀) = ρ • adForm R i y)
    (hne : ∃ x₀ : A.fam.amb.FL i A.μ0, R.thG i A.μ0 (R.jV i A.μ0 x₀) ≠ 0) : ∃ a, D.what₂.embLL a = ρ := by
  obtain ⟨x₀, hne⟩ := hne
  obtain ⟨y, hy⟩ := h x₀
  obtain ⟨m, a, f, hf⟩ := hrat x₀
  have hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i := O.hV
  have hm : ph • (R.HW i (sg0 D A)).e (R.thG i A.μ0 (jVx R i A.μ0 x₀)) ∈ R.Wall i (sg0 D A) :=
    (R.Wall i (sg0 D A)).smul_mem ph ((hHW i _).2.1.le (LinearMap.mem_range_self _ _))
  obtain ⟨y₁, h1⟩ := exists_adForm fw hHW hU hV hm a f 1 fun q => (hf q.out).trans (one_mul _).symm
  replace h1 := h1.trans (one_smul _ _)
  have h2 : adForm R i y₁ = ρ • adForm R i (GlobalTheory.OntoChain.goodOp R i y) := by
    refine h1.symm.trans ((congrArg (ph • ·) (hG i A.μ0 _)).trans ?_)
    refine ((LinearMap.map_smul _ ph _).symm.trans (congrArg _ hy)).trans ((LinearMap.map_smul _ ρ _).trans ?_)
    exact congrArg (ρ • ·) (adForm_goodOp hU i y).symm
  have h3 : (R.FW i).j (sg0 D A) y₁ = ρ • (R.FW i).j (sg0 D A) (GlobalTheory.OntoChain.goodOp R i y) :=
    (hHW i _).1 (h2.trans ((R.HW i (sg0 D A)).e.map_smul ρ _).symm)
  have h4 : (R.FW i).j (sg0 D A) y₁ ≠ 0 := fun h0 => by
    have h5 : adForm R i y₁ = 0 := (congrArg (R.HW i (sg0 D A)).e h0).trans (map_zero _)
    exact hne ((hHW i _).1 (((smul_eq_zero.1 (h1.trans h5)).resolve_left hph).trans (map_zero _).symm))
  exact ratio_of_j hU h3 h4

end Descent

variable (R) in

def BaseLiftNeZero : Prop := ∀ i, ∃ x₀ : A.fam.amb.FL i A.μ0, R.thG i A.μ0 (R.jV i A.μ0 x₀) ≠ 0

variable {F : Face D A} {ph : Fin D.R.m → ℂ}

variable (T R κ v₀) in

def SeriesIdentity (i : Fin D.R.m) : Prop :=
  ∀ O₀ : OMDat T.toCore R i T0 id, O₀.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O₀.s0) →
    ∃ cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ,
      ∀ O : OMDat T.toCore R i T0 id, O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) →
        (∃ u : ℂ, SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1) ∧ ∀ t x, ∃ f ∈ cuspOf O (κ i), IsCls O t x f

theorem rational_of_series (hHW : R.models_HW) (hmem : R.thP_thF_mem) (hG : R.thP_thG) (fw : FWTie T R κ v₀) (hU : R.LUnif)
    {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} (hQ : QGuard R) (hrow : OneMapRowR T R κ v₀ O ph i)
    (hL : PinsOverL T R κ v₀ i) (hS : SeriesIdentity T R κ v₀ i) (hne : BaseLiftNeZero R) (t : T0) (x₀ : A.fam.amb.FL i t) :
    ∃ y, adForm R i y = ph i • R.thF i t (jVx R i t x₀) := by
  refine Classical.byContradiction fun hn => ?_
  obtain ⟨O₁, -, hP₁, h₁⟩ := hrow.2 hQ
  obtain ⟨O₂, hF, hP₂⟩ := hL
  obtain ⟨cc, hcc⟩ := hS O₁ hP₁
  obtain ⟨⟨u₁, s₁⟩, -⟩ := hcc O₁ hP₁
  obtain ⟨⟨u₂, s₂⟩, hex⟩ := hcc O₂ hP₂
  have key := rational_upTo (O := O₁) (O' := O₂) fw hHW hmem hU hP₁ h₁ hF hP₂ s₁ s₂ hex
  obtain ⟨a, ha⟩ := ratio_rational (O := O₁) fw hHW hU hG
    (norm_ne_zero_iff.1 (h₁.2.1.2.2.2.2.1.trans_ne one_ne_zero)) h₁.2.2 (key A.μ0) (hne i)
  obtain ⟨y, hy⟩ := key t x₀
  exact hn ⟨a • y, ((adForm_smul a y).trans (congrArg (· • adForm R i y) ha)).trans hy.symm⟩

theorem tieIn (fw : FWTie T R κ v₀) : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩

theorem seriesIdentity_of_core (hC : GlobalTheory.Hk3.Core R F) (fw : FWTie T R κ v₀) (hio : IoExt R) (i : Fin D.R.m) :
    SeriesIdentity T R κ v₀ i := fun O₀ h₀ => by
  have hI := GlobalTheory.chartIndependence_unconditional
  obtain ⟨cc, hcc⟩ := GlobalTheory.T.exists_frameConstants_of_characterisationCore hI D G Pl0 T0 A T R F κ v₀ hC (tieIn fw) i _ _ O₀ h₀
  exact ⟨cc, fun O h => ⟨(GlobalTheory.T.exists_adelicLift_eq_geometric_classSum_all_tuples hI D G Pl0 T0 A T R F κ v₀ hC (tieIn fw) hio i _ _ O h cc hcc).imp fun _ h => h.2,
    GlobalTheory.T.exists_cuspForm_classSum_normalisedData hI D G Pl0 T0 A T R F κ v₀ hC (tieIn fw) i _ _ O h⟩⟩

theorem allRational_of_core (hC : GlobalTheory.Hk3.Core R F) (fw : FWTie T R κ v₀) (hio : IoExt R) (hU : R.LUnif)
    {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} (hQ : QGuard R) (hrow : ∀ i, OneMapRowR T R κ v₀ O ph i)
    (hL : ∀ i, PinsOverL T R κ v₀ i) (hne : BaseLiftNeZero R) : AllRational R ph := fun i =>
  rational_of_series hC.models.HW hC.thP.thF_mem hC.thP.thG fw hU hQ (hrow i) (hL i) (seriesIdentity_of_core hC fw hio i) hne

theorem twistedRational_of_core (hC : GlobalTheory.Hk3.Core R F) (fw : FWTie T R κ v₀) (hio : IoExt R) (hU : R.LUnif)
    {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} (hQ : QGuard R) (hrow : ∀ i, OneMapRowR T R κ v₀ O ph i)
    (hL : ∀ i, PinsOverL T R κ v₀ i) (hne : BaseLiftNeZero R) : TwistedRational R F ph :=
  (allRational_of_core hC fw hio hU hQ hrow hL hne).twisted hC.models.HW hU

theorem twistedRational (hC : R.Char F) (fw : FWTie T R κ v₀) (hio : IoExt R) (hU : R.LUnif)
    {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} (hO : ∀ i, OMPins T R κ v₀ O i) (hQ : QGuard R)
    (hrow : ∀ i, OneMapRowR T R κ v₀ O ph i) (hK : CoverField T R) (hne : BaseLiftNeZero R) : TwistedRational R F ph :=
  twistedRational_of_core ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩ fw hio hU hQ hrow
    (fun i => GlobalTheory.T.exists_normalisedTupleData_over_coefficientField D G Pl0 T0 A T R F κ v₀ O i hC ⟨fw⟩ (hO i) hQ hK) hne

end GlobalTheory.TwistedClassSum
