import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CXiValIff
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SecBCAndCuspBC
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ActLevAndActBC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlaceExtensionValues
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicCuspFormAutomorphicBoundedSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicLinearIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsSpanOfOnto
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelFormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelMapExtensionStatement

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.OneMapTuples

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Algebra

theorem ratio_mem {K C Y : Type} [Field K] [AddCommGroup C] [Module K C] [FiniteDimensional K C] [AddCommGroup Y] [Module ℂ Y]
    {σ : K →+* ℂ} (Φ : C →ₛₗ[σ] Y)
    (hind : ∀ (m : ℕ) (b : Fin m → C), LinearIndependent K b → LinearIndependent ℂ fun j => Φ (b j))
    (K' : IntermediateField ℚ ℂ) (hσ : ∀ a, σ a ∈ K') {m m' : ℕ} (as : Fin m → ℂ) (fs : Fin m → C) (as' : Fin m' → ℂ)
    (fs' : Fin m' → C) (ha : ∀ j, as j ∈ K') (ha' : ∀ j, as' j ∈ K') (ρ : ℂ)
    (h : ∑ j, as j • Φ (fs j) = ρ • ∑ j, as' j • Φ (fs' j)) (h0 : ∑ j, as j • Φ (fs j) ≠ 0) : ρ ∈ K' := by
  classical
  let b := Module.finBasis K C
  have key : ∀ {m : ℕ} (as : Fin m → ℂ) (fs : Fin m → C), (∀ j, as j ∈ K') →
      ∃ s : Fin (Module.finrank K C) → ℂ, (∀ l, s l ∈ K') ∧ ∑ j, as j • Φ (fs j) = ∑ l, s l • Φ (b l) := by
    intro m as fs ha
    refine ⟨fun l => ∑ j, as j * σ (b.repr (fs j) l), fun l => sum_mem fun j _ => mul_mem (ha j) (hσ _), ?_⟩
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← b.sum_repr (fs j), map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smulₛₗ, smul_smul]
  obtain ⟨s, hs, e⟩ := key as fs ha
  obtain ⟨s', hs', e'⟩ := key as' fs' ha'
  rw [e] at h0
  rw [e, e'] at h
  obtain ⟨l, hl⟩ : ∃ l, s l ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h0 (by simp [hn])
  have h1 : ∑ l, (s l - ρ * s' l) • Φ (b l) = 0 := by
    simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, h, sub_self]
  have h2 := sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (hind _ b b.linearIndependent) _ h1 l)
  have h3 : s' l ≠ 0 := fun h => hl (by rw [h2, h, mul_zero])
  have h4 : ρ = s l / s' l := by rw [h2, mul_div_cancel_right₀ _ h3]
  rw [h4]
  exact div_mem (hs l) (hs' l)

theorem eq_zero_of_out {W : HSp D} (Φ : GA D W → ℂ) (hΦ : ∀ γ ∈ GQ W, ∀ g, Φ (γ * g) = Φ g) (k : GA D W)
    (h : ∀ q : AutQ W, Φ (q.out * k) = 0) : Φ = 0 := by
  funext g
  let q : AutQ W := Quotient.mk _ (g * k⁻¹)
  have hr : g * k⁻¹ * q.out⁻¹ ∈ GQ W := QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq q))
  have := hΦ _ hr (q.out * k)
  rw [h q, show g * k⁻¹ * q.out⁻¹ * (q.out * k) = g by group] at this
  exact this

theorem exists_coef_ext {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (ι : K →+* K') (hσ : σ'.comp ι = σ)
    {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W] (c₀ : VV K lam →ₛₗ[σ] W) :
    ∃ c' : VV K' lam →ₛₗ[σ'] W, ∀ v : VV K lam, ∃ v' : VV K' lam,
      (v' : Pol K' I n) = MvPolynomial.map ι (v : Pol K I n) ∧ c' v' = c₀ v := by
  classical
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (VV K lam).subtype (Submodule.ker_subtype _)
  letI : Module K' W := Module.compHom W σ'
  let g : Pol K' I n →ₗ[K'] W := (MvPolynomial.basisMonomials _ K').constr K' fun m => c₀ (π (MvPolynomial.monomial m 1))
  have hg : ∀ P : Pol K I n, g (MvPolynomial.map ι P) = c₀ (π P) := fun P => by
    induction P using MvPolynomial.induction_on' with
    | monomial m a =>
      have e1 : MvPolynomial.map ι (MvPolynomial.monomial m a) = ι a • MvPolynomial.basisMonomials _ K' m := by
        simp [MvPolynomial.smul_monomial]
      have e2 : MvPolynomial.monomial m a = a • MvPolynomial.monomial m (1 : K) := by simp [MvPolynomial.smul_monomial]
      rw [e1, map_smul, Module.Basis.constr_basis, e2, map_smul, map_smulₛₗ, ← RingHom.congr_fun hσ a]
      rfl
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  refine ⟨{ toFun := fun v => g v, map_add' := fun x y => g.map_add _ _, map_smul' := fun a x => g.map_smul a _ },
    fun v => ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV ι lam _ v.2⟩, rfl, (hg v).trans (congrArg c₀ (LinearMap.congr_fun hπ v))⟩⟩

end Algebra

section Read

variable (T : CoreJ D) (j : ℕ) {W : HSp D} (hV : T.V j T.σ₀ = W)

def psi : T.R j →ₛₗ[T.σ₀] (GA D W → ℂ) :=
  (adel W (castDict hV (T.dict j T.σ₀))
    (muPin W (castDict hV (T.dict j T.σ₀)) (castDict hV (T.mu j T.σ₀)) (T.cE j T.σ₀))).comp (rdU (T.U j T.σ₀))

theorem psi_inv (hT : LawsJ T) (hj : InR D j) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom a n) {f : T.R j}
    (hf : f ∈ T.cuspA j a n) : ∀ γ ∈ GQ W, ∀ g, psi T j hV f (γ * g) = psi T j hV f g := by
  subst hV
  intro γ hγ g
  have h := (GlobalTheory.AdelicCusp.phiJ_automorphic D T hT j hj _ T.good_σ₀ a n hD f hf).1 γ hγ g
  have hl : ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  exact mul_left_cancel₀ hl h

theorem psi_indep (hT : LawsJ T) (hj : InR D j) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom a n) (m : ℕ)
    (b : Fin m → T.cuspA j a n) (hb : LinearIndependent T.Q.c.F b) :
    LinearIndependent ℂ fun l => psi T j hV (b l : T.R j) := by
  subst hV
  have h := (GlobalTheory.VolPairExists.adelic_linearIndependent D T hT j hj _ T.good_σ₀ a n hD).1 m b hb
  have e : ∀ f, T.phiJ j T.σ₀ a f = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) • psi T j rfl f := fun _ => rfl
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  refine h g ?_
  simp only [e, smul_comm (g _), ← Finset.smul_sum, hg, smul_zero]

def InForms (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (K' : IntermediateField ℚ ℂ) (Φ : GA D W → ℂ) : Prop :=
  ∃ (m : ℕ) (as : Fin m → ℂ) (fs : Fin m → T.cuspA j a n), (∀ l, as l ∈ K') ∧ Φ = ∑ l, as l • psi T j hV (fs l : T.R j)

variable {T j hV}

theorem InForms.inv (hT : LawsJ T) (hj : InR D j) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom a n)
    {K' : IntermediateField ℚ ℂ} {Φ : GA D W → ℂ} (h : InForms T j hV a n K' Φ) : ∀ γ ∈ GQ W, ∀ g, Φ (γ * g) = Φ g := by
  obtain ⟨m, as, fs, -, rfl⟩ := h
  intro γ hγ g
  simp only [Finset.sum_apply, Pi.smul_apply, psi_inv T j hV hT hj hD (fs _).2 γ hγ g]

theorem InForms.ratio (hT : LawsJ T) (hj : InR D j) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom a n)
    {K₀ K' : IntermediateField ℚ ℂ} (h0 : K₀ ≤ K') (hc : T.Q.c.F ≤ K') {Φ Φ' : GA D W → ℂ} (h : InForms T j hV a n K₀ Φ)
    (h' : InForms T j hV a n K' Φ') {ρ : ℂ} (e : Φ = ρ • Φ') (hne : Φ ≠ 0) : ρ ∈ K' := by
  obtain ⟨m, as, fs, ha, rfl⟩ := h
  obtain ⟨m', as', fs', ha', rfl⟩ := h'
  haveI : FiniteDimensional T.Q.c.F (T.cuspA j a n) := hT.cuspFD j hj a n hD
  exact ratio_mem ((psi T j hV).comp (T.cuspA j a n).subtype) (psi_indep T j hV hT hj hD) K' (fun x => hc x.2) as fs as' fs'
    (fun l => h0 (ha l)) ha' ρ e hne

end Read

section Data

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

abbrev chiG (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (g : G) : ℂ :=
  ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ)

theorem exists_read (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i) (hn : κ.n = (Vc D i).rank)
    (hE : O.EquivAt κ (T.cE ((i : ℕ) + 1) O.s0)) (hact : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c O.lev2)
    (k : G → GA D (Wc D i)) (hk : ∀ g, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (k g))
    {f : Rul (T.Q.Xo ((i : ℕ) + 1)) O.c'}
    (hf : f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (T.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank) :
    ∃ Φ, InForms T ((i : ℕ) + 1) hV (wtA κ) κ.n O.c'.F Φ ∧ ∀ z (q : AutQ (Wc D i)),
      T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 * rdQ O z f q = chiG R i z * Φ (q.out * k z) := by
  rw [← hn] at hf
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).2 _ (T.U ((i : ℕ) + 1)) _ _ f hf
  have hA := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hact).2
  refine ⟨_, ⟨m, fun l => (as l : ℂ), fun l => ⟨fs l, hfs l⟩, fun l => (as l).2, rfl⟩, fun z q => ?_⟩
  have h1 := rdU_unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c') (hA _ _ z m as fs f ((mem_cusp _ _ _ _ _ _).1 hf).1
    (fun l => ((mem_cusp _ _ _ _ _ _).1 (hfs l)).1) hBC)
  have h2 : ∀ l, O.phi (T.cE ((i : ℕ) + 1) O.s0) (actLev T.Q.c O.lev2 z (fs l)) q.out =
      chiG R i z * psi T ((i : ℕ) + 1) hV (fs l) (q.out * k z) := fun l => (hE z (k z) (hk z) (fs l) (hfs l)).2 q.out
  have h3 : rdQ O z f q = O.mu q.out * rdU (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) (actLev O.c' O.lev2 z f)
    (O.dict q.out).1 (O.dict q.out).2 := rfl
  rw [h3, h1]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm (chiG R i z), ← h2 l]
  show _ = (as l : ℂ) * (T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 * O.mu q.out *
    rdU (T.U ((i : ℕ) + 1) O.s0) (actLev T.Q.c O.lev2 z (fs l)) (O.dict q.out).1 (O.dict q.out).2)
  show _ * (_ * ((as l : ℂ) * _)) = _
  ring

end Data

section Change

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}

theorem isLev_scale {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (u : d.c₂.F) (hu : u ≠ 0) (h : d.IsLev) :
    ({ d with cδ := u • d.cδ } : DeltaDat Xo c n).IsLev := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := h
  have key : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra d.c₂.F k] (y : FrPt d.Xo₂ d.c₂ k),
      evR d.Xo₂ d.c₂ (u • d.cδ) y ≠ 0 := fun k _ _ _ y h0 => by
    have e := evR_sum_smul y (fun _ : Fin 1 => u) (fun _ => d.cδ)
    rw [Fin.sum_univ_one, Fin.sum_univ_one, h0] at e
    exact mul_ne_zero ((map_ne_zero _).2 hu) (l9 k y) e.symm
  exact ⟨l1, l2, l3, l4, l5, l6, l7, Submodule.smul_mem _ _ l8, key⟩

def scaleXi (u : O.c'.F) : OMDat C R i Tp tup :=
  { O with
    dδ := fun t => { O.dδ t with cδ := (O.dδ t).eF u • (O.dδ t).cδ }
    φ := O.φ, w := O.w, U₂ := O.U₂, dict₂ := O.dict₂ }

theorem xiConst_scaleXi (u : O.c'.F) {c0 : ℂ} (h : XiConst O ι x₀ c0) : XiConst (scaleXi O u) ι x₀ ((u : ℂ) * c0) := by
  intro t
  obtain ⟨h1, h2, g, e, F, ik, φ, th, h3, h4, h5⟩ := h t
  refine ⟨h1, h2, g, e, F, ik, φ, th, h3, h4, fun h γ hm => ?_⟩
  have h6 := h5 h γ hm
  show rdU (O.U₂ t) ((O.dδ t).eF u • (O.dδ t).cδ) (O.dict₂ t h).1 (O.dict₂ t h).2 = _
  rw [map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, h6, smul_eq_mul, mul_assoc]
  rfl

theorem pins_scaleXi (u : O.c'.F) (hu : u ≠ 0) {c0 : ℂ} (h : XiConst O ι x₀ c0) (hr : ∃ m : ℕ, 0 < m ∧ ((u : ℂ) * c0) ^ m = 1)
    (hP : O.Pins κ v₀ ι x₀) : (scaleXi O u).Pins κ v₀ ι x₀ := by
  refine ⟨hP.lift, hP.tuple, hP.act, hP.bad, hP.reps, hP.ep, hP.io, hP.w, fun t => ?_,
    ⟨_, hr, xiConst_scaleXi O u h⟩, hP.model₂⟩
  exact ⟨isLev_scale _ _ ((map_ne_zero _).2 hu) (hP.cov t).1, (hP.cov t).2⟩

set_option maxHeartbeats 1600000 in

theorem exists_retie {F : Face D A} (hR : R.Char F) (hP : O.Pins κ v₀ ι x₀)
    (lev : G → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La)
    (hlev : LevIs R i ι C.Q.l.M (Mfr C.Q.l) lev)
    (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c fun g => (lev g, LinearMap.id)) {gramR c0R c0L}
    (hT : Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L) :
    ∃ O' : OMDat C R i Tp tup, O'.c' = O.c' ∧ O'.Pins κ v₀ ι x₀ ∧ O'.lev = lev ∧ CoefficientBaseChange R i O'.jL (inC O'.c') (c0L i) O'.c0' := by
  classical
  obtain ⟨c1, hc1⟩ := exists_coef_ext (W := (R.cV i).W) O.jL hP.lift.field (lamV D i) (c0L i)
  choose h J' h1 h2 h3 h4 using fun t => (hP.tuple t).reps
  have hL : ThPinsR R i O.jL (inC O.c') v₀ c1 ι C.Q.l.M (Mfr C.Q.l) lev :=
    ⟨hP.lift.field, hP.lift.std, hP.lift.v0, ⟨_, _, _, hT, hc1⟩, hlev⟩
  have h0 : ∀ t y, (∀ k, (R.HV i (tup t)).e y (fin _ (h t k)) = 0) → onQ (Wc D i) (R.thF i (tup t) y v₀) = 0 := fun t y hy => by
    have e1 := h3 t y 0 fun k => (hy k).trans (map_zero _).symm
    have e2 := h3 t 0 0 fun k => by rw [map_zero]; exact (map_zero _).symm
    rw [← e1, e2, map_zero]
    rfl
  refine ⟨{ O with
    c0' := c1, lev := lev
    thAd := fun t x => if hx : ∃ y, Place R i (tup t) (h t) c1 y x then onQ (Wc D i) (R.thF i (tup t) hx.choose v₀) else 0
    Plc := fun t x => ∃ x₀, Place R i (tup t) (h t) c1 (jVx R i (tup t) x₀) x }, rfl,
    ⟨hL, fun t => ⟨⟨h t, J' t, h1 t, GlobalTheory.RationalValues.placeEx_of_char R F hR i _ _ hL _ _, fun y x hy => ?_, fun x => Iff.rfl⟩,
      (hP.tuple t).B, (hP.tuple t).xi, (hP.tuple t).phi, (hP.tuple t).half⟩,
      ⟨hact, (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hact).1⟩,
      hP.bad, hP.reps, hP.ep, hP.io, hP.w, hP.cov, hP.cxi, hP.model₂⟩, rfl, hc1⟩
  have hx : ∃ y, Place R i (tup t) (h t) c1 y x := ⟨y, hy⟩
  refine (dif_pos hx).trans ?_
  have h5 := h0 t (hx.choose - y) fun k => by
    rw [map_sub, Pi.sub_apply, hx.choose_spec k, hy k, sub_self]
  rw [map_sub] at h5
  exact sub_eq_zero.1 h5

end Change

section Compare

theorem eq_smul_of_out {W : HSp D} {θ e lam : AutQ W → ℂ} (hlam : ∀ q, lam q ≠ 0) {Φ Φ' : GA D W → ℂ}
    (hΦ : ∀ γ ∈ GQ W, ∀ g, Φ (γ * g) = Φ g) (hΦ' : ∀ γ ∈ GQ W, ∀ g, Φ' (γ * g) = Φ' g) (k : GA D W) {a b s s' c : ℂ}
    (hc : c ≠ 0) (hs : s ≠ 0) (hb : b ≠ 0) (h : ∀ q, a * (e q * θ q) = s * lam q * (c * Φ (q.out * k)))
    (h' : ∀ q, b * (e q * θ q) = s' * lam q * (c * Φ' (q.out * k))) : Φ = (a * s' / (b * s)) • Φ' := by
  refine sub_eq_zero.1 (eq_zero_of_out _ (fun γ hγ g => ?_) k fun q => ?_)
  · simp only [Pi.sub_apply, Pi.smul_apply, hΦ γ hγ g, hΦ' γ hγ g]
  · have h1 : (lam q * c) * (b * s * Φ (q.out * k) - a * s' * Φ' (q.out * k)) = 0 := by
      linear_combination a * h' q - b * h q
    have h2 := (mul_eq_zero.1 h1).resolve_left (mul_ne_zero (hlam q) hc)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination h2

theorem ne_zero_of_root {u : ℂ} (h : ∃ m : ℕ, 0 < m ∧ u ^ m = 1) : u ≠ 0 := by
  obtain ⟨m, hm, h⟩ := h
  rintro rfl
  rw [zero_pow hm.ne'] at h
  exact zero_ne_one h

theorem root_mul_div {u v w : ℂ} (hu : ∃ m : ℕ, 0 < m ∧ u ^ m = 1) (hv : ∃ m : ℕ, 0 < m ∧ v ^ m = 1)
    (hw : ∃ m : ℕ, 0 < m ∧ w ^ m = 1) : ∃ m : ℕ, 0 < m ∧ (u * (v / w)) ^ m = 1 := by
  obtain ⟨a, ha, h1⟩ := hu
  obtain ⟨b, hb, h2⟩ := hv
  obtain ⟨c, hc, h3⟩ := hw
  refine ⟨a * b * c, by positivity, ?_⟩
  have e1 : u ^ (a * b * c) = 1 := by rw [mul_assoc, pow_mul, h1, one_pow]
  have e2 : v ^ (a * b * c) = 1 := by rw [mul_comm a, mul_assoc, pow_mul, h2, one_pow]
  have e3 : w ^ (a * b * c) = 1 := by rw [mul_comm, pow_mul, h3, one_pow]
  rw [mul_pow, div_pow, e1, e2, e3, div_one, one_mul]

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}

theorem lift_of_plc {Tp : Type} {tup : Tp → T0} {O : OMDat T.toCore R i Tp tup} (hP : O.Pins κ v₀ ι x₀) {t : Tp}
    {x : O.Cl' t → VsV D i O.c'.F} (hx : O.Plc t x) : ∃ y, O.thAd t x = liftQ R i v₀ (tup t) y := by
  obtain ⟨h, J', -, -, h3, h4⟩ := (hP.tuple t).reps
  obtain ⟨y, hy⟩ := (h4 x).1 hx
  exact ⟨y, h3 _ x hy⟩

theorem plc_of_lift {Tp : Type} {tup : Tp → T0} {O : OMDat T.toCore R i Tp tup} (hP : O.Pins κ v₀ ι x₀) (t : Tp)
    (y : A.fam.amb.FL i (tup t)) : ∃ x, O.Plc t x ∧ O.thAd t x = liftQ R i v₀ (tup t) y := by
  obtain ⟨h, J', -, h2, h3, h4⟩ := (hP.tuple t).reps
  obtain ⟨x, hx⟩ := h2 y
  exact ⟨x, (h4 x).2 ⟨y, hx⟩, h3 _ x hx⟩

theorem chiG_ne (g : G) : chiG R i g ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _

abbrev cQ (T : CoreJ D) (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i) (q : AutQ (Wc D i)) : ℂ :=
  T.cE ((i : ℕ) + 1) T.σ₀ (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) q.out).1

set_option maxHeartbeats 1000000 in

theorem exists_base (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i) (hn : κ.n = (Vc D i).rank)
    {O : OMDat T.toCore R i Unit fun _ => A.μ0} (hP : O.Pins κ v₀ ι x₀) {ph : ℂ}
    (hrow : O.OneMapOf κ v₀ (T.cE ((i : ℕ) + 1) O.s0) ph)
    (k : G → GA D (Wc D i)) (hk : ∀ g, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (k g))
    {lam : AutQ (Wc D i) → ℂ} {z₀ : G} {c0 : ℂ} (hid : PtIdent O κ lam z₀ c0) :
    ∃ z₁ ∈ Subgroup.center G, ∃ s₁ s₀ : ℂ, s₁ ∈ D.what₂.embLL.toRatAlgHom.fieldRange ∧ (∃ m : ℕ, 0 < m ∧ s₁ ^ m = 1) ∧
      s₀ ∈ D.what₂.embLL.toRatAlgHom.fieldRange ∧ (∃ m : ℕ, 0 < m ∧ s₀ ^ m = 1) ∧
      ∀ y, ∃ Φ, InForms T ((i : ℕ) + 1) hV (wtA κ) κ.n O.c'.F Φ ∧
        (∀ q, ph * liftQ R i v₀ A.μ0 y q =
          s₁ * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * (chiG R i z₁ * Φ (q.out * k z₁))) ∧
        ∀ q, c0 * (cQ T i hV q * liftQ R i v₀ A.μ0 y q) = s₀ * lam q * (chiG R i z₀ * Φ (q.out * k z₀)) := by
  obtain ⟨hE, ⟨-, -, -, -, -, z₁, hz₁, h1⟩, -⟩ := hrow
  obtain ⟨s₁, a1, a2, h1⟩ := h1 ()
  obtain ⟨s₀, b1, b2, h0⟩ := hid ()
  refine ⟨z₁, hz₁, s₁, s₀, a1, a2, b1, b2, fun y => ?_⟩
  obtain ⟨x, hx, e⟩ := plc_of_lift hP () y
  obtain ⟨⟨f, hf, hf'⟩, h2⟩ := h1 x hx
  have hs := ((mem_cusp _ _ _ _ _ _).1 hf).1
  obtain ⟨Φ, hΦ, h3⟩ := exists_read O κ hV hn hE hP.act.1 k hk hf
  refine ⟨Φ, hΦ, fun q => ?_, fun q => ?_⟩
  · have h4 : ph * O.thAd () x q = s₁ * T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 *
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * rdQ O z₁ f q := h2 f hs hf' q
    rw [← h3 z₁ q, ← e, h4]
    ring
  · have h4 := h0 x hx f hs hf' q
    have h5 : cQ T i hV q = T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 := rfl
    rw [← h3 z₀ q, ← e, h5, mul_left_comm, h4]
    ring

set_option maxHeartbeats 1000000 in

theorem exists_transfer (hT : LawsJ T) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i) (hn : κ.n = (Vc D i).rank)
    {Tp : Type} {tup : Tp → T0} {O : OMDat T.toCore R i Tp tup} (hP : O.Pins κ v₀ ι x₀)
    (hE : O.EquivAt κ (T.cE ((i : ℕ) + 1) O.s0))
    (k : G → GA D (Wc D i)) (hk : ∀ g, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (k g))
    {lam : AutQ (Wc D i) → ℂ} (hlam : ∀ q, lam q ≠ 0) {z₀ : G} {c0 : ℂ} (hc0 : c0 ≠ 0) (hid : PtIdent O κ lam z₀ c0) (t : Tp) :
    ∃ s : ℂ, s ∈ D.what₂.embLL.toRatAlgHom.fieldRange ∧ (∃ m : ℕ, 0 < m ∧ s ^ m = 1) ∧ ∀ x, O.Plc t x →
      ∀ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (T.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank, IsCls O t x f →
      ∃ Φ', InForms T ((i : ℕ) + 1) hV (wtA κ) κ.n O.c'.F Φ' ∧
        (∀ z (q : AutQ (Wc D i)), cQ T i hV q * rdQ O z f q = chiG R i z * Φ' (q.out * k z)) ∧
        ∀ (Φ : GA D (Wc D i) → ℂ) (a s₀ : ℂ), s₀ ≠ 0 → (∀ γ ∈ GQ (Wc D i), ∀ g, Φ (γ * g) = Φ g) →
          (∀ q, a * (cQ T i hV q * O.thAd t x q) = s₀ * lam q * (chiG R i z₀ * Φ (q.out * k z₀))) →
          Φ = (a * s / (c0 * s₀)) • Φ' := by
  obtain ⟨s, b1, b2, h0⟩ := hid t
  refine ⟨s, b1, b2, fun x hx f hf hf' => ?_⟩
  obtain ⟨Φ', hΦ, h3⟩ := exists_read O κ hV hn hE hP.act.1 k hk hf
  refine ⟨Φ', hΦ, h3, fun Φ a s₀ hs hinv h => eq_smul_of_out hlam hinv
    (hΦ.inv hT ⟨Nat.le_add_left _ _, i.2⟩ (dom_wtA κ)) (k z₀) (chiG_ne z₀) hs hc0 h fun q => ?_⟩
  have h4 := h0 x hx f ((mem_cusp _ _ _ _ _ _).1 hf).1 hf' q
  have h5 : cQ T i hV q = T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 := rfl
  rw [← h3 z₀ q, h5, mul_left_comm, h4]
  ring

theorem span_read {W : HSp D} {I : Type} (θ : I → AutQ W → ℂ) (a b c d : AutQ W → ℂ) (k k' : GA D W)
    (h : ∀ y, ∃ Φ : GA D W → ℂ, (∀ γ ∈ GQ W, ∀ g, Φ (γ * g) = Φ g) ∧ (∀ q, a q * θ y q = b q * Φ (q.out * k)) ∧
      ∀ q, c q * θ y q = d q * Φ (q.out * k')) {w : AutQ W → ℂ} (hw : w ∈ Submodule.span ℂ (Set.range θ)) :
    ∃ Φ : GA D W → ℂ, (∀ γ ∈ GQ W, ∀ g, Φ (γ * g) = Φ g) ∧ (∀ q, a q * w q = b q * Φ (q.out * k)) ∧
      ∀ q, c q * w q = d q * Φ (q.out * k') := by
  induction hw using Submodule.span_induction with
  | mem w hw => obtain ⟨y, rfl⟩ := hw; exact h y
  | zero => exact ⟨0, fun _ _ _ => rfl, fun q => by simp, fun q => by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨Φ, h1, h2, h3⟩ := hu
    obtain ⟨Ψ, g1, g2, g3⟩ := hv
    refine ⟨Φ + Ψ, fun γ hγ g => by simp only [Pi.add_apply, h1 γ hγ g, g1 γ hγ g], fun q => ?_, fun q => ?_⟩
    · simp only [Pi.add_apply, mul_add, h2 q, g2 q]
    · simp only [Pi.add_apply, mul_add, h3 q, g3 q]
  | smul r u _ hu =>
    obtain ⟨Φ, h1, h2, h3⟩ := hu
    refine ⟨r • Φ, fun γ hγ g => by simp only [Pi.smul_apply, h1 γ hγ g], fun q => ?_, fun q => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; linear_combination r * h2 q
    · simp only [Pi.smul_apply, smul_eq_mul]; linear_combination r * h3 q

set_option maxHeartbeats 2000000 in

theorem oneMapOf_of_ptIdent (hT : LawsJ T) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i) (hn : κ.n = (Vc D i).rank)
    {O : OMDat T.toCore R i Unit fun _ => A.μ0} (hP : O.Pins κ v₀ ι x₀) {ph : ℂ}
    (hrow : O.OneMapOf κ v₀ (T.cE ((i : ℕ) + 1) O.s0) ph)
    {O' : OMDat T.toCore R i T0 id} (hle : D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F) (hP' : O'.Pins κ v₀ ι x₀)
    (hlev : O'.lev = O.lev) (hex : ClsEx O' κ) (hsp : LiftsSpan R i v₀)
    {lam : AutQ (Wc D i) → ℂ} (hlam : ∀ q, lam q ≠ 0) {z₀ : G} {c0 c0' : ℂ} (hc0 : c0 ≠ 0) (hc0' : c0' ≠ 0)
    (hid : PtIdent O κ lam z₀ c0) (hid' : PtIdent O' κ lam z₀ c0') (hc : c0' = c0 ∨ ∀ y, liftQ R i v₀ A.μ0 y = 0) :
    O'.OneMapOf κ v₀ (T.cE ((i : ℕ) + 1) O'.s0) ph := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hE : O'.EquivAt κ (T.cE ((i : ℕ) + 1) O'.s0) := by
    have h2 : O'.lev2 = O.lev2 := by funext g; simp only [OMDat.lev2, hlev]
    have h1 := hrow.1
    unfold OMDat.EquivAt at h1 ⊢
    rw [h2]
    exact h1
  choose k hk _ using hP.lift.lev
  obtain ⟨z₁, hz₁, s₁, s₀, a1, a2, b1, b2, hb⟩ := exists_base hV hn hP hrow k hk hid
  refine ⟨hE, ⟨hle, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O'.hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O'.hle _ _ hP'.act.1).2, hrow.2.1.2.2.2.1, hrow.2.1.2.2.2.2.1, z₁, hz₁,
    fun t => ?_⟩, hrow.2.2⟩
  obtain ⟨s, c1, c2, ht⟩ := exists_transfer hT hV hn hP' hE k hk hlam hc0' hid' t
  refine ⟨s₁ * (s / s₀), mul_mem a1 (div_mem c1 b1), root_mul_div a2 c2 b2, fun x hx => ?_⟩
  obtain ⟨f, hf, hf', hu⟩ := hex t x hx
  refine ⟨⟨f, hf, hf'⟩, fun f' h1 h2 q => ?_⟩
  obtain rfl := hu f' h1 h2
  obtain ⟨Φ', -, r1, r2⟩ := ht x hx f' hf hf'
  obtain ⟨y, hy⟩ := lift_of_plc hP' hx
  obtain ⟨Φ, hinv, e1, e0⟩ := span_read (liftQ R i v₀ A.μ0) (fun _ => ph)
    (fun _ => s₁ * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * chiG R i z₁) (fun q => c0 * cQ T i hV q)
    (fun q => s₀ * lam q * chiG R i z₀) (k z₁) (k z₀)
    (fun y => (hb y).imp fun Φ h => ⟨h.1.inv hT hj (dom_wtA κ), fun q => (h.2.1 q).trans (by ring),
      fun q => (mul_assoc _ _ _).trans ((h.2.2 q).trans (by ring))⟩) (hsp t y)
  have hs₀ := ne_zero_of_root b2
  have e2 := r2 Φ c0 s₀ hs₀ hinv fun q => by
    rw [hy, ← mul_assoc]
    exact (e0 q).trans (by ring)
  have e3 : ph * O'.thAd t x q = s₁ * (s / s₀) * cQ T i hV q * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
      rdQ O' z₁ f' q * (c0 / c0') := by
    have e4 := e1 q
    rw [e2, Pi.smul_apply, smul_eq_mul] at e4
    have e5 := r1 z₁ q
    rw [hy]
    refine e4.trans ?_
    linear_combination (-(s₁ * (s / s₀) * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * (c0 / c0'))) * e5
  show ph * O'.thAd t x q = s₁ * (s / s₀) * cQ T i hV q * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * rdQ O' z₁ f' q
  rcases hc with hc | hc
  · rw [e3, hc, div_self hc0, mul_one]
  · have h0 : O'.thAd t x = 0 := by
      have h3 := hsp t y
      rw [show Submodule.span ℂ (Set.range (liftQ R i v₀ A.μ0)) = ⊥ from
        Submodule.span_eq_bot.2 (by rintro _ ⟨y, rfl⟩; exact hc y)] at h3
      exact hy.trans h3
    rw [h0, Pi.zero_apply, mul_zero] at e3 ⊢
    exact ((mul_eq_zero.1 e3.symm).resolve_right (div_ne_zero hc0 hc0')).symm

set_option maxHeartbeats 2000000 in

theorem const_ratio_mem (hT : LawsJ T) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i) (hn : κ.n = (Vc D i).rank)
    {O : OMDat T.toCore R i Unit fun _ => A.μ0} (hF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange)
    (hP : O.Pins κ v₀ ι x₀) {ph : ℂ} (hrow : O.OneMapOf κ v₀ (T.cE ((i : ℕ) + 1) O.s0) ph)
    {O' : OMDat T.toCore R i T0 id} (hle : D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F) (hP' : O'.Pins κ v₀ ι x₀)
    (hlev : O'.lev = O.lev) (hex : ClsEx O' κ)
    {lam : AutQ (Wc D i) → ℂ} (hlam : ∀ q, lam q ≠ 0) {z₀ : G} {c0 c0' : ℂ} (hc0' : c0' ≠ 0)
    (hid : PtIdent O κ lam z₀ c0) (hid' : PtIdent O' κ lam z₀ c0') {y : A.fam.amb.FL i A.μ0} (hy : liftQ R i v₀ A.μ0 y ≠ 0) :
    c0 / c0' ∈ O'.c'.F := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hE : O'.EquivAt κ (T.cE ((i : ℕ) + 1) O'.s0) := by
    have h2 : O'.lev2 = O.lev2 := by funext g; simp only [OMDat.lev2, hlev]
    have h1 := hrow.1
    unfold OMDat.EquivAt at h1 ⊢
    rw [h2]
    exact h1
  choose k hk _ using hP.lift.lev
  obtain ⟨z₁, -, s₁, s₀, -, -, b1, b2, hb⟩ := exists_base hV hn hP hrow k hk hid
  obtain ⟨s, c1, c2, ht⟩ := exists_transfer hT hV hn hP' hE k hk hlam hc0' hid' A.μ0
  obtain ⟨x, hx, e⟩ := plc_of_lift hP' A.μ0 y
  obtain ⟨f, hf, hf', -⟩ := hex _ x hx
  obtain ⟨Φ', hΦ', -, r2⟩ := ht x hx f hf hf'
  obtain ⟨Φ, hΦ, e1, e0⟩ := hb y
  have hs₀ := ne_zero_of_root b2
  have hs := ne_zero_of_root c2
  have e2 := r2 Φ c0 s₀ hs₀ (hΦ.inv hT hj (dom_wtA κ)) fun q => by rw [e]; exact e0 q
  have hph : ph ≠ 0 := fun h => by
    have := hrow.2.1.2.2.2.2.1
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hne : Φ ≠ 0 := fun h => hy (funext fun q => by
    have := e1 q
    rw [h, Pi.zero_apply, mul_zero, mul_zero] at this
    exact (mul_eq_zero.1 this).resolve_left hph)
  have h1 := hΦ.ratio hT hj (dom_wtA κ) (hF.le.trans hle) O'.hle hΦ' e2 hne
  have h2 : c0 / c0' = c0 * s / (c0' * s₀) * (s₀ / s) := by field_simp
  rw [h2]
  exact mul_mem h1 (div_mem (hle b1) (hle c1))

end Compare

end GlobalTheory.OneMapTuples
