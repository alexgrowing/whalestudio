import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsIteratedQuotientIntegralFinsetSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepAdelicIntegralFiniteTwistPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Vac Moves InK Lat Pl latV idAt idOff intAt grpAt grpOff MxAt hand0 SplitPt extS extT)

noncomputable section
namespace GlobalTheory.QLawPf

variable {D : D7} {c : Comm D} {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle}

section Reps
variable (Q : QAt v χ)

def repS (j d : ℕ) (h : j + d = Q.s) : Finset (GL (Q.X j ⊕ Fin (d + 1)) Q.k) :=
  Finset.univ.map ⟨Q.rep j d h, Set.injOn_univ.1 (Q.rep_bij j d h).injOn⟩

theorem mem_repS {j d : ℕ} {h : j + d = Q.s} {g} : g ∈ repS Q j d h ↔ g ∈ Q.A j d h := by
  simp only [repS, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨a, rfl⟩
    exact (Q.rep_bij j d h).mapsTo (Set.mem_univ a)
  · intro hg
    obtain ⟨a, -, e⟩ := (Q.rep_bij j d h).surjOn hg
    exact ⟨a, e⟩

def repE (j d : ℕ) (h : j + d = Q.s) : Q.Ch j ≃ repS Q j d h :=
  Equiv.ofBijective (fun a => ⟨Q.rep j d h a, (mem_repS Q).2 ((Q.rep_bij j d h).mapsTo (Set.mem_univ a))⟩)
    ⟨fun _ _ e => Set.injOn_univ.1 (Q.rep_bij j d h).injOn (congrArg Subtype.val e), fun g => by
      obtain ⟨a, -, e⟩ := (Q.rep_bij j d h).surjOn ((mem_repS Q).1 g.2)
      exact ⟨a, Subtype.ext e⟩⟩

theorem rep_symm {j d : ℕ} {h : j + d = Q.s} (g : repS Q j d h) : Q.rep j d h ((repE Q j d h).symm g) = g.1 :=
  congrArg Subtype.val ((repE Q j d h).apply_symm_apply g)

theorem covers (j d : ℕ) (h : j + 1 + d = Q.s) {g} (hg : g ∈ Q.A j (d + 1) (by omega)) :
    Covers 1 (Q.T.lev (j + 1) (d + 1) (by omega)).J (repS Q (j + 1) d h)
      fun x => GlobalTheory.StepData.flat Q.ψk Q.ν (Q.T.mu (j + 1)) (Q.T.Phi j (d + 1) (by omega)) g x := by
  have H := Q.reps.bij j d h
  refine ⟨H.injOn.mono fun x hx => (mem_repS Q).1 hx, fun x hx => ?_⟩
  obtain ⟨t, ht, e⟩ := H.surjOn (Set.mem_biUnion hg ⟨x, rfl, hx⟩)
  exact ⟨t, (mem_repS Q).2 ht, e.symm⟩

theorem entry_eq (j d : ℕ) (h : j + 1 + d = Q.s) (g g') : Q.T.entry Q.ψk Q.ν j d h g g' =
    xi Q.ψk Q.ν (Q.T.mu (j + 1)) (Q.T.Phi j (d + 1) (by omega)) (Q.T.lev (j + 1) (d + 1) (by omega)).J 1 g g' := by
  unfold GlobalTheory.StepData.Chain.entry
  rw [Q.bas]

def oneC (j ρ : ℕ) (hρ : j + 2 * ρ + 2 = D.R.m) (d : ℕ) (h : j + d = Q.s) (α : Q.Ch j) : GL (Q.X j ⊕ Fin (d + 1)) Q.k →₀ ℂ :=
  (Q.εL_at j ρ hρ d h α).choose

theorem oneC_spec (j ρ : ℕ) (hρ : j + 2 * ρ + 2 = D.R.m) (d : ℕ) (h : j + d = Q.s) (α : Q.Ch j) :
    IsOneComb Q.ψk Q.ν (ρ + 1) (Q.T.lev j (d + 1) (by omega)) (Q.rep j d h α) (oneC Q j ρ hρ d h α) ∧
      Q.εL j α = (oneC Q j ρ hρ d h α).mapDomain (Q.gl j (d + 1) (by omega)) :=
  (Q.εL_at j ρ hρ d h α).choose_spec

end Reps

structure Chars (t : Tup c) (χ : ℕ → (AE D)ˣ →* Circle) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (χz : (AE D)ˣ →* Circle) : Prop where
  V₁ : (t.sBF j (σ + 1) h).χV = χ j * χz
  W₁ : (t.sBF j (σ + 1) h).χW = χ j
  V₂ : (t.sFB j σ h).χV = χ (j + 1)
  W₂ : (t.sFB j σ h).χW = χ (j + 1) * χz
  wa : IsWeilDatumO c.ψ _ _ (χ j) (χ j) (t.kom j)
  wb : IsWeilDatumO c.ψ _ _ (χ (j + 1)) (χ (j + 1)) (t.kom (j + 1))

variable {t : Tup c} {j σ : ℕ} {h : j + 2 * (σ + 1) + 2 = D.R.m} {χz : (AE D)ˣ →* Circle}

@[reducible] def dblOf (H : Chars t χ j σ h χz) : Dbl2 c.ψ σ where
  B := c.B j (σ + 1) h
  J := c.J j (σ + 1) h
  B' := c.B (j + 1 + 1) σ (idx_step h)
  s₁ := t.sBF j (σ + 1) h
  s₂ := t.sFB j σ h
  l := c.lnk j σ h
  vL := c.vL j σ h
  χ₁ := χ j
  χ₂ := χ (j + 1)
  χz := χz
  oma := t.kom j
  omb := t.kom (j + 1)
  V₁ := H.V₁
  W₁ := H.W₁
  V₂ := H.V₂
  W₂ := H.W₂
  weila := H.wa
  weilb := H.wb

theorem handIsLift (H : Chars t χ j σ h χz) (hW : WeilOK (t := t) v) : HandIsLift (dblOf H) := by
  intro φ Ξ₁ Ξ₂ hφ h₁ h₂
  obtain ⟨χA, χA', χz, omz, omz', e1, e2, w1, w2, w3, w4⟩ := hW.mid j σ h
  funext g
  exact (GlobalTheory.Unf.Contr.contrLaw D c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) χA χA' χz (t.kom j) omz
    (t.kom (j + 1)) omz' e1 e2 w1 w2 w3 w4 φ Ξ₁ Ξ₂ hφ h₁ h₂).2.2 g

theorem ix₀ (Q : QAt v χ) (h : j + 2 * (σ + 1) + 2 = D.R.m) : j + (2 * σ + 1 + 1) = Q.s := by have := Q.hs; omega
theorem ix₁ (Q : QAt v χ) (h : j + 2 * (σ + 1) + 2 = D.R.m) : j + 1 + (2 * σ + 1) = Q.s := by have := Q.hs; omega
theorem ix₂ (Q : QAt v χ) (h : j + 2 * (σ + 1) + 2 = D.R.m) : j + 1 + 1 + 2 * σ = Q.s := by have := Q.hs; omega

set_option maxHeartbeats 1000000 in

@[reducible] def stepOf (H : Chars t χ j σ h χz) (Q : QAt v χ) (α : Q.Ch j) : QStep (dblOf H) :=
  { k := Q.k
    ν := Q.ν
    unitVol := Q.unitVol
    q := Q.q
    ψk := Q.ψk
    char := Q.char
    cond := Q.cond
    n₀ := Q.X j
    n₁ := Q.X (j + 1)
    n₂ := Q.X (j + 1 + 1)
    c := 2 * σ
    F :=
      { s := Q.sc j
        s_ne := Q.sc_ne j
        F₀ := Q.FX j (by have := Q.hs; omega)
        F₁ := Q.FX (j + 1) (by have := Q.hs; omega)
        F₂ := Q.FX (j + 1 + 1) (by have := Q.hs; omega)
        G₀ := Q.FY j (2 * σ + 1 + 1 + 1) (by have := Q.hs; omega)
        G₁ := Q.FY (j + 1) (2 * σ + 1 + 1) (by have := Q.hs; omega)
        G₂ := Q.FY (j + 1 + 1) (2 * σ + 1) (by have := Q.hs; omega)
        bes := Q.bes j (σ + 1) h _ _
        jac := Q.jac j (σ + 1) h _ _
        bes' := Q.sc_step j ▸ Q.bes (j + 1 + 1) σ (idx_step h) _ _ }
    gl₀ := Q.gl j (2 * σ + 1 + 1 + 1) (by have := Q.hs; omega)
    gl₁ := Q.gl (j + 1) (2 * σ + 1 + 1) (by have := Q.hs; omega)
    gl₂ := Q.gl (j + 1 + 1) (2 * σ + 1) (by have := Q.hs; omega)
    loc₀ := Q.gl_loc _ _ _
    loc₁ := Q.gl_loc _ _ _
    loc₂ := Q.gl_loc _ _ _
    μ₁ := Q.T.mu (j + 1)
    μ₂ := Q.T.mu (j + 1 + 1)
    comp₁ := (Q.mu j (by have := Q.hs; omega)).1
    comp₂ := (Q.mu (j + 1) (by have := Q.hs; omega)).1
    open₁ := (Q.mu j (by have := Q.hs; omega)).2
    open₂ := (Q.mu (j + 1) (by have := Q.hs; omega)).2
    L₀ := Q.T.lev j (2 * σ + 1 + 1 + 1) (by have := Q.hs; omega)
    L₁ := Q.T.lev (j + 1) (2 * σ + 1 + 1) (by have := Q.hs; omega)
    L₂ := Q.T.lev (j + 1 + 1) (2 * σ + 1) (by have := Q.hs; omega)
    co₁ := ⟨(Q.reg.2.2 _ _ _).1, (Q.reg.2.2 _ _ _).2.1⟩
    co₂ := ⟨(Q.reg.2.2 _ _ _).1, (Q.reg.2.2 _ _ _).2.1⟩
    le₁ := Q.le _ _ _
    le₂ := Q.le _ _ _
    Φ₁ := ⟨Q.T.Phi j (2 * σ + 1 + 1) (ix₀ Q h), Q.reg.1 _ _ _⟩
    Φ₂ := ⟨Q.T.Phi (j + 1) (2 * σ + 1) (ix₁ Q h), Q.reg.1 _ _ _⟩
    ty₁ := Q.laws.1 _ _ _
    ty₂ := Q.laws.1 _ _ _
    D₁ := Q.eL j
    D₂ := Q.eL (j + 1)
    dat₁ := Q.eL_at _ _ _
    dat₂ := Q.eL_at _ _ _
    α := Q.rep j (2 * σ + 1 + 1) (ix₀ Q h) α
    A₁ := repS Q (j + 1) (2 * σ + 1) (ix₁ Q h)
    A₂ := repS Q (j + 1 + 1) (2 * σ) (ix₂ Q h)
    cov₁ := covers Q j _ _ ((Q.rep_bij _ _ _).mapsTo (Set.mem_univ α))
    cov₂ := fun _ hγ => covers Q (j + 1) _ _ ((mem_repS Q).1 hγ)
    d₁ := fun γ => Q.dL j α ((repE Q _ _ _).symm γ)
    d₂ := fun γ β => Q.dL (j + 1) ((repE Q _ _ _).symm γ) ((repE Q _ _ _).symm β)
    ent₁ := fun γ => by
      have := Q.dL_mid j (2 * σ + 1) (ix₁ Q h) α ((repE Q _ _ _).symm γ)
      rwa [entry_eq, rep_symm] at this
    ent₂ := fun γ β => by
      have := Q.dL_mid (j + 1) (2 * σ) (ix₂ Q h) ((repE Q _ _ _).symm γ) ((repE Q _ _ _).symm β)
      rwa [entry_eq, rep_symm, rep_symm] at this
    e₀ := oneC Q j (σ + 1) h _ (ix₀ Q h) α
    e₂ := fun β => oneC Q (j + 1 + 1) σ (idx_step h) _ (ix₂ Q h) ((repE Q _ _ _).symm β)
    one₀ := (oneC_spec Q j (σ + 1) h _ (ix₀ Q h) α).1
    one₂ := fun β => by
      have := (oneC_spec Q (j + 1 + 1) σ (idx_step h) _ (ix₂ Q h) ((repE Q _ _ _).symm β)).1
      rwa [rep_symm] at this
    m₁ := Q.m (j + 1)
    m₂ := Q.m (j + 1 + 1)
    haar₁ := (Q.haar _).1
    haar₂ := (Q.haar _).1
    vol₁ := (Q.haar _).2
    vol₂ := (Q.haar _).2 }

theorem norm_eq (hv : v.Is) {w : VTup t} (F : QFam v t) (hF : F.Pins w) (n : ℕ) (hn : n < D.R.m) (d : ℕ)
    (hd : ∀ i, n + d = (F.Q i).s + 1) (x : GA D (c.V n)) (hx : x ∈ grpAt (c.V n) (· ∈ w.Q)) :
    (∀ i, IntAt (F.Q i).q.v ((F.Q i).gl n d (hd i)) x) ↔ InK (c.V n) (v.N n) (· ∈ w.Q) x := by
  have key : ∀ i, IntAt (F.Q i).q.v ((F.Q i).gl n d (hd i)) x ↔ Moves (c.V n) x (v.N n) (v.N n) (· = (F.Q i).q.v) := fun i => by
    obtain ⟨-, h1, h2, -, h3⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D _ (F.Q i).q (c.V n) _ ((F.Q i).FY n d (hd i)) ((F.Q i).gl n d (hd i))
      ((F.Q i).gl_loc n d (hd i))
    exact intAt_iff_moves _ _ h1 h2 (h3 _ (hv.sd n hn) ((F.Q i).latY n d (hd i))) x
  simp only [key, InK, hx, true_and]
  rw [moves_iff_forall (hv.sd n hn) (· ∈ w.Q)]
  constructor
  · intro H p hp
    obtain ⟨i, rfl⟩ := (hF.places p).1 hp
    exact H i
  · exact fun H i => H _ ((hF.places _).2 ⟨i, rfl⟩)

theorem model_of_vac (hc : c.Is) (hv : v.Is) (Q : QAt v χ) (n : ℕ) (hn : n + 1 < D.R.m) (d : ℕ) (h₀ : n + (d + 1) = Q.s + 1)
    (h₁ : n + 1 + d = Q.s + 1) {P : Pl D → Prop} (hP : P Q.q.v) {f : WO (c.V n) (c.V (n + 1)) → ℂ}
    (hf : Vac c.ψ _ _ (v.N n) (v.N (n + 1)) P f) :
    ∃ T O, (ofSplit Q.q).IsModel c.ψ (Q.FY n (d + 1) h₀) (Q.FY (n + 1) d h₁) T ∧ IsOne O ∧ T O = f := by
  obtain ⟨T, hT, hO⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Q.k Q.q Q.unit _ _ _ _ (Q.FY n (d + 1) h₀) (Q.FY (n + 1) d h₁) c.ψ Q.ψk hc.std Q.char
    Q.cond _ _ (hv.sd n (by omega)) (hv.sd (n + 1) hn) (Q.latY _ _ _) (Q.latY _ _ _)).2 f
    (vac_single hc.std (hv.sd n (by omega)) (hv.sd (n + 1) hn) hP hf)
  obtain ⟨O, h1⟩ := GlobalTheory.BiComb.exists_isOne (k := Q.k) (Q.X (n + 1) ⊕ Fin d) (Q.X n ⊕ Fin (d + 1))
  exact ⟨T, O, hT, h1, hO O h1⟩

theorem fin_eQ {w : VTup t} (F : QFam v t) (hF : F.Pins w) (n : ℕ) (hn : n + 1 < D.R.m) : IsFinComb (w.eQ n) := by
  rw [hF.eQ n hn]
  refine isFinComb_aconv _ fun e he => ?_
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 he
  have := (F.Q i).hs
  exact isFinComb_of_half (F.Q i).q ((F.Q i).eL_at n ((F.Q i).s - n) (by omega)).1

theorem fin_dQ {w : VTup t} (F : QFam v t) (hF : F.Pins w) (n : ℕ) (hn : n + 3 ≤ D.R.m) (α γ) : IsFinComb (w.dQ n α γ) := by
  rw [hF.dQ n (by omega)]
  refine fun u hu => isFinComb_aconv _ (fun e he => ?_) u (Finsupp.support_smul hu)
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 he
  have := (F.Q i).hs
  exact isFinComb_of_half (F.Q i).q ((F.Q i).dL_mid n ((F.Q i).s - (n + 1)) (by omega) _ _).1

set_option maxHeartbeats 1000000 in

theorem oneChart (hc : c.Is) (hv : v.Is) (hW : WeilOK (t := t) v) {w : VTup t} (F : QFam v t) (hF : F.Pins w)
    (H : Chars t F.χ j σ h χz) {ρ₁ μ₁ ρ₂ μ₂}
    (hN₁ : IsNormAt (c.V (j + 1)) (jacGrp (c.jac j (σ + 1) h).d) (v.N (j + 1)) (· ∈ w.Q) ρ₁ μ₁)
    (hN₂ : IsNormAt (c.V (j + 1 + 1)) (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o)
      (v.N (j + 1 + 1)) (· ∈ w.Q) ρ₂ μ₂) {Ψ₁ Ψ₂} (hΨ₁ : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁)
    (hΨ₂ : Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂) (α : t.Ch j) {φ : GA D (c.X j) → ℂ} (hφ : IsContAut _ φ)
    {f} (hf : IsContAut _ f) (hfY : f ∈ w.FY (j + 1 + 1)) :
    Iter2 ρ₁ μ₁ ρ₂ μ₂
      (fun q₁ q₂ => ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
        (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (w.eQ j) Ψ₁)
          (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) φ g q₁.1 q₂.1) (rTrans q₂.1 f))
      (w.cQ j * ∑ γ, ∑ β, (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
        (c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β)
          (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂))) (trc (w.ε (j + 1 + 1) β) f)) := by
  have n₁ := norm_eq hv F hF (j + 1) (by omega) (2 * σ + 1 + 1) fun i => by have := (F.Q i).hs; omega
  have n₂ := norm_eq hv F hF (j + 1 + 1) (by omega) (2 * σ + 1) fun i => by have := (F.Q i).hs; omega
  have hQ : ∀ i, (F.Q i).q.v ∈ w.Q := fun i => (hF.places _).2 ⟨i, rfl⟩
  have away : ∀ {A T : HSp D} (e : AE D), ∀ u ∈ (Finsupp.single 0 1 : WO A T →₀ ℂ).support, IsHalf e u := by
    intro A T e u hu
    obtain rfl : u = 0 := Finset.mem_singleton.1 (Finsupp.support_single_subset hu)
    intro a b
    exact mul_zero _
  have V := GlobalTheory.T.doubleStep_adelicIntegral_finiteTwistPlaces D c.ψ hc.std σ (dblOf H) F.r (fun i => stepOf H (F.Q i) (F.eqv j α i)) hF.inj (· ∈ w.Q) hF.places
    μ₁ ρ₁ μ₂ ρ₂ hN₁.1 hN₁.2.1 hN₂.1 hN₂.2.1
    ((congrArg μ₁ (Set.ext fun x => n₁ x.1 x.2)).trans hN₁.2.2.1)
    ((congrArg ρ₁ (Set.ext fun x => n₁ x.1.1 x.1.2)).trans hN₁.2.2.2)
    ((congrArg μ₂ (Set.ext fun x => n₂ x.1 x.2)).trans hN₂.2.2.1)
    ((congrArg ρ₂ (Set.ext fun x => n₂ x.1.1 x.1.2)).trans hN₂.2.2.2)
    (Finsupp.single 0 1) (Finsupp.single 0 1) (fun i => ⟨away _, away _⟩) Ψ₁ Ψ₂ hΨ₁.1 hΨ₂.1
    (fun i => ⟨model_of_vac hc hv (F.Q i) j (by omega) _ _ _ (hQ i) hΨ₁,
      model_of_vac hc hv (F.Q i) (j + 1) (by omega) _ _ _ (hQ i) hΨ₂⟩)
    φ f hφ hf (fun i => hF.FY (j + 1 + 1) (by omega) f hfY i _ _) 1 (one_mem _) 1 (one_mem _) 1 (one_mem _)
  have V' := isIteratedQuotientIntegral_const_mul (∏ i, (F.Q i).wt j (F.eqv j α i)) V
  have t₁ := GlobalTheory.AvgMid.theta_comb hc.std (fin_eQ F hF j (by omega)) hΨ₁.1
  have t₂ := GlobalTheory.AvgMid.theta_comb hc.std (fin_eQ F hF (j + 1) (by omega)) hΨ₂.1
  have hε : ∀ n ρ (hn : n + 2 * ρ + 2 = D.R.m) d (hd : ∀ i, n + d = (F.Q i).s) β, w.ε n β = (∏ i, (F.Q i).wt n (F.eqv n β i)) •
      conv (List.ofFn fun i => (oneC (F.Q i) n ρ hn d (hd i) (F.eqv n β i)).mapDomain
        ((F.Q i).gl n (d + 1) (by have := hd i; omega))) := fun n ρ hn d hd β => by
    rw [hF.ε n ρ hn β]
    congr 3
    funext i
    exact (oneC_spec (F.Q i) n ρ hn d (hd i) _).2
  refine (congrArg₂ (Iter2 ρ₁ μ₁ ρ₂ μ₂) ?_ ?_).mp V'
  · funext x y
    rw [hε j (σ + 1) h _ (fun i => ix₀ (F.Q i) h) α]
    refine Eq.trans ?_ (sum_support_smul _ _ _).symm
    rw [smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_eq_mul, ← val_eq_hand (handIsLift H hW) t₁ t₂ hφ, hF.eQ j (by omega), hF.eQ (j + 1) (by omega)]
    simp only [one_mul]
  · have hvol : ∏ i, (stepOf H (F.Q i) (F.eqv j α i)).volJ = w.cQ j := by
      rw [hF.cQ j (by omega)]
      refine Finset.prod_congr rfl fun i _ => ?_
      have := (F.Q i).hs
      rw [(F.Q i).idx_mid (j + 1) (2 * σ + 1 + 1) (by omega), (F.Q i).idx_mid (j + 1 + 1) (2 * σ + 1) (by omega)]
      rfl
    rw [hvol, mul_left_comm, Finset.mul_sum]
    congr 1
    symm
    refine Fintype.sum_equiv ((F.eqv (j + 1)).trans (Equiv.piCongrRight fun i => repE (F.Q i) _ _ (ix₁ (F.Q i) h))) _ _ fun γ => ?_
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv ((F.eqv (j + 1 + 1)).trans (Equiv.piCongrRight fun i => repE (F.Q i) _ _ (ix₂ (F.Q i) h))) _ _
      fun β => ?_
    have hw : ∏ i, (stepOf H (F.Q i) (F.eqv j α i)).w₁ (repE (F.Q i) _ _ (ix₁ (F.Q i) h) (F.eqv (j + 1) γ i)) *
        (stepOf H (F.Q i) (F.eqv j α i)).w₂ (repE (F.Q i) _ _ (ix₂ (F.Q i) h) (F.eqv (j + 1 + 1) β i)) =
        (∏ i, (F.Q i).wt (j + 1) (F.eqv (j + 1) γ i)) * ∏ i, (F.Q i).wt (j + 1 + 1) (F.eqv (j + 1 + 1) β i) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [(F.Q i).wt_mid (j + 1) _ (ix₁ (F.Q i) h), (F.Q i).wt_mid (j + 1 + 1) _ (ix₂ (F.Q i) h)]
      rfl
    rw [val_one, aconv_single_cons, aconv_single_cons, hF.dQ j (by omega), hF.dQ (j + 1) (by omega),
      hε (j + 1 + 1) σ (idx_step h) _ (fun i => ix₂ (F.Q i) h) β, biComb_smul_left, trc_smul_left, Comm.bl,
      GlobalTheory.SeeSawRhs.biLift_smul, GlobalTheory.HandHom.per_smul]
    simp only [Equiv.trans_apply, Equiv.piCongrRight_apply, Pi.map_apply, Equiv.symm_apply_apply]
    rw [hw]
    simp only [mul_assoc]
    rfl

set_option maxHeartbeats 1000000 in

theorem qLaw_of_pin : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPin v w → QLaw v w := by
  intro D c v t w hc _ hv hW ⟨F, hF⟩ j σ h ρ₁ μ₁ ρ₂ μ₂ hN₁ hN₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ f hf hfY
  obtain ⟨χz, e1, e2, e3, e4⟩ := hF.mid j σ h
  have H : Chars t F.χ j σ h χz := ⟨e1, e2, e3, e4, hF.kom j (by omega), hF.kom (j + 1) (by omega)⟩
  have hf' : IsContAut _ f := ⟨hf.left, hf.cont⟩
  have key := isIteratedQuotientIntegral_finset_sum Finset.univ _ _ fun α _ => oneChart hc hv hW F hF H hN₁ hN₂ hΨ₁ hΨ₂ α (hφ α).1 hf' hfY
  refine (congrArg (Iter2 ρ₁ μ₁ ρ₂ μ₂ _) ?_).mp key
  rw [← Finset.mul_sum]
  congr 1
  rw [← Fintype.sum_prod_type', Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← Fintype.sum_prod_type']
  have hX : ∀ p : t.Ch j × t.Ch (j + 1), IsContAut (c.X (j + 1 + 1)) (c.bl j (t.kom j) (t.kom (j + 1)) (φ p.1)
      (biComb c.ψ _ _ _ (w.dQ j p.1 p.2) (w.dQ (j + 1) p.2 β) (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂))) := fun p =>
    contAut_lift (S := dblOf H) hc.std (handIsLift H hW) (fin_dQ F hF j (by omega) p.1 p.2)
      (fin_dQ F hF (j + 1) (by omega) p.2 β) hΨ₁.1 hΨ₂.1 (hφ p.1).1
  exact (per_sum hc.std (c.B (j + 1 + 1) σ (idx_step h)) (GlobalTheory.QValOuter.contAut_trc (w.ε (j + 1 + 1) β) hf') _ hX).symm

end GlobalTheory.QLawPf
end
