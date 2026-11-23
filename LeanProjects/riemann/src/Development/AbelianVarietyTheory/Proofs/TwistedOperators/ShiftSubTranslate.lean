import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointIntertwines
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.HeckeSup

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Lev ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {Γ G : Type} [Group Γ] [Group G] (L : G → Γ → Prop) (u : Γ → ℂ)

def liftSub : Submodule ℂ (Γ → ℂ) where
  carrier := {Φ | (∀ g k, L g k → ∀ h, u (h * k) * Φ (h * k) = u h * Φ (h * k)) ∧
    ∀ g k k', L g k → L g k' → ∀ h, Φ (h * k) = Φ (h * k')}
  add_mem' := by
    rintro Φ Ψ ⟨a1, a2⟩ ⟨b1, b2⟩
    refine ⟨fun g k hk h => ?_, fun g k k' hk hk' h => ?_⟩
    · simp only [Pi.add_apply, mul_add, a1 g k hk h, b1 g k hk h]
    · simp only [Pi.add_apply, a2 g k k' hk hk' h, b2 g k k' hk hk' h]
  zero_mem' := ⟨fun _ _ _ _ => by simp, fun _ _ _ _ _ _ => rfl⟩
  smul_mem' := by
    rintro c Φ ⟨a1, a2⟩
    refine ⟨fun g k hk h => ?_, fun g k k' hk hk' h => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_left_comm, a1 g k hk h, mul_left_comm]
    · simp only [Pi.smul_apply, a2 g k k' hk hk' h]

def shiftSub (c : ℂ) (k₀ : Γ) : Submodule ℂ (Γ → ℂ) :=
  liftSub L u ⊓
    { carrier := {Φ | ∀ h, Φ h = c * u h * Φ (h * k₀)}
      add_mem' := fun {Φ Ψ} a b h => by
        simp only [Pi.add_apply, mul_add]
        rw [← a h, ← b h]
      zero_mem' := fun _ => by simp
      smul_mem' := fun a Φ b h => by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [mul_left_comm, ← b h] }

variable {L u}

theorem shiftSub_translate (hmul : ∀ g g' k k', L g k → L g' k' → L (g * g') (k * k')) {c : ℂ} {z : G}
    (hz : z ∈ Subgroup.center G) {k₀ : Γ} (h₀ : L z k₀) {Φ : Γ → ℂ} (hΦ : Φ ∈ shiftSub L u c k₀) {g : G} {k : Γ}
    (hk : L g k) : (fun h => Φ (h * k)) ∈ shiftSub L u c k₀ := by
  obtain ⟨⟨a1, a2⟩, a3⟩ := hΦ
  have key : ∀ g' k', L g' k' → ∀ h, u (h * k') * Φ (h * k' * k) = u h * Φ (h * k' * k) := fun g' k' hk' h => by
    rw [← a1 g k hk, mul_assoc, a1 _ _ (hmul _ _ _ _ hk' hk)]
  refine ⟨⟨key, fun g' k' k'' h1 h2 h => ?_⟩, fun h => ?_⟩
  · show Φ (h * k' * k) = Φ (h * k'' * k)
    rw [mul_assoc, mul_assoc, a2 _ _ _ (hmul _ _ _ _ h1 hk) (hmul _ _ _ _ h2 hk)]
  · show Φ (h * k) = c * u h * Φ (h * k₀ * k)
    have e : L (z * g) (k * k₀) := (Subgroup.mem_center_iff.1 hz g) ▸ hmul _ _ _ _ hk h₀
    rw [a3 (h * k), mul_assoc c, ← a1 z k₀ h₀, mul_assoc h, a1 _ _ e, a2 _ _ _ e (hmul _ _ _ _ h₀ hk), mul_assoc h, mul_assoc c]

omit [Group G] in
theorem shift_eq {n : ℕ} {θ : Γ → ℂ} {a : Fin n → ℂ} {p pE : Fin n → Γ → ℂ} {k g : Γ} {c ph : ℂ} (hph : ph ≠ 0)
    (e1 : θ = ∑ j, a j • p j) (hr : ∀ j h, pE j h = u h * p j h) (hu : u (g * k) * θ (g * k) = u g * θ (g * k))
    (e3 : ph * θ g = c * ∑ j, a j * pE j (g * k)) : θ g = c / ph * u g * θ (g * k) := by
  have e4 : ∑ j, a j * pE j (g * k) = u g * θ (g * k) := by
    rw [← hu, e1]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, hr]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e4] at e3
  field_simp
  linear_combination e3

end Abstract

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem eq_of_out {W : HSp D} (Φ Ψ : GA D W → ℂ) (hΦ : ∀ γ ∈ GQ W, ∀ g, Φ (γ * g) = Φ g)
    (hΨ : ∀ γ ∈ GQ W, ∀ g, Ψ (γ * g) = Ψ g) (h : ∀ q : AutQ W, Φ q.out = Ψ q.out) (g : GA D W) : Φ g = Ψ g := by
  let q : AutQ W := Quotient.mk _ g
  have hr : g * q.out⁻¹ ∈ GQ W := QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq q))
  have h1 := hΦ _ hr q.out
  have h2 := hΨ _ hr q.out
  rw [inv_mul_cancel_right] at h1 h2
  rw [h1, h2, h]

section Lift

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev LiftW (g : G) (k : GA D (Wc D i)) : Prop := IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k

theorem liftW_mul (g g' : G) (k k' : GA D (Wc D i)) (h : LiftW R i g k) (h' : LiftW R i g' k') : LiftW R i (g * g') (k * k') := by
  refine ⟨mul_mem h.1 h'.1, by rw [map_mul]; exact mul_mem h.2.1 h'.2.1, ?_⟩
  rw [map_mul, Formalism.L2.DIV.rTup_mul h.2.1 h'.2.1, h.2.2, h'.2.2, map_mul]
  rfl

theorem levChi_flagW (k : GA D (Wc D i)) : levChi (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)) k = 1 := by
  unfold levChi levFn
  have h : ext1 (flagL (R.datWp i R.triv)).P.H (flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (flagL (R.datWp i R.triv)) (finE (Wc D i) k)) = 1 := subgroupCharExtension_one_apply _ _
  rw [h]
  show (((1 * (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ ∅, _ : ℂˣ)) : ℂ) = 1
  simp

theorem exists_liftW_act {g : G} (hk : ∃ k, LiftW R i g k) : ∃ k, LiftW R i g k ∧
    ∀ Φ h, Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) Φ h = Φ (h * k) := by
  refine ⟨hk.choose, hk.choose_spec, fun Φ h => ?_⟩
  refine (GlobalTheory.SecLift.actL_apply (L := R.datWp i R.triv) hk Φ h).trans ?_
  rw [levChi_flagW, inv_one, one_mul]

theorem chiC_coe (g : G) : ((chiC R i g : ℂˣ) : ℂ) =
    ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ) := Units.coe_prod _ _

end Lift

section Shift

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  (O : OMDat C R i Unit (fun _ => A.μ0)) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
  {cE c0 : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ}

def ratio (cE c0 : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (h : GA D (Wc D i)) : ℂ := cE (O.dict h).1 / c0 (O.dict h).1

theorem phi_apply (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (f : C.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    O.phi cc f h = cc (O.dict h).1 * O.mu h * rdU (C.U ((i : ℕ) + 1) O.s0) f (O.dict h).1 (O.dict h).2 := rfl

theorem phi_ratio (h0 : ∀ k, c0 k ≠ 0) (f : C.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    O.phi cE f h = ratio O cE c0 h * O.phi c0 f h := by
  rw [phi_apply, phi_apply, ratio]
  have := h0 (O.dict h).1
  field_simp

theorem phi_mem_liftSub (h0 : ∀ k, c0 k ≠ 0) (hE : O.EquivAt κ cE) (hE0 : O.EquivAt κ c0) {f : C.R ((i : ℕ) + 1)}
    (hf : f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) : O.phi c0 f ∈ liftSub (LiftW R i) (ratio O cE c0) := by
  refine ⟨fun g k hk h => ?_, fun g k k' hk hk' h => ?_⟩
  · have e1 := (hE g k hk f hf).2 h
    have e2 := (hE0 g k hk f hf).2 h
    rw [← chiC_coe] at e1 e2
    rw [phi_ratio O h0, phi_ratio O h0 f, e2, mul_left_comm] at e1
    exact (mul_left_cancel₀ (chiC R i g).ne_zero e1).symm
  · have e1 := (hE0 g k hk f hf).2 h
    have e2 := (hE0 g k' hk' f hf).2 h
    rw [← chiC_coe] at e1 e2
    exact mul_left_cancel₀ (chiC R i g).ne_zero (e1.symm.trans e2)

set_option maxHeartbeats 4000000 in

theorem shift_of_span (hP : O.Pins κ v₀ ι x₀) (hn : κ.n = (Vc D i).rank) (hHV : R.models_HV) (hjV : R.models_jV)
    (hmem : R.thP_thF_mem) (hsp : GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.SpanAt R i A.μ0) {ph : ℂ} (hE : O.OneMapOf κ v₀ cE ph)
    (hE0 : O.EquivAt κ c0) (hS : GlobalTheory.AdTh.SerOf O κ v₀ c0 1)
    (hW : ∀ f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n, ∃ U ∈ R.Wall i (sg0 D A), ∀ h,
      U v₀ h = (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.phi cE f h) :
    ∃ (z : G) (c : ℂ), c ≠ 0 ∧ (∃ k, LiftW R i z k) ∧ ∀ k, LiftW R i z k →
      ∀ f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n, ∀ h, O.phi c0 f h = c * O.phi cE f (h * k) := by
  obtain ⟨hEq, ⟨-, hBC, hAct, hcE, hph, z, hz, hrow⟩, -⟩ := hE
  obtain ⟨ze, -, ⟨m, hm, hze⟩, hrow⟩ := hrow ()
  have hze0 : ze ≠ 0 := fun h => by
    rw [h, zero_pow hm.ne'] at hze
    exact zero_ne_one hze
  have hph0 : ph ≠ 0 := fun h => by simp [h] at hph
  have h0 : ∀ k, c0 k ≠ 0 := fun k h => by simpa [h] using hS.1 k
  have hE0' : ∀ k, cE k ≠ 0 := fun k h => by simpa [h] using hcE k
  have hl : ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  have hlift : ∀ g, ∃ k, LiftW R i g k := fun g => (hP.lift.lev g).imp fun _ h => h.1
  have hinvW : ∀ U ∈ R.Wall i (sg0 D A), ∀ γ ∈ GQ (Wc D i), ∀ g, U v₀ (γ * g) = U v₀ g := fun U hU =>
    (GlobalTheory.mult_value_left_cont_level R.θ _ _ _ U hU v₀).1
  have hinv : ∀ f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n, ∀ γ ∈ GQ (Wc D i), ∀ g, O.phi cE f (γ * g) = O.phi cE f g := by
    intro f hf γ hγ g
    obtain ⟨U, hU, e⟩ := hW f hf
    exact mul_left_cancel₀ hl (by rw [← e, ← e, hinvW U hU γ hγ])
  refine ⟨z, ze * chiC R i z / ph, div_ne_zero (mul_ne_zero hze0 (chiC R i z).ne_zero) hph0, hlift z, fun k hk => ?_⟩
  have hbase : ∀ y, R.thF i A.μ0 (jVx R i A.μ0 y) v₀ ∈
      shiftSub (LiftW R i) (ratio O cE c0) (ze * chiC R i z / ph) k := by
    intro y
    obtain ⟨hh, J', hrep, hPl, hth, hpl⟩ := (hP.tuple ()).reps
    obtain ⟨x, hx⟩ := hPl y
    obtain ⟨⟨f', hf', hcl⟩, hid⟩ := hrow x ((hpl x).2 ⟨y, hx⟩)
    have hs := hS.2.2 () hh J' hrep _ x hx f' hf'.1 hcl
    have hq := hid f' hf'.1 hcl
    have hth' : ∀ q : AutQ (Wc D i), O.thAd () x q = R.thF i A.μ0 (jVx R i A.μ0 y) v₀ q.out := fun q => congrFun (hth _ x hx) q
    have hf'' : f' ∈ cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank := hf'
    have hb := hBC (wtA κ) (Vc D i).rank f' hf''
    obtain ⟨n, as, fs, hfs, hbc⟩ := hb
    have hbc' := hAct _ _ z n as fs f' hf'.1 (fun j => (hfs j).1) hbc
    have hfs' : ∀ j, fs j ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n := fun j => by rw [hn]; exact hfs j
    have r1 := rdU_unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') hbc
    have r2 := rdU_unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') hbc'
    have e1 : R.thF i A.μ0 (jVx R i A.μ0 y) v₀ = ∑ j, ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
        inC O.c' (as j)) • O.phi c0 (fs j) := by
      funext g
      have := hs g
      rw [one_mul, r1] at this
      rw [this]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, phi_apply]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hmemL : R.thF i A.μ0 (jVx R i A.μ0 y) v₀ ∈ liftSub (LiftW R i) (ratio O cE c0) := by
      rw [e1]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (phi_mem_liftSub O h0 hEq hE0 (hfs' j))
    refine ⟨hmemL, fun g => ?_⟩
    have e2 : ∀ q : AutQ (Wc D i), ph * R.thF i A.μ0 (jVx R i A.μ0 y) v₀ q.out =
        ze * chiC R i z * ∑ j, ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * inC O.c' (as j)) *
          O.phi cE (fs j) (q.out * k) := by
      intro q
      have h3 : ph * R.thF i A.μ0 (jVx R i A.μ0 y) v₀ q.out = ze * cE (O.dict q.out).1 *
          (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * (O.mu q.out *
            rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) (actLev O.c' O.lev2 z f') (O.dict q.out).1 (O.dict q.out).2) :=
        (congrArg (ph * ·) (hth' q)).symm.trans (hq q)
      rw [h3, r2]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h2 := (hEq z k hk (fs j) (hfs' j)).2 q.out
      rw [← chiC_coe, phi_apply] at h2
      linear_combination (ze * (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * inC O.c' (as j)) * h2
    have e3 : ph * R.thF i A.μ0 (jVx R i A.μ0 y) v₀ g =
        ze * chiC R i z * ∑ j, ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * inC O.c' (as j)) *
          O.phi cE (fs j) (g * k) := by
      refine eq_of_out (fun g => ph * R.thF i A.μ0 (jVx R i A.μ0 y) v₀ g) (fun g => ze * chiC R i z *
        ∑ j, ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * inC O.c' (as j)) * O.phi cE (fs j) (g * k))
        (fun γ hγ g => congrArg (ph * ·) (hinvW _ (hmem i A.μ0 _) γ hγ g)) (fun γ hγ g => ?_) e2 g
      refine congrArg (ze * chiC R i z * ·) (Finset.sum_congr rfl fun j _ => ?_)
      rw [mul_assoc γ, hinv _ (hfs' j) γ hγ]
    exact shift_eq (pE := fun j => O.phi cE (fs j)) hph0 e1 (fun j h => phi_ratio O h0 (fs j) h) (hmemL.1 z k hk g) e3
  let ev : MMap (R.MW i (sg0 D A)) →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    { toFun := fun U => U v₀, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hall : ∀ y, R.thF i A.μ0 y v₀ ∈ shiftSub (LiftW R i) (ratio O cE c0) (ze * chiC R i z / ph) k :=
    GlobalTheory.SecLift.span_of_pres (R.B.L i A.μ0).pres (R.HV i A.μ0).e (hHV i A.μ0).1 (hHV i A.μ0).2.1 (jVx R i A.μ0) (hjV i A.μ0)
      ((shiftSub (LiftW R i) (ratio O cE c0) (ze * chiC R i z / ph) k).comap (ev ∘ₗ R.thF i A.μ0)) hbase
  have hWall : R.Wall i (sg0 D A) ≤ (shiftSub (LiftW R i) (ratio O cE c0) (ze * chiC R i z / ph) k).comap ev := by
    rw [← hsp]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, y, rfl⟩
    obtain ⟨k', hk', e⟩ := exists_liftW_act R i (hlift g)
    have h1 := shiftSub_translate (liftW_mul R i) hz hk (hall y) hk'
    rw [← funext (e (R.thF i A.μ0 y v₀))] at h1
    exact h1
  intro f hf h
  obtain ⟨U, hU, e⟩ := hW f hf
  have h1 : U v₀ h = ze * chiC R i z / ph * ratio O cE c0 h * U v₀ (h * k) := (hWall hU).2 h
  rw [e, e, phi_ratio O h0 f h] at h1
  have hr : ratio O cE c0 h ≠ 0 := div_ne_zero (hE0' _) (h0 _)
  refine mul_left_cancel₀ (mul_ne_zero hl hr) ?_
  linear_combination h1

end Shift

end GlobalTheory.HeckeSup
