import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistField.Read

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem mult_inv {V : HSp D} {S : D.what₂.Tau → _} (θ) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) {Φ : MMap M}
    (hΦ : Φ ∈ Mult θ M J χ) (v : M.Vec) : ∀ γ ∈ GQ V, ∀ g, Φ v (γ * g) = Φ v g := by
  intro γ hγ g
  induction hΦ using Submodule.span_induction with
  | mem x hx => exact (hx.aut v).left γ hγ g
  | zero => rfl
  | add x y _ _ hx hy => simp only [_root_.add_apply, Pi.add_apply, hx, hy]
  | smul a x _ hx => simp only [_root_.smul_apply, Pi.smul_apply, hx]

theorem eq_of_out {W : HSp D} {Φ Ψ : GA D W → ℂ} (hΦ : ∀ γ ∈ GQ W, ∀ g, Φ (γ * g) = Φ g)
    (hΨ : ∀ γ ∈ GQ W, ∀ g, Ψ (γ * g) = Ψ g) (h : ∀ q : AutQ W, Φ q.out = Ψ q.out) : Φ = Ψ := by
  funext g
  let q : AutQ W := Quotient.mk _ g
  have hr : g * q.out⁻¹ ∈ GQ W := QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq q))
  have h1 := hΦ _ hr q.out
  have h2 := hΨ _ hr q.out
  rw [inv_mul_cancel_right] at h1 h2
  rw [h1, h2, h q]

theorem ev_sum {L H Y : Type} [Field L] [AddCommGroup H] [Module ℂ H] [AddCommGroup Y] [Module L Y] {σ : L →+* ℂ}
    (j : Y →ₛₗ[σ] H) {V : HSp D} {S : D.what₂.Tau → _} {M : DSModel V S} (e : H →ₗ[ℂ] MMap M) (v : M.Vec) (g : GA D V) {m : ℕ}
    (a : Fin m → L) (y : Fin m → Y) : e (j (∑ l, a l • y l)) v g = ∑ l, σ (a l) * e (j (y l)) v g := by
  rw [map_sum, map_sum, _root_.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smulₛₗ, map_smul]
  rfl

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem ev_base (fw : FWTie T R κ v₀) (hev : fw.Evaluates) {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
    (O : OMDat T.toCore R i Tp tup) (f : Cu T κ i) (h : GA D (Wc D i)) :
    (R.HW i (sg0 D A)).e (fw.jK i (sg0 D A) f) (v₀ i (sg0 D A)) h =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
        O.phi (T.cE ((i : ℕ) + 1) O.s0) (f : T.R ((i : ℕ) + 1)) h := by
  have e : res T (sg0 D A) = O.s0 :=
    ((congrArg (res T) (show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0)).trans
      (res_embLL T fw.alg_eq fw.laws.pins.2.2.1)).trans (sOv_eq T.toCore O.c' O.hle).symm
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) e).trans O.hV
  have h1 := hev i (sg0 D A) (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) hV f
  have key : ∀ (σ σ' : T.Q.c.F →+* ℂ) (_ : σ' = σ) (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W)
      (hV' : T.V ((i : ℕ) + 1) σ' = W) (g : GA D W), phiC T hV' (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) g =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * adel W (castDict hV (T.dict ((i : ℕ) + 1) σ))
        (muPin W (castDict hV (T.dict ((i : ℕ) + 1) σ)) (castDict hV (T.mu ((i : ℕ) + 1) σ)) (T.cE ((i : ℕ) + 1) σ))
        (rdU (T.U ((i : ℕ) + 1) σ) (f : T.R ((i : ℕ) + 1))) g := by
    intro σ σ' e W hV hV' g
    subst e
    subst hV
    rfl
  exact (congrFun h1 h).trans (key _ _ e _ O.hV hV h)

set_option maxHeartbeats 1000000 in

theorem exists_comb {i : Fin D.R.m} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v : (R.MW i (sg0 D A)).Vec} {ι x₀} {ph : ℂ}
    (hn : κ.n = (Vc D i).rank) (O : OMDat T.toCore R i T0 id) (hP : O.Pins κ v ι x₀)
    (hrow : O.OneMapOf κ v (T.cE ((i : ℕ) + 1) O.s0) ph) (t : T0) (y : A.fam.amb.FL i t) :
    ∃ ze ∈ D.what₂.embLL.toRatAlgHom.fieldRange, ∃ (m : ℕ) (as : Fin m → O.c'.F) (fs : Fin m → T.cuspA ((i : ℕ) + 1) (wtA κ) κ.n),
      ∀ q : AutQ (Wc D i), ph * R.thF i t (R.jV i t y) v q.out =
        ∑ l, ze * (as l : ℂ) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
          O.phi (T.cE ((i : ℕ) + 1) O.s0) (fs l : T.R ((i : ℕ) + 1)) q.out) := by
  obtain ⟨hE, ⟨-, hC, hA, -, -, z, -, h1⟩, -⟩ := hrow
  have aux1 := h1 t
  obtain ⟨ze, a1, -, h1⟩ := aux1
  have aux2 := (hP.tuple t).reps
  obtain ⟨h, J', -, p2, p3, p4⟩ := aux2
  have aux3 := p2 y
  obtain ⟨x, hx⟩ := aux3
  have e := p3 _ x hx
  have aux4 := h1 x ((p4 x).2 ⟨y, hx⟩)
  obtain ⟨⟨f, hf, hf'⟩, h2⟩ := aux4
  have hs := ((mem_cusp _ _ _ _ _ _).1 hf).1
  have h4 := h2 f hs hf'
  rw [← hn] at hf
  have aux5 := hC _ _ f hf
  obtain ⟨m, as, fs, hfs, hBC⟩ := aux5
  have aux6 := hP.lift.lev z
  obtain ⟨k, hk, -⟩ := aux6
  have h5 := rdU_unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c') (hA _ _ z m as fs f ((mem_cusp _ _ _ _ _ _).1 hf).1
    (fun l => ((mem_cusp _ _ _ _ _ _).1 (hfs l)).1) hBC)
  refine ⟨ze, a1, m, as, fun l => ⟨_, (hE z k hk (fs l) (hfs l)).1⟩, fun q => ?_⟩
  have h6 : ph * R.thF i t (R.jV i t y) v q.out = ze * T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 *
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * (O.mu q.out *
        rdU (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) (actLev O.c' O.lev2 z f) (O.dict q.out).1 (O.dict q.out).2) :=
    (congrArg (ph * ·) (congrFun e q)).symm.trans (h4 q)
  rw [h6, h5]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  show _ = ze * (as l : ℂ) * (_ * (T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 * O.mu q.out *
    rdU (T.U ((i : ℕ) + 1) O.s0) (actLev T.Q.c O.lev2 z (fs l)) (O.dict q.out).1 (O.dict q.out).2))
  show _ * (_ * ((as l : ℂ) * _)) = _
  ring

set_option maxHeartbeats 1000000 in

theorem ratAt_of_oneMap (fw : FWTie T R κ v₀) {ph : ℂ} {i : Fin D.R.m} (hW : R.models_HW) (hP : R.IsThP) (hU : R.LUnif)
    (hev : fw.Evaluates) (hinj : EvInj T R v₀) (h : OneMapOverL T R κ v₀ ph i) (t : T0) : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.RatAt R i ph t := by
  intro x₀
  obtain ⟨O, hF, hpin, hrow⟩ := h
  have hn : (κ i).n = (Vc D i).rank :=
    (fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm
  have aux7 := exists_comb hn O hpin hrow t x₀
  obtain ⟨ze, hze, m, as, fs, hq⟩ := aux7
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have ha : ∀ l, ∃ a : D.what₂.LL, sg0 D A a = ze * (as l : ℂ) := fun l => by
    have aux8 := AlgHom.mem_fieldRange.1 (mul_mem hze (hF.le (as l).2))
    obtain ⟨a, ha⟩ := aux8
    exact ⟨a, (RingHom.congr_fun hs a).trans ha⟩
  choose a ha using ha
  have hmem := (hW i (sg0 D A)).2.1.ge (hP.thF_mem i t (R.jV i t x₀))
  obtain ⟨w, hw⟩ := hmem
  have hinv : ∀ u : (R.HW i (sg0 D A)).H, ∀ γ ∈ GQ (Wc D i), ∀ g,
      evAt R i _ (v₀ i _) u (γ * g) = evAt R i _ (v₀ i _) u g := fun u =>
    mult_inv R.θ _ _ _ ((hW i _).2.1.le (LinearMap.mem_range_self _ u)) _
  have e0 : (R.HW i (sg0 D A)).e (ph • w) = ph • R.thF i t (R.jV i t x₀) :=
    (map_smul (R.HW i (sg0 D A)).e ph w).trans (congrArg (ph • ·) hw)
  have key : (R.FW i).j (sg0 D A) (∑ l, a l • ((fw.e i (fs l) : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)) = ph • w := by
    refine hinj i _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) (eq_of_out (hinv _) (hinv _) fun q => ?_)
    have e1 : evAt R i _ (v₀ i _) (ph • w) q.out = ph * R.thF i t (R.jV i t x₀) (v₀ i _) q.out :=
      congrArg (fun Φ : MMap (R.MW i (sg0 D A)) => Φ (v₀ i _) q.out) e0
    refine (ev_sum _ _ _ _ _ _).trans (Eq.trans ?_ ((hq q).symm.trans e1.symm))
    exact Finset.sum_congr rfl fun l _ => congrArg₂ (· * ·) (ha l) (ev_base fw hev O (fs l) q.out)
  have h1 := (congrArg (R.HW i (sg0 D A)).e key).trans e0
  exact ⟨_, h1, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.proj_clause R i ph t hP.thG (hW i _).1 (hU i _).2.2 _ _ h1⟩

theorem rat_of_oneMapOverL : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T R κ v₀) (ph : ℂ) (i : Fin D.R.m), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → R.IsThP → R.LUnif → fw.Evaluates → EvInj T R v₀ → GlobalTheory.TwistField.OneMapOverL T R κ v₀ ph i → ∀ t : T0, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.RatAt R i ph t :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ fw _ _ _ _ hM hP hU hev hinj h t => ratAt_of_oneMap fw hM.HW hP hU hev hinj h t

end GlobalTheory.TwistField.Read
