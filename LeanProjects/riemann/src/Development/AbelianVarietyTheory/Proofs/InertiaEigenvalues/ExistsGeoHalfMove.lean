import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramePinSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfRealisationGeometricAction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsUniformisationIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeoHalfUpd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PbEqOfPins
import Formalism.LocalToGlobal.IndefiniteReal.WeakCharacterisationWithError

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.Unframe

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Lev ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HeckeSup GlobalTheory.RealGeo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev moveForms {LL Ks WL G : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] {W : (LL →+* ℂ) → Type}
    [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] [Group G]
    (B : Arith.FormsL LL Ks WL W G) (w : (LL →+* ℂ) → G) : Arith.FormsL LL Ks WL W G :=
  { B with j := fun σ => (B.j σ).comp (B.ρ (w σ)) }

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

abbrev moveR {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G) : RealDat D A Ks :=
  updFW R R.nW fun i => moveForms (R.FW i) (w i)

variable {T : CoreJ D} [iA : Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}

open Classical in
variable (T) in

def overEmb (w : Fin D.R.m → (T.Q.c.F →+* ℂ) → G) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : G :=
  if GoodEmb T.Q.c (res T σ) then w i (res T σ) else w i (resC T σ)

section Half

variable (B : GeoHalf T R fun _ => 1) (c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ)
  (w : Fin D.R.m → (T.Q.c.F →+* ℂ) → G)

def Moves : Prop :=
  ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (B.κ i)) (B.κ i).n,
      phiC (setCE T c') hV (wtA (B.κ i)) f = phiC T hV (wtA (B.κ i)) (actLev T.Q.c (B.O i).lev2 (w i σ) f)

variable {B c' w}

theorem rho_e (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (i : Fin D.R.m) (g : G) (f : Cu T B.κ i) :
    (R.FW i).ρ g ((B.fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) =
      (B.fw.e i ⟨actLev T.Q.c (B.O i).lev2 g f, hK i g f f.2⟩ : (R.FW i).WK) :=
  (((B.rhoGeo i).1 (hK i) g f).choose_spec).symm

set_option maxHeartbeats 1600000 in
theorem ev_move (hJ : JEvExists T R B.κ B.v₀) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hσ : GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (f : Cu T B.κ i) :
    (R.HW i σ).e ((R.FW i).j σ ((R.FW i).ρ (overEmb T w i σ) ((B.fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)))
      (B.v₀ i σ) = phiC (setCE T c') hV (wtA (B.κ i)) (f : T.R ((i : ℕ) + 1)) := by
  rw [overEmb, if_pos hσ, rho_e hK, hM i _ hσ hV f f.2]
  exact B.fw.evaluates hJ i σ hσ hV ⟨_, hK i _ f f.2⟩

set_option maxHeartbeats 1600000 in
theorem bar_move (hJ : JEvBar T R B.κ) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hσ : ¬ GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i) :
    ∃ v : (R.MW i σ).Vec, IsUnitV v ∧ ∀ f : Cu T B.κ i,
      (R.HW i σ).e ((R.FW i).j σ ((R.FW i).ρ (overEmb T w i σ) ((B.fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) v =
        fun g => starRingEnd ℂ (phiC (setCE T c') hV (wtA (B.κ i)) (f : T.R ((i : ℕ) + 1)) g) := by
  obtain ⟨v, hv, h⟩ := (B.bar i σ hσ hV).1 (hJ i σ hσ hV)
  refine ⟨v, hv, fun f => ?_⟩
  rw [overEmb, if_neg hσ, rho_e hK, hM i _ (good_resC T hσ) hV f f.2]
  exact h ⟨_, hK i _ f f.2⟩

set_option maxHeartbeats 3200000 in

def tieMove (hL : LawsJ (setCE T c')) (hJ : JEvExists T R B.κ B.v₀) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w) :
    @FWTie D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) B.κ B.v₀ :=
  @FWTie.mk D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) B.κ B.v₀ B.fw.alg_eq B.fw.e B.fw.ks B.fw.kap B.fw.pt
    B.fw.nrm_eq hL B.fw.chiR B.fw.hv₀ B.fw.x0
    (fun i σ hσ hV h => absurd ⟨((R.FW i).j σ).comp ((R.FW i).ρ (overEmb T w i σ)), ev_move hJ hK hM i σ hσ hV⟩ h)
    (fun i σ hσ hV _ => ev_move hJ hK hM i σ hσ hV)

set_option maxHeartbeats 3200000 in

theorem exists_geoHalf_move (hL : LawsJ (setCE T c')) (hI : InGeo B) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w)
    (hF : @Fired D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ B.O fun _ => 1) :
    ∃ B' : @GeoHalf D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) fun _ => 1,
      @GeoHalf.v₀ D G _ _ Pl0 T0 A (setCE T c') iA _ _ B' = B.v₀ := by
  have hF' := @Half.fired_upd D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ R.nW (fun i => moveForms (R.FW i) (overEmb T w i)) B.O _ hF
  refine ⟨@GeoHalf.mk D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) _ B.κ B.v₀ (tieMove hL hI.jEvExists hK hM)
    (fun i σ hσ hV => ?_) (fun i => @Half.updO D G _ _ Pl0 T0 A (setCE T c') iA R _ _ _ _ _ (B.O i))
    (fun i => @Half.omPins_upd D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ _ _ B.O i (B.pins i)) B.rhoGeo
    (fun i σ hσ hV _ => hF'.2 i σ hσ hV) (fun i _ => ⟨1, hF'.1 i⟩) (fun i _ _ => hF'.1 i), rfl⟩
  obtain ⟨v, hv, h⟩ := bar_move hI.jEvBar hK hM i σ hσ hV
  exact ⟨fun _ => ⟨v, hv, h⟩, fun h' => absurd ⟨v, hv, (tieMove hL hI.jEvExists hK hM).jK i σ, h⟩ h'⟩

end Half

omit iA in
theorem phiC_setCE_of_eq {c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ} {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D}
    (hV : T.V j σ = W) (e : c' j σ = T.cE j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC (setCE T c') hV a f = phiC T hV a f := by
  funext h
  rw [phiC_apply, phiC_apply]
  exact congrArg (fun c => (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * adel W (castDict hV (T.dict j σ))
      (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) c) (rdU (T.U j σ) f) h) e

set_option maxHeartbeats 3200000 in

theorem exists_framed_half (hP : GlobalTheory.Published.CuspRapidDecay) (hsz : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) {F : Face D A}
    (hC : GlobalTheory.Core5 R F) (B : GeoHalf T R fun _ => 1) (hU : R.LUnif) (hI : InGeo B) :
    ∃ (c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G),
      (∀ i σ, w i σ ∈ Subgroup.center G) ∧
      (∀ (i : Fin D.R.m) hV, @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin D G _ _ Pl0 T0 A (setCE T c') iA R i T.σ₀ hV) ∧
      ∃ B' : @GeoHalf D G _ _ Pl0 T0 A (setCE T c') iA (moveR R w) fun _ => 1,
        @GeoHalf.v₀ D G _ _ Pl0 T0 A (setCE T c') iA _ _ B' = B.v₀ := by
  classical
  choose c1 z hz hO hfr hs using exists_shift hP hsz hC B hU hI.jEvExists
  have ht : TieIn T R B.κ B.v₀ := ⟨B.fw.laws, B.fw.alg_eq, B.fw.kap, B.fw.hv₀, B.fw.chiR, B.fw.x0⟩
  have hpb : T.pb = R.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R B.fw.laws.toLawsM hC.lev ((B.pins ⟨0, by have := D.R.two_le_m; omega⟩).2.tuple ()).half
  have hx := GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding T R B.κ B.v₀ B.O hC.lev ht hpb B.pins
  have H : ∀ (n : ℕ) (σ : T.Q.c.F →+* ℂ), ∃ c : (T.U (n + 1) σ).Comp → ℂ, ∀ hn : n < D.R.m,
      (σ = T.σ₀ → HEq c (c1 ⟨n, hn⟩)) ∧ (σ ≠ T.σ₀ → c = T.cE (n + 1) σ) := by
    intro n σ
    by_cases hσ : σ = T.σ₀
    · subst hσ
      by_cases hn : n < D.R.m
      · exact ⟨c1 ⟨n, hn⟩, fun _ => ⟨fun _ => HEq.rfl, fun h => absurd rfl h⟩⟩
      · exact ⟨fun _ => 1, fun h => absurd h hn⟩
    · exact ⟨T.cE (n + 1) σ, fun _ => ⟨fun h => absurd h hσ, fun _ => rfl⟩⟩
  choose c hc using H
  have h0 : ∀ i : Fin D.R.m, c i T.σ₀ = c1 i := fun i => eq_of_heq ((hc i T.σ₀ i.2).1 rfl)
  have h1 : ∀ (i : Fin D.R.m) σ, σ ≠ T.σ₀ → c i σ = T.cE ((i : ℕ) + 1) σ := fun i σ => (hc i σ i.2).2
  let c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ :=
    fun j => Nat.casesOn (motive := fun j => ∀ σ : T.Q.c.F →+* ℂ, (T.U j σ).Comp → ℂ) j (fun _ _ => 1) c
  let w : Fin D.R.m → (T.Q.c.F →+* ℂ) → G := fun i σ => if σ = T.σ₀ then z i else 1
  have hK : ∀ i, ActKeeps (κ := B.κ) B.O i := fun i g f hf => by
    obtain ⟨k, hk, -⟩ := (B.pins i).2.lift.lev g
    exact ((hO i).1 g k hk f hf).1
  have hL : LawsJ (setCE T c') := lawsJ_setCE B.fw.laws fun j hj σ hσ => by
    cases j with
    | zero => exact fun _ => norm_one
    | succ n =>
      by_cases e : σ = T.σ₀
      · subst e
        have h : CUnit (c1 ⟨n, hj.2⟩) := (hO ⟨n, hj.2⟩).2.1.2.2.2.1
        rw [← h0 ⟨n, hj.2⟩] at h
        exact h
      · have h := B.fw.laws.cUnit _ hj σ hσ
        have e2 : c n σ = T.cE (n + 1) σ := h1 ⟨n, hj.2⟩ σ e
        rw [← e2] at h
        exact h
  have hM : Moves B c' w := fun i σ hσ hV f hf => by
    by_cases e : σ = T.σ₀
    · subst e
      rw [show w i T.σ₀ = z i from if_pos rfl]
      funext h
      rw [phiC_apply, phiC_apply]
      have h2 := hs i f hf h
      rw [← h0 i] at h2
      exact congrArg (_ * ·) h2
    · rw [show w i σ = 1 from if_neg e, phiC_setCE_of_eq hV (h1 i σ e)]
      have h2 := rho_e hK i 1 ⟨f, hf⟩
      rw [map_one] at h2
      have h3 := congrArg Subtype.val ((B.fw.e i).injective (Subtype.ext h2))
      exact congrArg _ h3
  have hF : @Fired D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ B.O fun _ => 1 := by
    refine ⟨fun i => ?_, fun i σ hσ hV => ?_⟩
    · have h := hO i
      rw [← h0 i] at h
      exact h
    · by_cases e : σ = T.σ₀
      · subst e
        have h := GlobalTheory.RealGeoConst.eqAt_base T R B.κ B.v₀ hC.lev ht i (B.O i) (c1 i) (hO i).1 hV
        rw [← h0 i] at h
        exact h
      · have h := B.equivAll i σ hσ hV (hx i σ hσ hV)
        rw [← h1 i σ e] at h
        exact h
  refine ⟨c', overEmb T w, fun i σ => ?_, fun i hV => hfr i c' (h0 i) hV, exists_geoHalf_move hL hI hK hM hF⟩
  have key : ∀ s, w i s ∈ Subgroup.center G := fun s => by
    by_cases e : s = T.σ₀
    · rw [show w i s = z i from if_pos e]
      exact hz i
    · rw [show w i s = 1 from if_neg e]
      exact one_mem _
  unfold overEmb
  split_ifs
  · exact key _
  · exact key _

end GlobalTheory.Unframe
