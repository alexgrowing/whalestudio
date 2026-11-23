import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VStdOfOrthonormalSpan

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.BigOn.Exp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Sets

variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ D.nexp i j b)

def baseSet : Set (D.nexp.Fm i ((j : ℕ) + 1) b) := {f | ∃ s h P, ρ.IsDatum i j b s h P ∧ rd f = ρ.theta i j b h P}

def twSet (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) :
    Set (D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i ((j : ℕ) + 1) b) :=
  {x | ∃ s h P, ρ.IsDatum i j b s h P ∧ rdK rd hρ k x ∈ ρ.gens i j b k Q ψ h P}

def SameBut (ρ ρ' : Setup D.ntw) : Prop := ρ'.rc = ρ.rc ∧ ρ'.ch = ρ.ch ∧ ρ'.bad = ρ.bad ∧ ρ'.B = ρ.B ∧ ρ'.om = ρ.om

theorem SameBut.symm {ρ ρ' : Setup D.ntw} (h : SameBut ρ ρ') : SameBut ρ' ρ :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

theorem isConjPl_of_lev {P P' : Pl D.host.E} (h : Lev.IsConjPl P P') : Formalism.BasicNotions.IsConjPl D.host P P' := by
  let f : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)
  have h1 : P.asIdeal ≤ P'.asIdeal.comap f := fun c hc => by
    obtain ⟨c', h2, h3⟩ := h c hc
    have e : f c = c' := RingOfIntegers.ext (by
      change D.host.conj (c : D.host.E) = (c' : D.host.E)
      rw [h3, Formalism.BasicNotions.Examples₂.star_eq_conj])
    exact Ideal.mem_comap.2 (e ▸ h2)
  have h2 := P.isMaximal.eq_of_le (Ideal.comap_ne_top f P'.isPrime.ne_top) h1
  intro x y hxy
  have e : f x = y := RingOfIntegers.ext hxy.symm
  rw [h2, Ideal.mem_comap, e]

end Sets

section Hyp

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}

structure RatHyp (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (F : Face D A3.A)
    (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (i : D.ntw.Tw) (j : Fin D.R.m)
    (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j) : Prop where
  size : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV
  host : HostHyp D
  std : VStd D j
  laws : LawsJ T
  core : GlobalTheory.Hk3.Core Rl.toRealDat F
  unif : Rl.toRealDat.LUnif
  fw : Nonempty (FWTie T Rl.toRealDat κ v₀)
  tieIn : TieIn T Rl.toRealDat κ v₀
  io : IoExt Rl.toRealDat
  guard : QGuard Rl.toRealDat
  fin : Finite T0
  pins : OMPins T Rl.toRealDat κ v₀ O j
  phase : PhaseTie T Rl.toRealDat κ v₀ O (fun j => cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j)) j
  frame : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV
  galois : IsGalois ℚ D.LL0
  small : SmallHas D Rl.C
  inUse : D.ntw.NonzeroIndexPlace i
  low : ∀ P : Pl D.host.E, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK *
    (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → P ∈ D.ntw.S0 i

theorem levelOf_congr {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks}
    {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ ρ' : Setup D.ntw} (hρ : ρ.Good) (hρ' : ρ'.Good) (hp : RealPin Rl cG ρ)
    (hp' : RealPin Rl cG ρ') (hB : ρ'.B = ρ.B)
    (hv : ∀ i b (u : D.nexp.U), ∃ x, ((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      sideEmb D.ntw i b x) (h : ρ.LevelOf D.nexp) : ρ'.LevelOf D.nexp := by
  have k := hρ.e_LL0
  have k' := hρ'.e_LL0
  have g := hp.grp
  have g' := hp'.grp
  have q := hp.Pg
  obtain ⟨h1, h2⟩ := h
  clear hρ hρ' hp hp'
  cases ρ
  cases ρ'
  cases hB
  rename_i eG _ _ _ _ _ _ _ _ _ _ eG'
  have e : ∀ i j b a, eG' i j b a = eG i j b a := fun i j b a => funext fun P => Units.ext (Matrix.ext fun c d =>
    (g' i j b a P.1 P.2 (q i j b ▸ P.2) c d).trans (g i j b a P.1 P.2 (q i j b ▸ P.2) c d).symm)
  refine ⟨fun i j b a => (e i j b a ▸ h1 i j b a :), fun i j b u hu => ?_⟩
  obtain ⟨x, hx⟩ := hv i b u
  have h3 := h2 i j b u ((h1 i j b u).2 u.2)
  rw [hx, k] at h3
  rw [hx, k', ← h3]
  congr 2
  exact Subtype.ext (e i j b u)

end Hyp

def RatStep : Prop :=
  ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw)
    (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1))
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0))
    (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j),
    RealPin Rl cG ρ → ρ.LevelOf D.nexp → D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK →
      RatHyp T Rl F κ v₀ O i j hV → RatRow YS v₀ hρ i j b

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)

abbrev Tgt (ex : Extra D L hT Gi Gl Kc Y cX) (w : D.what₂.places.Pl) (j : Fin D.R.m) : Type :=
  FmExt D.nexp (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w) (ex.nch.Oe w)

abbrev Can : Type := (Fin ((R2 p).nW j) → D.what₂.LL) →ₛₗ[ex.nch.embW w] Tgt ex w j

variable {w j} in

def IsCan (rd : Can p w j) : Prop :=
  ∀ f : NX.FmK p.Sx ((j : ℕ) + 1), rd ((p.nexp.fi j).e (Subtype.val f)) = (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)]
    (p.nexp.eF (ex.nch.twI w) _ (ex.nch.sd w) (Nat.le_add_left _ _) j.2).symm
      ((1 : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] f : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w) ⊗[p.Sx.Ks] _)

def Adapted (ρ : Setup D.ntw) : Prop :=
  RealPin p.R p.cG ρ ∧ ∃ e : FractionRing (ex.nch.Oe w) →+* ℂ, (∀ x, e (ex.nch.embW w x) = D.what₂.embLL x) ∧
    ∀ a : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w),
      e (algebraMap (ex.nch.Oe w) _ (algebraMap _ (ex.nch.Oe w) a)) = ρ.eOk (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) a

abbrev rdAt {ρ : Setup D.ntw} (hρ : ρ.Good) (ν : ℂ) : Rd ρ D.nexp (ex.nch.twI w) j (ex.nch.sd w) :=
  realRd p.nexp p.v₀ hρ (ex.nch.twI w) j (ex.nch.sd w) ν

def RatAt {ρ : Setup D.ntw} (hρ : ρ.Good) (ν : ℂ) : Prop :=
  RatBase (rdAt p w j hρ ν) ∧ ∀ s h P, ρ.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h P →
    ρ.gens (ex.nch.twI w) j (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w) h P ⊆
      Set.range (rdK (rdAt p w j hρ ν) hρ (ex.nch.k' w))

def baseLat {ρ : Setup D.ntw} (hρ : ρ.Good) (ν : ℂ) : Submodule (ex.nch.Oe w) (Tgt ex w j) :=
  Submodule.span _ ((fun f => (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] f) '' baseSet (rdAt p w j hρ ν))

def twLat {ρ : Setup D.ntw} (hρ : ρ.Good) (ν : ℂ) : Submodule (ex.nch.Oe w) (Tgt ex w j) :=
  Submodule.span _ (incl D.nexp (ex.nch.twI w) _ (ex.nch.sd w) (ex.nch.Oe w) (ex.nch.k' w) ''
    twSet hρ (rdAt p w j hρ ν) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))

variable {w j} in

def realBase (rd : Can p w j) : Submodule (ex.nch.Oe w) (Tgt ex w j) :=
  Submodule.span _ (rd '' thetaBase (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ 1 (D.plEq w) (ownAt D (D.plEq w)))

variable {w j} in

def realTw (rd : Can p w j) : Submodule (ex.nch.Oe w) (Tgt ex w j) :=
  Submodule.span _ (rd '' thetaTuple (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ 1 ((R2 p).mu (D.plEq w)))

def Fit {ρ : Setup D.ntw} (hρ : ρ.Good) (ν : ℂ) : Prop :=
  Adapted p w ρ ∧ IsNorm p.R p.v₀ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) ν ∧ RatAt p w j hρ ν ∧ ρ.LevelOf D.nexp

def PlacesAt (ρ : Setup D.ntw) : Prop :=
  (∀ P, P ∈ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q ↔ P ∈ p.R.Q (p.R.mu (D.plEq w)) ∧ P ∈ D.ntw.pD (ex.nch.twI w)) ∧
    ∀ P, (P ∈ p.R.Q (p.R.mu (D.plEq w)) ∨ ∃ P' ∈ p.R.Q (p.R.mu (D.plEq w)), Lev.IsConjPl P' P) ↔
      P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w

variable {p w j}

namespace Fit

variable {ρ : Setup D.ntw} {hρ : ρ.Good} {ν : ℂ} (h : Fit p w j hρ ν)
include h

theorem adapted : Adapted p w ρ := h.1

theorem pin : RealPin p.R p.cG ρ := h.1.1

theorem norm : IsNorm p.R p.v₀ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) ν := h.2.1

theorem rat : RatAt p w j hρ ν := h.2.2.1

theorem level : ρ.LevelOf D.nexp := h.2.2.2

end Fit

theorem levelOf_exportTie (Z : ExportTie p.nexp p.v₀) : Z.ρ.LevelOf D.nexp :=
  ⟨fun i j b => (Z.tie i j b).U_eq, fun i j b => (Z.tie i j b).psiU_eq⟩

theorem levelOf_of_sameBut (hm : RecTies p) {ρ ρ' : Setup D.ntw} (hρ : ρ.Good) (hρ' : ρ'.Good) (hp : RealPin p.R p.cG ρ)
    (hp' : RealPin p.R p.cG ρ') (hs : SameBut ρ ρ') (h : ρ.LevelOf D.nexp) : ρ'.LevelOf D.nexp := by
  refine levelOf_congr hρ hρ' hp hp' hs.2.2.2.1 (fun i b ⟨u, hu⟩ => ?_) h
  obtain ⟨g, rfl⟩ := (p.R.eG.trans p.cG).surjective u
  obtain ⟨x, -, hx⟩ := hm.level.2 i b ⟨g, (hm.level.1 g).1 hu⟩ hu
  exact ⟨x, hx⟩

theorem mem_level_iff (hm : RecTies p) {ρ : Setup D.ntw} (h : ρ.LevelOf D.nexp) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (g : p.P.Gp) : ρ.eG i j b ((p.R.eG.trans p.cG) g) ∈ (ρ.B i j b).G.P.H ↔ g ∈ p.P.P0 :=
  (h.U_eq i j b _).trans (hm.level.1 g)

theorem level_chi (hm : RecTies p) {ρ : Setup D.ntw} (hρ : ρ.Good) (h : ρ.LevelOf D.nexp) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (u : p.P.P0) (hu : ρ.eG i j b ((p.R.eG.trans p.cG) u) ∈ (ρ.B i j b).G.P.H) :
    (((ρ.B i j b).G.P.chi ⟨_, hu⟩ : ℂˣ) : ℂ) = (D.what₂.embLL (p.P.ψ0 u : D.what₂.LLˣ))⁻¹ ∧
      (((ρ.B i j b).G.P.chi ⟨_, hu⟩ : ℂˣ) : ℂ) ∈ (Formalism.L2.Host.embLL0 D).fieldRange := by
  have hU := (hm.level.1 u).2 u.2
  obtain ⟨x, hx, hy⟩ := hm.level.2 i b u hU
  have e := h.psiU_eq i j b ⟨_, hU⟩ hu
  rw [hy, hρ.e_LL0] at e
  refine ⟨e.trans ?_, x, e.symm⟩
  change D.what₂.embLL (x : D.what₂.LL) = _
  rw [hx, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]

theorem placesAt (hw : D.plEq w ∈ p.R.twPl) {ρ : Setup D.ntw} (hρ : ρ.Good) (hp : RealPin p.R p.cG ρ) : PlacesAt p w j ρ := by
  have hw' := (p.tw_iff w).1 hw
  have hL := p.charW.base.lev
  have hψ := p.Tp.psi_is w hw'
  have h2 : p.R.toRealDat.toLevCh.xiH (p.R.mu (D.plEq w)) = p.R.C.delAt (D.ntw.l (ex.nch.twI w)) * p.Tp.psi w := by
    rw [← p.tupAt w, p.tupXi _ (Or.inr ⟨w, rfl⟩), (D.what₂.muAt_or w).resolve_left hw', p.Tp.xi_tw, ex.nch.twI_l]
  obtain ⟨q, hδ, hq⟩ : ∃ q : ℕ, Formalism.L2.Host.IsDelta q (p.R.C.delAt (D.ntw.l (ex.nch.twI w))) ∧
      ∀ P : Pl D.host.E, P ∈ D.ntw.pD (ex.nch.twI w) ↔ (q : 𝓞 D.host.E) ∈ P.asIdeal := by
    refine ⟨if D.ntw.l (ex.nch.twI w) = D.host.pde then D.host.pde' else D.host.pde, ?_, fun P => ?_⟩
    · unfold Formalism.L2.Host.CharFrame.delAt
      split_ifs
      exacts [p.R.C.isDel', p.R.C.isDel]
    · rw [← Finset.mem_coe, D.ntw.pD_eq]
      rfl
  have key : ∀ P, (P ∈ p.R.Q (p.R.mu (D.plEq w)) ∨ ∃ P' ∈ p.R.Q (p.R.mu (D.plEq w)), Lev.IsConjPl P' P) ↔
      P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w := fun P => by
    refine (hL.Q_ram _ P).symm.trans ?_
    rw [h2]
    have hm : ∀ x, (p.R.C.delAt (D.ntw.l (ex.nch.twI w)) * p.Tp.psi w).loc P x =
        (p.R.C.delAt (D.ntw.l (ex.nch.twI w))).loc P x * (p.Tp.psi w).loc P x := fun _ => rfl
    by_cases hP : P ∈ D.ntw.pD (ex.nch.twI w)
    · refine iff_of_true (fun hu => ?_) (Or.inl hP)
      obtain ⟨a, ha⟩ := hψ.ord
      have h15 := (hδ.ine P ((hq P).1 hP) (D.what₂.places.resChar w ^ a)).1 fun x hx => by
        have h3 : (p.Tp.psi w).loc P x ^ (D.what₂.places.resChar w ^ a) = 1 :=
          (MonoidHom.pow_apply ..).symm.trans (congrArg (fun χ : Formalism.L2.Host.HChar D.host.E => χ.loc P x) ha)
        rw [eq_inv_of_mul_eq_one_left ((hm x).symm.trans (hu x hx)), inv_pow, h3, inv_one]
      have hl : (D.what₂.places.resChar w).Prime := ex.nch.twI_l w ▸ (D.ntw.lPrime _).out
      have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).1 (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
      have h5 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hl).1 (Nat.prime_five.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
      omega
    · have hd := hδ.unr P fun h => hP ((hq P).2 h)
      rw [or_iff_right hP, ← not_iff_not, not_not, ← hψ.ram]
      exact forall₂_congr fun x hx => by rw [hm, hd x hx, one_mul]
  refine ⟨fun P => ?_, key⟩
  rw [hρ.delta]
  refine mem_half.trans ⟨fun ⟨h1, hc⟩ => ⟨?_, h1⟩, fun ⟨h1, h3⟩ => ⟨h3, hp.deltaPl _ _ P h1 h3⟩⟩
  refine ((key P).2 (Or.inl h1)).elim id fun ⟨P', h3, h4⟩ => ?_
  have h5 := isConjPl_of_lev h4
  have h6 : P' ∈ D.ntw.pD (ex.nch.twI w) := (hq P').2 ((h5 _ _ (by simp)).2 ((hq P).1 h1))
  by_cases e : P' = P
  · exact e ▸ h3
  · exact absurd hc (((hρ.ch _).pair _ _ h5 e).1 (hp.deltaPl _ _ P' h3 h6))

end Point

def AtTw (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i →
    (Fm.D x i).what₂.places.Pl → Fin (Fm.D x i).R.m → Prop) : Prop :=
  AtPts fun Fm x hx i p => ∀ w, (Fm.D x i).plEq w ∈ p.R.twPl → ∀ j, Q Fm x hx i p w j

section AtTw

variable {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i →
  (Fm.D x i).what₂.places.Pl → Fin (Fm.D x i).R.m → Prop}

theorem AtTw.and (h : AtTw Q) (h' : AtTw Q') : AtTw fun Fm x hx i p w j => Q Fm x hx i p w j ∧ Q' Fm x hx i p w j :=
  Closed.imp (Closed.and h h') fun _ _ _ H =>
    let ⟨x0, K⟩ := EvPt.and H.1 H.2
    ⟨x0, fun x hx h0 i p r m w hw j => ⟨(K x hx h0 i p r).1 m w hw j, (K x hx h0 i p r).2 m w hw j⟩⟩

theorem AtTw.imp (h : AtTw Q) (f : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.Rows →
    More p → ∀ w, (Fm.D x i).plEq w ∈ p.R.twPl → ∀ j, Q Fm x hx i p w j → Q' Fm x hx i p w j) : AtTw Q' :=
  Closed.imp h fun Fm _ _ ⟨x0, K⟩ => ⟨x0, fun x hx h0 i p r m w hw j => f Fm x hx i p r m w hw j (K x hx h0 i p r m w hw j)⟩

theorem AtTw.of_forall (f : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.Rows →
    More p → ∀ w, (Fm.D x i).plEq w ∈ p.R.twPl → ∀ j, Q Fm x hx i p w j) : AtTw Q :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ⟨0, fun x hx _ i p => f Fm x hx i p⟩⟩⟩

end AtTw

def CanEx : Prop := AtTw fun Fm x hx i p w j => ∃ rd : Can p w j, IsCan p rd ∧
  ∃ (n : ℕ) (β : Module.Basis (Fin n) (Fm.D x i).what₂.LL (Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL)),
    LinearIndependent (FractionRing ((Fm.ex x hx i).nch.Oe w)) fun a => rd (β a)

def CanProj : Prop := AtTw fun Fm x _ i p w j => ∀ rd : Can p w j, IsCan p rd → ∀ y,
  rd ((((R2 p).FW j).eOp fun g => (idemOf p.P.A3.A.X).coeff g) y) = eExt (Fm.D x i).nexp _ _ _ _ (rd y)

def TwAdm : Prop := AtTw fun Fm x hx i _ w _ =>
  IntegralHeckeForms.TwOK ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
                     (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w) ∧
    IntegralHeckeForms.ClsQ (D := Fm.D x i) ((Fm.ex x hx i).nch.Q w) ∧ (Fm.D x i).ntw.NonzeroIndexPlace ((Fm.ex x hx i).nch.twI w)

def LowAt : Prop := AtTw fun Fm x hx i _ w _ => ∀ P : Pl (Fm.D x i).host.E,
  (((Fm.D x i).host.QS * (Fm.D x i).host.q * Ideal.absNorm (Fm.D x i).host.ccK * ((Fm.D x i).host.g 0 * (Fm.D x i).host.g 1 * (Fm.D x i).host.pde *
    (Fm.D x i).host.pde') : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ P.asIdeal → P ∈ (Fm.D x i).ntw.S0 ((Fm.ex x hx i).nch.twI w)

def RowAt : Prop := AtTw fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good), RealPin p.R p.cG ρ →
  ρ.LevelOf (Fm.D x i).nexp → RatRow p.nexp p.v₀ hρ ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)

def RatHypAt : Prop := AtTw fun Fm x hx i p w j =>
  ∃ (T' : CoreJ (Fm.D x i)) (_ : Algebra T'.Q.c.F (Fm.D x i).what₂.LL) (Rl' : RealDat3 (Fm.D x i) p.P.A3 T'.Q.c.F)
    (cG' : G0 Rl'.Pg (Fm.D x i).R.r ≃* G0g (Fm.D x i).nd) (S' : NX.RatDat (Fm.D x i).ntw) (YS' : NX.NExpRealS Rl' cG' S')
    (F' : Face (Fm.D x i) p.P.A3.A) (κ' : ∀ j : Fin (Fm.D x i).R.m, WeightFamilies.Wt (Fm.D x i) ((j : ℕ) + 1))
    (v₀' : ∀ (j : Fin (Fm.D x i).R.m) (σ : (Fm.D x i).what₂.LL →+* ℂ), (Rl'.MW j σ).Vec)
    (O' : ∀ j, OMDat T'.toCore Rl'.toRealDat j Unit (fun _ => p.P.A3.A.μ0)) (hV' : T'.V ((j : ℕ) + 1) T'.σ₀ = Wc (Fm.D x i) j),
    RatHyp T' Rl' F' κ' v₀' O' ((Fm.ex x hx i).nch.twI w) j hV' ∧
      (∀ ρ : Setup (Fm.D x i).ntw, RealPin p.R p.cG ρ → RealPin Rl' cG' ρ) ∧
      ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (b : Bool), RatRow YS' v₀' hρ ((Fm.ex x hx i).nch.twI w) j b →
        RatRow p.nexp p.v₀ hρ ((Fm.ex x hx i).nch.twI w) j b

theorem rowAt_of_ratStep (h : RatHypAt) (hR : RatStep) : RowAt :=
  AtTw.imp h fun Fm x hx i _ _ _ _ _ j ⟨T', _, Rl', cG', S', YS', F', κ', v₀', O', hV', h1, h2, h3⟩ ρ hρ hp hL =>
    h3 ρ hρ _ (hR _ _ _ _ _ _ T' Rl' cG' S' YS' F' κ' v₀' O' ρ hρ _ j _ hV' (h2 ρ hp) hL
      ⟨(Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.1, (Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.2⟩ h1)

def TieRat : Prop := AtTw fun Fm x hx i p w j => ∀ Z : ExportTie p.nexp p.v₀,
  IsNorm p.R p.v₀ (Z.ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ∧ RatAt p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))

def RecSide : Prop := AtTw fun Fm x hx i p w j => ∀ Z : ExportTie p.nexp p.v₀, RatAt p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) →
  Submodule.span ((Fm.ex x hx i).nch.Oe w) ((fun a => (1 : FractionRing ((Fm.ex x hx i).nch.Oe w)) ⊗ₜ (Fm.D x i).nexp.th _ _ _ a) ''
      IntegralHeckeForms.SgJ (Fm.D x i).nexp (twE Fm x hx i) ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w)) = baseLat p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ∧
  Submodule.span ((Fm.ex x hx i).nch.Oe w) (incl (Fm.D x i).nexp _ _ _ ((Fm.ex x hx i).nch.Oe w) ((Fm.ex x hx i).nch.k' w) ''
      ⋃ a ∈ IntegralHeckeForms.SgJ (Fm.D x i).nexp (twE Fm x hx i) ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w),
        (Fm.D x i).nexp.thPsi _ _ _ ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
          (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w) a) = twLat p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))

def AdaptEx : Prop := AtTw fun Fm x _ i p w _ => ∀ ρ : Setup (Fm.D x i).ntw, ρ.Good → RealPin p.R p.cG ρ →
  ∃ ρ' : Setup (Fm.D x i).ntw, ρ'.Good ∧ SameBut ρ ρ' ∧ Adapted p w ρ'

def ConjBase : Prop := AtTw fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → SameBut ρ ρ' → IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
    RatAt p w j hρ ν → Fit p w j hρ' ν' → baseLat p w j hρ ν = baseLat p w j hρ' ν'

def ConjTw : Prop := AtTw fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → SameBut ρ ρ' → IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
    RatAt p w j hρ ν → Fit p w j hρ' ν' → twLat p w j hρ ν = twLat p w j hρ' ν'

def TwChr : Prop := AtTw fun Fm x hx i p w j => ∀ ρ : Setup (Fm.D x i).ntw, ρ.Good → Adapted p w ρ →
  ChrEq (ρ.tw ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
      (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w)).chi (p.Tp.psi w) ∧
    p.R.xi (p.R.mu ((Fm.D x i).plEq w)) = (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).de.chi *
      (ρ.tw ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
        (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w)).chi

def TwPl : Prop := AtTw fun Fm x _ i p w j => ∀ ρ : Setup (Fm.D x i).ntw, ρ.Good → RealPin p.R p.cG ρ → PlacesAt p w j ρ

theorem twPl : TwPl := AtTw.of_forall fun _ _ _ _ _ _ _ _ hw _ _ hρ hp => placesAt hw hρ hp

def AtFit (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i) (w : (Fm.D x i).what₂.places.Pl)
    (j : Fin (Fm.D x i).R.m) (ρ : Setup (Fm.D x i).ntw), ρ.Good → ℂ → Can p w j → Prop) : Prop :=
  AtTw fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ) (rd : Can p w j), Fit p w j hρ ν → IsCan p rd →
    Q Fm x hx i p w j ρ hρ ν rd

def BaseLe : Prop := AtFit fun _ _ _ _ p w j _ hρ ν rd => realBase p rd ≤ baseLat p w j hρ ν

def BaseGe : Prop := AtFit fun _ _ _ _ p w j _ hρ ν rd => baseLat p w j hρ ν ≤ realBase p rd

def TwLe : Prop := AtFit fun _ _ _ _ p w j _ hρ ν rd => realTw p rd ≤ twLat p w j hρ ν

def TwGe : Prop := AtFit fun _ _ _ _ p w j _ hρ ν rd => twLat p w j hρ ν ≤ realTw p rd

def Steps : Prop := CanEx ∧ CanProj ∧ TwAdm ∧ RowAt ∧ TieRat ∧ RecSide ∧ AdaptEx ∧ ConjBase ∧ ConjTw ∧ BaseLe ∧ BaseGe ∧ TwLe ∧ TwGe

theorem exists_fit (h1 : TwAdm) (h2 : RowAt) (h3 : AdaptEx) : AtTw fun Fm x _ i p w j => Nonempty (ExportTie p.nexp p.v₀) ∧
    ∀ Z : ExportTie p.nexp p.v₀, ∃ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ), SameBut Z.ρ ρ ∧ Fit p w j hρ ν :=
  AtTw.imp (AtTw.and h1 (AtTw.and h2 h3)) fun _ _ _ _ _ _ hm _ _ _ ⟨a1, a2, a3⟩ => ⟨hm.2.2.series, fun Z =>
    let ⟨ρ, hρ, hs, ha⟩ := a3 Z.ρ Z.good Z.pin
    have hL := levelOf_of_sameBut hm.2.2 Z.good hρ Z.pin ha.1 hs (levelOf_exportTie Z)
    let ⟨ν, hn, hr⟩ := a2 ρ hρ ha.1 hL
    ⟨ρ, hρ, ν, hs, ha, hn, ⟨hr.1, hr.2.1 _ _ _ a1.1 a1.2.1⟩, hL⟩⟩

theorem Steps.exportSt (h : Steps) : ExportSt := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  refine Closed.imp (AtTw.and (exists_fit h3 h4 h7) (AtTw.and h1 (AtTw.and h2 (AtTw.and h5 (AtTw.and h6 (AtTw.and h8 (AtTw.and h9
    (AtTw.and h10 (AtTw.and h11 (AtTw.and h12 h13)))))))))) fun Fm _ _ ⟨x0, K⟩ => ⟨x0, fun x hx h0 i p r m v hv j => ?_⟩
  obtain ⟨⟨⟨Z⟩, a0⟩, ⟨rd, hc, hβ⟩, a2, a5, a6, a8, a9, a10, a11, a12, a13⟩ :=
    K x hx h0 i p r m ((Fm.D x i).plEq.symm v) (by rwa [Equiv.apply_symm_apply]) j
  obtain ⟨ρ, hρ, ν, hs, hf⟩ := a0 Z
  obtain ⟨hN, hR⟩ := a5 Z
  obtain ⟨r1, r2⟩ := a6 Z hR
  have b1 := le_antisymm (a10 ρ hρ ν rd hf hc) (a11 ρ hρ ν rd hf hc)
  have b2 := le_antisymm (a12 ρ hρ ν rd hf hc) (a13 ρ hρ ν rd hf hc)
  simp only [realBase, realTw, Equiv.apply_symm_apply] at b1 b2
  exact ⟨rd, hβ, a2 rd hc, (b1.trans (a8 Z.ρ ρ Z.good hρ _ ν Z.pin hs hN hR hf).symm).trans r1.symm,
    (b2.trans (a9 Z.ρ ρ Z.good hρ _ ν Z.pin hs hN hR hf).symm).trans r2.symm⟩

example {D : D7} (ρ : Setup D.ntw) : SameBut ρ ρ := ⟨rfl, rfl, rfl, rfl, rfl⟩

example {D : D7} {ρ : Setup D.ntw} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ D.nexp i j b) {s h}
    (hd : ρ.IsDatum i j b s h 0) : 0 ∈ baseSet rd := ⟨s, h, 0, hd, rd.map_zero.trans (LinearMap.map_zero _).symm⟩

end GlobalTheory.BigOn.Exp
