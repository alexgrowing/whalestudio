import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicCoreTransportEnlargedCoefficientBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelSame
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult
set_option maxHeartbeats 4000000

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.EqvMove

open Formalism.L2.DIV

variable {D : D7} (T : CoreJ D) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ)
  (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ)

abbrev datW (Pg : Finset (Pl D.host.E)) : LevDat D.host.E ℂ (Wc D i).rank :=
  datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B

def EqAtP (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {G : Type} [Group G] (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)
    (β : GL (Fin (Wc D i).rank) (EAf D)) (Pg : Finset (Pl D.host.E)) (eG : G → G0 Pg D.R.r) (X : G → ℂ) : Prop :=
  ∀ g k, Lev.IsLevelLift (Wc D i) β (datW i Pg) (eG g) k →
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) a n,
      actLev T.Q.c (fun g => (lev g, LinearMap.id)) g f ∈ T.cuspA ((i : ℕ) + 1) a n ∧
      ∃ y : T.Q.c.F, (y : ℂ) = X g ∧
        ∀ h, phiAt T i σ hV c (actLev T.Q.c (fun g => (lev g, LinearMap.id)) g f) h = σ y * phiAt T i σ hV c f (h * k)

def EquivP (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {G : Type} [Group G] (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)
    (β : GL (Fin (Wc D i).rank) (EAf D)) (Pg : Finset (Pl D.host.E)) (eG : G → G0 Pg D.R.r) (X : G → ℂ) : Prop :=
  ∀ g k, Lev.IsLevelLift (Wc D i) β (datW i Pg) (eG g) k →
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) a n,
      actLev T.Q.c (fun g => (lev g, LinearMap.id)) g f ∈ T.cuspA ((i : ℕ) + 1) a n ∧
        ∀ h, phiAt T i σ hV c (actLev T.Q.c (fun g => (lev g, LinearMap.id)) g f) h = X g * phiAt T i σ hV c f (h * k)

section Gen

variable {D : D7} (T : CoreJ D) (i : Fin D.R.m) (κi : WeightFamilies.Wt D ((i : ℕ) + 1))

theorem phi_eq_phiAt {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup)
    (cc : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (f : T.R ((i : ℕ) + 1)) : O.phi cc f = phiAt T i O.s0 O.hV cc f := by
  have key : ∀ (σ : T.Q.c.F →+* ℂ) (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W) (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ),
      adel W (castDict hV (T.dict ((i : ℕ) + 1) σ)) (muPin W (castDict hV (T.dict ((i : ℕ) + 1) σ))
        (castDict hV (T.mu ((i : ℕ) + 1) σ)) c) (rdU (T.U ((i : ℕ) + 1) σ) f) =
      castDict hV (adel (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ)
        (muPin (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ) (T.mu ((i : ℕ) + 1) σ) c) (rdU (T.U ((i : ℕ) + 1) σ) f)) := by
    intro σ W hV c
    subst hV
    rfl
  exact key O.s0 _ O.hV cc

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

theorem eqAt_iff (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup)
    (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ)
    (halg : ∀ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = (y : ℂ)) (hχ : R.grp_chiW) :
    EqAt T R κ O σ hV c ↔ EqAtP T i σ hV c (wtA (κ i)) (κ i).n O.lev (R.βW i) R.Pg (fun g => R.eG g)
      (fun g => D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)) := by
  constructor
  · intro h g k hk f hf
    obtain ⟨h1, y, hy, h2⟩ := h g k hk f hf
    exact ⟨h1, y, (halg y).symm.trans (hy.trans (hχ i g).symm), h2⟩
  · intro h g k hk f hf
    obtain ⟨h1, y, hy, h2⟩ := h g k hk f hf
    exact ⟨h1, y, (halg y).trans (hy.trans (hχ i g)), h2⟩

theorem equivAt_iff {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) (cc : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ)
    (hχ : R.grp_chiW) :
    O.EquivAt κi cc ↔ EquivP T i O.s0 O.hV cc (wtA κi) κi.n O.lev (R.βW i) R.Pg (fun g => R.eG g)
      (fun g => D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)) := by
  constructor
  · intro h g k hk f hf
    obtain ⟨h1, h2⟩ := h g k hk f hf
    refine ⟨h1, fun x => ?_⟩
    have := h2 x
    rw [phi_eq_phiAt, phi_eq_phiAt] at this
    rw [this, ← hχ i g]
  · intro h g k hk f hf
    obtain ⟨h1, h2⟩ := h g k hk f hf
    refine ⟨h1, fun x => ?_⟩
    rw [phi_eq_phiAt, phi_eq_phiAt, h2 x, ← hχ i g]

end Gen

section Congr

variable {D : D7} (T : CoreJ D) (i : Fin D.R.m)

theorem eqAtP_congr {a a' : (D.host.E →+* ℂ) × ℕ → ℕ} (ha : a' = a) {n n' : ℕ} (hn : n' = n) {σ σ' : T.Q.c.F →+* ℂ} (hσ : σ' = σ)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (hV' : T.V ((i : ℕ) + 1) σ' = Wc D i)
    {c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ} {c' : (T.U ((i : ℕ) + 1) σ').Comp → ℂ} (hc : HEq c' c)
    {G G' : Type} [iG : Group G] [iG' : Group G'] (hG : G' = G) (hi : HEq iG' iG)
    {lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La}
    {lev' : G' → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La} (hl : HEq lev' lev)
    {β β' : GL (Fin (Wc D i).rank) (EAf D)} (hβ : β' = β) {Pg Pg' : Finset (Pl D.host.E)} (hP : Pg' = Pg)
    {eG : G → G0 Pg D.R.r} {eG' : G' → G0 Pg' D.R.r} (he : HEq eG' eG) {X : G → ℂ} {X' : G' → ℂ} (hX : HEq X' X) :
    EqAtP T i σ' hV' c' a' n' lev' β' Pg' eG' X' ↔ EqAtP T i σ hV c a n lev β Pg eG X := by
  subst ha hn hσ hG hβ hP
  cases hi; cases hc; cases hl; cases he; cases hX
  rfl

theorem equivP_congr {a a' : (D.host.E →+* ℂ) × ℕ → ℕ} (ha : a' = a) {n n' : ℕ} (hn : n' = n) {σ σ' : T.Q.c.F →+* ℂ} (hσ : σ' = σ)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (hV' : T.V ((i : ℕ) + 1) σ' = Wc D i)
    {c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ} {c' : (T.U ((i : ℕ) + 1) σ').Comp → ℂ} (hc : HEq c' c)
    {G G' : Type} [iG : Group G] [iG' : Group G'] (hG : G' = G) (hi : HEq iG' iG)
    {lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La}
    {lev' : G' → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La} (hl : HEq lev' lev)
    {β β' : GL (Fin (Wc D i).rank) (EAf D)} (hβ : β' = β) {Pg Pg' : Finset (Pl D.host.E)} (hP : Pg' = Pg)
    {eG : G → G0 Pg D.R.r} {eG' : G' → G0 Pg' D.R.r} (he : HEq eG' eG) {X : G → ℂ} {X' : G' → ℂ} (hX : HEq X' X) :
    EquivP T i σ' hV' c' a' n' lev' β' Pg' eG' X' ↔ EquivP T i σ hV c a n lev β Pg eG X := by
  subst ha hn hσ hG hβ hP
  cases hi; cases hc; cases hl; cases he; cases hX
  rfl

end Congr

theorem heq_fun_of {G G' : Type} {Y : Type} (hG : G' = G) (X : G → Y) (X' : G' → Y)
    (h : ∀ g' g, HEq g' g → X' g' = X g) : HEq X' X := by
  subst hG
  exact heq_of_eq (funext fun g => h g g HEq.rfl)

theorem heq_coe_eG {E : Type} [Field E] [NumberField E] {G G' : Type} [iG : Group G] [iG' : Group G'] (hG : G' = G)
    (hi : HEq iG' iG) {Pg Pg' : Finset (Pl E)} {r : ℕ} (hP : Pg' = Pg) (e : G ≃* G0 Pg r) (e' : G' ≃* G0 Pg' r)
    (h : HEq e' e) : HEq (fun g => e' g) (fun g => e g) := by
  subst hG hP
  cases hi
  cases h
  rfl

theorem equivAll_enl : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (hX' : B'.fields.Ok) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq w'.px w.px →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        GlobalTheory.Mem.R3.Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → RSide z Wt' R' →
        ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
        ∀ (O' : ∀ i, OMDat core'.toCore R'.toRealDat i Unit (fun _ => (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → HEq (O' i').lev (z.geo.O i).lev) →
        EquivAll core' R'.toRealDat κ' O' ∧ ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          (z.geo.O i).EquivAt (z.geo.κ i) (z.core.cE ((i : ℕ) + 1) (z.geo.O i).s0) →
          (O' i').EquivAt (κ' i') (core'.cE ((i' : ℕ) + 1) (O' i').s0) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg' hcore Xg tr R' cG' hP hRS κ' hκ O' hO
  obtain ⟨h1, -, -, hR⟩ := hE
  have hι := enlEmb_spec hR
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  have hpx' : w'.px = w.px := eq_of_heq hpx
  have hG : Gc _ w'.px = Gc B w.px := by rw [hpx']; rfl
  have hi : HEq (inferInstance : Group (Gc _ w'.px)) (inferInstance : Group (Gc B w.px)) := by rw [hpx']; exact HEq.rfl
  have hχ' : R'.toRealDat.grp_chiW := hP.char.base.grp.chiW
  have hχ : z.R.toRealDat.grp_chiW := z.pins.char.base.grp.chiW
  obtain ⟨-, -, hβW, -, -, -, -, -, -, hPg, heG, -, hI, -⟩ := hRS.1
  rcases core' with ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩
  obtain ⟨hH, hl, hc, hDw, hXo, hU, hV, hdict, hmu, -, hcE, -, -, -⟩ := hcore
  obtain rfl : H' = z.core.Q.H := eq_of_heq hH
  obtain rfl : l' = z.core.Q.l := eq_of_heq hl
  obtain rfl : c' = z.core.Q.c := eq_of_heq hc
  obtain rfl : Dw' = z.core.Q.Dw := eq_of_heq hDw
  obtain rfl : Xo' = z.core.Q.Xo := eq_of_heq hXo
  obtain rfl : U' = z.core.U := eq_of_heq hU
  obtain rfl : V' = z.core.V := eq_of_heq hV
  obtain rfl : dict' = z.core.dict := eq_of_heq hdict
  obtain rfl : mu' = z.core.mu := eq_of_heq hmu
  obtain rfl : cE' = z.core.cE := eq_of_heq hcE

  refine ⟨fun i σ hg hV' hex => ?_, fun i i' hii hE => ?_⟩
  · obtain ⟨c₁, hcu, hq⟩ := hex
    have hA' := (eqAt_iff _ i R'.toRealDat κ' (O' i) σ hV' c₁ halg' hχ').1 hq
    obtain ⟨a1, a2, a3⟩ := hκ i i rfl
    have ha : wtA (κ' i) = wtA (z.geo.κ i) := by
      have e1 := eq_of_heq a1
      have e2 := eq_of_heq a2
      unfold wtA
      rw [e1, e2]
      rfl
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hιc⟩ := hI i i rfl
    obtain ⟨-, -, hchi, -⟩ := hιc (enlEmb hR) hι
    have hX : HEq (fun g => (w'.st Z').toD7.what₂.embLL (((R'.FW i).chi g : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL))
        (fun g => (w.st Z).toD7.what₂.embLL (((z.R.FW i).chi g : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) :=
      heq_fun_of hG _ _ fun g' g hgg => by rw [hchi g' g hgg]; exact hι _
    have he := heq_coe_eG hG hi (eq_of_heq hPg) z.R.eG R'.eG heG
    have hβ : R'.βW i = z.R.βW i := congrFun (eq_of_heq hβW) i
    have key := eqAtP_congr z.core i ha a3 (σ := σ) (σ' := σ) rfl hV' hV' (c := c₁) (c' := c₁) HEq.rfl hG hi (hO i i rfl) hβ
      (eq_of_heq hPg) he hX
    have hA := key.1 ((hA'))
    have hz := z.geo.equivAll i σ hg hV' ⟨c₁, hcu, (eqAt_iff z.core i z.R.toRealDat z.geo.κ (z.geo.O i) σ hV' c₁ z.alg_eq hχ).2 hA⟩
    have hB := (eqAt_iff z.core i z.R.toRealDat z.geo.κ (z.geo.O i) σ hV' _ z.alg_eq hχ).1 hz
    have key2 := eqAtP_congr z.core i ha a3 (σ := σ) (σ' := σ) rfl hV' hV' (c := z.core.cE ((i : ℕ) + 1) σ)
      (c' := z.core.cE ((i : ℕ) + 1) σ) HEq.rfl hG hi (hO i i rfl) hβ (eq_of_heq hPg) he hX
    exact (eqAt_iff _ i R'.toRealDat κ' (O' i) σ hV' _ halg' hχ').2 ((key2.mpr hB))

  · obtain rfl : i = i' := Fin.ext hii
    obtain ⟨a1, a2, a3⟩ := hκ i i rfl
    have ha : wtA (κ' i) = wtA (z.geo.κ i) := by
      have e1 := eq_of_heq a1
      have e2 := eq_of_heq a2
      unfold wtA
      rw [e1, e2]
      rfl
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hιc⟩ := hI i i rfl
    obtain ⟨-, -, hchi, -⟩ := hιc (enlEmb hR) hι
    have hX : HEq (fun g => (w'.st Z').toD7.what₂.embLL (((R'.FW i).chi g : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL))
        (fun g => (w.st Z).toD7.what₂.embLL (((z.R.FW i).chi g : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) :=
      heq_fun_of hG _ _ fun g' g hgg => by rw [hchi g' g hgg]; exact hι _
    have he := heq_coe_eG hG hi (eq_of_heq hPg) z.R.eG R'.eG heG
    have hβ : R'.βW i = z.R.βW i := congrFun (eq_of_heq hβW) i
    have hB := (equivAt_iff z.core i (z.geo.κ i) z.R.toRealDat (z.geo.O i) _ hχ).1 hE
    have hσ : (O' i).s0 = (z.geo.O i).s0 := (sOv_eq _ _ _).trans (sOv_eq _ _ _).symm
    have key := equivP_congr z.core i ha a3 hσ (z.geo.O i).hV (O' i).hV (c := z.core.cE ((i : ℕ) + 1) (z.geo.O i).s0)
      (c' := z.core.cE ((i : ℕ) + 1) (O' i).s0) (by rw [hσ]) hG hi (hO i i rfl) hβ (eq_of_heq hPg) he hX
    exact (equivAt_iff (D := (w'.st Z').toD7) _ i (κ' i) R'.toRealDat (O' i) _ hχ').2 ((key.mpr hB))

end GlobalTheory.Mem.R3.Rw.EqvMove

end
