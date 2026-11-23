import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QTw
open GlobalTheory.QPl

variable {D : D7} {c : Comm D}

set_option maxHeartbeats 4000000 in

structure QGeo (v : VCom c) (B : GlobalTheory.Fam.Base c) (PP : Formalism.L2.DIV.Pl D.host.E) where
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  [mea : MeasurableSpace k]
  [bor : BorelSpace k]
  ν : Measure k
  unitVol : IsUnitVol ν
  q : GlobalTheory.FinPl.SplitPt D k
  idem : Formalism.L2.NTheta.IsIdemAt q.e PP
  unit : q.UnitAA
  ψk : AddChar k Circle
  char : (ofSplit q).IsChar c.ψ ψk
  cond : HasConductor ψk 1
  ϖ : kˣ
  unif : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ
  compl : GlobalTheory.SymBridge.IsCompl PP (Formalism.L2.Col.qOf PP) (q.pr.comp (incA D)) ϖ
  s : ℕ
  hs : s + 1 + 1 = D.R.m
  FX : ∀ j, j ≤ s + 1 → Frame k (c.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j)
  FT : Frame k c.T.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2))
  FM : Frame k (c.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)
  FY : ∀ j d, j + d = s + 1 → Frame k (c.V j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin d)
  sc : ℕ → k
  sc_ne : ∀ j, sc j ≠ 0
  sc_step : ∀ j, sc (j + 1 + 1) = sc j * (ofSplit q).xi
  bes : ∀ j ρ h d (hd : j + d = s + 1), (ofSplit q).IsBesFrame (c.B j ρ h) (sc j) (FX j (by omega)) (FY j d hd)
  jac : ∀ j ρ h d (hd : j + 1 + d = s + 1), (ofSplit q).IsJacFrame (c.J j ρ h) (sc j) ((ofSplit q).hz (c.B j ρ h))
    (FX (j + 1) (by omega)) (FY (j + 1) d hd)
  z₀ : Fin c.Lz.rank → k
  last : FM.β = fromCols ((c.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
    (Matrix.of fun r _ => ((c.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r)
  tau : ∀ h, (v.τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * sc s)) • fun i => (ofSplit q).pr ((c.bes s 0 h).ζ i)
  latX : ∀ j hj (y : XIx (Fin D.R.k) (Fin D.R.t) j → k), (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec (((FX j hj).β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (c.X j) (c.x j).L (· = q.v)
  latM : ∀ y : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit → k, (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec ((FM.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (c.X (s + 1 + 1)) (c.x (s + 1 + 1)).L (· = q.v)
  latY : ∀ j d hd (y : XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin d → k), (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec (((FY j d hd).β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (c.V j) (v.N j) (· = q.v)
  latT : ∀ y : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV c.T v.NT (· = q.v)
  gl : ∀ j d, j + d = s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin d) k →* GA D (c.V j)
  gl_loc : ∀ j d hd g, (ofSplit q).IsLoc (FY j d hd) (gl j d hd g) g
  frame : ∀ j d (hd : j + d = s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) j ≃ Fin (c.V j).rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) (c.V j) (B.b j) (B.β j)
      ((FY j d hd).β.submatrix id fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j d hd (e.symm i))
  frameTop : ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ≃ Fin c.T.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) c.T B.bT B.βT (FT.β.submatrix id e.symm)

attribute [instance] QGeo.fld QGeo.val QGeo.top QGeo.loc QGeo.mea QGeo.bor

variable {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E}

abbrev QGeo.T (G : QGeo v B PP) (δ : G.kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → G.kˣ →* ℂˣ) :=
  twistChain G.s (Fin D.R.t) (Fin D.R.k) δ hδ η

structure QGeo.UnitScal (G : QGeo v B PP) : Prop where
  sc_unit : ∀ j, valuation G.k (G.sc j) = 1
  hz_unit : ∀ j ρ h, valuation G.k ((ofSplit G.q).hz (c.B j ρ h)) = 1

theorem isOpen_ker_unram_mul_tame {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {η δ : kˣ →* ℂˣ} (hη : IsUnram η) (hδ : IsTame δ) : IsOpen ((η * δ).ker : Set kˣ) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    (x := Units.val ⁻¹' ((· - 1) ⁻¹' {x : k | valuation k x < 1}))
    (IsOpen.mem_nhds (IsOpen.preimage Units.continuous_val (IsOpen.preimage (by fun_prop) ?_)) (by simp)) fun x hx => ?_)
  · simpa using (valuation k).isOpen_ball 1
  · have h1 : valuation k (x : k) = 1 := by
      have := (valuation k).map_one_add_of_lt (x := (x : k) - 1) hx
      rwa [add_sub_cancel] at this
    change η x * δ x = 1
    rw [hη x h1, hδ x hx, one_mul]

namespace QGeo
variable (G : QGeo v B PP) (δ : G.kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → G.kˣ →* ℂˣ)

theorem T_regular : (G.T δ hδ η).Regular := Chain.ofTwist_regular _ _ _ _ _

theorem T_laws (hη : ∀ j, IsUnram (η j)) : (G.T δ hδ η).Laws := Chain.ofTwist_laws _ _ _ hη _ _

theorem T_le (j d : ℕ) (h : j + d = G.s + 1) : ((G.T δ hδ η).lev j d h).J ≤ KO G.k _ := fun g hg => by
  have := ((G.T_regular δ hδ η).2.2 j d h).2.2 hg
  rw [show (G.T δ hδ η).bas j d h = 1 from rfl, mem_stabLat] at this
  simpa using this

theorem T_leTop : (G.T δ hδ η).levTop.J ≤ KO G.k _ := fun g hg => by
  have := (TypeDatum.map_conj (parahoric (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin (G.s + 2) × Fin D.R.t) δ hδ) (LatFrame.refl G.k _)).2.2 hg
  rw [show (LatFrame.refl G.k (Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (G.s + 2))).bas = 1 from rfl, mem_stabLat] at this
  simpa using this

theorem T_openTop :
    IsOpen ((G.T δ hδ η).levTop.J : Set (GL (Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (G.s + 2)) G.k)) :=
  (TypeDatum.map_conj (parahoric (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin (G.s + 2) × Fin D.R.t) δ hδ) (LatFrame.refl G.k _)).1

example (j : ℕ) : (G.T δ hδ η).mu j = η j * δ := rfl

end QGeo

set_option maxHeartbeats 4000000 in

structure QExt (G : QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle) where
  δ : G.kˣ →* ℂˣ
  tame : IsTame δ
  η : ℕ → G.kˣ →* ℂˣ
  unr : ∀ j, IsUnram (η j)

  mu_comp : ∀ j, j ≤ G.s + 1 → (ofSplit G.q).IsComp (χ j)⁻¹ (η (j + 1) * δ)
  A : RepFam G.k G.s (XIx (Fin D.R.k) (Fin D.R.t))
  reps : (G.T δ tame η).IsRepSystem A G.ψk G.ν
  Ch : ℕ → Type
  [fC : ∀ j, Fintype (Ch j)]
  rep : ∀ j d, j + d = G.s → Ch j → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (d + 1)) G.k
  rep_bij : ∀ j d h, Set.BijOn (rep j d h) Set.univ (A j d h)
  M : ℕ
  adapt : (G.T δ tame η).Adapted A (box _ (G.ϖ ^ M)⁻¹) (box _ (G.ϖ ^ M))
  cos : Ch (G.s + 1) → (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) → G.k) ⧸ box (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1)) (G.ϖ ^ M)
  cos_inj : ∀ y y', SameOrb ((G.T δ tame η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ M)) (cos y) (cos y') → y = y'
  cos_all : ∀ z ∈ box (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1)) (G.ϖ ^ M)⁻¹,
    ∃ y, SameOrb ((G.T δ tame η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ M)) (cos y) (Submodule.Quotient.mk z)
  one : Fintype.card (Ch (G.s + 1 + 1)) = 1
  eL : ∀ j, WO (c.V j) (c.V (j + 1)) →₀ ℂ
  eLT : WO (c.V (G.s + 1)) c.T →₀ ℂ
  eL_at : ∀ j d (h : j + d = G.s), (ofSplit G.q).IsCombAt c.ψ (G.FY j (d + 1) (by omega)) (G.FY (j + 1) d (by omega)) (eL j)
    ((G.T δ tame η).Phi j d h)
  eLT_at : (ofSplit G.q).IsCombAt c.ψ (G.FY (G.s + 1) 0 rfl) G.FT eLT (G.T δ tame η).PhiTop
  dL : ∀ j, Ch j → Ch (j + 1) → WO (c.X j) (c.X (j + 1)) →₀ ℂ
  dL_mid : ∀ j d (H : j + 1 + d = G.s) α γ, (ofSplit G.q).IsCombAt c.ψ (G.FX j (by omega)) (G.FX (j + 1) (by omega)) (dL j α γ)
    ((G.T δ tame η).entry G.ψk G.ν j d H (rep j (d + 1) (by omega) α) (rep (j + 1) d H γ))
  dL_pen : ∀ α y, (ofSplit G.q).IsCombAt c.ψ (G.FX G.s (by omega)) (G.FX (G.s + 1) le_rfl) (dL G.s α y)
    ((G.T δ tame η).xiPen (box _ (G.ϖ ^ M)) (rep G.s 0 rfl α) (cos y))
  dL_top : ∀ y u, (ofSplit G.q).IsCombAt c.ψ (G.FX (G.s + 1) le_rfl) G.FM (dL (G.s + 1) y u)
    ((G.T δ tame η).xiTop (box _ (G.ϖ ^ M)) G.ψk G.ν (-1) (cos y))
  εL : ∀ j, Ch j → GA D (c.V j) →₀ ℂ
  εL_at : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → ∀ d (h : j + d = G.s) α, ∃ e,
    IsOneComb G.ψk G.ν (ρ + 1) ((G.T δ tame η).lev j (d + 1) (by omega)) (rep j d h α) e ∧
      εL j α = e.mapDomain (G.gl j (d + 1) (by omega))

  εL_zero : ∀ α, εL 0 α = Finsupp.single 1 1
  idx : ℕ → ℕ
  idx_mid : ∀ j d h, idx j = ((G.T δ tame η).lev j d h).J.relIndex (KO G.k _)
  idx_top : idx (G.s + 1 + 1) = (G.T δ tame η).levTop.J.relIndex (KO G.k _)
  m : ∀ j, Measure (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k)
  haar : ∀ j, (m j).IsHaarMeasure ∧ m j (KO G.k (XIx (Fin D.R.k) (Fin D.R.t) j)) = 1
  wt : ∀ j, Ch j → ℂ
  wt_mid : ∀ j d (h : j + d = G.s) α,
    wt j α = (((m j (prX (Cgrp ((G.T δ tame η).lev j (d + 1) (by omega)).J (rep j d h α)))).toReal⁻¹ : ℝ) : ℂ)
  wt_pen : ∀ y, wt (G.s + 1) y =
    idx (G.s + 1) * Nat.card {yb | SameOrb ((G.T δ tame η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ M)) (cos y) yb}
  wt_top : ∀ u, wt (G.s + 1 + 1) u = idx (G.s + 1 + 1)

attribute [instance] QExt.fC

namespace QExt
variable {G : QGeo v B PP} {χ : ℕ → (AE D)ˣ →* Circle} (E : QExt G χ)

theorem reg : (G.T E.δ E.tame E.η).Regular := G.T_regular _ _ _

theorem laws : (G.T E.δ E.tame E.η).Laws := G.T_laws _ _ _ E.unr

theorem le : ∀ j d h, ((G.T E.δ E.tame E.η).lev j d h).J ≤ KO G.k _ := G.T_le _ _ _

theorem leT : (G.T E.δ E.tame E.η).levTop.J ≤ KO G.k _ := G.T_leTop _ _ _

theorem openT :
    IsOpen ((G.T E.δ E.tame E.η).levTop.J : Set (GL (Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (G.s + 2)) G.k)) :=
  G.T_openTop _ _ _

theorem mu : ∀ j, j ≤ G.s + 1 →
    (ofSplit G.q).IsComp (χ j)⁻¹ (E.η (j + 1) * E.δ) ∧ IsOpen ((E.η (j + 1) * E.δ).ker : Set G.kˣ) :=
  fun j hj => ⟨E.mu_comp j hj, isOpen_ker_unram_mul_tame (E.unr _) E.tame⟩

structure Exact : Prop where
  ram : ¬ IsUnram E.δ
  unitary : ∀ x, ‖(E.δ x : ℂ)‖ = 1
  one_le : 1 ≤ E.M
  normal : (G.T E.δ E.tame E.η).RepsNormal E.A G.ϖ
  cos_mem : ∀ y, ∃ z ∈ box (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1)) (G.ϖ ^ E.M)⁻¹, Submodule.Quotient.mk z = E.cos y

example : Nonempty (E.Ch (G.s + 1)) := ⟨(E.cos_all 0 (zero_mem _)).choose⟩

example (d h α) : E.rep 0 d h α = 1 := by
  have := (E.rep_bij 0 d h).1 (Set.mem_univ α)
  rwa [E.reps.zero] at this

end QExt

set_option maxHeartbeats 4000000 in

def QExt.toAt {G : QGeo v B PP} {χ : ℕ → (AE D)ˣ →* Circle} (E : QExt G χ) : QAt v χ where
  k := G.k
  ν := G.ν
  unitVol := G.unitVol
  q := G.q
  unit := G.unit
  ψk := G.ψk
  char := G.char
  cond := G.cond
  s := G.s
  hs := G.hs
  X := XIx (Fin D.R.k) (Fin D.R.t)
  Z := Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (G.s + 2)
  T := G.T E.δ E.tame E.η
  reg := E.reg
  laws := E.laws
  bas := fun _ _ _ => rfl
  le := E.le
  leT := E.leT
  openT := E.openT
  mu := E.mu
  FX := G.FX
  FT := G.FT
  FM := G.FM
  FY := G.FY
  sc := G.sc
  sc_ne := G.sc_ne
  sc_step := G.sc_step
  bes := G.bes
  jac := G.jac
  z₀ := G.z₀
  last := G.last
  tau := G.tau
  latY := G.latY
  latT := G.latT
  gl := G.gl
  gl_loc := G.gl_loc
  A := E.A
  reps := E.reps
  Ch := E.Ch
  rep := E.rep
  rep_bij := E.rep_bij
  c₁ := (G.ϖ ^ E.M)⁻¹
  c₂ := G.ϖ ^ E.M
  adapt := E.adapt
  cos := E.cos
  cos_inj := E.cos_inj
  cos_cov := fun yb h => by
    obtain ⟨y, hy, e, -⟩ := h
    exact e ▸ E.cos_all y hy
  one := E.one
  eL := E.eL
  eLT := E.eLT
  eL_at := E.eL_at
  eLT_at := E.eLT_at
  dL := E.dL
  dL_mid := E.dL_mid
  dL_pen := E.dL_pen
  dL_top := E.dL_top
  εL := E.εL
  εL_at := E.εL_at
  idx := E.idx
  idx_mid := E.idx_mid
  idx_top := E.idx_top
  m := E.m
  haar := E.haar
  wt := E.wt
  wt_mid := E.wt_mid
  wt_pen := E.wt_pen
  wt_top := E.wt_top

example {G : QGeo v B PP} {χ : ℕ → (AE D)ˣ →* Circle} (E : QExt G χ) :
    E.toAt.T = G.T E.δ E.tame E.η ∧ E.toAt.Ch = E.Ch ∧ E.toAt.c₁ = (G.ϖ ^ E.M)⁻¹ ∧ E.toAt.c₂ = G.ϖ ^ E.M := ⟨rfl, rfl, rfl, rfl⟩

end GlobalTheory.QTw
end
