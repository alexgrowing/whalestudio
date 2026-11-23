import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CXiValIff

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.OneMapTuples

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Data

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

def XiConst (ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) (c0 : ℂ) : Prop :=
  ∀ t, GlobalTheory.OneMapAll.CXiAt (Wc D i) (rank_Wc i) (inC O.c') (O.dδ t) (O.U₂ t) (O.dict₂ t) ι x₀ (O.xi t) c0

abbrev IsCls (t : Tp) (x : O.Cl' t → VsV D i O.c'.F) (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') : Prop :=
  IsThClsD (C.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f

abbrev rdQ (z : G) (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') : AutQ (Wc D i) → ℂ :=
  jFn (Wc D i) (inC O.c') (rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c'))) O.dict O.mu (actLev O.c' O.lev2 z f)

def ClsEx : Prop :=
  ∀ t x, O.Plc t x →
    ∃ f ∈ cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank, IsCls O t x f ∧
      ∀ f' ∈ sec (C.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank, IsCls O t x f' → f' = f

def PtIdent (lam : AutQ (Wc D i) → ℂ) (z : G) (c0 : ℂ) : Prop :=
  ∀ t, ∃ ze : ℂ, ze ∈ D.what₂.embLL.toRatAlgHom.fieldRange ∧ (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x, O.Plc t x →
    ∀ f ∈ sec (C.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank, IsCls O t x f →
      ∀ q, c0 * O.thAd t x q = ze * lam q * rdQ O z f q

end Data

abbrev liftQ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (v : (R.MW i (sg0 D A)).Vec) (t : T0) (x : A.fam.amb.FL i t) : AutQ (Wc D i) → ℂ :=
  onQ (Wc D i) (R.thF i t (jVx R i t x) v)

def LiftsSpan {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (v : (R.MW i (sg0 D A)).Vec) : Prop :=
  ∀ (t : T0) (x : A.fam.amb.FL i t), liftQ R i v t x ∈ Submodule.span ℂ (Set.range (liftQ R i v A.μ0))

theorem liftsSpan_of_onto {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (v : (R.MW i (sg0 D A)).Vec) (hmem : R.thP_thF_mem)
    (honto : R.Wall i (sg0 D A) ≤ Submodule.span ℂ (Set.range fun x => R.thF i A.μ0 (jVx R i A.μ0 x))) : LiftsSpan R i v := by
  intro t x
  have key : ∀ w ∈ Submodule.span ℂ (Set.range fun x => R.thF i A.μ0 (jVx R i A.μ0 x)),
      onQ (Wc D i) (w v) ∈ Submodule.span ℂ (Set.range (liftQ R i v A.μ0)) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨y, rfl⟩ := hw; exact Submodule.subset_span ⟨y, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul c a _ ha => exact Submodule.smul_mem _ c ha
  exact key _ (honto (hmem i t _))

def PinsExist (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (i : Fin D.R.m) : Prop :=
  QGuard R → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧
    O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0)

end GlobalTheory.OneMapTuples
