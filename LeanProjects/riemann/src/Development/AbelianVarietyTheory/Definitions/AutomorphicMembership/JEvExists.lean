import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
import Formalism.LocalToGlobal.LatticeGeometry.InstAddCommSemigroupWt

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Data

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

structure PreChar : Prop where
  lev : R.toLevCh.Is A.μ0
  red_R : R.grp_red_R
  red_L : R.grp_red_L
  record : R.grp_record
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChain
  thP : R.IsThP

theorem PreChar.of_char {F : Face D A} (h : R.Char F) : PreChar R :=
  ⟨h.lev, h.grp.red_R, h.grp.red_L, h.grp.record, h.fam, h.models, h.chain, h.thP⟩

def ValKs : Prop :=
  ∀ (i : Fin D.R.m) (x : (AE D)ˣ), infPart D (x : AE D) = 1 →
    ∃ y : Ks, ((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = D.what₂.embLL (algebraMap Ks D.what₂.LL y)

def FrameKs (Ks : Type) [Field Ks] [Algebra Ks D.what₂.LL]
    (MW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), DSModel (Wc D i) (parAt (Wc D i) σ)) : Prop :=
  (∀ i σ σ', σ.comp (algebraMap Ks D.what₂.LL) = σ'.comp (algebraMap Ks D.what₂.LL) →
    ∀ ρ, x0Mat (MW i σ) ρ = x0Mat (MW i σ') ρ) ∧
  ∀ i σ, (∀ ρ, labE σ (lab σ ρ) = tauE D ρ) →
    ∀ τ a, (MW i σ).ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)

def LevKs (F : Face D A) : Prop :=
  (∀ p, ((F.ψ0 p : D.what₂.LLˣ) : D.what₂.LL) ∈ (algebraMap Ks D.what₂.LL).range) ∧
    ∀ g, (idemOf A.X).coeff g ∈ (algebraMap Ks D.what₂.LL).range

structure MjTie (F : Face D A) where
  eW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H
  eW_range : ∀ i, LinearMap.range (eW i) = (R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).comap (R.HW i (sg0 D A)).e
  eW_norm : ∀ i x, ‖eW i x‖ ^ 2 = RealDat.nP F false * ‖x‖ ^ 2
  eW_lat : ∀ (i : Fin D.R.m) x, x ∈ (D.what₂.MjLat ((i : ℕ) + 1)).carrier ↔
    ∃ y ∈ (R.FW i).MK, y ∈ (R.FW i).Wgood F.P0 F.ψ0⁻¹ (fun g => (idemOf A.X).coeff g) ∧ eW i x = (R.FW i).j (sg0 D A) y

def volRec (F : Face D A) (i : Fin D.R.m) : ℝ := (R.νW i (R.fdW i)).toReal / RealDat.nP F false

end Data

abbrev reCore (T : CoreJ D) (dict : ∀ j σ, GA D (T.V j σ) → Σ k, Frame ((T.U j σ).X k).Ψ D.R.r)
    (mu : ∀ j σ, GA D (T.V j σ) → ℂ) (chiW : ℕ → (T.Q.c.F →+* ℂ) → (AE D)ˣ →* Circle)
    (x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
    (cE : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ) : CoreJ D :=
  { Q := T.Q, U := T.U, V := T.V, dict := dict, mu := mu, Kf := T.Kf, pb := T.pb, cE := cE, chiW := chiW, x₀ := x₀,
    iota := T.iota }

abbrev setCE (T : CoreJ D) (cE : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ) : CoreJ D :=
  reCore T T.dict T.mu T.chiW T.x₀ cE

def MjCusp {T : Core D} (h : LawsCore T) (j : ℕ) (w : WeightFamilies.Wt D j) (vol : ℝ) : Prop :=
  ∃ (s : Submodule T.Q.c.F (T.C j w)) (φ : s →ₛₗ[T.σ₀] D.what₂.Mj j),
    (∀ {n : ℕ} (v : Fin n → s), LinearIndependent T.Q.c.F v → LinearIndependent ℂ (φ ∘ v)) ∧
    Submodule.span ℂ (Set.range φ) = ⊤ ∧
    (D.what₂.MjLat j).carrier ⊆ Set.range φ ∧
    (∀ x : s, (∀ la (y : T.PtM j la), 0 ≤ y.1 ((x : T.C j w) : T.R j)) ↔ φ x ∈ (D.what₂.MjLat j).carrier) ∧
    ∀ x : s, ‖φ x‖ = Real.sqrt (vol * Formalism.L2.Geo.dimKap D j) * h.Nl j w T.σ₀ ((x : T.C j w) : T.R j)

section Forms

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

open Classical in

def geoRho (i : Fin D.R.m) : G →* ((Fin (nTop T κ i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (nTop T κ i) → D.what₂.LL)) :=
  if h : HasB T.Q.c.F (Cu T κ i) (nTop T κ i) ∧ ∃ ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i),
      ∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c (O i).lev2 g (f : T.R ((i : ℕ) + 1))
  then rhoB D.what₂.LL h.1.some h.2.choose else 1

def formsGeo (i : Fin D.R.m) :
    Arith.FormsL D.what₂.LL T.Q.c.F (Fin (nTop T κ i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G :=
  { formsN T R κ v₀ i (nTop T κ i) with ρ := geoRho T R κ O i }

abbrev geoR : RealDat D A T.Q.c.F := updFW R (nTop T κ) (formsGeo T R κ v₀ O)

def Fired (ph : Fin D.R.m → ℂ) : Prop :=
  (∀ i, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) (ph i)) ∧
  ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)

end Forms

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure GeoHalf (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (ph : Fin D.R.m → ℂ) : Type 1 where
  κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)
  v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec
  fw : FWTie T R κ v₀
  bar : BarTie fw
  O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)
  pins : ∀ i, OMPins T R κ v₀ O i
  rhoGeo : RhoGeo fw O
  equivAll : EquivAll T R κ O
  cTie : ∀ i, CTie T R κ v₀ O i
  phase : ∀ i, R.LUnif → PhaseTie T R κ v₀ O ph i

structure InGeo {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {ph : Fin D.R.m → ℂ}
    (B : GeoHalf T R ph) : Prop where
  jEvExists : JEvExists T R B.κ B.v₀
  jEvBar : JEvBar T R B.κ
  evInj : EvInj T R B.v₀
  jUnif : JUnif T R B.κ B.v₀
  geoAct : GeoAct T R B.κ B.v₀
  latFull : LatFull T B.κ
  dimMatch : DimMatch T R B.κ

end GlobalTheory.RealGeo
