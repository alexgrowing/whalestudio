import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefInjective

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.LiftScalarCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}
variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Source

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem span_jVx (hV : R.models_HV) (hj : R.models_jV) : Submodule.span ℂ (Set.range (jVx R i A.μ0)) = ⊤ := by
  have h0 : (R.HV i A.μ0).e '' Set.range (jVx R i A.μ0) = Set.range (R.B.jL i A.μ0) :=
    (Set.range_comp _ _).symm.trans (congrArg Set.range (funext (hj i A.μ0)))
  have h1 : (Submodule.span ℂ (Set.range (jVx R i A.μ0))).map (R.HV i A.μ0).e = (⊤ : Submodule ℂ _).map (R.HV i A.μ0).e :=
    ((Submodule.map_span _ _).trans (congrArg (Submodule.span ℂ) h0)).trans
      ((GlobalTheory.PresBasic.ext_span (R.B.L i A.μ0).pres).trans ((hV i A.μ0).2.1.symm.trans (LinearMap.range_eq_map _)))
  exact Submodule.map_injective_of_injective (hV i A.μ0).1 h1

end Source

section Target

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem eval_inj (hW : R.models_HW) {v₀ : (R.MW i (sg0 D A)).Vec} (hv : IsChosenExtremalVector R i (sg0 D A) v₀) {x y : (R.HW i (sg0 D A)).H}
    (h : (R.HW i (sg0 D A)).e x v₀ = (R.HW i (sg0 D A)).e y v₀) : x = y := by
  have h0 : (R.HW i (sg0 D A)).e (x - y) v₀ = 0 := by
    rw [LinearMap.map_sub]
    exact sub_eq_zero.2 h
  have h1 := (hW i (sg0 D A)).2.2 (x - y) (x - y)
  rw [ipAt, GlobalTheory.EvalAtUnitVector.ipM_self_eq_zero _ _ _ _ v₀ (IsChosenExtremalVector.norm R hv) h0, mul_zero] at h1
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)

theorem eC_idem (hr : R.grp_record) : GoodBasisCentralIdempotents.IsCentralIdem (RealDat.eC (A := A) (sg0 D A)) := by
  obtain ⟨eR, _, _, h, _⟩ := hr
  have h0 : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have h1 : ∀ g, RealDat.eC (A := A) (sg0 D A) g = D.ntypes.e0.coeff (eR g) := fun g => by rw [h0]; exact h g
  obtain ⟨h2, h3⟩ := GlobalTheory.GoodLatCompare.isCentralIdempotent_of_goodSeriesIdempotent (D := D) (RingHom.id ℂ) (eC := fun g => D.ntypes.e0.coeff g) fun _ => rfl
  refine ⟨fun g k => ?_, fun g => ?_⟩
  · rw [h1, h1, map_mul eR, map_mul eR, map_inv eR]
    exact h2 _ _
  · rw [h1]
    refine Eq.trans (Fintype.sum_equiv eR.toEquiv _ _ fun k => ?_) (h3 (eR g))
    rw [h1, h1, map_mul eR, map_inv eR]
    rfl

def projW (R : RealDat D A Ks) (i : Fin D.R.m) : (R.HW i (sg0 D A)).H →ₗ[ℂ] (R.HW i (sg0 D A)).H :=
  ∑ g, RealDat.eC (A := A) (sg0 D A) g • R.gW i (sg0 D A) g

theorem postOn_of_good {P : LevelP R.Pg D.R.r ℂ} {U : MMap (R.MW i (sg0 D A))} (hU : U ∈ R.Wat i (sg0 D A) P) :
    postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) U = U :=
  sub_eq_zero.1 (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hU).2)

def GoodScalar (R : RealDat D A Ks) (i : Fin D.R.m) (c : HookProductDictionary.EigSys D) (l : ℝ) : Prop :=
  ∀ U ∈ R.Wat i (sg0 D A) R.triv ⊓ AdelicScalarSectionLift.cuspPart R i c, ∃ y : (R.HV i A.μ0).H,
    (∀ f, ipAt (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) U (R.thF i A.μ0 f) = ⟪y, f⟫_ℂ) ∧
      postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) (R.thF i A.μ0 y) = (l : ℂ) • U

end Target

section Geometric

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  (O : OMDat C R i Unit (fun _ => A.μ0)) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ)

def tr : AdelicScalarSectionLift.Sec O →ₗ[ℂ] AdelicScalarSectionLift.Sec O := GlobalTheory.CuspSecCompare.trunc (C.U ((i : ℕ) + 1) O.s0).X

structure DictFacts : Prop where
  dom : ∀ g, (O.dict g).2 ∈ ((C.U ((i : ℕ) + 1) O.s0).X (O.dict g).1).dom
  mu : ∀ g, ‖O.mu g‖ = 1
  cc : ∀ k, ‖cc k‖ = 1
  lifts : Lev.LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv)

def prin : Submodule ℂ (AdelicScalarSectionLift.Sec O) where
  carrier := {S | Lev.HasType (Wc D i) (R.βW i) (R.datWp i R.triv) (AdelicScalarSectionLift.dict O κ cc S)}
  zero_mem' := fun k _ h => by
    rw [LinearMap.map_zero]
    exact (mul_zero _).symm
  add_mem' := fun {S S'} hS hS' k hk h => by
    rw [LinearMap.map_add]
    exact (congrArg₂ (· + ·) (hS k hk h) (hS' k hk h)).trans (mul_add _ _ _).symm
  smul_mem' := fun a S hS k hk h => by
    rw [LinearMap.map_smul]
    exact (congrArg (a * ·) (hS k hk h)).trans (mul_left_comm _ _ _)

def IntOn (S S' : AdelicScalarSectionLift.Sec O) : Prop :=
  IntegrableOn (fun g => AdelicScalarSectionLift.unitVal O κ S g * star (AdelicScalarSectionLift.unitVal O κ S' g)) (R.fdW i) (R.νW i)

variable {O cc} (hd : DictFacts O cc)
include hd

omit hd

variable (O cc)

def DictOnM (v₀ : (R.MW i (sg0 D A)).Vec) (P : LevelP R.Pg D.R.r ℂ) : Prop :=
  (∀ S ∈ AdelicScalarSectionLift.goodAt O κ cc P ⊓ prin O κ cc, AdelicScalarSectionLift.dict O κ cc S = 0 → S = 0) ∧
  (∀ S ∈ AdelicScalarSectionLift.goodAt O κ cc P ⊓ prin O κ cc, ∃ U ∈ R.Wat i (sg0 D A) P, U v₀ = AdelicScalarSectionLift.dict O κ cc S) ∧
  ∀ S ∈ AdelicScalarSectionLift.goodAt O κ cc P ⊓ prin O κ cc, ∀ S' ∈ AdelicScalarSectionLift.goodAt O κ cc P ⊓ prin O κ cc,
    ∀ U ∈ R.Wall i (sg0 D A), ∀ U' ∈ R.Wall i (sg0 D A), U v₀ = AdelicScalarSectionLift.dict O κ cc S → U' v₀ = AdelicScalarSectionLift.dict O κ cc S' →
      IntOn O κ S S' ∧ AdelicScalarSectionLift.ipSec O κ P S S' = ((Nat.card P.H : ℕ) : ℂ)⁻¹ * ipAt (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) U' U

def ActsOn (L : (R.HV i A.μ0).H →ₗ[ℂ] AdelicScalarSectionLift.Sec O) (P : LevelP R.Pg D.R.r ℂ) (c : HookProductDictionary.EigSys D) (l : ℝ) : Prop :=
  ∀ S ∈ AdelicScalarSectionLift.partAt O κ cc P c ⊓ prin O κ cc, ∃ y ∈ AdelicScalarSectionLift.srcAt R i P,
    (∀ f ∈ AdelicScalarSectionLift.srcAt R i P, IntOn O κ (L f) S ∧ AdelicScalarSectionLift.ipSec O κ P (L f) S = AdelicScalarSectionLift.ipSrc R i P f y) ∧ L y = (l : ℂ) • S

variable {O cc}

include hd

omit hd

end Geometric

section Main

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

abbrev Bound (i : Fin D.R.m) (b l : ℝ) : Prop :=
  AdelicScalarSectionLift.hookSum D i - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * AdelicScalarSectionLift.logSize D b ≤ Real.log l

def CommonPart (i : Fin D.R.m) : Prop :=
  R.Char F → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → HookProductDictionary.RegularGaps D →
  ∀ (cc : (T.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ph : ℂ), (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph →
    ∀ h, AdelicScalarSectionLift.IsRepSystem (O i) (v₀ i (sg0 D A)) h →
      (∃ th, AdelicScalarSectionLift.IsSecLift (O i) (κ i) h th) ∧ (∃ e, AdelicScalarSectionLift.IsSrcProj R i e) ∧
      ∀ s, DictOnM (O i) (κ i) cc (v₀ i (sg0 D A)) (AdelicScalarSectionLift.level R F s) ∧
        ∀ c, AdelicScalarSectionLift.partAt (O i) (κ i) cc (AdelicScalarSectionLift.level R F s) c ⊓ prin (O i) (κ i) cc ≠ ⊥ →
          ∃ l : ℝ, 0 < l ∧ (R.Wat i (sg0 D A) R.triv ⊓ AdelicScalarSectionLift.cuspPart R i c ≠ ⊥ ∧ GoodScalar R i c l) ∧
            (∀ th e, AdelicScalarSectionLift.IsSecLift (O i) (κ i) h th → AdelicScalarSectionLift.IsSrcProj R i e →
              ActsOn (O i) (κ i) cc (th ∘ₗ e) (AdelicScalarSectionLift.level R F s) c l) ∧
            ∀ b, (∀ j, AdelicScalarSectionLift.IsSize D j b) → Bound i b l

def ExtraClauses : Prop :=
  R.Char F → Nonempty (FWTie T R κ v₀) → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i →
  ∀ (cc : (T.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ph : ℂ), (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph →
    AdelicScalarSectionLift.DictClauses (O i) (κ i) cc F (v₀ i (sg0 D A)) ∧
    ∀ h, AdelicScalarSectionLift.IsRepSystem (O i) (v₀ i (sg0 D A)) h →
      (∀ th th', AdelicScalarSectionLift.IsSecLift (O i) (κ i) h th → AdelicScalarSectionLift.IsSecLift (O i) (κ i) h th' → th = th') ∧
      ∀ b, AdelicScalarSectionLift.IsSize D i b → ∀ th, AdelicScalarSectionLift.IsSecLift (O i) (κ i) h th →
        (∀ y, th y ∈ AdelicScalarSectionLift.cuspC (O i) (κ i)) ∧
        (∃ (u : ℂ) (z : G), ‖u‖ = 1 ∧ z ∈ Subgroup.center G ∧ ∀ y,
          actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG z) (AdelicScalarSectionLift.dict (O i) (κ i) cc (th y)) =
            u • R.thF i A.μ0 y (v₀ i (sg0 D A))) ∧
        ∀ s c, AdelicScalarSectionLift.partAt (O i) (κ i) cc (AdelicScalarSectionLift.level R F s) c ≠ ⊥ → ∀ l, GoodScalar R i c l →
          AdelicScalarSectionLift.IsAdelicScalar R i c l ∧ ((¬ ∀ j, AdelicScalarSectionLift.IsSize D j b) → Bound i b l)

variable {T R F κ v₀ O}

variable (T R F κ v₀ O)

end Main

end GlobalTheory.LiftScalarCompare

end
