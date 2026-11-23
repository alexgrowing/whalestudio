import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.ProjectiveLattices.KsHecke

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
  Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def qC (P : Pl D.host.E) : ℂ := (Nat.card (kP P) : ℂ)

def sqrtQ (P : Pl D.host.E) : ℂ := ((Real.sqrt (Nat.card (kP P) : ℝ) : ℝ) : ℂ)

def IsLocAt (V : HSp D) (P : Pl D.host.E) (a : Bridge.Gf V) : Prop :=
  ∃ (e : AE D) (β : GA D V), Formalism.L2.NTheta.IsIdemAt e P ∧ β ∈ GfC V ∧ SuppAt e V β ∧
    a = (finHom V).rangeRestrict β

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levV (i : Fin D.R.m) (t : T0) : Subgroup (Bridge.Gf (Vc D i)) :=
  (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J

abbrev levW (i : Fin D.R.m) : Subgroup (GA D (Wc D i)) :=
  Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)

def IsCosetOpV (i : Fin D.R.m) (t : T0) (P : Pl D.host.E) (m : ℕ) (S : (R.HV i t).H →ₗ[ℂ] (R.HV i t).H) : Prop :=
  ∃ (α : GA D (Vc D i)) (Av : Finset (Bridge.Gf (Vc D i))),
    IsHeckeAt (Vc D i) P m α ∧ Bridge.IsDC (levV R i t) ((finHom (Vc D i)).rangeRestrict α) Av ∧
    (∀ a ∈ Av, IsLocAt (Vc D i) P a) ∧
    ∀ x, (R.HV i t).e (S x) = Bridge.dcOp Av ((R.HV i t).e x)

def IsCosetFamV (i : Fin D.R.m) (t : T0) (P : Pl D.host.E) (tV : ℕ → (R.HV i t).H →ₗ[ℂ] (R.HV i t).H) : Prop :=
  ∀ m, m ≤ D.R.nV → IsCosetOpV R i t P m (tV m)

def mu0At (i : Fin D.R.m) (P : Pl D.host.E) : ℂ := (((R.C.mu0 i).val P : ℂˣ) : ℂ)

def xiAt (t : T0) (P : Pl D.host.E) : ℂ := (((R.xiH t).val P : ℂˣ) : ℂ)

def etaAt (P : Pl D.host.E) : ℂ := ((R.C.eta.val P : ℂˣ) : ℂ)

def cW (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) : ℂ := (mu0At R i P ^ k)⁻¹ * (sqrtQ P ^ (k * D.R.nV))⁻¹

def bV (i : Fin D.R.m) (t : T0) (P : Pl D.host.E) : ℂ := mu0At R i P * xiAt R t P * (etaAt R P)⁻¹ * sqrtQ P

def TransferEq (i : Fin D.R.m) (t : T0) (P : Pl D.host.E) (k : ℕ) (Rc : Finset (GA D (Wc D i)))
    (tV : ℕ → (R.HV i t).H →ₗ[ℂ] (R.HV i t).H) : Prop :=
  ∀ x : (R.HV i t).H,
    cW R i P k • heckeOn (R.MW i (sg0 D A)) Rc (R.thF i t x) =
      xiAt R t P ^ k • R.thF i t (KsHecke.TVk (bV R i t P) (qC P) D.R.r D.R.nV D.R.t tV k x)

def TransferAt (i : Fin D.R.m) (t : T0) : Prop :=
  ∀ P : Pl D.host.E, Bridge.SplitOff P ((R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E))) →
    (∃ tV, IsCosetFamV R i t P tV) ∧
    ∀ tV, IsCosetFamV R i t P tV → ∀ k, k ≤ D.R.r → ∀ α : GA D (Wc D i), IsHeckeAt (Wc D i) P k α →
      ∀ Rc : Finset (GA D (Wc D i)), Bridge.IsDC (levW R i) α Rc → TransferEq R i t P k Rc tV

end Real

def HeckeTransfer {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) : Prop :=
  R.Char F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (t : T0), TransferAt R i t

theorem rank_Vc (i : Fin D.R.m) : (Vc D i).rank = D.R.nV ∧ D.R.nV = D.R.r + D.R.t :=
  ⟨D.sp.V_rank _ (Nat.le_add_left _ _) i.2, rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne
