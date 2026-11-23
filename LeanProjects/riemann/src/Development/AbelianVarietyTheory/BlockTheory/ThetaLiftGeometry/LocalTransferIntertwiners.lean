import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.InertSphericalIndices

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsInertPl (P : Pl D.host.E) : Prop :=
  Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal

def IsLocA (V : HSp D) (P : Pl D.host.E) (α : GA D V) : Prop :=
  α ∈ GfC V ∧ ∃ ε : AF D.host.F, IsPlaceIdem D (P.under (𝓞 D.host.F)) ε ∧
    ∀ a b, algebraMap (AF D.host.F) (AE D) ε * (mt V α - 1) a b = (mt V α - 1) a b

def IsLocF (V : HSp D) (P : Pl D.host.E) (x : Bridge.Gf V) : Prop :=
  ∃ α : GA D V, IsLocA V P α ∧ (x : GL _ _) = finHom V α

def InertIx (V : HSp D) : Type := {y : Pl D.host.E × Bridge.Gf V // IsInertPl y.1 ∧ IsLocF V y.1 y.2}

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable (A) in

abbrev SphIx (j : Fin D.R.m) (t : T) : Type := (A.ok t × ℕ) ⊕ InertIx (Vc D j)

variable (R : RealDat D A Ks) (F : Face D A)

def IsSphOp (j : Fin D.R.m) (t : T) : SphIx A j t → Module.End ℂ (R.HV j t).H → Prop
  | Sum.inl i, TV => ∀ f : (A.MtCSD j t).Forms, TV (R.jV j t f) = R.jV j t (A.heckeL j t i f)
  | Sum.inr y, TV => ∃ B : Finset (Bridge.Gf (Vc D j)),
      Bridge.IsDC (levEnv (Vc D j) (R.βV j) (R.datVt j t)).J y.1.2 B ∧ (∀ a ∈ B, IsLocF (Vc D j) y.1.1 a) ∧
        ∀ f, (R.HV j t).e (TV f) = Bridge.dcOp B ((R.HV j t).e f)

variable (A) in

def HasResC (j : Fin D.R.m) (Sg : Pl0 → D.what₂.LL[X]) (x : SphIx A j A.μ0 → ℂ) : Prop :=
  ∀ P : A.ok A.μ0, Formalism.L2.Col.heckePolyOf (A.r + A.t) (A.q P) (fun k => x (Sum.inl (P, k))) =
    (Sg P * (A.fam.L j A.μ0).blockProd P).map D.what₂.embLL

abbrev OpsV : Type := ∀ (j : Fin D.R.m) (t : T), SphIx A j t → Module.End ℂ (R.HV j t).H

abbrev OpsW : Type := ∀ (j : Fin D.R.m) (t : T), SphIx A j t → Module.End ℂ (R.HW j (sg0 D A)).H

def Intw (TV : OpsV R) (hW : OpsW R) : Prop :=
  ∀ j t i, R.thG j t ∘ₗ TV j t i = hW j t i ∘ₗ R.thG j t

def Comm (hW : OpsW R) : Prop := ∀ j, Formalism.L2.Col.PairComm (hW j A.μ0)

def Parts (hW : OpsW R) : Prop :=
  ∀ j (p : A.fam.base.Ix), R.Wp j p =
    Formalism.L2.Col.eigSum (hW j A.μ0) (HasResC A j (trLift A.r D.R.m A.t A.q A.etaVal p.1))

def HeckeOps : Prop :=
  ∃ (TV : OpsV R) (hW : OpsW R), (∀ j t i, IsSphOp R j t i (TV j t i)) ∧ Intw R TV hW ∧ Comm R hW ∧ Parts R hW

def HeckeLifts : Prop := R.Char F → HeckeOps R

def goodPr (j : Fin D.R.m) : Module.End ℂ (R.HW j (sg0 D A)).H :=
  ∑ g, RealDat.eC (A := A) (sg0 D A) g • R.gW j (sg0 D A) g

def IsOpW (j : Fin D.R.m) (α : GA D (Wc D j)) (TW : Module.End ℂ (R.HW j (sg0 D A)).H) : Prop :=
  ∃ B : Finset (GA D (Wc D j)), Bridge.IsDC (levG _ (R.βW j) (R.datWp j R.triv)) α B ∧
    ∀ f, (R.HW j (sg0 D A)).e (TW f) = heckeOn (R.MW j (sg0 D A)) B ((R.HW j (sg0 D A)).e f)

def IsTransfer (j : Fin D.R.m) (t : T) : SphIx A j t → Module.End ℂ (R.HW j (sg0 D A)).H → Prop
  | Sum.inl i, H => ∃ TW : ℕ → Module.End ℂ (R.HW j (sg0 D A)).H,
      (∀ a ≤ (Wc D j).rank, ∃ α, IsHeckeAt (Wc D j) (R.pl i.1) a α ∧ IsOpW R j α⁻¹ (TW a)) ∧
      ((-1) ^ i.2 * (A.q i.1 : ℂ) ^ (i.2 * (i.2 - 1) / 2)) • H =
        ∑ a ∈ Finset.range (min i.2 (Wc D j).rank + 1),
          ((-1) ^ a * (A.q i.1 : ℂ) ^ (a * (a - 1) / 2) *
            (D.what₂.embLL (A.etaVal i.1 : D.what₂.LL) * (A.q i.1 : ℂ) ^ ((A.t + 1) / 2)) ^ a *
            D.what₂.embLL (((A.fam.L j t).blockProd i.1).coeff (i.2 - a))) • (TW a * goodPr R j)
  | Sum.inr y, H => H ∈ Submodule.span ℂ
      {H' | ∃ α TW, IsLocA (Wc D j) y.1.1 α ∧ IsOpW R j α TW ∧ H' = TW * goodPr R j}

def HeckeOpsNamed : Prop :=
  ∃ (TV : OpsV R) (hW : OpsW R), (∀ j t i, IsSphOp R j t i (TV j t i)) ∧ (∀ j t i, IsTransfer R j t i (hW j t i)) ∧
    Intw R TV hW ∧ Comm R hW ∧ Parts R hW

def HeckeLiftsNamed : Prop := R.Char F → HeckeOpsNamed R

theorem HasResC.zero {j : Fin D.R.m} {Sg : Pl0 → D.what₂.LL[X]} {x : SphIx A j A.μ0 → ℂ} (h : HasResC A j Sg x) (P : A.ok A.μ0) :
    x (Sum.inl (P, 0)) = D.what₂.embLL ((Sg P * (A.fam.L j A.μ0).blockProd P).coeff 0) := by
  have h0 := congrArg (fun f : ℂ[X] => f.coeff 0) (h P)
  simp only [Formalism.L2.Col.heckePolyOf, finset_sum_coeff, coeff_C_mul_X_pow, coeff_map] at h0
  rw [← h0, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
  · intro hb
    simp at hb

end GlobalTheory.IndefiniteRowSideFullHecke.InertSphericalIndices

end
