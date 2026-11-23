import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult

namespace GlobalTheory.Mem.R3.Rw.GeoTies

def ModelSame {D D' : D7} {V : HSp D} {V' : HSp D'} {S : D.what₂.Tau → SPar} {S' : D'.what₂.Tau → SPar}
    (M : DSModel V S) (M' : DSModel V' S') : Prop :=
  HEq M'.H M.H ∧ HEq M'.nacg M.nacg ∧ HEq M'.ips M.ips ∧ HEq M'.σ M.σ ∧ HEq M'.lam M.lam ∧ HEq M'.ε M.ε ∧ HEq M'.fr M.fr

theorem ModelSame.refl {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : ModelSame M M :=
  ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

section Two

variable {D D' : D7} {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 T0 Pl0' T0' : Type}
  {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {A' : FamIn D'.what₂.LL G' Pl0' T0' D'.R.m}

def MWOver {Ks Ks' : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' D'.what₂.LL]
    (R : RealDat D A Ks) (R' : RealDat D' A' Ks') : Prop :=
  ∀ (i : Fin D.R.m) (i' : Fin D'.R.m), (i : ℕ) = i' → ∀ ι : D.what₂.LL →+* D'.what₂.LL, (∀ x, D'.what₂.embLL (ι x) = D.what₂.embLL x) →
    ∀ σ' : D'.what₂.LL →+* ℂ, ModelSame (R.MW i (σ'.comp ι)) (R'.MW i' σ')

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  {C' : Formalism.L2.Pj.Core D'} [Algebra C'.Q.c.F D'.what₂.LL] {R' : RealDat D' A' C'.Q.c.F} {i' : Fin D'.R.m}

def OmOver (O : OMDat C R i Unit (fun _ => A.μ0)) (O' : OMDat C' R' i' Unit (fun _ => A'.μ0)) : Prop :=
  HEq O'.lev O.lev ∧ ∃ (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff C.Q.l) (hle : O.c'.F ≤ c.F), HEq O'.c' c ∧
    ∀ h J, RepsR R i A.μ0 h (O.bad ()) J (O.Lh ()) (O.gam ()) (O.vol ()) →
      ∃ h' J', RepsR R' i' A'.μ0 h' (O'.bad ()) J' (O'.Lh ()) (O'.gam ()) (O'.vol ()) ∧
        ∀ (x₀ : A.fam.amb.FL i A.μ0) (x : O.Cl' () → VsV D i O.c'.F), Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x →
          ∀ y' : (R'.HV i' A'.μ0).H, HEq y' (jVx R i A.μ0 x₀) →
            ∃ x' : O'.Cl' () → VsV D' i' O'.c'.F, Place R' i' A'.μ0 h' O'.c0' y' x' ∧
              ∀ a n, ∀ f ∈ sec (C.Q.Xo ((i : ℕ) + 1)) O.c' a n, GlobalTheory.OneMapAll.IsSum O () x f →
                ∀ f' : Rul (C'.Q.Xo ((i' : ℕ) + 1)) O'.c', HEq f' (GlobalTheory.FieldBC.rulBC hle f) → GlobalTheory.OneMapAll.IsSum O' () x' f'

end Two

end GlobalTheory.Mem.R3.Rw.GeoTies

end
