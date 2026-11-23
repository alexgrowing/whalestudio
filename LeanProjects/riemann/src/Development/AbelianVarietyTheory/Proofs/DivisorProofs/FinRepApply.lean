import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspMult

section Abstract

variable {H S X : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X]

def homInto (σ : Representation ℂ H S) (ρ : Representation ℂ H X) (C : Submodule ℂ X) : Submodule ℂ (S →ₗ[ℂ] X) where
  carrier := {f | (∀ s, f s ∈ C) ∧ ∀ g s, f (σ g s) = ρ g (f s)}
  add_mem' := by
    intro f f' hf hf'
    exact ⟨fun s => C.add_mem (hf.1 s) (hf'.1 s), fun g s => by simp [hf.2 g s, hf'.2 g s]⟩
  zero_mem' := ⟨fun _ => C.zero_mem, fun g s => by simp⟩
  smul_mem' := by
    intro a f hf
    exact ⟨fun s => C.smul_mem a (hf.1 s), fun g s => by simp [hf.2 g s]⟩

def killed (ρ : Representation ℂ H X) (I : Set (MonoidAlgebra ℂ H)) : Submodule ℂ X :=
  ⨅ x ∈ I, LinearMap.ker (ρ.asAlgebraHom x)

theorem mem_killed {ρ : Representation ℂ H X} {I : Set (MonoidAlgebra ℂ H)} {v : X} :
    v ∈ killed ρ I ↔ ∀ x ∈ I, ρ.asAlgebraHom x v = 0 := by
  simp [killed]

def irrSum [TopologicalSpace H] (ρ : Representation ℂ H X) (C : Submodule ℂ X) : Submodule ℂ X :=
  ⨆ (U : Subrepresentation ρ) (_ : U.toSubmodule ≤ C ∧ U.toRepresentation.IsIrreducible ∧
    GlobalTheory.PRep.IsAdmissible U.toRepresentation), U.toSubmodule

def IsDecomp [TopologicalSpace H] (ρ : Representation ℂ H X) (C : Submodule ℂ X) : Prop :=
  ∀ x ∈ C, IsOpen {g : H | ρ g x = x} → x ∈ irrSum ρ C

end Abstract

variable {D : D7}

def finRep {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : Representation ℂ (GfC V) (MMap M) where
  toFun g := postOn M (LinearMap.funLeft ℂ ℂ fun x => x * (g : GA D V))
  map_one' := by
    ext T v x
    simp [postOn_apply, LinearMap.funLeft]
  map_mul' a b := by
    ext T v x
    simp [postOn_apply, LinearMap.funLeft, mul_assoc]

theorem finRep_apply {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (g : GfC V) (T : MMap M) (v : M.Vec) (x : GA D V) :
    finRep M g T v x = T v (x * (g : GA D V)) := rfl

abbrev allMaps (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) : Submodule ℂ (MMap M) := Mult θ M ∅ (fun _ => 1)

def cuspMult (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) : Cardinal :=
  Module.rank ℂ (homInto σ (finRep M) (allMaps θ M))

variable (D) in

def CuspDecomp : Prop :=
  ∀ (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsDecomp (finRep M) (allMaps θ M)

structure IsFinIso (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (Pg : Finset (Pl D.host.E))
    (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (Φ : GfC V ≃ₜ* GfC V') : Prop where
  isom : HMul.hMul (HMul.hMul (Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) j)
      (V'.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)))) j =
    V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))
  conj : ∀ g : GfC V, HMul.hMul (finE V' (Φ g : GA D V')).val j = HMul.hMul j (finE V (g : GA D V)).val
  frame : ∃ (h : V.rank = V'.rank) (u : GL (Fin V'.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)),
    HMul.hMul j β.val = (β' * intGL D.host.F D.host.E V'.rank u).val.submatrix id (Fin.cast h) ∧
      ∀ PP ∈ Pg, Formalism.UG.bc (resS D.host.F PP) u = 1

theorem IsFinIso.refl (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Pg : Finset (Pl D.host.E)) :
    IsFinIso V V β β Pg 1 (ContinuousMulEquiv.refl _) where
  isom := by rw [Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  conj g := by rw [Matrix.one_mul, Matrix.mul_one]; rfl
  frame := ⟨rfl, 1, by rw [map_one, mul_one, Matrix.one_mul]; rfl, fun _ _ => map_one _⟩

abbrev princDat (n r t : ℕ) (hr : r ≤ n) (Pg : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    LevDat D.host.E ℂ n :=
  datY n r t 0 hr Pg ∅ (LevelP.triv Pg r ℂ) χ (fun _ => 1) Frm.B

section Equations

variable (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G]
  (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)

def eqSet (P : LevelP L.Pg L.r ℂ) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) :
    Set (MonoidAlgebra ℂ (GfC V)) :=
  {x | ∃ k : GfC V, (k : GA D V) ∈ levG V β (withP L P) ∧
      x = MonoidAlgebra.single k 1 - MonoidAlgebra.single 1 (levChi V β (withP L P) k)} ∪
  {x | ∃ κ : G → GfC V, (∀ g, IsLevelLift V β L (eG g) (κ g)) ∧
      x = ∑ g, MonoidAlgebra.single (κ g) (c g) - MonoidAlgebra.single 1 1} ∪
  {x | ∃ P0 ∈ ok, ∃ k ≤ V.rank, ∃ (α : GfC V) (R : Finset (GfC V)), IsHeckeAt V (pl P0) k α ∧
      Bridge.IsDC ((levG V β (flag1L L)).subgroupOf (GfC V)) α⁻¹ R ∧
      x = ∑ γ ∈ R, MonoidAlgebra.single γ 1 -
        MonoidAlgebra.single 1 ((Sg P0).coeff k / ((-1) ^ k * (q P0 : ℂ) ^ (k * (k - 1) / 2)))}

def IsGoodRep {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) : Prop :=
  ∃ v : W, v ≠ 0 ∧ (∀ k : GfC V, (k : GA D V) ∈ levG V β (flag1L L) → σ k v = v) ∧
    ∃ κ : G → GfC V, (∀ g, IsLevelLift V β L (eG g) (κ g)) ∧ ∑ g, c g • σ (κ g) v = v

end Equations

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def MultEq (R : RealDat D A Ks) : Prop :=
  ∀ (i : Fin D.R.m) (M₀ : DSModel (Yc D 0) (parA (Ptw D) 0)) (j : Matrix (Fin (Wc D i).rank) (Fin (Yc D 0).rank) (EAf D))
    (Φ : GfC (Yc D 0) ≃ₜ* GfC (Wc D i)), IsFinIso (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) R.Pg j Φ →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC (Yc D 0)) W), σ.IsIrreducible →
      GlobalTheory.PRep.IsAdmissible σ →
      IsGoodRep (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL) σ →
      cuspMult R.θ M₀ σ = cuspMult R.θ (R.MW i (sg0 D A)) (σ.comp Φ.symm.toMulEquiv.toMonoidHom)

end GlobalTheory.CuspMult

end
