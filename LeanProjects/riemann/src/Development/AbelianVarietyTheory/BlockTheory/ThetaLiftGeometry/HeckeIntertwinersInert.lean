import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Polynomial
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev plF (PP : Pl D.host.E) : HeightOneSpectrum (𝓞 D.host.F) := PP.under (𝓞 D.host.F)

def IsInertPl (PP : Pl D.host.E) : Prop :=
  Formalism.UG.IsInertAt D.host.F D.host.E (plF PP) PP

def LocAt (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Bridge.Gf V) : Prop :=
  ∀ v', v' ≠ v →
    ((x : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _).map
      (Algebra.TensorProduct.map (evalV D.host.F v') (AlgHom.id D.host.F D.host.E)) = 1

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev levX (R : RealDat D A Ks) (t : T) : Subgroup (Bridge.Gf D.sp.X') := (levEnv D.sp.X' R.βX (R.datXt t)).J

def IsInertDC (R : RealDat D A Ks) (t : T) (PP : Pl D.host.E) (x : Bridge.Gf D.sp.X') (B : Finset (Bridge.Gf D.sp.X')) : Prop :=
  IsInertPl PP ∧ PP ∉ R.Sb ∧ PP ∉ R.Q t ∧ LocAt D.sp.X' (plF PP) x ∧ (∀ b ∈ B, LocAt D.sp.X' (plF PP) b) ∧
    Bridge.IsDC (levX R t) x B

abbrev InertIx (R : RealDat D A Ks) (t : T) : Type :=
  {a : Pl D.host.E × Bridge.Gf D.sp.X' × Finset (Bridge.Gf D.sp.X') // IsInertDC R t a.1 a.2.1 a.2.2}

def IsInertOp (R : RealDat D A Ks) (t : T) (i : InertIx R t) (U : Module.End ℂ (R.HX t).H) : Prop :=
  ∀ f, (R.HX t).e (U f) = Bridge.dcOp i.1.2.2 ((R.HX t).e f)

theorem IsInertOp.unique {R : RealDat D A Ks} {F : Face D A} (hC : R.Char F) {t : T} {i : InertIx R t}
    {U U' : Module.End ℂ (R.HX t).H} (h : IsInertOp R t i U) (h' : IsInertOp R t i U') : U = U' :=
  LinearMap.ext fun f => (hC.models.HX t).1 ((h f).trans (h' f).symm)

def HasResC (A : FamIn D.what₂.LL G Pl0 T D.R.m) (p : Pl0 → D.what₂.LL[X]) (x : A.ok A.μ0 × ℕ → ℂ) : Prop :=
  ∀ P : A.ok A.μ0, Col.heckePoly (A.fam.R A.μ0).n (A.fam.R A.μ0).q x P =
    (p ((A.fam.R A.μ0).pl P) * (A.fam.R A.μ0).blockProd P).map D.what₂.embLL

section Fam

variable (R : RealDat D A Ks) {I : T → Type} (lab : ∀ t, I t → InertIx R t)
  (hE : ∀ t, (A.ok t × ℕ) ⊕ I t → Module.End ℂ R.HE.H)

def IntwSplit : Prop :=
  ∀ t (i : A.ok t × ℕ) (f : (A.MtildeCSD t).Forms),
    R.Th t (R.jX t (A.heckeR t i f)) = hE t (Sum.inl i) (R.Th t (R.jX t f))

def IntwInert : Prop :=
  ∀ t (i : I t) (U : Module.End ℂ (R.HX t).H), IsInertOp R t (lab t i) U →
    R.Th t ∘ₗ U = hE t (Sum.inr i) ∘ₗ R.Th t

def Comm : Prop := Col.PairComm (hE A.μ0)

def Parts : Prop :=
  ∀ p : A.fam.base.Ix, R.EEp p = Col.eigSum (hE A.μ0) fun x => HasResC A p.1 fun i => x (Sum.inl i)

def RowsAt : Prop :=
  ∃ hE : ∀ t, (A.ok t × ℕ) ⊕ I t → Module.End ℂ R.HE.H, IntwSplit R hE ∧ IntwInert R lab hE ∧ Comm R hE ∧ Parts R hE

end Fam

def HeckeRows (R : RealDat D A Ks) : Prop := RowsAt R (I := InertIx R) fun _ i => i

def HeckeRowsSplit (R : RealDat D A Ks) : Prop := RowsAt R (I := fun _ => Empty) fun _ i => i.elim

theorem eigSum_comp {V I J : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {op : I → Module.End ℂ V}
    (hc : Col.PairComm op) (φ : J → I) (C : (J → ℂ) → Prop) :
    Col.eigSum op (fun x => C fun j => x (φ j)) = Col.eigSum (fun j => op (φ j)) C := by
  have hle : ∀ C' : (J → ℂ) → Prop,
      Col.eigSum op (fun x => C' fun j => x (φ j)) ≤ Col.eigSum (fun j => op (φ j)) C' := fun C' =>
    iSup₂_le fun x hx => le_trans (le_iInf fun j => Col.eigAt_le op x (φ j))
      (Col.eigAt_le_eigSum (op := fun j => op (φ j)) (C := C') (x := fun j => x (φ j)) hx)
  have hs : Col.SplitOver op := fun i => Module.End.iSup_maxGenEigenspace_eq_top (op i)
  have h1 := Col.isCompl_eigSum hc hs fun x => C fun j => x (φ j)
  have h2 : Disjoint (Col.eigSum (fun j => op (φ j)) C) (Col.eigSum (fun j => op (φ j)) fun y => ¬ C y) :=
    Col.disjoint_eigSum (fun j j' => hc (φ j) (φ j')) fun _ h h' => h' h
  exact eq_of_le_of_inf_le_of_le_sup (hle C)
    (le_of_eq_of_le (h2.mono_right (hle fun y => ¬ C y)).eq_bot bot_le)
    (le_of_le_of_eq le_top h1.sup_eq_top.symm)

theorem HeckeRows.rowsAt {R : RealDat D A Ks} (h : HeckeRows R) {I : T → Type} (lab : ∀ t, I t → InertIx R t) :
    RowsAt R lab := by
  obtain ⟨hE, h1, h2, h3, h4⟩ := h
  refine ⟨fun t i => hE t (Sum.map id (lab t) i), h1, fun t i U hU => h2 t (lab t i) U hU, fun i j => h3 _ _, fun p => ?_⟩
  rw [h4 p]
  exact eigSum_comp h3 (Sum.map id (lab A.μ0)) fun x => HasResC A p.1 fun i => x (Sum.inl i)

theorem HeckeRows.split {R : RealDat D A Ks} (h : HeckeRows R) : HeckeRowsSplit R := h.rowsAt _

def Statement : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.Char F → HeckeRows R

def StatementAt (D : D7) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.Char F → HeckeRows R

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert

end
