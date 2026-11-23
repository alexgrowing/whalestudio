import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev lamV (D : D7) (i : Fin D.R.m) : D.what₂.Tau → DomWeight (Vc D i).rank :=
  fun τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ

def IsCoefExt {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (ι : K →+* K')
    {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (c₀ : VV K lam →ₛₗ[σ] W) (c' : VV K' lam →ₛₗ[σ'] W) : Prop :=
  ∀ (v : VV K lam) (v' : VV K' lam), (v' : Pol K' I n) = MvPolynomial.map ι (v : Pol K I n) → c' v' = c₀ v

section Row

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def formFn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (x : A.fam.amb.FL i t) : Bridge.Gf (Vc D i) → (R.cV i).W :=
  (R.HV i t).e (R.jV i t x)

def ValuesIn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {K' : Type} [Field K'] {σ' : K' →+* ℂ}
    (c' : VV K' (lamV D i) →ₛₗ[σ'] (R.cV i).W) : Prop :=
  ∀ (x : A.fam.amb.FL i t) (h : Bridge.Gf (Vc D i)), ∃ v : VV K' (lamV D i), c' v = formFn R i t x h

def RationalValuesAt (R : RealDat D A Ks) : Prop :=
  ∀ (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W)
    (c0L : ∀ i : Fin D.R.m, VV D.what₂.LL (lamV D i) →ₛₗ[D.what₂.embLL] (R.cV i).coef.W),
    Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (lamV D) gramR c0R c0L →
    ∀ (i : Fin D.R.m) (t : T) (K' : Type) [Field K'] (ι : D.what₂.LL →+* K') (σ' : K' →+* ℂ), σ'.comp ι = D.what₂.embLL →
      ∀ c' : VV K' (lamV D i) →ₛₗ[σ'] (R.cV i).W, IsCoefExt (W := (R.cV i).W) ι (lamV D i) (c0L i) c' → ValuesIn R i t c'

theorem ValuesIn.reps {R : RealDat D A Ks} {i : Fin D.R.m} {t : T} {K' : Type} [Field K'] {σ' : K' →+* ℂ}
    {c' : VV K' (lamV D i) →ₛₗ[σ'] (R.cV i).W} (H : ValuesIn R i t c') {J : Subgroup (Bridge.Gf (Vc D i))} {Cl : Type}
    {y : Cl → Bridge.Gf (Vc D i)} (_hy : Bridge.IsReps (Bridge.ratF (Vc D i)) J y) (x : A.fam.amb.FL i t) :
    ∃ val : Cl → VV K' (lamV D i), ∀ k, c' (val k) = formFn R i t x (y k) :=
  ⟨fun k => (H x (y k)).choose, fun k => (H x (y k)).choose_spec⟩

end Row

def RationalValues : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → RationalValuesAt R

end GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues

end
