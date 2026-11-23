import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Columns.RowFormsAdelic
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.InitialDataUntwistedOfModelChoice
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Col Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2
open scoped TensorProduct

namespace GlobalTheory.Mem.R3

def MatEq {A : Type} [CommRing A] {a b : ℕ} (x : GL (Fin a) A) (y : GL (Fin b) A) : Prop :=
  a = b ∧ ∀ (i j : Fin a) (i' j' : Fin b), (i : ℕ) = i' → (j : ℕ) = j' → x.1 i j = y.1 i' j'

section Gen

variable {X : Fields} {n : ℕ} [NeZero n] {a : ℕ} {H Γ W : Type} [AddCommGroup W] [Module ℂ W] (σ : X.K →+* ℂ)
  (mat : H → GL (Fin a) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) (rat : Γ → GL (Fin a) X.E → Prop) (ρ : Γ → W → W)

def StdSide {ι : Type} (lam : X.Tau → DomWeight n) (rho : GL (Fin n) X.E →* Module.End X.K (VV X.K lam))
    (SG : ι → Finset (Pl X.E)) (Fm : ι → Type) (val : ∀ t, Fm t → DecoSet X.E n ∅ (SG t) → VV X.K lam)
    (ad : ∀ t, Fm t → H → W) : Prop :=
  ∃ c : VV X.K lam →ₛₗ[σ] W,
    (∀ γ γE g, rat γ γE → MatEq γE g → ∀ v, c (rho g v) = ρ γ (c v)) ∧
    (∀ (hc : CMData X.F X.E) t (φ : Fm t) (h : H) (x : Formalism.L2.Col.UAd hc n), MatEq (mat h) (x : GL (Fin n) _) →
      ad t φ h = c (val t φ (decoPt hc n ∅ (SG t) (QuotientGroup.mk x)))) ∧
    (LinearIndependent ℂ fun i => c (bVV X.K lam i)) ∧
    ∃ hc : CMData X.F X.E, ∀ h : H, ∃ x : Formalism.L2.Col.UAd hc n, MatEq (mat h) (x : GL (Fin n) _)

theorem StdSide.value {ι : Type} {lam : X.Tau → DomWeight n} {rho : GL (Fin n) X.E →* Module.End X.K (VV X.K lam)}
    {SG : ι → Finset (Pl X.E)} {Fm : ι → Type} {val : ∀ t, Fm t → DecoSet X.E n ∅ (SG t) → VV X.K lam} {ad : ∀ t, Fm t → H → W}
    (s : StdSide σ mat rat ρ lam rho SG Fm val ad) :
    ∃ c : VV X.K lam →ₛₗ[σ] W, (LinearIndependent ℂ fun i => c (bVV X.K lam i)) ∧
      ∀ h t, ∃ d : DecoSet X.E n ∅ (SG t), ∀ φ, ad t φ h = c (val t φ d) := by
  obtain ⟨c, -, hr, hli, hc, hx⟩ := s
  refine ⟨c, hli, fun h t => ?_⟩
  obtain ⟨x, hm⟩ := hx h
  exact ⟨_, fun φ => hr hc t φ h x hm⟩

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def matIn {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (h : Bridge.Gf V) : GL (Fin V.rank) (Lev.EAf D) :=
  Formalism.UG.bc (swapAE D) (h : GL (Fin V.rank) _) * β

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL))
  (tr : TrI X.B px)

set_option maxHeartbeats 2000000 in

def BrgStdR (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (cX : CoefA X.toD7.sp.X')
    (jR : ∀ t, (famR X I hX U Xg tr).A.fam.amb.FR t → Bridge.Gf X.toD7.sp.X' → cX.W) : Prop :=
  StdSide (X := X.B.fields) (n := X.B.R.N X.B.R.m - 1) (a := X.toD7.sp.X'.rank) (H := Bridge.Gf X.toD7.sp.X') (Γ := GQ X.toD7.sp.X')
    (W := cX.W) ((X.B.embLL)) ((matIn X.toD7.sp.X' L.βX)) ((Bridge.IsRatMat X.toD7.sp.X'))
    (fun γ v => cX.coef.ρ γ v) (ι := TupU I U) X.B.wts.sgTrue (rhoV X.B.fields.emb X.B.wts.sgTrue)
    (fun t => rowSG (X.B.primes px) I.sel t.1)
    (fun t => PLift (mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).Ok ×
      (mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).EqFun)
    (fun _ φ => φ.2.1)
    fun t φ => jR t ((by with_unfolding_all exact ((mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).res φ.1.down φ.2 :)))

set_option maxHeartbeats 2000000 in

def BrgStdV (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (i : Fin X.toD7.R.m) (cV : CoefA (Vc X.toD7 i))
    (jL : ∀ t, (famR X I hX U Xg tr).A.fam.amb.FL i t → Bridge.Gf (Vc X.toD7 i) → cV.W) : Prop :=
  StdSide (X := X.B.fields) (n := X.B.R.nV) (a := (Vc X.toD7 i).rank) (H := Bridge.Gf (Vc X.toD7 i)) (Γ := GQ (Vc X.toD7 i))
    (W := cV.W) ((X.B.embLL)) ((matIn (Vc X.toD7 i) (L.βV i))) ((Bridge.IsRatMat (Vc X.toD7 i)))
    (fun γ v => cV.coef.ρ γ v) (ι := TupU I U) (X.B.wts.lamV ((i : ℕ) + 1)) (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)))
    (fun t => rowSG (X.B.primes px) I.sel t.1)
    (fun t => PLift (mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).Ok ×
      (mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun)
    (fun _ φ => φ.2.1)
    fun t φ => jL t ((by with_unfolding_all exact ((mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res φ.1.down φ.2 :)))

def BrgStd {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks X.toD7.what₂.LL] (R : RealDat X.toD7 (famR X I hX U Xg tr).A Ks) : Prop :=
  BrgStdR X I hX U Xg tr R.toLevCh R.cX (fun t φ => R.B.jR t φ) ∧
    ∀ i, BrgStdV X I hX U Xg tr R.toLevCh i (R.cV i) fun t φ => R.B.jL i t φ

variable {X I hX} in

def Dat.Std {T : Top.TwDat X.B} {Wt : Set X.B.places.Pl} (z : Dat X I hX T Wt) : Prop :=
  BrgStd X I hX (usedOf I T Wt) z.Xg z.tr z.R.toRealDat

end GlobalTheory.Mem.R3

end
