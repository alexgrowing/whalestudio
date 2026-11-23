import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.KernelCond
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands.TateLocalFactor

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}

structure Term {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {v : HeightOneSpectrum (𝓞 K)}
    (h : IsPlaceOver A v) (ψ : AddChar (v.adicCompletion K) Circle) : Type 1 where
  L : Type
  [instField : Field L]
  [instNF : NumberField L]
  [instAlg : Algebra L Ω]
  [instCl : IsAlgClosure L Ω]
  [instKL : Algebra K L]
  [instTow : IsScalarTower K L Ω]
  v' : HeightOneSpectrum (𝓞 L)
  h' : IsPlaceOver A v'
  loc : IsLocalExt L h
  ψ' : AddChar (v'.adicCompletion L) Circle
  cont : Continuous ψ'
  ne : ψ' ≠ 1
  tr : ∀ z : L, ψ' (algebraMap L _ z) = ψ (algebraMap K _ (Algebra.trace K L z))
  a : Weil h' →* (v'.adicCompletion L)ˣ
  ha : IsLocalArtin h' a
  χ : (v'.adicCompletion L)ˣ →* ℂˣ
  hχ : IsSmoothChar χ
  c : ℤ
  x : WD h
  x₀ : WD h
  ix : Induces (WD.lpOfChar h' (χ.comp a) (ha.smooth hχ)) x
  ix₀ : Induces (WD.lpOfChar h' ((1 : (v'.adicCompletion L)ˣ →* ℂˣ).comp a)
    (ha.smooth (isSmoothChar_of_isUnram fun _ _ => rfl))) x₀
  e : ℂˣ
  e₀ : ℂˣ
  he : IsTateMeas ψ' 1 χ e
  he₀ : IsTateMeas ψ' 1 1 e₀

attribute [instance] Term.instField Term.instNF Term.instAlg Term.instCl Term.instKL Term.instTow

section Pres

variable {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {v : HeightOneSpectrum (𝓞 K)}
  {h : IsPlaceOver A v} {ψ : AddChar (v.adicCompletion K) Circle}

def Term.pos (T : Term h ψ) (σ : Weil h) : ℂ[X] :=
  T.x.charPol σ ^ T.c.toNat * T.x₀.charPol σ ^ (-T.c).toNat

def Term.neg (T : Term h ψ) (σ : Weil h) : ℂ[X] :=
  T.x₀.charPol σ ^ T.c.toNat * T.x.charPol σ ^ (-T.c).toNat

def Term.val (T : Term h ψ) : ℂˣ := (T.e / T.e₀) ^ T.c

def listPos (l : List (Term h ψ)) (σ : Weil h) : ℂ[X] := (l.map fun T => T.pos σ).prod

def listNeg (l : List (Term h ψ)) (σ : Weil h) : ℂ[X] := (l.map fun T => T.neg σ).prod

def listVal (l : List (Term h ψ)) : ℂˣ := (l.map Term.val).prod

def IsPres (x : WD h) (l : List (Term h ψ)) : Prop :=
  ∀ σ, x.charPol σ * listNeg l σ = (X - 1) ^ x.lpDim * listPos l σ

end Pres

def tateOne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (t : ℝ) : ℂˣ :=
  open Classical in if H : ∃ e : ℂˣ, IsTateMeas ψ t 1 e then H.choose else 1

def presVal {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {v : HeightOneSpectrum (𝓞 K)}
    (h : IsPlaceOver A v) (ψ : AddChar (v.adicCompletion K) Circle) (x : WD h) : ℂˣ :=
  open Classical in if H : ∃ l : List (Term h ψ), IsPres x l then listVal H.choose else 1

variable (A) in

def epsFam : EpsMeasFamily A := fun _ _ _ _ _ _ h ψ t x => tateOne ψ t ^ x.lpDim * presVal h ψ x

end PositivityTheory.Pf1.LocalLanglands.TateLocalFactor

end
