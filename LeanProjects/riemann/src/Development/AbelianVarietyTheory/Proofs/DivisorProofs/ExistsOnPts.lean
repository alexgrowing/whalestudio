import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

set_option autoImplicit false

noncomputable section

open GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ShFam.Pad

namespace GlobalTheory.FlatSecCover

variable {D : D7} (O : Setup D)

def lineAdl (c : O.s.Comp) (B : ℝ) (st : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ) : Adl (cxSt D.what₂.LL) (O.var c) :=
  O.adl0 c (Finsupp.single (ArIn.ind (FlagAr.setB O.Y B), none, st) 1)

def rootFn (c : O.s.Comp) (B : ℝ) (x : D.what₂.Tau × Fin O.N) (z : (O.var c).X) : (O.var c).Fn :=
  if (x.2 : ℕ) < O.j then genAt (lineAdl O c B (.inl (DV.tauEmb D x.1, x.2))).D z
  else (genAt (lineAdl O c B (.inl (conjEmb (DV.tauEmb D x.1), O.N - 1 - x.2))).D z)⁻¹

def rootLn (c : O.s.Comp) (B : ℝ) (x : D.what₂.Tau × Fin O.N) (σ : D.what₂.LL →+* ℂ) (y : Pts (O.var c) σ) : ℝ :=
  if (x.2 : ℕ) < O.j then lnAdl (lineAdl O c B (.inl (DV.tauEmb D x.1, x.2))) σ y
  else -lnAdl (lineAdl O c B (.inl (conjEmb (DV.tauEmb D x.1), O.N - 1 - x.2))) σ y

def detFn (c : O.s.Comp) (B : ℝ) (τ : D.what₂.Tau) (z : (O.var c).X) : (O.var c).Fn :=
  ∏ i : Fin O.N, rootFn O c B (τ, i) z

def detLn (c : O.s.Comp) (B : ℝ) (τ : D.what₂.Tau) (σ : D.what₂.LL →+* ℂ) (y : Pts (O.var c) σ) : ℝ :=
  ∑ i : Fin O.N, rootLn O c B (τ, i) σ y

theorem exists_onPts {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y) (g : M.Fun) :
    ∃ gY : ∀ σ : F →+* ℂ, Pts Y σ → ℝ, ∀ a z, gY (I.ε a) (I.pt a z) = g a z := by
  classical
  refine ⟨fun σ y => if h : ∃ a, I.ε a = σ then
    g h.choose ((I.pt h.choose).symm (cast (congrArg (Pts Y) h.choose_spec.symm) y)) else 0, fun a z => ?_⟩
  have h : ∃ a', I.ε a' = I.ε a := ⟨a, rfl⟩
  have key : ∀ (b : Fin (M.n + 1)) (hb : I.ε b = I.ε a),
      g b ((I.pt b).symm (cast (congrArg (Pts Y) hb.symm) (I.pt a z))) = g a z := by
    intro b hb
    obtain rfl := I.ε.injective hb
    simp
  simp only [dif_pos h]
  exact key _ h.choose_spec

end GlobalTheory.FlatSecCover
