import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Formalism.LocalToGlobal.Divisibility.Frames

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.abelian₂

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l}

structure LevelLaws (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (V : HSp D)
    (dict : ∀ σ : c.F →+* ℂ, GA D V → Σ k, Frame ((U σ).X k).Ψ D.R.r) : Prop where

  hostD : H.d = D.host.d

  levA : l.A = 1

  sig : V.SigOK
  unf : ∀ σ, GoodEmb c σ → IsUnf (U σ)
  chiTriv : ∀ σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (laU (U σ) a n k) γ = 1
  dictU : ∀ σ, GoodEmb c σ → ∃ Kf th hr, IsLevelK V l.M Kf ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    DictIsUnif V (dict σ) Kf th hr ∧ ∀ g τ k, ‖dmin ((U σ).X (dict σ g).1).Gm (dict σ g).2 τ k‖ = 1
  xiAbs : ∀ σ, GoodEmb c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D

def absA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) : ℕ := ∑ b : E →+* ℂ, ∑ i : Fin (Dw.mult b), a (b, i)

def SizeRows (D : D7) (M : ℕ) (S L : ℝ) : Prop :=
  16 ≤ D.R.f ∧ 2 ≤ L ∧ 1 ≤ S ∧ Real.log D.R.r ≤ L ∧ Real.log D.R.f ≤ 2 * L ∧
    Real.log (dE D.host.E) ≤ 4 * D.R.f * L ∧ Real.log (Ideal.absNorm D.host.ccK) ≤ 4 * L ∧
    Real.log M ≤ 30 * L ∧ Real.log S ≤ 3 * L

def petProd {σ : c.F →+* ℂ} (U : Unf Xo c σ D.R.r) (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ D.R.r) (t : ℝ)
    (f g : Rul Xo c) : ℂ :=
  ((t ^ 2 : ℝ) : ℂ) * ∫ q : AutQ V, starRingEnd ℂ (rdU U f (dict q.out).1 (dict q.out).2) *
    rdU U g (dict q.out).1 (dict q.out).2 ∂(muQ1 V)

open Classical in

def gramAt (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (V : HSp D)
    (dict : ∀ σ : c.F →+* ℂ, GA D V → Σ k, Frame ((U σ).X k).Ψ D.R.r) (t : ℝ) {N : ℕ} (b : Fin N → Rul Xo c)
    (σ : c.F →+* ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  if GoodEmb c σ then Matrix.of fun i j => petProd (U σ) V (dict σ) t (b i) (b j)
  else (Matrix.of fun i j => petProd (U ((starRingEnd ℂ).comp σ)) V (dict ((starRingEnd ℂ).comp σ)) t (b i) (b j))ᵀ

def latCoord (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {N : ℕ}
    (b : Module.Basis (Fin N) c.F (cusp Xo c U a n)) : Submodule (𝓞 c.F) (Fin N → c.F) :=
  (GlobalTheory.AllWt.supLat (cusp Xo c U a n)).map (b.equivFun.toLinearMap.restrictScalars (𝓞 c.F))

end GlobalTheory.CompanionTheory.Ar.abelian₂
