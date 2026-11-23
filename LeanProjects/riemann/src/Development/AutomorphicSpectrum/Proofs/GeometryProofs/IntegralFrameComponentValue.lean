import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntMemModelSmall
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdZpowLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.FinTr

theorem ev_genValue_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Z : Comp Xo c) (ex : Ix Dw → ℤ) (f : Rul Xo c), f ∈ GlobalTheory.AllWt.secZ Xo c ex → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (A : Subring (Om Z)) (ev : A →+* T.Fr), FinTr.RegAt h Z io A ev y.1 → evI y f ≠ 0 → ∀ hb : evC h Z f ∈ A, ev ⟨_, hb⟩ ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U h e hL Z ex f hf T io y A ev hR hy hb h0
  letI := io.toAlgebra
  obtain ⟨-, q, φ, ψ, yq, z, t, h1, h2, h3, h4⟩ := hR
  have hg : evC h Z f = φ (f q yq) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of _ _ hL.evalWD f hf.1 q φ yq (genFr h Z) h1
  have hz : evR Xo c f z = ψ (f q yq) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of _ _ hL.evalWD f hf.1 q ψ yq z h2
  obtain ⟨hr, hψ⟩ := h3 (f q yq)
  have hψ0 : ψ (f q yq) = 0 := by
    rw [hψ, ← h0]
    exact congrArg ev (Subtype.ext hg.symm)
  have hS : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hw := GlobalTheory.evR_frBor_of_mem_secZ hS Xo c ex hf T.Fr t z y.1 h4
  apply hy
  show evR Xo c f y.1 = 0
  rw [hw, hz, hψ0, mul_zero]

end GlobalTheory.CompanionTheory.Ar.Plug.FinTr
