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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AllWeightSectionsCompat
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Definitions.RegularCharts.NotFamConstZero
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.TestMem
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem ModelDimension.regular_chart_nonzero_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (h : GenFrEx Xo c) (C : GlobalTheory.Reg.FChart h), ∃ g₀ : C.R, g₀ ≠ 0 ∧ ∀ (A : Subring (Om C.Z)) (hA : ∀ r : C.R, (r : Om C.Z) ∈ A), (g₀ : Om C.Z)⁻¹ ∈ A → ∀ (L : Type) [Field L] (io : c.F →+* L) (ev : A →+* L), letI := io.toAlgebra; ∀ (ψ : C.R →ₐ[c.F] L), (∀ r : C.R, ψ r = ev ⟨r, hA r⟩) → ∀ (z y : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ C.y z → FrBor t z y → FinTr.RegAt h C.Z io A ev y := by
  intro E _ _ _ H Dw l Xo c hL h C
  classical
  obtain ⟨q, φ₀, y₀, hy₀⟩ := hL.test _ (genFr h C.Z)
  choose a ha b hb hb0 hab using C.frac
  let x : Fin q.n ⊕ Ix Dw → Om C.Z := fun k => match k with
    | .inl i => φ₀ (Ideal.Quotient.mk q.I (MvPolynomial.X i))
    | .inr k => (((C.t k)⁻¹ : (Om C.Z)ˣ) : Om C.Z)
  let bb : Fin q.n ⊕ Ix Dw → C.R := fun k => ⟨b (x k), hb (x k)⟩
  have hbb : ∀ k, bb k ≠ 0 := fun k h0 => hb0 (x k) (congrArg Subtype.val h0)
  refine ⟨∏ k, bb k, Finset.prod_ne_zero_iff.2 fun k _ => hbb k, fun A hA hg L _ io ev => ?_⟩
  letI := io.toAlgebra
  intro ψ hψ z y t hz hb'
  have hx : ∀ k, x k ∈ A := fun k => by
    have e1 : ((∏ k, bb k : C.R) : Om C.Z) = b (x k) * ((∏ j ∈ Finset.univ.erase k, bb j : C.R) : Om C.Z) := by
      rw [← Finset.mul_prod_erase _ bb (Finset.mem_univ k)]; rfl
    have hne : ((∏ k, bb k : C.R) : Om C.Z) ≠ 0 := fun h0 =>
      Finset.prod_ne_zero_iff.2 (fun k _ => hbb k) (Subtype.ext h0)
    have e2 : x k = a (x k) * ((∏ j ∈ Finset.univ.erase k, bb j : C.R) : Om C.Z) *
        ((∏ k, bb k : C.R) : Om C.Z)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hne, e1, ← mul_assoc, hab]
    rw [e2]
    exact A.mul_mem (A.mul_mem (hA ⟨_, ha _⟩) (hA _)) hg
  have hc : ∀ a : c.F, algebraMap c.F (Om C.Z) a ∈ A := fun a => hA (algebraMap c.F C.R a)
  have hev : ∀ (a : c.F) (h : algebraMap c.F (Om C.Z) a ∈ A), ev ⟨_, h⟩ = io a := fun a h => by
    have := hψ (algebraMap c.F C.R a)
    rw [ψ.commutes] at this
    exact this.symm
  have hφ : ∀ r, φ₀ r ∈ A := ModelDimension.Spread.test_mem q φ₀ A hc (fun i => hx (.inl i))
  let ψq := ModelDimension.Spread.evAlg φ₀ A hφ ev hev
  obtain ⟨zq, hzq⟩ := hL.bc _ _ ψq y₀
  obtain ⟨t', ht'⟩ := ModelDimension.Spread.spec_bor φ₀ C.R.val hy₀ C.gen C.bor A hφ hA (fun k => hx (.inr k)) ev ψq ψ
    (fun _ => rfl) hψ hzq hz
  exact ⟨fun a => ⟨hc a, hev a _⟩, q, φ₀, ψq, y₀, zq, _, hy₀, hzq, fun r => ⟨hφ r, rfl⟩,
    (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L).2.1 _ _ _ _ _ ht' hb'⟩
