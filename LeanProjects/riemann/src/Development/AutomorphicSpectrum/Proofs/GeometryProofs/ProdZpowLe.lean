import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntMemModelSmall
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.FinTr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S : Finset ℕ} {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y S RM Fx} {Fr : Small.GenFrame Or} {h : GenFrEx Xo c} {Z : Comp Xo c}

def phiAlg (Rd : Reading Fr h Z) : letI := Small.cstAlg Or; Om Z →ₐ[c.F] RM.Ω :=
  letI := Small.cstAlg Or
  { Rd.φ with commutes' := fun a => Rd.φ_cst a }

def Linked (Rd : Reading Fr h Z) : Prop :=
  letI := Small.cstAlg Or
  ∃ (w : FrPt Xo c RM.Ω) (t : Ix Dw → RM.Ωˣ), FrMap (phiAlg Rd) (genFr h Z) w ∧ FrBor t w Fr.y₀

def RegAt (h : GenFrEx Xo c) (Z : Comp Xo c) {L : Type} [Field L] (io : c.F →+* L) (A : Subring (Om Z))
    (ev : A →+* L) (y : letI := io.toAlgebra; FrPt Xo c L) : Prop :=
  letI := io.toAlgebra
  (∀ a : c.F, ∃ ha : algebraMap c.F (Om Z) a ∈ A, ev ⟨_, ha⟩ = io a) ∧
  ∃ (q : TRing c.F) (φ : q.R →ₐ[c.F] Om Z) (ψ : q.R →ₐ[c.F] L) (yq : FrPt Xo c q.R) (z : FrPt Xo c L)
    (t : Ix Dw → Lˣ), FrMap φ yq (genFr h Z) ∧ FrMap ψ yq z ∧ (∀ r, ∃ hr : φ r ∈ A, ψ r = ev ⟨φ r, hr⟩) ∧ FrBor t z y

end GlobalTheory.CompanionTheory.Ar.Plug.FinTr

namespace GlobalTheory.CompanionTheory.Ar.Plug.FinTr

theorem prod_zpow_le {R : Type} [Fintype R] (S rec : R → ℝ) (n : R → ℤ) (C : ℝ) (hS : ∀ r, 0 < S r)
    (hr : ∀ r, 0 < rec r) (h : ∀ r, |Real.log (S r) - Real.log (rec r)| ≤ C) :
    ∏ r, S r ^ n r ≤ (∏ r, rec r ^ n r) * Real.exp ((∑ r, |(n r : ℝ)|) * C) := by
  have key : ∀ r ∈ (Finset.univ : Finset R), S r ^ n r ≤ rec r ^ n r * Real.exp (|(n r : ℝ)| * C) := by
    intro r _
    rw [← Real.rpow_intCast, ← Real.rpow_intCast, Real.rpow_def_of_pos (hS r), Real.rpow_def_of_pos (hr r),
      ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : (n r : ℝ) * (Real.log (S r) - Real.log (rec r)) ≤ |(n r : ℝ)| * C := by
      calc (n r : ℝ) * (Real.log (S r) - Real.log (rec r))
          ≤ |(n r : ℝ) * (Real.log (S r) - Real.log (rec r))| := le_abs_self _
        _ = |(n r : ℝ)| * |Real.log (S r) - Real.log (rec r)| := abs_mul _ _
        _ ≤ |(n r : ℝ)| * C := mul_le_mul_of_nonneg_left (h r) (abs_nonneg _)
    linarith
  calc ∏ r, S r ^ n r ≤ ∏ r, rec r ^ n r * Real.exp (|(n r : ℝ)| * C) :=
        Finset.prod_le_prod (fun r _ => (zpow_pos (hS r) _).le) key
    _ = _ := by rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_mul]

theorem supMet_sum {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {𝕜 : Type} [NormedField 𝕜]
    {R : Type} [Fintype R] (n : R → ℤ) (d : R → K → ℤ) (z : (Σ k, ι k) → 𝕜)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : Small.supMet (∑ r, n r • d r) z = ∏ r, Small.supMet (d r) z ^ n r := by
  have hN : ∀ k, ‖fun i : ι k => z ⟨k, i⟩‖ ≠ 0 := fun k h0 => by
    obtain ⟨i, hi⟩ := hz k
    exact hi (congrFun (norm_eq_zero.1 h0) i)
  unfold Small.supMet
  simp only [← Finset.prod_zpow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hs : ∀ (s : Finset R), ‖fun i : ι k => z ⟨k, i⟩‖ ^ (∑ r ∈ s, n r • d r) k =
      ∏ r ∈ s, (‖fun i : ι k => z ⟨k, i⟩‖ ^ d r k) ^ n r := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, Pi.add_apply, zpow_add₀ (hN k), ih]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← zpow_mul, mul_comm (n a)]
  exact hs Finset.univ

end GlobalTheory.CompanionTheory.Ar.Plug.FinTr
