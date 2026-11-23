import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDiscreteValuationRingIntO
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem mk_padicComplex_le (p : ℕ) [Fact p.Prime] : Cardinal.mk ℂ_[p] ≤ Cardinal.continuum := by
  have hQ : Cardinal.mk ℚ_[p] ≤ Cardinal.continuum := by
    have hd : DenseRange ((↑) : ℚ → ℚ_[p]) := Padic.denseRange_ratCast p
    refine (GlobalTheory.SmallClosedField.mk_le_of_denseRange _ hd).trans ?_
    refine (Cardinal.power_le_power_right (Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum)).trans
      Cardinal.continuum_power_aleph0.le
  have hA : Cardinal.mk (PadicAlgCl p) ≤ Cardinal.continuum :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)).trans (max_le hQ Cardinal.aleph0_le_continuum)
  have hd : DenseRange ((↑) : PadicAlgCl p → ℂ_[p]) := UniformSpace.Completion.denseRange_coe
  refine (GlobalTheory.SmallClosedField.mk_le_of_denseRange _ hd).trans ?_
  exact (Cardinal.power_le_power_right hA).trans Cardinal.continuum_power_aleph0.le

theorem UpperTheory.exists_spherically_complete_isometric :
    ∀ (p : ℕ) [Fact p.Prime], ∃ (C : Formalism.MainNotions.DIV.Cons.SCF p) (j : ℂ_[p] ≃+* ↥C.S), ∀ a, ‖j a‖ = ‖a‖ := by
  intro p _
  have hnp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p, norm_algebraMap', Padic.norm_p]
  obtain ⟨D, e, he, hs⟩ := GlobalTheory.LocM.Cht.CompletedClosure.exists_scf_equiv hnp (mk_padicComplex_le p)
  exact ⟨D, RingEquiv.ofBijective e ⟨e.injective, hs⟩, he⟩
