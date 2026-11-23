import Development.AbelianVarietyTheory.Definitions.Divisors.InclEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormEqOfCsq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelFiltrationAtGoodSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelLatticeSystemHypStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSystemSlopeBoundOfDeterminantSlopeInequStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShortTop

theorem geoBound_of_abstract : Quoted → BertiniNF → HeightTie → SlopeBound → GeoBound := by
  intro hQ hB hT hS F _ _ X Λ₀ hG h hh
  obtain ⟨dd, f, hdpos, hf, hfh⟩ := hh
  obtain ⟨hdel, Q, hQ0, hQs⟩ := hB F X.toTuple X.geom hG.bir dd f hf
  have hHyp := GlobalTheory.T.hilbertSamuelLatticeSystem_hyp F X Λ₀ hG
  have hFlat := GlobalTheory.T.hilbertSamuel_filtration_at_good_sections hQ F X Λ₀ hG dd f Q hQs
  have hirr : Irreducible f := GlobalTheory.ChowHt.irreducible_of_irreducible_map hf.irred
  obtain ⟨hpos, hcl⟩ := hS F (Tot X.toGeo) (sysOf X Λ₀) hHyp dd f Q (by omega) hf.homog hirr hQ0 hFlat
  have hfr : Module.finrank F ((sysOf X Λ₀).V (sysOf X Λ₀).T) = X.d := by
    rw [X.d_eq_finrank]; exact (inclEquiv X X.T).finrank_eq.symm
  have hdeg : deg ((sysOf X Λ₀).nm (sysOf X Λ₀).T) ((sysOf X Λ₀).M (sysOf X Λ₀).T) = X.degM X.T := by
    have := GlobalTheory.IsoDeg.deg_map_eq F (X.V X.T) (LinearMap.range (incl X X.T)) (X.nm X.T)
      (comap (X.nm X.T) (inclEquiv X X.T).symm.toLinearMap (inclEquiv X X.T).symm.injective) (inclEquiv X X.T)
      (fun σ m c g => by simp only [csq, HermTools.comap, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]) (X.M X.T) (X.full X.T).fg
    exact this
  have hTie := (hT F X.toHermSys X.abelian₂ hHyp.lat h ⟨dd, f, hdpos, hf, hfh⟩ dd 1 f 1 hf le_rfl one_ne_zero).2
  rw [hfr, hdeg] at hcl
  have hd' : ((X.del : ℤ) : ℝ) = (dd : ℝ) := by rw [← hdel]; push_cast; rfl
  rw [hd']
  refine GlobalTheory.T.hermitianSystemSlopeBound_of_determinantSlopeInequality X.T X.D X.n X.abelian₂ X.beta Λ₀ X.LamD X.LamT dd h _ X.d (X.degM X.T)
    (by exact_mod_cast hHyp.one_le) hHyp.le_T (by exact_mod_cast X.one_le_n) hHyp.lat.one_le hHyp.one_le_beta
    (by exact_mod_cast hdpos) ?_ hcl
  have h2 : h - (Real.log X.n + 1) / 2 ≤ ht X.w X.A f / (((X.D : ℝ) + 1) * dd) := by
    simp at hTie; linarith
  exact h2

end GlobalTheory.HSShortTop
