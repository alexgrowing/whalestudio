import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

noncomputable section

namespace GlobalTheory.TieIdem

theorem coeff_conj_of_central' {K : Type} [Field K] {G : Type} [Group G] (e : MonoidAlgebra K G)
    (he : ∀ x, x * e = e * x) (k g : G) : e.coeff (k * g * k⁻¹) = e.coeff g := by
  have h := congrArg (fun a : MonoidAlgebra K G => a.coeff (k * g)) (he (MonoidAlgebra.single k 1))
  simp only [MonoidAlgebra.mul_single_apply, MonoidAlgebra.single_mul_apply] at h
  simpa [mul_assoc] using h.symm

theorem idemOf_props {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G] (X : Finset (G → K))
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) :
    (∀ k : G, ∑ g, (idemOf X).coeff g * (idemOf X).coeff (g⁻¹ * k) = (idemOf X).coeff k) ∧
    (∀ g h : G, (idemOf X).coeff (h * g * h⁻¹) = (idemOf X).coeff g) ∧
    (∀ g : G, IsIntegral ℤ ((Fintype.card G : K) * (idemOf X).coeff g)) ∧
    ∀ (σ : K →+* ℂ) (g : G), σ ((idemOf X).coeff g⁻¹) = starRingEnd ℂ (σ ((idemOf X).coeff g)) := by
  refine ⟨fun k => ?_, fun g h => ?_, fun g => ?_, fun σ g => ?_⟩
  · rw [← coeff_mul_fin, idemOf_mul_self X hX]
  · exact coeff_conj_of_central' _ (fun b => idemOf_central X hX b) h g
  · obtain ⟨b, hb⟩ := idemOf_integral X hX g
    rw [← hb]
    exact b.isIntegral_coe
  · rw [coeff_idemOf, coeff_idemOf, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have h1 := (hX χ hχ).map_inv σ 1
    have h2 := (hX χ hχ).map_inv σ g
    rw [inv_one] at h1
    simp only [map_mul, map_div₀, map_natCast, inv_inv, h2, Complex.conj_conj]
    rw [← h1]

end GlobalTheory.TieIdem

namespace GlobalTheory.TieIdem

theorem tied_good_idem : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → GlobalTheory.CovTop.RecTied D L →
    (∀ k : p.P.Gp, ∑ g, (idemOf p.P.A3.A.X).coeff g * (idemOf p.P.A3.A.X).coeff (g⁻¹ * k) = (idemOf p.P.A3.A.X).coeff k) ∧
    (∀ g h : p.P.Gp, (idemOf p.P.A3.A.X).coeff (h * g * h⁻¹) = (idemOf p.P.A3.A.X).coeff g) ∧
    (∀ g : p.P.Gp, IsIntegral ℤ ((Fintype.card p.P.Gp : D.what₂.LL) * (idemOf p.P.A3.A.X).coeff g)) ∧
    ∀ (σ : D.what₂.LL →+* ℂ) (g : p.P.Gp), σ ((idemOf p.P.A3.A.X).coeff g⁻¹) = starRingEnd ℂ (σ ((idemOf p.P.A3.A.X).coeff g)) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p hr _
  exact idemOf_props p.P.A3.A.X hr.ok.ok2.irr

end GlobalTheory.TieIdem
