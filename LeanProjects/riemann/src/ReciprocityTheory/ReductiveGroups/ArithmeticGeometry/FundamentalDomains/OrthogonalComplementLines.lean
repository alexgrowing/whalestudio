import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnitaryComplementMoveOfIsotropic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TraceFormIndependence

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthogonalComplementLines

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

private lemma hermC_add_left_of_ringHom (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' v : Fin r → ℂ) :
    hermC τ G (u + u') v = hermC τ G u v + hermC τ G u' v := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma hermC_sub_left_of_ringHom (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' v : Fin r → ℂ) :
    hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma ppos_add (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.ppos x τ (u + v) = X.ppos x τ u + X.ppos x τ v := by
  simp only [Data.ppos, hermC_add_left_of_ringHom, add_mul, Finset.sum_add_distrib, add_smul]

lemma ppos_sub (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.ppos x τ (u - v) = X.ppos x τ u - X.ppos x τ v := by
  simp only [Data.ppos, hermC_sub_left_of_ringHom, sub_mul, Finset.sum_sub_distrib, sub_smul]

lemma emb_smul (τ : E →+* ℂ) (a : E) (v : Fin r → E) :
    Data.emb τ (a • v) = τ a • Data.emb τ v := by
  funext a
  simp only [Data.emb, Pi.smul_apply, smul_eq_mul, map_mul]

variable {X : Data E r}

end ReciprocityTheory.ChartRestriction.G.FD.OrthogonalComplementLines
