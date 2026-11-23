import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.FinalJoin

theorem secNorm_of_netIn : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (ka : WeightFamilies.Wt D j) (Pd : ℝ), NetIn large₂ B j ka K Pd → ∃ n : SecNorm B, SupBoundByL2AtWeight large₂ n.base j ka K.CG K.AG ∧ DeepHerm (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) ka ∧ DeepLogD (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) ka Pd := by
  intro D B P j X large₂ K ka Pd h
  obtain ⟨Nt, σ₀, hM, hL, hP, hI, hd⟩ := h
  refine ⟨⟨(Nt.Bp hM hL).l2NormAlt, (Nt.Bp hM hL).l2Norm_nonneg_bis, (Nt.Bp hM hL).l2Norm_eq_zero_iff, (Nt.Bp hM hL).l2Norm_smul_alt,
    (Nt.Bp hM hL).l2Norm_add_le', (Nt.Bp hM hL).l2Norm_le_supNorm_alt⟩, NetNorms.sup_L2_bound_of_net Nt hM hL large₂ _ _ hP, ?_, ?_⟩
  · exact NetNorms.deepHermNet P Nt hM hL _
  · exact NetNorms.deepLogDNet P Nt hM hL (PJ.tol2NormAlt _ _ _ _ _ _ X) σ₀ Pd hI hd

end GlobalTheory.FinalJoin
