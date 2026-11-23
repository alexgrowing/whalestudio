import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ShortPlace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightAssemblyClause

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

theorem Thc_le_Mlat {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) (s : 𝓞 B.KO)
    (w : WeightFamilies.Wt D j)
    (hb : ∀ G ∈ X.shortTh w, ∀ la (y : X.Pt la),
      (((-(((vAdd la ((s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * w.n) : 𝓞 B.KO) :
        B.KO) : ℤ) : ℝ))) : ℝ) : EReal) ≤ X.vAt la y (X.inc w G)) :
    X.Thc s w ≤ B.Mlat j w := by
  intro x hx
  simp only [Formalism.MainNotions.WeightAlgebra.PJ.Thc, Formalism.MainNotions.WeightAlgebra.PJ.scaled, Submodule.mem_map] at hx
  obtain ⟨x', ⟨G, hG, rfl⟩, rfl⟩ := hx
  rw [X.Mlat_eq]
  intro la y
  have hne := X.vAt_ne_bot la y (X.inc w G)
  have key : ∀ t : 𝓞 B.KO, ((-(((vAdd la (t : B.KO) : ℤ) : ℝ)) : ℝ) : EReal) ≤ X.vAt la y (X.inc w G) →
      0 ≤ X.vAt la y (X.inc w (t • G)) := by
    intro t hb'
    have e : algebraMap (𝓞 B.KO) B.KO t = (t : B.KO) := rfl
    rw [← algebraMap_smul B.KO t G, map_smul, e]
    by_cases h0 : (t : B.KO) = 0
    · rw [h0, zero_smul, X.vAt_zero]
      exact le_top
    rw [X.vAt_smul la y _ _ h0]
    generalize X.vAt la y (X.inc w G) = V at hb' hne ⊢
    induction V using EReal.rec with
    | bot => exact absurd rfl hne
    | coe v =>
      rw [← EReal.coe_add]
      have h1 := EReal.coe_le_coe_iff.mp hb'
      exact EReal.coe_nonneg.mpr (by linarith)
    | top => simp
  have hb' := hb G hG la y
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
  exact key _ hb'

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
