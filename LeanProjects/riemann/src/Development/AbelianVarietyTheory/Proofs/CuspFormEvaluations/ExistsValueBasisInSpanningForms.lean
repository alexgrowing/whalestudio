import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DescentStatementPf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem exists_indep_of_span_image {α : Type} {δ : ℕ} (S : Set α) (v : α → Fin δ → ℂ)
    (h : Submodule.span ℂ (v '' S) = ⊤) :
    ∃ θ : Fin δ → α, (∀ i, θ i ∈ S) ∧ LinearIndependent ℂ fun i => v (θ i) := by
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent ℂ (v '' S)
  rw [h] at hsp
  let bs : Module.Basis b ℂ (Fin δ → ℂ) := Module.Basis.mk hli (by rw [Subtype.range_coe, hsp])
  let e : Fin δ ≃ b := (Pi.basisFun ℂ (Fin δ)).indexEquiv bs
  choose θ hθ hv using fun i : Fin δ => hb (e i).2
  refine ⟨θ, hθ, ?_⟩
  have : (fun i => v (θ i)) = (Subtype.val : b → Fin δ → ℂ) ∘ e := funext hv
  rw [this]
  exact hli.comp e e.injective

theorem ev_mem_sp_of_mem_span {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} (R : Rdg X)
    (u : WeightFamilies.Wt D j) (s : Set (B.Cusp j u)) (F : B.Cusp j u) (hF : F ∈ Submodule.span B.KO s) :
    R.ev (X.inc u F) ∈ R.sp u s := by
  induction hF using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul, R.ev_smul]; exact Submodule.smul_mem _ _ hx

theorem exists_valueBasis_in_spanning (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j)
    (ka wL wF : WeightFamilies.Wt D j) (N : ℕ) (w : Fin N → B.Cusp j wL) (R : Rdg X) (t : Idx D j N → ℂ) (T : ℕ)
    (Mg : Submodule B.KO (B.Cusp j ka)) (δ : ℕ) (xs : Fin δ → R.Y) (hA : AnFacts R w t ka wF T Mg xs)
    (Sh : Set (B.Cusp j wF)) (hS : Submodule.span B.KO Sh = ⊤) :
    ∃ θ : Fin δ → B.Cusp j wF, (∀ i, θ i ∈ Sh) ∧
      LinearIndependent ℂ (vals xs fun i => R.ev (X.inc wF (θ i))) := by
  refine exists_indep_of_span_image Sh (fun F q => R.ev (X.inc wF F) (xs q)) ?_
  rw [eq_top_iff]
  intro v _
  obtain ⟨f, hf, hv⟩ := hA.interp v
  have h1 : R.sp wF Set.univ ≤ R.sp wF Sh := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨F, -, rfl⟩
    exact ev_mem_sp_of_mem_span R wF Sh F (hS ▸ Submodule.mem_top)
  have h2 : LinearMap.funLeft ℂ ℂ xs f ∈ (R.sp wF Sh).map (LinearMap.funLeft ℂ ℂ xs) :=
    Submodule.mem_map_of_mem (h1 hf)
  rw [Rdg.sp, Submodule.map_span, Set.image_image] at h2
  have h3 : v = LinearMap.funLeft ℂ ℂ xs f := funext fun q => (hv q).symm
  rw [h3]
  exact h2

end GlobalTheory.Shares
