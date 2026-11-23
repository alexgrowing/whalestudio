import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFrameCoverTangentCompat

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
open scoped TensorProduct NNReal

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.HalfGeo GlobalTheory.HtGen.CoverChart GlobalTheory.LineNorm.Chart GlobalTheory.LieMet in

theorem GlobalTheory.HalfGeo.chartSt_holds : ChartSt := by
  intro E _ _ _ H X t F _ _ Y V ρ' ρ hρ m u₀ f T hf hT hc U hU g e he N h
  by_cases hgen : V.j (genericPoint V.G) ∈ U
  swap
  · exact ⟨0, fun z hz => absurd
      (((genericPoint_specializes z).map V.j.continuous).mem_open U.isOpen hz) hgen⟩
  choose α hα using fun (z : V.G) (hz : V.j z ∈ U) => exists_stalkHom hU V.j z hz
  have hα' : ∀ z hz, spMap (α z hz) ≫ hU.fromSpec ≫ ρ' = V.G.fromSpecStalk z ≫ V.π ≫ ρ := fun z hz => by
    rw [← Category.assoc, hα, Category.assoc, hρ]
  let ι₀ : Γ(V.X, U) →+* V.G.functionField := α _ hgen
  have hι : spMap ι₀ ≫ hU.fromSpec ≫ ρ' = spMap V.φ ≫ GlobalTheory.ShFam.genericPt Y ≫ ρ :=
    (hα' _ hgen).trans (by rw [← Category.assoc, V.φ_spec, Category.assoc]; rfl)
  have hαι : ∀ z hz, (algebraMap (V.G.presheaf.stalk z) V.G.functionField).comp (α z hz) = ι₀ := fun z hz =>
    ringHom_ext hU (by
      rw [sp_comp, Category.assoc, hα, ← Category.assoc, gen_eq']
      exact (hα _ hgen).symm)
  have ha : ∀ z (hz : V.j z ∈ U) l, ∃ a, IsCombAtG t (spMap (α z hz) ≫ hU.fromSpec ≫ ρ')
      (fun i => spMap (dualMap (α z hz)) ≫ e i) a (spMap (dualMap (V.π.stalkMap z).hom) ≫ f (V.π z) l) := fun z hz l =>
    (he.2 _ (α z hz) _ (isTan_map _ (by
      rw [hα', ← Category.assoc, ← Category.assoc, ← stalk_eq]; rfl) (hf (V.π z) l))).exists
  choose a ha using ha
  have key : ∀ z (hz : V.j z ∈ U) i,
      IsCombAtG t (spMap ι₀ ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap ι₀) ≫ e i)
        (∑ l, V.φ (T (V.π z) l i) • fun j => algebraMap (V.G.presheaf.stalk z) V.G.functionField (a z hz l j))
        (spMap (dualMap V.φ) ≫ u₀ i) := by
    intro z hz i
    have h4 := GlobalTheory.LatDRFree.comb_map t V.φ (hc (V.π z) i)
    refine comb_comb (fun j => isTan_map _ rfl (he.1 j)) (fun l => ?_) (hι ▸ h4)
    have := coord_map _ (algebraMap (V.G.presheaf.stalk z) V.G.functionField) (ha z hz l)
    rw [hαι, dual_comp, alg_comp_stalkMap] at this
    rw [dual_comp]
    exact this
  have hA₀ : ∀ i, ∃ b, IsCombAtG t (spMap ι₀ ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap ι₀) ≫ e i) b
      (spMap (dualMap V.φ) ≫ u₀ i) := fun i => ⟨_, key _ hgen i⟩
  choose A₀ hA₀ using hA₀
  have hA : ∀ z hz i, A₀ i =
      ∑ l, V.φ (T (V.π z) l i) • fun j => algebraMap (V.G.presheaf.stalk z) V.G.functionField (a z hz l j) :=
    fun z hz i =>
    (he.2 _ ι₀ _ (comb_tan (fun j => isTan_map _ rfl (he.1 j)) (key z hz i))).unique (hA₀ i) (key z hz i)
  refine ⟨Matrix.of fun r i => ∑ j, ι₀ (h r j) * A₀ i j,
    fun z hz => ⟨α z hz, a z hz, hα z hz, ha z hz, fun r l => ?_⟩⟩
  have hι₀ : ∀ b, ι₀ b = algebraMap (V.G.presheaf.stalk z) V.G.functionField (α z hz b) := fun b =>
    (congrArg (fun q => q b) (hαι z hz)).symm
  have hdet : IsUnit ((T (V.π z)).map V.φ).det := by
    have h0 := (hT (V.π z)).map V.φ
    rw [RingHom.map_det] at h0
    exact h0
  have hM : (Matrix.of fun r i => ∑ j, ι₀ (h r j) * A₀ i j) =
      (Matrix.of fun r l => algebraMap (V.G.presheaf.stalk z) V.G.functionField
        (∑ j, α z hz (h r j) * a z hz l j)) * (T (V.π z)).map V.φ := by
    ext r i
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, hA z hz i, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, map_sum, map_mul, hι₀, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hM, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
  rfl

end
