import Mathlib
import Formalism.PeriodIntegrals.FoldDCUnfold
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldUnfold
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.TransExists

open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

namespace PI.FoldDCUnfold.W

universe u

theorem pointwise_of (h1 : TransIndep.{u}) (h3 : DCTrans.{u})
    {G : Type u} [Group G] (Γ S S' : Subgroup G) (hS : S ≤ Γ) (hS' : S' ≤ Γ)
    (D D' : Set G) (hD : IsRightTransversal Γ S D) (hD' : IsRightTransversal Γ S' D')
    (R : Set G) (hR : IsDoubleTransversal Γ S S' R)
    (E : G → Set G) (hE : ∀ r ∈ R, IsRightTransversal S (stab S S' r) (E r))
    (g h : G → ℝ≥0∞) (hg : ∀ s ∈ S, ∀ y : G, g (s * y) = g y)
    (hh : ∀ s ∈ S', ∀ y : G, h (s * y) = h y) (x : G) :
    (∑' δ : D, g ((δ : G) * x)) * (∑' δ' : D', h ((δ' : G) * x)) =
      ∑' r : R, ∑' p : (E (r : G) × D),
        g ((p.1 : G) * (p.2 : G) * x) * h ((r : G)⁻¹ * ((p.1 : G) * (p.2 : G) * x)) := by
  obtain ⟨hinj, hT⟩ := h3 G Γ S S' hS hS' R hR E hE
  have key : ∀ δ : D, ∑' δ' : D', h ((δ' : G) * x) =
      ∑' r : R, ∑' t : E (r : G), h ((r : G)⁻¹ * ((t : G) * (δ : G) * x)) := by
    intro δ
    have hδ : (δ : G) ∈ Γ := hD.1 δ.2
    have h1' : ∑' η : Set.range (fun q : (Σ r : R, E (r : G)) => (q.1 : G)⁻¹ * (q.2 : G)),
        h ((η : G) * (δ : G) * x) = ∑' η : D', h ((η : G) * x) :=
      h1 G Γ S' _ D' hT hD' (δ : G) hδ (fun y => h (y * x))
        (fun s hs y => by rw [mul_assoc]; exact hh s hs (y * x))
    have h2' : ∑' η : Set.range (fun q : (Σ r : R, E (r : G)) => (q.1 : G)⁻¹ * (q.2 : G)),
        h ((η : G) * (δ : G) * x) =
        ∑' q : (Σ r : R, E (r : G)), h ((q.1 : G)⁻¹ * (q.2 : G) * (δ : G) * x) :=
      tsum_range (fun η : G => h (η * (δ : G) * x)) hinj
    rw [← h1', h2', ENNReal.tsum_sigma']
    refine tsum_congr fun r => tsum_congr fun t => ?_
    simp only [mul_assoc]
  have hg' : ∀ r : R, ∀ t : E (r : G), ∀ δ : D,
      g ((t : G) * (δ : G) * x) = g ((δ : G) * x) := by
    intro r t δ
    have ht : (t : G) ∈ S := (hE r r.2).1 t.2
    rw [mul_assoc]
    exact hg _ ht _
  calc (∑' δ : D, g ((δ : G) * x)) * (∑' δ' : D', h ((δ' : G) * x))
      = ∑' δ : D, g ((δ : G) * x) * ∑' δ' : D', h ((δ' : G) * x) := ENNReal.tsum_mul_right.symm
    _ = ∑' δ : D, ∑' r : R, ∑' t : E (r : G),
          g ((t : G) * (δ : G) * x) * h ((r : G)⁻¹ * ((t : G) * (δ : G) * x)) := by
        refine tsum_congr fun δ => ?_
        rw [key δ, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun r => ?_
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun t => ?_
        rw [hg' r t δ]
    _ = ∑' r : R, ∑' t : E (r : G), ∑' δ : D,
          g ((t : G) * (δ : G) * x) * h ((r : G)⁻¹ * ((t : G) * (δ : G) * x)) := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun r => ?_
        rw [ENNReal.tsum_comm]
    _ = _ := by
        refine tsum_congr fun r => ?_
        exact (ENNReal.tsum_prod (f := fun (t : E (r : G)) (δ : D) =>
          g ((t : G) * (δ : G) * x) * h ((r : G)⁻¹ * ((t : G) * (δ : G) * x)))).symm

theorem foldDCUnfold_of (h0 : TransExists.{u}) (h1 : TransIndep.{u}) (h2 : TransProd.{u})
    (h3 : DCTrans.{u}) (hU : PI.FoldUnfold.FoldUnfold.{u}) : PI.FoldDCUnfold.FoldDCUnfold.{u} := by
  intro G _ _ _ μ _ Γ S S' _ hS hS' D D' hD hD' R hR Fs hFs FΓ hFΓ g h hgm hhm hg hh
  have hΓc : (Γ : Set G).Countable := Set.countable_coe_iff.mp (inferInstanceAs (Countable Γ))
  have hstabS : ∀ r : G, stab S S' r ≤ S := fun r => inf_le_left
  choose E hE using fun r : G => h0 G S (stab S S' r) (hstabS r)
  have hTP := fun r : G => h2 G Γ S (stab S S' r) (E r) D (hstabS r) hS (hE r) hD
  have hpt : ∀ x : G, (∑' δ : D, g ((δ : G) * x)) * (∑' δ' : D', h ((δ' : G) * x)) =
      ∑' r : R, ∑' η : Set.range (fun p : E (r : G) × D => (p.1 : G) * (p.2 : G)),
        g ((η : G) * x) * h ((r : G)⁻¹ * ((η : G) * x)) := by
    intro x
    rw [pointwise_of h1 h3 Γ S S' hS hS' D D' hD hD' R hR E (fun r _ => hE r) g h hg hh x]
    refine tsum_congr fun r => ?_
    have h2' : ∑' η : Set.range (fun p : E (r : G) × D => (p.1 : G) * (p.2 : G)),
        g ((η : G) * x) * h ((r : G)⁻¹ * ((η : G) * x)) =
        ∑' p : E (r : G) × D,
          g ((p.1 : G) * (p.2 : G) * x) * h ((r : G)⁻¹ * ((p.1 : G) * (p.2 : G) * x)) :=
      tsum_range (fun η : G => g (η * x) * h ((r : G)⁻¹ * (η * x))) (hTP (r : G)).1
    rw [h2']
  have hFm : ∀ r : G, Measurable (fun y : G => g y * h (r⁻¹ * y)) := fun r =>
    hgm.mul (hhm.comp (measurable_const_mul r⁻¹))
  have hinv : ∀ r : G, ∀ s ∈ stab S S' r, ∀ y : G,
      g (s * y) * h (r⁻¹ * (s * y)) = g y * h (r⁻¹ * y) := by
    intro r s hs y
    have hs2 := Subgroup.mem_inf.mp
      (show s ∈ S ⊓ S'.comap (MulAut.conj r⁻¹).toMonoidHom from hs)
    have hs' : r⁻¹ * s * r ∈ S' := by
      simpa [MulAut.conj_apply] using Subgroup.mem_comap.mp hs2.2
    rw [hg s hs2.1 y]
    congr 1
    calc h (r⁻¹ * (s * y)) = h ((r⁻¹ * s * r) * (r⁻¹ * y)) := by congr 1; group
      _ = h (r⁻¹ * y) := hh _ hs' _
  haveI : Countable R := (hΓc.mono hR.1).to_subtype
  simp_rw [hpt]
  rw [lintegral_tsum (fun r => ?_)]
  · refine tsum_congr fun r => ?_
    exact hU G μ Γ (stab S S' r) ((hstabS r).trans hS) (Fs r) (hFs r r.2) FΓ hFΓ _
      (hTP (r : G)).2 (fun y : G => g y * h ((r : G)⁻¹ * y)) (hFm r) (hinv r)
  · haveI : Countable (Set.range (fun p : E (r : G) × D => (p.1 : G) * (p.2 : G))) :=
      (hΓc.mono (hTP (r : G)).2.1).to_subtype
    exact (Measurable.ennreal_tsum fun η : Set.range (fun p : E (r : G) × D => (p.1 : G) * (p.2 : G)) =>
      (hFm (r : G)).comp (measurable_const_mul (η : G))).aemeasurable

end PI.FoldDCUnfold.W
