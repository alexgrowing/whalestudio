import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IdealPull

theorem germ_appLE {X Y : Scheme.{0}} (t : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (hV : V ≤ t ⁻¹ᵁ U)
    (y : Y) (hy : y ∈ V) (a : Γ(X, U)) :
    (Y.presheaf.germ V y hy).hom ((t.appLE U V hV).hom a) =
      (t.stalkMap y).hom ((X.presheaf.germ U (t y) (show t y ∈ U from hV hy)).hom a) := by
  show (Y.presheaf.germ V y hy).hom (resG Y hV ((t.app U).hom a)) = _
  rw [germ_resG]
  exact (Scheme.Hom.germ_stalkMap_apply t U y _ a).symm

theorem regAt_and_unitAt_div_gen : ∀ (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₁] (t : Y₁ ⟶ Y₀) (I : Y₀.IdealSheafData) (y : Y₁) (U : Y₀.Opens) (hx : t y ∈ U) (n : ℕ) (b : Fin n → Γ(Y₀, U)), (∀ (k : Fin n) (W : Y₀.affineOpens) (h : W.1 ≤ U), resG Y₀ h (b k) ∈ I.ideal W) → (∀ (W : Y₀.affineOpens) (hxW : t y ∈ W.1) (a : Γ(Y₀, W.1)), a ∈ I.ideal W → Y₀.presheaf.germ W.1 (t y) hxW a ∈ Ideal.span (Set.range fun k => Y₀.presheaf.germ U (t y) hx (b k))) → ∀ (U' : Y₁.affineOpens) (f : Γ(Y₁, U'.1)) (hyU' : y ∈ U'.1), fnOf U'.1 (gen_mem hyU') f ≠ 0 → (I.comap t).ideal U' = Ideal.span {f} → ∀ (V : Y₁.Opens) (hV : V ≤ t ⁻¹ᵁ U) (hyV : y ∈ V), (∀ k, RegAt y (fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f)) ∧ ∃ k, UnitAt y (fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f) := by
  intro Y₀ Y₁ _ t I y U hx n b hb hgerm U' f hyU' hf0 hU' V hV hyV
  obtain ⟨_, ⟨W, hWa, rfl⟩, hxW, hWU⟩ := Y₀.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  have hWU' : W ≤ U := hWU
  obtain ⟨_, ⟨V₀, hV₀a, rfl⟩, hyV₀, hV₀le⟩ := Y₁.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ U'.1 ⊓ t ⁻¹ᵁ W from ⟨hyU', hxW⟩) (U'.1 ⊓ t ⁻¹ᵁ W).isOpen
  have hV₀U' : V₀ ≤ U'.1 := fun z hz => (hV₀le hz).1
  have hV₀W : V₀ ≤ t ⁻¹ᵁ W := fun z hz => (hV₀le hz).2
  let R := Y₁.presheaf.stalk y
  let g : R := (Y₁.presheaf.germ U'.1 y hyU').hom f
  let β : Fin n → R := fun k => (t.stalkMap y).hom ((Y₀.presheaf.germ U (t y) hx).hom (b k))
  have hI1 : (I.comap t).ideal ⟨V₀, hV₀a⟩ = Ideal.span {resG Y₁ hV₀U' f} := by
    rw [← (I.comap t).map_ideal (U := ⟨V₀, hV₀a⟩) (V := U') hV₀U', hU', Ideal.map_span,
      Set.image_singleton]
    rfl
  have hI2 := GlobalTheory.Principalise.comapIdealAffine I t ⟨W, hWa⟩ ⟨V₀, hV₀a⟩ hV₀W
  have hgf : (Y₁.presheaf.germ V₀ y hyV₀).hom (resG Y₁ hV₀U' f) = g := germ_resG _ _ _ _
  have hc : ∀ k, ∃ c : R, β k = c * g := by
    intro k
    have hmem : (t.appLE W V₀ hV₀W).hom (resG Y₀ hWU' (b k)) ∈ (I.comap t).ideal ⟨V₀, hV₀a⟩ := by
      rw [hI2]; exact Ideal.mem_map_of_mem _ (hb k ⟨W, hWa⟩ hWU')
    rw [hI1, Ideal.mem_span_singleton'] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨(Y₁.presheaf.germ V₀ y hyV₀).hom c, ?_⟩
    have := congrArg (Y₁.presheaf.germ V₀ y hyV₀).hom hc
    rw [map_mul, hgf, germ_appLE, germ_resG] at this
    exact this.symm
  choose c hcβ using hc
  have hgmem : g ∈ Ideal.span (Set.range β) := by
    have hmem : resG Y₁ hV₀U' f ∈ (I.comap t).ideal ⟨V₀, hV₀a⟩ := by
      rw [hI1]; exact Ideal.mem_span_singleton_self _
    rw [hI2] at hmem
    have h2 := Ideal.mem_map_of_mem (Y₁.presheaf.germ V₀ y hyV₀).hom hmem
    rw [hgf, Ideal.map_map] at h2
    refine (Ideal.map_le_iff_le_comap.2 ?_) h2
    intro a ha
    rw [Ideal.mem_comap, RingHom.comp_apply, germ_appLE]
    have h3 := Ideal.mem_map_of_mem (t.stalkMap y).hom (hgerm ⟨W, hWa⟩ hxW a ha)
    rw [Ideal.map_span, ← Set.range_comp] at h3
    exact h3
  have hfK : algebraMap R Y₁.functionField g = fnOf U'.1 (gen_mem hyU') f := algebraMap_germ hyU' f
  have hg0 : g ≠ 0 := fun h => hf0 (by rw [← hfK, h, map_zero])
  have hFk : ∀ k, fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f =
      algebraMap R Y₁.functionField (c k) := by
    intro k
    rw [← algebraMap_germ hyV, ← hfK, germ_appLE]
    change algebraMap R _ (β k) / _ = _
    rw [hcβ k, map_mul, mul_div_assoc, div_self (hfK ▸ hf0), mul_one]
  refine ⟨fun k => hFk k ▸ ⟨c k, rfl⟩, ?_⟩
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hgmem
  have hsum : ∑ k, e k * c k = 1 := by
    have : (∑ k, e k * c k) * g = 1 * g := by
      rw [one_mul, Finset.sum_mul]
      conv_rhs => rw [← he]
      exact Finset.sum_congr rfl fun k _ => by rw [hcβ k, smul_eq_mul, mul_assoc]
    exact mul_right_cancel₀ hg0 this
  obtain ⟨k, hk⟩ : ∃ k, IsUnit (c k) := by
    by_contra hcon
    push_neg at hcon
    have : (1 : R) ∈ IsLocalRing.maximalIdeal R := hsum ▸ Ideal.sum_mem _ fun k _ =>
      Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hcon k))
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top this
  exact ⟨k, c k, hk, (hFk k).symm⟩

end GlobalTheory.IdealPull
