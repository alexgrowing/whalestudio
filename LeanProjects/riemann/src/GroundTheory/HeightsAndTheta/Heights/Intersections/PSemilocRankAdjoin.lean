import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocRankFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.StChartScalingIndep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PAdjoinIndepRelfinrank
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFinrankAdjoinRange
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem SemilocRankAdjoin.chart_congr {K' Ω : Type*} {ι' : K' → Type*} (x' : (Σ k', ι' k') → Ω)
    (i' : ∀ k', ι' k') {a b : K'} (h : a = b) : x' ⟨a, i' a⟩ = x' ⟨b, i' b⟩ := by
  subst h
  rfl

theorem SemilocRankAdjoin.isMultiHomogIdeal_map {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    IsMultiHomogIdeal (P.map (MvPolynomial.map (Int.castRingHom ℚ) : MRing ι →+* MRingOver ℚ ι)) := by
  obtain ⟨S, hS, rfl⟩ := hP
  refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, Ideal.map_span _ _⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, fun m hm => ha m (MvPolynomial.support_map_subset _ _ hm)⟩

theorem SemilocRankAdjoin.chain (hT : ChartScalingIndep.Statement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K → K'}
    {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} (G : GenFibre v P') (i' : ∀ k', ι' k')
    (F : Type) [Field F] [Algebra F G.Φ] [Algebra F G.Φ'] [IsScalarTower F G.Φ G.Φ'] (hv : IsBlockMap κ v)
    (hx : ∀ k', G.x' ⟨k', i' k'⟩ ≠ 0)
    (hmh : IsMultiHomogIdeal (RingHom.ker (aeval G.x' : MRingOver F ι' →ₐ[F] G.Φ'))) :
    IntermediateField.relfinrank
        (IntermediateField.adjoin F (Set.range ((fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩) ∘ v)))
        (IntermediateField.adjoin F (Set.range fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩)) =
      Module.finrank G.Φ (IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i' q.1.1⟩)) := by
  let y' : (Σ k', ι' k') → G.Φ' := fun q => G.x' q / G.x' ⟨q.1, i' q.1⟩
  let t : K → G.Φ' := fun k => G.x' ⟨κ k, i' (κ k)⟩
  let Φ₁ := (IsScalarTower.toAlgHom F G.Φ G.Φ').fieldRange
  let L₀ := IntermediateField.adjoin F (Set.range (y' ∘ v))
  let L := IntermediateField.adjoin F (Set.range y')
  let E := IntermediateField.adjoin F (Set.range t)
  have mono : ∀ {A B : Set G.Φ'}, A ⊆ B → IntermediateField.adjoin F A ≤ IntermediateField.adjoin F B :=
    fun h => IntermediateField.adjoin_le_iff.2 (h.trans (IntermediateField.subset_adjoin _ _))
  have hchart : ∀ q : Σ k, ι k, G.x' ⟨(v q).1, i' (v q).1⟩ = t q.1 :=
    fun q => SemilocRankAdjoin.chart_congr G.x' i' (hv.2.2.1 q)
  have hmem : ∀ c, algebraMap G.Φ G.Φ' c ∈ Φ₁ := fun c => AlgHom.mem_fieldRange.2 ⟨c, rfl⟩
  have ht1 : ∀ k, t k ∈ Φ₁ := fun k => by
    obtain ⟨p₀, h⟩ := hv.2.2.2 ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    show G.x' ⟨κ k, i' (κ k)⟩ ∈ Φ₁
    rw [← h, G.compat]
    exact hmem _
  have hyv : ∀ q, y' (v q) ∈ Φ₁ := fun q => by
    show G.x' (v q) / G.x' ⟨(v q).1, i' (v q).1⟩ ∈ Φ₁
    rw [hchart, G.compat]
    exact div_mem (hmem _) (ht1 q.1)
  have hL₀E : L₀ ⊔ E = Φ₁ := by
    refine le_antisymm (sup_le (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)) ?_
    · rintro _ ⟨q, rfl⟩
      exact hyv q
    · rintro _ ⟨k, rfl⟩
      exact ht1 k
    · intro z hz
      obtain ⟨c, rfl⟩ := AlgHom.mem_fieldRange.1 hz
      obtain ⟨f, g, -, rfl⟩ := G.gen c
      have hpoly : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) ∈ L₀ ⊔ E := by
        intro f
        induction f using MvPolynomial.induction_on with
        | C a =>
          rw [aeval_C, ← IsScalarTower.algebraMap_apply, algebraMap_int_eq, eq_intCast]
          exact intCast_mem _ a
        | add f g hf hg =>
          rw [map_add, map_add]
          exact add_mem hf hg
        | mul_X f q hf =>
          rw [map_mul, map_mul, aeval_X, ← G.compat]
          refine mul_mem hf ?_
          have hq : G.x' (v q) = y' (v q) * t q.1 := by
            show _ = G.x' (v q) / G.x' ⟨(v q).1, i' (v q).1⟩ * t q.1
            rw [hchart, div_mul_cancel₀ _ (hx (κ q.1))]
          rw [hq]
          exact mul_mem ((le_sup_left : L₀ ≤ L₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩))
            ((le_sup_right : E ≤ L₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q.1, rfl⟩))
      show IsScalarTower.toAlgHom F G.Φ G.Φ' (aeval G.x f / aeval G.x g) ∈ L₀ ⊔ E
      rw [map_div₀]
      exact div_mem (hpoly f) (hpoly g)
  have hLE : L ⊔ E = Φ₁ ⊔ IntermediateField.adjoin F
      (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i' q.1.1⟩) := by
    refine le_antisymm (sup_le (IntermediateField.adjoin_le_iff.2 ?_)
      (((le_sup_right : E ≤ L₀ ⊔ E).trans hL₀E.le).trans le_sup_left)) (sup_le ?_ ?_)
    · rintro _ ⟨q, rfl⟩
      by_cases hq : q.1 ∈ Set.range κ
      · obtain ⟨r, rfl⟩ := hv.2.2.2 q hq
        exact (le_sup_left : Φ₁ ≤ _) (hyv r)
      · exact (le_sup_right : IntermediateField.adjoin _ _ ≤ _)
          (IntermediateField.subset_adjoin _ _ ⟨⟨⟨q.1, hq⟩, q.2⟩, rfl⟩)
    · rw [← hL₀E]
      exact sup_le_sup_right (mono (Set.range_comp_subset_range v y')) E
    · refine (mono ?_).trans le_sup_left
      rintro _ ⟨q, rfl⟩
      exact ⟨⟨q.1.1, q.2⟩, rfl⟩
  have hindep : AlgebraicIndependent L t := (hT F G.Φ' K' ι' G.x' i' hx hmh).comp κ hv.1
  rw [← AdjoinIndepRelfinrank.proof F G.Φ' L₀ L K t (mono (Set.range_comp_subset_range v y')) hindep,
    FinrankAdjoinRange.proof F G.Φ G.Φ']
  change IntermediateField.relfinrank (L₀ ⊔ E) (L ⊔ E) = _
  rw [hL₀E, hLE]

theorem SemilocRankAdjoin.proof (hF : SemilocRankFrac.Statement) (hT : ChartScalingIndep.Statement) :
    SemilocRankAdjoin.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G s α W i' hv hP' hZ hs hsP hW hi'

  have hker : ∀ f : MRing ι', aeval G.x' f = 0 ↔ f ∈ P' := fun f => by rw [← RingHom.mem_ker, G.genericFibre_ker_target]
  have : CharZero G.Φ' := charZero_of_inj_zero fun m hm => by
    have h : (C (m : ℤ) : MRing ι') ∈ P' := (hker _).1 (by rw [aeval_C]; exact_mod_cast hm)
    have h' : (m : ℤ) ∈ P'.comap (C : ℤ →+* MRing ι') := h
    rw [hP'.2.2.1, Ideal.mem_bot] at h'
    exact_mod_cast h'
  have : CharZero G.Φ := (RingHom.charZero_iff (algebraMap G.Φ G.Φ').injective).2 inferInstance
  have : IsScalarTower ℚ G.Φ G.Φ' := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

  have hkerQ : RingHom.ker (aeval G.x' : MRingOver ℚ ι' →ₐ[ℚ] G.Φ') =
      P'.map (MvPolynomial.map (Int.castRingHom ℚ) : MRing ι' →+* MRingOver ℚ ι') := by
    let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k', ι' k') (R := ℤ) (S := ℚ)
    have _ : IsLocalization ((nonZeroDivisors ℤ).map (C (σ := Σ k', ι' k') (R := ℤ))) (MRingOver ℚ ι') :=
      MvPolynomial.isLocalization _ _
    refine (IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := Σ k', ι' k') (R := ℤ))) (MRingOver ℚ ι')
      (RingHom.ker (aeval G.x' : MRingOver ℚ ι' →ₐ[ℚ] G.Φ'))).symm.trans ?_
    congr 1
    ext f
    rw [Ideal.mem_comap, RingHom.mem_ker, algebraMap_def, aeval_map_algebraMap, hker]
  have hx : ∀ k', G.x' ⟨k', i' k'⟩ ≠ 0 := fun k' h => hi' k' ((hker _).1 (by rw [aeval_X, h]))
  rw [hF K ι K' ι' κ v P' n G s α W i' hv hP' hZ hs hsP hW hi',
    SemilocRankAdjoin.chain hT G i' ℚ hv hx (hkerQ ▸ SemilocRankAdjoin.isMultiHomogIdeal_map hP'.2.1.2.1)]

end GroundTheory.Heights₂.Heights.Inter
