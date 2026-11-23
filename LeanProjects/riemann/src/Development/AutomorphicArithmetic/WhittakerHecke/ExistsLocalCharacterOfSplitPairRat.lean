import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws
import GroundTheory.GlobalFields.SemilocalAlgebras.LocalDegree
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

namespace UpperTheory.AdeleBaseChangeSplitting
open UpperTheory.ConvolutionTheory.R2.H GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem split_iota (v : P F) (w : P E) [hl : w.asIdeal.LiesOver v.asIdeal] (h : SplitAt v w) :
    ∃ i : Kv v ≃+* Kv w, (∀ x, completionMap v w x = i x) ∧
      (∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) ∧
      ∀ x, Valued.v (i x) = Valued.v x := by
  obtain ⟨-, i, hc, ha, hv⟩ := h
  refine ⟨i, ?_, ha, hv⟩
  have := (HeightOneSpectrum.denseRange_algebraMap (K := F) v).equalizer
    (continuous_completionMap v w) hc (by
      funext x
      change completionMap v w (algebraMap F (Kv v) x) = i (algebraMap F (Kv v) x)
      rw [ha, completionMap_algebraMap, IsScalarTower.algebraMap_apply F E (Kv w)])
  exact fun x => congrFun this x

private theorem adeleMap_split_two_places (v : P F) (w w' : P E) [hl : w.asIdeal.LiesOver v.asIdeal]
    [hl' : w'.asIdeal.LiesOver v.asIdeal] (hne : w ≠ w')
    (hu : ∀ u : P E, u.asIdeal.LiesOver v.asIdeal → u = w ∨ u = w') (x : Kv v) :
    adeleMap F E (sg v x) = sg w (completionMap v w x) + sg w' (completionMap v w' x) := by
  obtain ⟨-, -, hc, -, -, -, -, hs, -, -⟩ := sgLaws F v
  obtain ⟨-, -, hc', -, -, -, -, hs', -, -⟩ := sgLaws E w
  obtain ⟨-, -, hc'', -, -, -, -, hs'', -, -⟩ := sgLaws E w'
  refine Prod.ext ?_ (FiniteAdeleRing.ext E fun u => ?_)
  · change InfinitePlace.infiniteAdeleRingMap (sg v x).1 = (sg w _).1 + (sg w' _).1
    rw [(hs x).1, (hs' _).1, (hs'' _).1, map_zero, add_zero]
  · change completionMap (below F u) u ((sg v x).2 (below F u)) = (sg w _).2 u + (sg w' _).2 u
    by_cases h : u = w
    · subst h
      have hb : below F u = v := (below_eq_iff _ _).2 hl
      subst hb
      rw [(hs'' _).2 _ hne, add_zero]
      exact (congrArg _ (hc x)).trans (hc' _).symm
    · by_cases h' : u = w'
      · subst h'
        have hb : below F u = v := (below_eq_iff _ _).2 hl'
        subst hb
        rw [(hs' _).2 _ h, zero_add]
        exact (congrArg _ (hc x)).trans (hc'' _).symm
      · have hb : below F u ≠ v := fun hb => (hu u ((below_eq_iff _ _).1 hb)).elim h h'
        rw [(hs x).2 _ hb, map_zero, (hs' _).2 _ h, (hs'' _).2 _ h', add_zero]

private theorem main (D : Dat F E) (v : P F) (w w' : P E) [hl : w.asIdeal.LiesOver v.asIdeal]
    [hl' : w'.asIdeal.LiesOver v.asIdeal] (hne : w ≠ w') (h1 : SplitAt v w) (h2 : SplitAt v w')
    (hu : ∀ u : P E, u.asIdeal.LiesOver v.asIdeal → u = w ∨ u = w') (hG : Gd D.δ v) :
    ∃ χ : Kv w → ℂ, Good χ ∧ ∀ x, ∃ u t, sg w x = D.mkE u t ∧ ψ (-t) = χ x := by
  obtain ⟨i, hi, hia, hiv⟩ := split_iota v w h1
  obtain ⟨j, hj, hja, hjv⟩ := split_iota v w' h2
  obtain ⟨τ, hτ⟩ := i.surjective (algebraMap E (Kv w) D.θ)
  have hτ2 : τ ^ 2 = algebraMap F (Kv v) D.δ := by
    apply i.injective
    rw [map_pow, hτ, hia, ← map_pow, D.sq]
  have hτv : Valued.v τ = 1 := by
    have h := hG.del
    rw [← hτ2, map_pow] at h
    exact (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 h
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτv
  have h20 : (2 : Kv v) ≠ 0 := fun h => by simpa [h] using hG.two
  have hτ' : j τ = -algebraMap E (Kv w') D.θ := by
    have hsq : (j τ) ^ 2 = (algebraMap E (Kv w') D.θ) ^ 2 := by
      rw [← map_pow, hτ2, hja, ← map_pow, D.sq]
    refine (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left fun he => hne ?_
    have hval : ∀ y : E, w.valuation E y = w'.valuation E y := by
      intro y
      have hy : y = algebraMap F E (D.b.repr y 0) + algebraMap F E (D.b.repr y 1) * D.θ := by
        conv_lhs => rw [← D.b.sum_repr y]
        simp [Fin.sum_univ_two, D.b0, D.b1, Algebra.smul_def]
      set a := algebraMap F (Kv v) (D.b.repr y 0)
      set b := algebraMap F (Kv v) (D.b.repr y 1)
      have e1 : algebraMap E (Kv w) y = i (a + b * τ) := by
        rw [map_add, map_mul, hτ, hia, hia, ← map_mul, ← map_add, ← hy]
      have e2 : algebraMap E (Kv w') y = j (a + b * τ) := by
        rw [map_add, map_mul, he, hja, hja, ← map_mul, ← map_add, ← hy]
      rw [← valued_algebraMap_field, ← valued_algebraMap_field, e1, e2, hiv, hjv]
    refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), hval]
  have hcv : Valued.v (2 * τ) = 1 := by rw [map_mul, hG.two, hτv, mul_one]
  obtain ⟨g1, g2, g3⟩ := hG.psi
  obtain ⟨hadd, hmul, -⟩ := sgLaws F v
  obtain ⟨hadd1, hmul1, -⟩ := sgLaws E w
  obtain ⟨hadd2, hmul2, -⟩ := sgLaws E w'
  have hsv : ∀ x : Kv w, Valued.v (-(i.symm x / (2 * τ))) = Valued.v x := by
    intro x
    rw [Valuation.map_neg, map_div₀, hcv, div_one, ← hiv, RingEquiv.apply_symm_apply]
  refine ⟨fun x => ψ (sg v (-(i.symm x / (2 * τ)))), ⟨fun x y => ?_, fun x hx => ?_, fun x hx => ?_⟩,
    fun x => ⟨sg v (i.symm x / 2), sg v (i.symm x / (2 * τ)), ?_, ?_⟩⟩
  · have e : -(i.symm (x + y) / (2 * τ)) = -(i.symm x / (2 * τ)) + -(i.symm y / (2 * τ)) := by
      rw [map_add]; ring
    show ψ (sg v (-(i.symm (x + y) / (2 * τ)))) = _
    rw [e]
    exact g1 _ _
  · exact g2 _ (by unfold IsInt at *; rw [hsv]; exact hx)
  · have := g3 (-(i.symm x / (2 * τ))) fun c hc => by
      have h := hx (i c) (by unfold IsInt at *; rw [hiv]; exact hc)
      have e : -(i.symm (i c * x) / (2 * τ)) = c * -(i.symm x / (2 * τ)) := by
        rw [map_mul, RingEquiv.symm_apply_apply]; ring
      change ψ (sg v (-(i.symm (i c * x) / (2 * τ)))) = 1 at h
      rw [e] at h
      exact h
    unfold IsInt at *
    rwa [hsv] at this
  · have hmk : ∀ u t : A F, D.mkE u t = adeleMap F E u + adeleMap F E t * rt D.θ := fun _ _ => rfl
    obtain ⟨y, rfl⟩ := i.surjective x
    have z2 : sg w' 0 = 0 := by
      have := hmul2 0 0
      simpa using this.symm
    have c1 : cp w (rt D.θ) = i τ := hτ.symm
    have c2 : cp w' (rt D.θ) = - j τ := by rw [hτ', neg_neg]; rfl
    rw [RingEquiv.symm_apply_apply, hmk, adeleMap_split_two_places v w w' hne hu, adeleMap_split_two_places v w w' hne hu,
      add_mul, mul_comm (sg w _), mul_comm (sg w' _), hmul1, hmul2, add_add_add_comm, ← hadd1, ← hadd2,
      c1, c2, hi, hi, hj, hj, ← map_neg, ← map_mul, ← map_mul, ← map_add, ← map_add,
      show y / 2 + τ * (y / (2 * τ)) = y by field_simp; ring,
      show y / 2 + -τ * (y / (2 * τ)) = 0 by field_simp; ring, map_zero, z2, add_zero]
  · have := hmul (-1) (i.symm x / (2 * τ))
    rw [map_neg, map_one, neg_one_mul, neg_one_mul] at this
    rw [this]

end UpperTheory.AdeleBaseChangeSplitting

theorem UpperTheory.exists_localCharacter_of_split_pair_rat :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (v : H.P ℚ) (w w' : H.P E), w ≠ w' → w.under (𝓞 ℚ) = v → w'.under (𝓞 ℚ) = v → H.SplitAt v w → H.SplitAt v w' →
          (∀ w'' : H.P E, w''.under (𝓞 ℚ) = v → w'' = w ∨ w'' = w') → H.Gd D.δ v →
          ∃ χ : H.Kv w → ℂ, H.Good χ ∧ ∀ x, ∃ u t, H.sg w x = D.mkE u t ∧ ψ (-t) = χ x := by
  intro E _ _ D v w w' hne hw hw' h1 h2 hu hG
  haveI hl : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw]; rfl⟩
  haveI hl' : w'.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw']; rfl⟩
  exact UpperTheory.AdeleBaseChangeSplitting.main D v w w' hne h1 h2
    (fun u h => hu u (HeightOneSpectrum.ext h.1.symm)) hG
