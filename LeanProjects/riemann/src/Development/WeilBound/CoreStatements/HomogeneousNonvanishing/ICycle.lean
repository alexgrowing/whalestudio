import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem icyc_mem {R : Type*} [CommRing R] {P W : Ideal R} (hW : W.IsPrime) (hP : P ≤ W) {f g u v : R}
    (hu : u ∉ W) (h : u * f - v * g ∈ P) (hg : g ∈ W) : f ∈ W := by
  have : u * f ∈ W := by simpa using W.add_mem (hP h) (W.mul_mem_left v hg)
  exact (hW.mem_or_mem this).resolve_left hu

theorem icyc_sub {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι)
    (h : ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W →
      ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P)
    (h' : ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W →
      ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * g - v * f ∈ P) : divSupp P f ⊆ divSupp P g := by
  rintro W ⟨⟨⟨hWp, hle⟩, hmin⟩, hr⟩
  have hPW : P ≤ W := le_sup_left.trans hle
  have hf : f ∈ W := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  refine ⟨⟨⟨hWp, sup_le hPW ?_⟩, ?_⟩, hr⟩
  · obtain ⟨u, v, hu, -, huv⟩ := h' W hWp hPW hr
    rw [Ideal.span_singleton_le_iff_mem]
    exact icyc_mem hWp hPW hu huv hf
  · rintro W' ⟨hW'p, hle'⟩ hWW
    have hPW' : P ≤ W' := le_sup_left.trans hle'
    have hr' : IsRelevant W' := fun k => (hr k).imp fun i hi hi' => hi (hWW hi')
    obtain ⟨u, v, hu, -, huv⟩ := h W' hW'p hPW' hr'
    refine hmin ⟨hW'p, sup_le hPW' ?_⟩ hWW
    rw [Ideal.span_singleton_le_iff_mem]
    exact icyc_mem hW'p hPW' hu huv (hle' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)))

theorem icyc_map {R : Type*} [CommRing R] (W : Ideal R) [W.IsPrime] (P : Ideal R) (f g u v : R)
    (hu : u ∉ W) (h : u * f - v * g ∈ P) :
    Ideal.map (algebraMap R (Localization.AtPrime W)) (P ⊔ Ideal.span {f}) ≤
      Ideal.map (algebraMap R (Localization.AtPrime W)) (P ⊔ Ideal.span {g}) := by
  rw [Ideal.map_le_iff_le_comap]
  refine sup_le (le_sup_left.trans Ideal.le_comap_map) ?_
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
  have hU : IsUnit (algebraMap R (Localization.AtPrime W) u) :=
    IsLocalization.map_units (Localization.AtPrime W) (⟨u, hu⟩ : W.primeCompl)
  rw [← Ideal.unit_mul_mem_iff_mem _ hU, ← map_mul]
  apply Ideal.mem_map_of_mem
  have := (P ⊔ Ideal.span {g}).add_mem (Ideal.mem_sup_left h)
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ v (Ideal.mem_span_singleton_self g)))
  simpa using this

theorem icyc_len {R : Type*} [CommRing R] (W : Ideal R) [W.IsPrime] (J : Ideal R) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ Ideal.map (algebraMap R (Localization.AtPrime W)) J) := by
  refine LinearEquiv.length_eq ?_
  exact ((LocalizedModule.equivTensorProduct W.primeCompl (R ⧸ J)).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime W) J).toLinearEquiv.symm)

theorem i_cycle : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι), UnitRatio P f g → divSupp P f = divSupp P g ∧ ∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
  intro K _ ι _ P f g h
  obtain ⟨-, -, h⟩ := h
  have h' : ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W →
      ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * g - v * f ∈ P := by
    intro W hW hP hr
    obtain ⟨u, v, hu, hv, huv⟩ := h W hW hP hr
    exact ⟨v, u, hv, hu, by simpa using P.neg_mem huv⟩
  refine ⟨Set.Subset.antisymm (icyc_sub P f g h h') (icyc_sub P g f h' h), fun W hW => ?_⟩
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
  obtain ⟨u, v, hu, hv, huv⟩ := h W hWp hPW hW.2
  unfold multAt
  rw [dif_pos hWp, dif_pos hWp]
  congr 1
  rw [icyc_len, icyc_len]
  have e : Ideal.map (algebraMap (MRing ι) (Localization.AtPrime W)) (P ⊔ Ideal.span {f}) =
      Ideal.map (algebraMap (MRing ι) (Localization.AtPrime W)) (P ⊔ Ideal.span {g}) :=
    le_antisymm (icyc_map W P f g u v hu huv) (icyc_map W P g f v u hv (by simpa using P.neg_mem huv))
  rw [e]

end PositivityTheory.UnitarySelfGeneration
