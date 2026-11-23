import Formalism.SharpRestriction.GrowthBounds.AevalValuation.PlDefs
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.TwistSubXMemSupported
import Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.LowestWeightNonposOffSet

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TraceSpectra

open Formalism.MainNotions.G Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.NormalSetCounting Formalism.MainNotions.TestSideWords.TwistedFiltration.G1

private theorem le_valS_iff_forall_coeff_ne_zero {R : Type} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι)
    (S : Set ι) (G : MvPolynomial (ι × Fin n) R) (a : WithTop ℤ) :
    a ≤ valS LL S G ↔ ∀ (m : ι × Fin n →₀ ℕ) (k : ℤ),
      (coeff m (twistSub LL S (lastIdx n) G)).coeff k ≠ 0 → a ≤ (k : WithTop ℤ) := by
  rw [valS, Finset.le_inf_iff]
  constructor
  · intro h m k hk
    apply h
    rw [sDegs, Finset.mem_biUnion]
    refine ⟨m, ?_, ?_⟩
    · rw [mem_support_iff]
      intro h0
      rw [h0] at hk
      simp at hk
    · rw [Finsupp.mem_support_iff]
      exact hk
  · intro h k hk
    rw [sDegs, Finset.mem_biUnion] at hk
    obtain ⟨m, -, hm⟩ := hk
    exact h m k (Finsupp.mem_support_iff.mp hm)

private theorem ringHom_eq_of_mem_supported_of_eqOn {σ R T : Type} [CommRing R] [CommRing T] (φ ψ : MvPolynomial σ R →+* T)
    (s : Set σ) (hC : ∀ c, φ (C c) = ψ (C c)) (hX : ∀ v ∈ s, φ (X v) = ψ (X v))
    {F : MvPolynomial σ R} (hF : F ∈ supported R s) : φ F = ψ F := by
  rw [supported_eq_range_rename, AlgHom.mem_range] at hF
  obtain ⟨p, rfl⟩ := hF
  have h : φ.comp (rename ((↑) : s → σ)).toRingHom = ψ.comp (rename ((↑) : s → σ)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [hC]
    · intro v
      simp [hX v.1 v.2]
  exact RingHom.congr_fun h p

private theorem homComp_eq_polComp {R ι : Type} [CommRing R] {n : ℕ} (d : ι → ℕ)
    (F : MvPolynomial (ι × Fin n) R) : homComp d F = Joints.StandardMonomialSpace.polComp R n d F := by
  conv_rhs => rw [F.as_sum]
  rw [map_sum]
  simp only [Joints.StandardMonomialSpace.polComp, Joints.StandardMonomialSpace.suppProj_monomial, Set.mem_setOf_eq]
  rw [homComp, Finset.sum_filter]

theorem valS_sum_ge {R : Type} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι) {α : Type}
    (s : Finset α) (f : α → MvPolynomial (ι × Fin n) R) (a : WithTop ℤ) (h : ∀ i ∈ s, a ≤ valS LL S (f i)) :
    a ≤ valS LL S (∑ i ∈ s, f i) := by
  rw [le_valS_iff_forall_coeff_ne_zero]
  intro m k hk
  have hs : Joints.StandardMonomialSpace.SuppIn {k : ℤ | a ≤ (k : WithTop ℤ)}
      (coeff m (twistSub LL S (lastIdx n) (∑ i ∈ s, f i))) := by
    rw [map_sum, coeff_sum]
    apply Joints.StandardMonomialSpace.SuppIn.sum
    intro i hi k' hk'
    exact (le_valS_iff_forall_coeff_ne_zero LL S (f i) a).mp (h i hi) m k' hk'
  exact hs k hk

theorem filtQ_eq_sum {Kf : Type} [Field Kf] {ι : Type} {n : ℕ} (Q : (ι → ℕ) → Prop) (F : MvPolynomial (ι × Fin n) Kf) :
    filtQ Q F = ∑ δ ∈ (F.support.image fun mo => fun i => multideg mo i).filter Q, homComp δ F := by
  have hmaps : ∀ mo ∈ F.support.filter (fun mo => Q fun i => multideg mo i),
      (fun i => multideg mo i) ∈ (F.support.image fun mo => fun i => multideg mo i).filter Q := by
    intro mo hmo
    rw [Finset.mem_filter] at hmo
    rw [Finset.mem_filter, Finset.mem_image]
    exact ⟨⟨mo, hmo.1, rfl⟩, hmo.2⟩
  rw [filtQ, ← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro δ hδ
  rw [homComp, Finset.filter_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext mo
  simp only [Finset.mem_filter, funext_iff]
  constructor
  · rintro ⟨hm, -, he⟩
    exact ⟨hm, he⟩
  · rintro ⟨hm, he⟩
    refine ⟨hm, ?_, he⟩
    have hδ' : (fun i => multideg mo i) = δ := funext he
    rw [hδ']
    exact (Finset.mem_filter.mp hδ).2

theorem valFilt : ValFilt := by
  intro Kf _ ι n _ LL S Q F
  rw [filtQ_eq_sum]
  apply valS_sum_ge
  intro δ _
  refine Finset.le_inf fun k hk => ?_
  rw [homComp_eq_polComp] at hk
  exact Finset.inf_le (Joints.StandardMonomialSpace.sDegs_polComp_subset LL S (lastIdx n) δ F hk)

section Aeval

variable {Kf : Type} [Field Kf] {ι κ : Type} {n : ℕ}

def thetaG (g : ι × Fin n → MvPolynomial (κ × Fin n) Kf) :
    MvPolynomial (ι × Fin n) (GLLaurent Kf n) →+* MvPolynomial (κ × Fin n) (GLLaurent Kf n) :=
  eval₂Hom C fun v => MvPolynomial.map (coefL Kf n) (g v)

theorem twist_aeval (LL : Letters ι) (LL' : Letters κ) (S L : Set ι) (S' : Set κ) (f : ι → κ)
    (g : ι × Fin n → MvPolynomial (κ × Fin n) Kf) (F : MvPolynomial (ι × Fin n) Kf)
    (hF : F ∈ supported Kf {v : ι × Fin n | v.1 ∈ L})
    (h1 : ∀ v : ι × Fin n, v.1 ∈ L → v.1 ∈ S → g v = X (f v.1, v.2) ∧ f v.1 ∈ S' ∧ LL'.vec (f v.1) = LL.vec v.1)
    (h2 : ∀ v : ι × Fin n, v.1 ∈ L → v.1 ∉ S → g v ∈ supported Kf {u : κ × Fin n | u.1 ∉ S'}) (j : Fin n) :
    twistSub LL' S' j (aeval g F) = thetaG g (twistSub LL S j F) := by
  have key := ringHom_eq_of_mem_supported_of_eqOn ((twistSub LL' S' j).comp (aeval g).toRingHom)
    ((thetaG g).comp (twistSub LL S j)) {v | v.1 ∈ L} ?_ ?_ hF
  · simpa using key
  · intro c
    simp [twistSub, thetaG]
  · intro v hv
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
    by_cases hS : v.1 ∈ S
    · obtain ⟨hg, hf, hvec⟩ := h1 v hv hS
      rw [hg]
      simp only [twistSub, eval₂Hom_X', if_pos hS, if_pos hf, hvec]
      split_ifs
      · simp only [map_sum, map_mul, thetaG, eval₂Hom_C, eval₂Hom_X']
        apply Finset.sum_congr rfl
        intro b _
        rw [(h1 (v.1, b) hv hS).1, map_X]
      · simp only [map_sum, map_mul, thetaG, eval₂Hom_C, eval₂Hom_X']
        apply Finset.sum_congr rfl
        intro b _
        rw [(h1 (v.1, b) hv hS).1, map_X]
    · have hgv := h2 v hv hS
      have hx : twistSub LL S j (X v : MvPolynomial (ι × Fin n) Kf) = X v := by
        simp only [twistSub, eval₂Hom_X', if_neg hS]
      rw [hx, thetaG, eval₂Hom_X']
      refine ringHom_eq_of_mem_supported_of_eqOn (twistSub LL' S' j) (MvPolynomial.map (coefL Kf n))
        {u | u.1 ∉ S'} ?_ ?_ hgv
      · intro c
        simp [twistSub]
      · intro u hu
        have hu' : u.1 ∉ S' := hu
        simp only [twistSub, eval₂Hom_X', if_neg hu', map_X]

theorem thetaG_mem (g : ι × Fin n → MvPolynomial (κ × Fin n) Kf) (e t : ℤ)
    (P : MvPolynomial (ι × Fin n) (GLLaurent Kf n)) (hP : P ∈ (laurentCoeffFiltration Kf n (ι × Fin n) e).F t) :
    thetaG g P ∈ (laurentCoeffFiltration Kf n (κ × Fin n) e).F t := by
  refine flt_hom_mem (flt_L (GLCoord Kf n) e) (laurentCoeffFiltration Kf n (κ × Fin n) e) (thetaG g) 0 ?_ ?_ hP
  · intro t b hb
    rw [thetaG, eval₂Hom_C]
    exact flt_C_mem hb
  · intro w
    rw [thetaG, eval₂Hom_X']
    intro m
    rw [coeff_map]
    simp only [AddMonoidHom.zero_apply, sub_zero]
    exact flt_L_C e _

end Aeval

theorem valAeval : ValAeval := by
  intro Kf _ ι κ n _ LL LL' S L S' f g F hF h1 h2
  have := flt_withTop_le (a := valS LL S F) (b := valS LL' S' (aeval g F)) (N := 0) ?_
  · simpa using this
  · intro t ht
    rw [flt_le_valS] at ht
    rw [sub_zero, flt_le_valS, twist_aeval LL LL' S L S' f g F hF h1 h2]
    exact thetaG_mem g 1 t _ ht

end Formalism.MainNotions.TraceSpectra
