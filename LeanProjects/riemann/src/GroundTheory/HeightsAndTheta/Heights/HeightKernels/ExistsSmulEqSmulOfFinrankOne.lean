import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithDegree
import GroundTheory.HeightsAndTheta.Heights.HermitianSum
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StdCoordMapInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

noncomputable section

section Coefficient

variable {K : Type*} [Field K] [NumberField K] {E : HermitianBundle K}

theorem exists_smul_eq_smul_of_finrank_one {N : Submodule (𝓞 K) E.carrier}
    (hN : Module.finrank (𝓞 K) N = 1) {l : E.carrier} (hl : l ∈ N) (hl0 : l ≠ 0)
    {w : E.carrier} (hw : w ∈ N) : ∃ t s : 𝓞 K, t ≠ 0 ∧ t • w = s • l := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hli : LinearIndependent (𝓞 K) ![(⟨w, hw⟩ : N), ⟨l, hl⟩] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h : s • w + t • l = 0 := congrArg Subtype.val hst
    by_cases hs : s = 0
    · subst hs
      rw [zero_smul, zero_add] at h
      exact ⟨rfl, (smul_eq_zero.mp h).resolve_right hl0⟩
    · exact absurd (by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h) (hcon s (-t) hs)
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, hN] at this
  omega

theorem lineCoef_ratio_unique {l w : E.carrier} (hl0 : l ≠ 0) {t s t' s' : 𝓞 K} (ht : t ≠ 0) (ht' : t' ≠ 0)
    (h : t • w = s • l) (h' : t' • w = s' • l) : (s : K) / t = s' / t' := by
  have key : (t' * s - t * s') • l = 0 := by
    rw [sub_smul, mul_smul, mul_smul, ← h, ← h', smul_comm t' t, sub_self]
  have key' : t' * s = t * s' := sub_eq_zero.mp ((smul_eq_zero.mp key).resolve_right hl0)
  have h1 : (t : K) ≠ 0 := by exact_mod_cast ht
  have h2 : (t' : K) ≠ 0 := by exact_mod_cast ht'
  have h3 := congrArg (fun x : 𝓞 K => (x : K)) key'
  push_cast at h3
  rw [div_eq_div_iff h1 h2]
  linear_combination h3

variable {N : Submodule (𝓞 K) E.carrier} (hN : Module.finrank (𝓞 K) N = 1) {l : E.carrier}
  (hl : l ∈ N) (hl0 : l ≠ 0)

def lineCoefFun (w : N) : K :=
  ((exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2).choose_spec.choose : K) /
    ((exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2).choose : K)

theorem lineCoefFun_eq (w : N) {t s : 𝓞 K} (ht : t ≠ 0) (h : t • (w : E.carrier) = s • l) :
    lineCoefFun hN hl hl0 w = (s : K) / t :=
  lineCoef_ratio_unique hl0 (exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2).choose_spec.choose_spec.1 ht
    (exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2).choose_spec.choose_spec.2 h

def lineCoef : N →ₗ[𝓞 K] K where
  toFun := lineCoefFun hN hl hl0
  map_add' w w' := by
    obtain ⟨t, s, ht, h⟩ := exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2
    obtain ⟨t', s', ht', h'⟩ := exists_smul_eq_smul_of_finrank_one hN hl hl0 w'.2
    have h'' : (t * t') • ((w + w' : N) : E.carrier) = (t' * s + t * s') • l := by
      rw [Submodule.coe_add, smul_add, mul_smul, mul_smul, h', smul_comm t t' (w : E.carrier), h,
        ← mul_smul, ← mul_smul, ← add_smul]
    rw [lineCoefFun_eq hN hl hl0 w ht h, lineCoefFun_eq hN hl hl0 w' ht' h',
      lineCoefFun_eq hN hl hl0 (w + w') (mul_ne_zero ht ht') h'']
    have h1 : (t : K) ≠ 0 := by exact_mod_cast ht
    have h2 : (t' : K) ≠ 0 := by exact_mod_cast ht'
    push_cast
    field_simp
  map_smul' c w := by
    obtain ⟨t, s, ht, h⟩ := exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2
    have h' : t • ((c • w : N) : E.carrier) = (c * s) • l := by
      rw [Submodule.coe_smul, smul_comm, h, mul_smul]
    rw [lineCoefFun_eq hN hl hl0 w ht h, lineCoefFun_eq hN hl hl0 (c • w) ht h', RingHom.id_apply,
      Algebra.smul_def]
    push_cast
    rw [mul_div_assoc]

theorem lineCoef_eq (w : N) {t s : 𝓞 K} (ht : t ≠ 0) (h : t • (w : E.carrier) = s • l) :
    lineCoef hN hl hl0 w = (s : K) / t :=
  lineCoefFun_eq hN hl hl0 w ht h

theorem lineCoef_self : lineCoef hN hl hl0 ⟨l, hl⟩ = 1 := by
  rw [lineCoef_eq hN hl hl0 ⟨l, hl⟩ (t := 1) (s := 1) one_ne_zero rfl]
  simp

theorem lineCoef_eq_zero {w : N} (hw : lineCoef hN hl hl0 w = 0) : (w : E.carrier) = 0 := by
  obtain ⟨t, s, ht, h⟩ := exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2
  rw [lineCoef_eq hN hl hl0 w ht h, div_eq_zero_iff] at hw
  have hs : s = 0 := by
    rcases hw with hw | hw
    · exact_mod_cast hw
    · exact absurd hw (by exact_mod_cast ht)
  rw [hs, zero_smul] at h
  exact (smul_eq_zero.mp h).resolve_left ht

theorem fibreVec_lineCoef (σ : K →+* ℂ) (w : N) :
    fibreVec E.metric σ (w : E.carrier) = σ (lineCoef hN hl hl0 w) • fibreVec E.metric σ l := by
  obtain ⟨t, s, ht, h⟩ := exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2
  have hst : σ (t : K) ≠ 0 := by rw [map_ne_zero]; exact_mod_cast ht
  have h1 := congrArg (fibreVec E.metric σ) h
  rw [fibreVec_smul, fibreVec_smul] at h1
  rw [lineCoef_eq hN hl hl0 w ht h, map_div₀, div_eq_inv_mul, mul_smul, ← h1, smul_smul,
    inv_mul_cancel₀ hst, one_smul]

end Coefficient

theorem fibreVec_finset_sum {K : Type*} [Field K] [NumberField K] {E : HermitianBundle K} (σ : K →+* ℂ)
    {ι : Type*} (S : Finset ι) (f : ι → E.carrier) :
    fibreVec E.metric σ (∑ i ∈ S, f i) = ∑ i ∈ S, fibreVec E.metric σ (f i) := by
  simp only [fibreVec, tmul_sum, map_sum]

theorem S6.LineCoordinates.proof : S6.LineCoordinates.Statement := by
  intro K _ _ E X _ _ L hI hr ho
  set n := Fintype.card X
  let e : Fin n ≃ X := (Fintype.equivFin X).symm
  have hne : ∀ x, ∃ l ∈ L x, l ≠ 0 := by
    intro x
    have hb : L x ≠ ⊥ := by
      intro h
      have h1 := hr x
      rw [h] at h1
      simp [HermitianBundle.rank] at h1
    exact (Submodule.ne_bot_iff _).mp hb
  choose l hl hl0 using hne
  let α : ∀ x, L x →ₗ[𝓞 K] K := fun x => lineCoef (hr x) (hl x) (hl0 x)
  let Φ := LinearEquiv.ofBijective (DirectSum.coeLinearMap L) hI
  let comp : ∀ x, E.carrier →ₗ[𝓞 K] L x := fun x =>
    (DirectSum.component (𝓞 K) X (fun x => L x) x).comp Φ.symm.toLinearMap
  have hcomp_same : ∀ x (w : E.carrier) (hw : w ∈ L x), comp x w = ⟨w, hw⟩ := fun x w hw =>
    hI.ofBijective_coeLinearMap_of_mem hw
  have hcomp_ne : ∀ x y (w : E.carrier), w ∈ L x → x ≠ y → comp y w = 0 := fun x y w hw hxy =>
    hI.ofBijective_coeLinearMap_of_mem_ne hxy hw
  have hsum : ∀ v : E.carrier, ∑ x, (comp x v : E.carrier) = v := by
    intro v
    conv_rhs => rw [← Φ.apply_symm_apply v, ← DirectSum.sum_univ_of (Φ.symm v)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    show _ = DirectSum.coeLinearMap L (DirectSum.of (fun i => L i) x (Φ.symm v x))
    rw [DirectSum.coeLinearMap_of]
    rfl
  let ψ : E.carrier →ₗ[𝓞 K] (Fin n → K) := LinearMap.pi fun i => (α (e i)).comp (comp (e i))
  have hψ_apply : ∀ v i, ψ v i = α (e i) (comp (e i) v) := fun _ _ => rfl
  have hψ_line : ∀ i (w : E.carrier) (hw : w ∈ L (e i)),
      ψ w = Pi.single i (α (e i) ⟨w, hw⟩) := by
    intro i w hw
    funext j
    rw [hψ_apply]
    by_cases hj : j = i
    · subst hj
      rw [hcomp_same _ w hw, Pi.single_eq_same]
    · rw [hcomp_ne _ _ w hw (e.injective.ne (Ne.symm hj)), map_zero, Pi.single_eq_of_ne hj]

  have hfrac : ∀ i, IsFractional (𝓞 K)⁰ (LinearMap.range (α (e i))) := fun i =>
    FractionalIdeal.isFractional_of_fg (by
      rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _)
  let a : Fin n → FractionalIdeal (𝓞 K)⁰ K := fun i => ⟨LinearMap.range (α (e i)), hfrac i⟩
  have ha : ∀ i, a i ≠ 0 := by
    intro i h
    have h1 : (1 : K) ∈ (a i : Submodule (𝓞 K) K) :=
      LinearMap.mem_range.mpr ⟨⟨l (e i), hl (e i)⟩, lineCoef_self _ _ _⟩
    rw [h, FractionalIdeal.coe_zero, Submodule.mem_bot] at h1
    exact one_ne_zero h1

  have hψl : ∀ i, ψ (l (e i)) = Pi.single i 1 := fun i => by
    rw [hψ_line i _ (hl (e i))]
    exact congrArg (Pi.single i) (lineCoef_self _ _ _)
  have hlin : LinearIndependent (𝓞 K) (fun i => l (e i)) := by
    apply LinearIndependent.of_comp ψ
    have h1 : (ψ ∘ fun i => l (e i)) = fun i => Pi.basisFun K (Fin n) i := by
      funext i
      simp only [Function.comp_apply, hψl, Pi.basisFun_apply]
    rw [h1, LinearIndependent.iff_fractionRing (𝓞 K) K]
    exact (Pi.basisFun K (Fin n)).linearIndependent
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hc : ∀ i, comp (e i) v = 0 := by
      intro i
      have h := congrFun hv i
      rw [hψ_apply, Pi.zero_apply] at h
      exact Subtype.ext (lineCoef_eq_zero _ _ _ h)
    rw [← hsum v]
    refine Finset.sum_eq_zero fun x _ => ?_
    obtain ⟨i, rfl⟩ := e.surjective x
    rw [hc i, Submodule.coe_zero]
  have hrange : LinearMap.range ψ = idealLattice a := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      rw [idealLattice, Submodule.mem_pi]
      intro i _
      exact LinearMap.mem_range.mpr ⟨comp (e i) v, rfl⟩
    · intro f hf
      rw [idealLattice, Submodule.mem_pi] at hf
      have h1 : ∀ i, ∃ w : L (e i), α (e i) w = f i := fun i =>
        LinearMap.mem_range.mp (hf i (Set.mem_univ i))
      choose w hw using h1
      refine ⟨∑ i, (w i : E.carrier), ?_⟩
      have h2 : ∀ i, ψ (w i) = Pi.single i (f i) := fun i => by
        rw [hψ_line i _ (w i).2, ← hw i]
      rw [map_sum]
      simp only [h2]
      exact Finset.univ_sum_single f
  have hfin : Module.finrank (𝓞 K) E.carrier = n := by
    apply le_antisymm
    · obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K) (M := E.carrier) le_rfl
      have h1 : LinearIndependent K (ψ ∘ f) := (LinearIndependent.iff_fractionRing (𝓞 K) K).mp
        (hf.map' ψ (LinearMap.ker_eq_bot.mpr hinj))
      simpa using h1.fintype_card_le_finrank
    · simpa using hlin.fintype_card_le_finrank
  have hlines : ∀ i, (L (e i)).map ψ = idealLattice a ⊓
      (Submodule.span K {(Pi.single i 1 : Fin n → K)}).restrictScalars (𝓞 K) := by
    intro i
    ext f
    simp only [Submodule.mem_map, Submodule.mem_inf, Submodule.restrictScalars_mem,
      Submodule.mem_span_singleton]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨hrange ▸ LinearMap.mem_range_self ψ w, α (e i) ⟨w, hw⟩, ?_⟩
      rw [hψ_line i w hw]
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_eq_of_ne hj]
    · rintro ⟨hf1, c, rfl⟩
      have hmem : (c • Pi.single i 1 : Fin n → K) i ∈ (a i : Submodule (𝓞 K) K) := by
        rw [idealLattice, Submodule.mem_pi] at hf1
        exact hf1 i (Set.mem_univ _)
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hmem
      refine ⟨w, w.2, ?_⟩
      rw [hψ_line i w w.2]
      rw [show α (e i) ⟨(w : E.carrier), w.2⟩ = α (e i) w from rfl, hw]
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_eq_of_ne hj]

  have hinnerF : ∀ σ (v w : E.carrier), inner ℂ (fibreVec E.metric σ v) (fibreVec E.metric σ w) =
      (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w) :=
    fun _ _ _ => rfl
  let d : (K →+* ℂ) → Fin n → ℝ := fun σ i =>
    (inner ℂ (fibreVec E.metric σ (l (e i))) (fibreVec E.metric σ (l (e i)))).re
  have hF0 : ∀ σ i, fibreVec E.metric σ (l (e i)) ≠ 0 := fun σ i =>
    (linearIndependent_fibreVec E.metric σ hlin).ne_zero i
  have hd : ∀ σ i, 0 < d σ i := fun σ i => by
    have h := (re_inner_self_pos (𝕜 := ℂ)).mpr (hF0 σ i)
    rw [RCLike.re_to_complex] at h
    exact h
  have hc : ∀ σ i, d (conjugate σ) i = d σ i := fun σ i => by
    simp only [d, hinnerF]
    have h := E.metric.form_conj σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] l (e i))
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] l (e i))
    rw [conjMap_tmul, map_one] at h
    rw [h, Complex.conj_re]
  have hdi : ∀ σ i, inner ℂ (fibreVec E.metric σ (l (e i))) (fibreVec E.metric σ (l (e i))) =
      ((d σ i : ℝ) : ℂ) := fun σ i => by
    apply Complex.ext
    · simp [d]
    · simp only [Complex.ofReal_im, hinnerF]
      exact core_inner_self_im _ _

  have hexp : ∀ σ (v : E.carrier),
      fibreVec E.metric σ v = ∑ i, σ (ψ v i) • fibreVec E.metric σ (l (e i)) := by
    intro σ v
    conv_lhs => rw [← hsum v]
    rw [fibreVec_finset_sum, ← e.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact fibreVec_lineCoef (hr (e i)) (hl (e i)) (hl0 (e i)) σ (comp (e i) v)
  have hmet : ∀ (σ : K →+* ℂ) (v w : E.carrier),
      (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w) =
        star (embVec σ (ψ v)) ⬝ᵥ (diagMetric d σ *ᵥ embVec σ (ψ w)) := by
    intro σ v w
    rw [← hinnerF, hexp σ v, hexp σ w, sum_inner]
    simp only [inner_sum, inner_smul_left, inner_smul_right]
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [hdi]
      simp only [diagMetric, mulVec_diagonal, embVec, Pi.star_apply, starRingEnd_apply]
      ring
    · intro j _ hji
      rw [hinnerF, ho σ (e i) (e j) (e.injective.ne (Ne.symm hji)) _ (hl _) _ (hl _), mul_zero,
        mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  exact ⟨n, e, a, d, ψ, ha, hd, hc, hinj, hrange, hfin, hlines, hmet⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
