import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainTensorComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormaliseAtSmoothPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountKernelNonzero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDominatingVarietyPointNoTrBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFractionRingOfIsLocModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFractionRingOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceWeightedOverPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace GlobalTheory.LocalHeart

theorem closure_rep {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (ι : A →+* C)
    (j : B →+* C) {x : C} (hx : x ∈ Subring.closure (Set.range ι ∪ Set.range j)) :
    ∃ (l : ℕ) (a : Fin l → A) (b : Fin l → B), x = ∑ q, ι (a q) * j (b q) := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact ⟨1, fun _ => a, fun _ => 1, by simp⟩
    · exact ⟨1, fun _ => 1, fun _ => b, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | one => exact ⟨1, fun _ => 1, fun _ => 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨l, a, b, rfl⟩ := hx
    obtain ⟨l', a', b', rfl⟩ := hy
    exact ⟨l + l', Fin.append a a', Fin.append b b', by simp [Fin.sum_univ_add]⟩
  | neg x _ hx =>
    obtain ⟨l, a, b, rfl⟩ := hx
    exact ⟨l, fun q => -a q, b, by simp [Finset.sum_neg_distrib]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, a, b, rfl⟩ := hx
    obtain ⟨l', a', b', rfl⟩ := hy
    refine ⟨l * l', fun q => a (finProdFinEquiv.symm q).1 * a' (finProdFinEquiv.symm q).2,
      fun q => b (finProdFinEquiv.symm q).1 * b' (finProdFinEquiv.symm q).2, ?_⟩
    rw [← finProdFinEquiv.sum_comp]
    simp only [Equiv.symm_apply_apply]
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [map_mul]
    ring

theorem ordQ_mapDomain {K' K'' : Type} [Field K'] (c : ℂ →+* K') (V : Place c) (f : K'' → K')
    (φ : K'' →₀ ℚ) : V.ordQ (Finsupp.mapDomain f φ) = ∑ g ∈ φ.support, φ g * (V.ord (f g) : ℚ) := by
  rw [Place.ordQ, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply, Finsupp.sum]
  simp [smul_eq_mul]

theorem mem_ring_of_ord {K' : Type} [Field K'] {c : ℂ →+* K'} (V : Place c) {f : K'}
    (h : f ≠ 0 → V.ord f = 0) : f ∈ V.ring := by
  by_cases hf : f = 0
  · rw [hf]; exact V.ring.zero_mem
  · exact (V.ord_nonneg_iff hf).1 (h hf).ge

theorem not_klt_at_points : GlobalTheory.Published.Principalisation →
  ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ] (n k c l M : ℕ) (R : Fin c → Subring K)
    (π : ∀ i, R i →+* κ) (w : ∀ i, Fin l → R i) (lam : Fin c → κ) (wb : Fin l → κ),
  (∃ x : Fin n → K, TrBasis (algebraMap ℂ K) x) → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) → 1 ≤ k →
  (∀ i, IsLocModel (algebraMap ℂ K) (R i) ∧ IsIntegrallyClosed (R i) ∧ RatRes (algebraMap ℂ K) (R i)) →
  (∀ i a (h : algebraMap ℂ K a ∈ R i), π i ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ i (f : κ), ∃ a b : R i, π i b ≠ 0 ∧ f * π i b = π i a) →
  (∀ i, IsLocModel (algebraMap ℂ κ) (π i).range ∧ RatRes (algebraMap ℂ κ) (π i).range) →
  (∀ i, lam i ≠ 0 ∧ ∀ j, π i (w i j) = lam i * wb j) →
  c * (M + k - 1).choose k < l → 1 ≤ M →
  ∃ a : Fin l → ℂ, a ≠ 0 ∧ ∀ (i : Fin c) (xi : Fin n → R i) (φ : R i →₀ ℚ) (u s : R i) (t : ℚ),
    TrBasis (algebraMap ℂ K) (fun j => (xi j : K)) → (∀ g ∈ φ.support, g ≠ 0) →
    EffAt (algebraMap ℂ K) n (R i) (dForm (algebraMap ℂ K) (fun j => (xi j : K)))
      (Finsupp.mapDomain (fun g : R i => (g : K)) φ) →
    π i u = 0 → 0 ≤ t → (s : K) = ∑ j, algebraMap ℂ K (a j) * (w i j : K) + u → (s : K) ≠ 0 →
    ((Function.Injective (π i) ∧ (k : ℚ) ≤ t * M) ∨
      ∃ E : Place (algebraMap ℂ K), E.Contains (R i) ∧ (∀ r : R i, (r : K) ≠ 0 → (π i r = 0 ↔ 0 < E.ord r)) ∧
        (k : ℚ) + M * (E.disc (dForm (algebraMap ℂ K) (fun j => (xi j : K)))
          (Finsupp.mapDomain (fun g : R i => (g : K)) φ) + 1) ≤ t * M) →
    ¬ Klt (algebraMap ℂ K) n (R i) (dForm (algebraMap ℂ K) (fun j => (xi j : K)))
      (Finsupp.mapDomain (fun g : R i => (g : K)) φ + Finsupp.single (s : K) t) := by
  intro hP K κ _ _ _ _ n k c l M R π w lam wb hxK hzκ hk hR hπc hπf hπO hw hl hM
  obtain ⟨z, hz⟩ := hzκ
  obtain ⟨κ', _, _, ρ, O', hO', hO'r, hdom, k', z', hz'⟩ :=
    GlobalTheory.CommonPoint.exists_common_field c (fun i => (π i).range) (fun i => hπO i) ⟨k, z, hz⟩
  obtain ⟨b, hb0, hbM⟩ := GlobalTheory.count_kernel_nonzero k c M l ρ wb ⟨z, hz⟩ hl
  obtain ⟨B, hB, r, τ, hBr, hBO, hmax, het, hτ, j₀, hj₀, hbB⟩ := GlobalTheory.SmoothNormalise.normalise_at_smooth_point O' l b hO' hO'r hb0
  choose a ha using fun j => hBr _ (hbB j)
  have ha0 : a ≠ 0 := by
    intro h
    have h1 := ha j₀
    rw [h, div_self hj₀] at h1
    simp only [Pi.zero_apply, map_zero, sub_zero] at h1
    exact not_nonUnit_one B h1
  refine ⟨a, ha0, ?_⟩
  intro i xi φ u s t hxi hφ hEff hu ht hs hs0 hcase hKlt
  haveI := GlobalTheory.TensorFields.isDomain_tensor_complex K κ'
  obtain ⟨T, ι, ψ, jB, hT, hι, hj, hψj, hTfrac⟩ := GlobalTheory.FieldPair.TensorTower.exists_isEtTower_tensor (L := FractionRing (K ⊗[ℂ] κ'))
    (R i) B hB r τ (hR i).1 (hR i).2.1 (hR i).2.2 hBr hmax het
  let β : Fin l → B := fun j => ⟨b j / b j₀, hbB j⟩
  have hψβ : ∀ j, ((ψ (jB (β j)) : R i) : K) = algebraMap ℂ K (a j) := fun j => hψj _ _ (ha j)
  let σ : T := ∑ j, ι (w i j) * jB (β j) + ι u
  have hψσ : ψ σ = s := by
    apply Subtype.ext
    rw [hs]
    simp only [σ, map_add, map_sum, map_mul, hT.retr]
    push_cast
    simp_rw [hψβ, mul_comm]

  have hσ0 : ψ σ ≠ 0 := by
    rw [hψσ]; intro h; exact hs0 (by simp [h])
  have hKT := GlobalTheory.FieldPair.klt_of_isEtTower hP (algebraMap ℂ K) (algebraMap ℂ (FractionRing (K ⊗[ℂ] κ'))) n r (R i) T ι ψ
    (fun q => jB (τ q)) xi φ (Finsupp.single σ t) hT hxi hφ
    (fun g hg => by
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg), Finsupp.single_eq_same]
      exact ⟨hσ0, ht⟩)
    hEff (by rwa [Finsupp.mapDomain_single, hψσ])
  have hV : ∃ V : Place (algebraMap ℂ (FractionRing (K ⊗[ℂ] κ'))),
      (∀ r : R i, algebraMap (K ⊗[ℂ] κ') (FractionRing (K ⊗[ℂ] κ')) ((r : K) ⊗ₜ 1) ∈ V.ring) ∧
      (∀ b : κ', b ≠ 0 → V.ord (algebraMap (K ⊗[ℂ] κ') (FractionRing (K ⊗[ℂ] κ')) (1 ⊗ₜ b)) = 0) ∧
      (∀ (l : ℕ) (a : Fin l → R i) (b : Fin l → κ'), ∑ q, ρ i (π i (a q)) * b q ≠ 0 →
        ∑ q, algebraMap (K ⊗[ℂ] κ') (FractionRing (K ⊗[ℂ] κ')) ((a q : K) ⊗ₜ b q) ≠ 0 ∧
        V.ord (∑ q, algebraMap (K ⊗[ℂ] κ') (FractionRing (K ⊗[ℂ] κ')) ((a q : K) ⊗ₜ b q)) = 0) ∧
      (∀ (l : ℕ) (a : Fin l → R i) (b : Fin l → κ'),
        ∑ q, algebraMap (K ⊗[ℂ] κ') (FractionRing (K ⊗[ℂ] κ')) ((a q : K) ⊗ₜ b q) ≠ 0 →
        ∑ q, π i (a q) ⊗ₜ[ℂ] b q ∈ (RingHom.ker (Algebra.TensorProduct.productMap (ρ i) (AlgHom.id ℂ κ'))) ^ M →
        (M : ℤ) ≤ V.ord (∑ q, algebraMap (K ⊗[ℂ] κ') (FractionRing (K ⊗[ℂ] κ')) ((a q : K) ⊗ₜ b q))) ∧
      ((V.formOrd (dForm (algebraMap ℂ (FractionRing (K ⊗[ℂ] κ')))
          (Fin.append (fun q => algebraMap (K ⊗[ℂ] κ') (FractionRing (K ⊗[ℂ] κ')) (1 ⊗ₜ (τ q : κ')))
            (fun q => algebraMap (K ⊗[ℂ] κ') (FractionRing (K ⊗[ℂ] κ')) ((xi q : K) ⊗ₜ 1)))) : ℚ) + 1 -
        V.ordQ (Finsupp.mapDomain
          (fun g : R i => algebraMap (K ⊗[ℂ] κ') (FractionRing (K ⊗[ℂ] κ')) ((g : K) ⊗ₜ 1)) φ) ≤ t * M) := by
    have hfr : ∀ g : K, ∃ a b : R i, (b : K) ≠ 0 ∧ g * b = a := fun g => by
      obtain ⟨a', ha', b', hb', hb0', e⟩ := (hR i).1.frac g
      exact ⟨⟨a', ha'⟩, ⟨b', hb'⟩, hb0', e⟩
    rcases hcase with ⟨hinj, htM⟩ | ⟨E, hEc, hEπ, hEd⟩
    · obtain ⟨V, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.FieldPair.GraphPlace.exists_place (L := FractionRing (K ⊗[ℂ] κ')) n k r
        (fun q => (xi q : K)) (fun q => (τ q : κ')) (R i) (π i) (ρ i) hxi hτ ⟨O', hO'⟩ ⟨z, hz⟩ (hπc i) (hπf i)
        (hR i).1 hinj hfr M hk hM
      refine ⟨V, fun r => h1 r, h2, h4, h5, ?_⟩
      rw [ordQ_mapDomain, Finset.sum_eq_zero (fun g hg => by
        rw [h3 _ (fun h => hφ g hg (Subtype.ext h))]; simp)]
      have h6' := (Int.cast_le (R := ℚ)).2 h6
      push_cast at h6'
      have : (k : ℚ) ≤ t * M := htM
      linarith
    · obtain ⟨V, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.FieldPair.exists_place_weighted_over_place (L := FractionRing (K ⊗[ℂ] κ')) n k r
        (fun q => (xi q : K)) (fun q => (τ q : κ')) (R i) (π i) (ρ i) hxi hτ ⟨O', hO'⟩ ⟨z, hz⟩ (hπc i)
        (hR i).1.const_mem (hπf i) E hEc hEπ M hk hM
      refine ⟨V, h1, h2, h4, h5, ?_⟩
      have hq : V.ordQ (Finsupp.mapDomain
          (fun g : R i => algebraMap (K ⊗[ℂ] κ') (FractionRing (K ⊗[ℂ] κ')) ((g : K) ⊗ₜ 1)) φ) =
          M * E.ordQ (Finsupp.mapDomain (fun g : R i => (g : K)) φ) := by
        rw [ordQ_mapDomain, ordQ_mapDomain, Finset.mul_sum]
        refine Finset.sum_congr rfl fun g hg => ?_
        rw [h3 _ (fun h => hφ g hg (Subtype.ext h))]
        push_cast; ring
      rw [hq]
      have h6' := (Int.cast_le (R := ℚ)).2 h6
      push_cast at h6'
      rw [Place.disc] at hEd
      linarith

  obtain ⟨V, h1, h2, h4, h5, h6⟩ := hV
  have hjmem : ∀ bb : B, (jB bb : FractionRing (K ⊗[ℂ] κ')) ∈ V.ring := fun bb =>
    mem_ring_of_ord V (fun hne => by
      rw [hj]
      exact h2 _ (fun h0 => hne (by rw [hj, h0, TensorProduct.tmul_zero, map_zero])))
  have hιmem : ∀ a' : R i, (ι a' : FractionRing (K ⊗[ℂ] κ')) ∈ V.ring := fun a' => by
    rw [hι]; exact h1 a'
  have hsum : ∀ (l' : ℕ) (a' : Fin l' → R i) (b' : Fin l' → B),
      (((∑ q, ι (a' q) * jB (b' q) : T)) : FractionRing (K ⊗[ℂ] κ')) =
        ∑ q, algebraMap (K ⊗[ℂ] κ') (FractionRing (K ⊗[ℂ] κ')) ((a' q : K) ⊗ₜ (b' q : κ')) := by
    intro l' a' b'
    push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hι, hj, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hcl : ∀ x ∈ Subring.closure (Set.range ι ∪ Set.range jB),
      (x : FractionRing (K ⊗[ℂ] κ')) ∈ V.ring := by
    intro x hx
    obtain ⟨l', a', b', rfl⟩ := closure_rep ι jB hx
    push_cast
    exact V.ring.toSubring.sum_mem fun q _ => V.ring.toSubring.mul_mem (hιmem _) (hjmem _)
  have hunit : ∀ x ∈ Subring.closure (Set.range ι ∪ Set.range jB), IsUnit (ψ x) →
      (x : FractionRing (K ⊗[ℂ] κ')) ≠ 0 ∧ V.ord (x : FractionRing (K ⊗[ℂ] κ')) = 0 := by
    intro x hx hux
    obtain ⟨l', a', b', rfl⟩ := closure_rep ι jB hx
    rw [hsum]
    apply h4
    intro hD
    letI := hB.isLocalRing
    choose cc hcc using fun q => hBr _ (b' q).2
    have hψb : ∀ q, ψ (jB (b' q)) = ⟨algebraMap ℂ K (cc q), (hR i).1.const_mem _⟩ :=
      fun q => Subtype.ext (hψj _ _ (hcc q))
    obtain ⟨v, hv⟩ := hux
    have hyv : π i (ψ (∑ q, ι (a' q) * jB (b' q))) = ∑ q, π i (a' q) * algebraMap ℂ κ (cc q) := by
      simp only [map_sum, map_mul, hT.retr, hψb, hπc]
    have hρB : ∀ f ∈ (π i).range, ρ i f ∈ B := fun f hf => (hBO _ ((hdom i) f hf).1).1
    have hu1 : IsUnit (⟨ρ i (π i v), hρB _ ⟨_, rfl⟩⟩ : B) := by
      refine IsUnit.of_mul_eq_one (⟨ρ i (π i ↑v⁻¹), hρB _ ⟨_, rfl⟩⟩ : B) (Subtype.ext ?_)
      show ρ i (π i v) * ρ i (π i ↑v⁻¹) = 1
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    let m : B := ∑ q, ⟨ρ i (π i (a' q)), hρB _ ⟨_, rfl⟩⟩ *
      (b' q - ⟨algebraMap ℂ κ' (cc q), hB.const_mem _⟩)
    have hm : m ∈ IsLocalRing.maximalIdeal B := by
      refine Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ ?_
      exact (IsLocalRing.mem_maximalIdeal _).2 ((nonUnit_iff _).1 (hcc q))
    have he : (⟨ρ i (π i v), hρB _ ⟨_, rfl⟩⟩ : B) = -m := by
      apply Subtype.ext
      have hmc : (m : κ') = ∑ q, ρ i (π i (a' q)) * (b' q : κ') -
          ∑ q, ρ i (π i (a' q)) * algebraMap ℂ κ' (cc q) := by
        simp only [m]
        push_cast
        rw [← Finset.sum_sub_distrib]
        simp_rw [mul_sub]
      rw [Subring.coe_neg, hmc, hD, zero_sub, neg_neg]
      show ρ i (π i v) = _
      rw [hv, hyv, map_sum]
      simp only [map_mul, AlgHom.commutes]
    have hm' : -m ∈ IsLocalRing.maximalIdeal B := neg_mem hm
    rw [← he] at hm'
    exact (IsLocalRing.mem_maximalIdeal _).1 hm' hu1

  have hVT : V.Contains T := by
    intro f hf
    obtain ⟨s1, s2, hs1, hs2, hu2, e⟩ := hTfrac ⟨f, hf⟩
    obtain ⟨hs20, hs2o⟩ := hunit s2 hs2 hu2
    have h1' := hcl s1 hs1
    by_cases hf0 : f = 0
    · rw [hf0]; exact V.ring.zero_mem
    have e' : f * (s2 : FractionRing (K ⊗[ℂ] κ')) = s1 := e
    have hs10 : (s1 : FractionRing (K ⊗[ℂ] κ')) ≠ 0 := by rw [← e']; exact mul_ne_zero hf0 hs20
    have ho := V.ord_mul hf0 hs20
    rw [e', hs2o, add_zero] at ho
    exact (V.ord_nonneg_iff hf0).1 (by rw [← ho]; exact (V.ord_nonneg_iff hs10).2 h1')
  have hKT' : Klt (algebraMap ℂ (FractionRing (K ⊗[ℂ] κ'))) (r + n) T
      (dForm (algebraMap ℂ (FractionRing (K ⊗[ℂ] κ')))
          (Fin.append (fun q => algebraMap (K ⊗[ℂ] κ') (FractionRing (K ⊗[ℂ] κ')) (1 ⊗ₜ (τ q : κ')))
            (fun q => algebraMap (K ⊗[ℂ] κ') (FractionRing (K ⊗[ℂ] κ')) ((xi q : K) ⊗ₜ 1))))
      (Finsupp.mapDomain
          (fun g : R i => algebraMap (K ⊗[ℂ] κ') (FractionRing (K ⊗[ℂ] κ')) ((g : K) ⊗ₜ 1)) φ +
        Finsupp.single (σ : FractionRing (K ⊗[ℂ] κ')) t) := by
    have e1 : (fun q => algebraMap (K ⊗[ℂ] κ') (FractionRing (K ⊗[ℂ] κ')) (1 ⊗ₜ (τ q : κ'))) =
        fun q => ((jB (τ q) : T) : FractionRing (K ⊗[ℂ] κ')) := funext fun q => (hj _).symm
    have e2 : (fun q => algebraMap (K ⊗[ℂ] κ') (FractionRing (K ⊗[ℂ] κ')) ((xi q : K) ⊗ₜ 1)) =
        fun q => ((ι (xi q) : T) : FractionRing (K ⊗[ℂ] κ')) := funext fun q => (hι _).symm
    have e3 : (fun g : R i => algebraMap (K ⊗[ℂ] κ') (FractionRing (K ⊗[ℂ] κ')) ((g : K) ⊗ₜ 1)) =
        fun g => ((ι g : T) : FractionRing (K ⊗[ℂ] κ')) := funext fun g => (hι _).symm
    have h := hKT
    rw [Finsupp.mapDomain_single] at h
    rw [e1, e2, e3]
    exact h
  have hlt := hKT'.lt_disc hVT
  rw [Place.disc, map_add, Place.ordQ_single] at hlt
  have hσL : ((σ : T) : FractionRing (K ⊗[ℂ] κ')) = ∑ q : Fin (l + 1),
      algebraMap (K ⊗[ℂ] κ') (FractionRing (K ⊗[ℂ] κ'))
        ((((Fin.cons u (w i) : Fin (l + 1) → R i) q : R i) : K) ⊗ₜ
          ((Fin.cons 1 (fun j => (β j : κ')) : Fin (l + 1) → κ') q)) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, σ]
    push_cast
    rw [hι u, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hι, hj, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hσne : ((σ : T) : FractionRing (K ⊗[ℂ] κ')) ≠ 0 := fun h => hσ0 (by
    rw [show σ = 0 from Subtype.ext h, map_zero])
  have hker : ∑ q : Fin (l + 1), π i ((Fin.cons u (w i) : Fin (l + 1) → R i) q) ⊗ₜ[ℂ]
      ((Fin.cons 1 (fun j => (β j : κ')) : Fin (l + 1) → κ') q) ∈
      (RingHom.ker (Algebra.TensorProduct.productMap (ρ i) (AlgHom.id ℂ κ'))) ^ M := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, hu, TensorProduct.zero_tmul, zero_add, (hw i).2]
    have hh : ∑ j, (lam i * wb j) ⊗ₜ[ℂ] (β j : κ') = (lam i ⊗ₜ[ℂ] (b j₀)⁻¹) * ∑ j, wb j ⊗ₜ[ℂ] b j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      show (lam i * wb j) ⊗ₜ[ℂ] (b j / b j₀) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, div_eq_inv_mul]
    rw [hh]
    exact Ideal.mul_mem_left _ _ (hbM i)
  have hσM := h5 (l + 1) (Fin.cons u (w i)) (Fin.cons 1 (fun j => (β j : κ')))
    (by rw [← hσL]; exact hσne) hker
  rw [← hσL] at hσM
  have hσM' : (M : ℚ) ≤ (V.ord (σ : FractionRing (K ⊗[ℂ] κ')) : ℚ) := by exact_mod_cast hσM
  have hmul := mul_le_mul_of_nonneg_left hσM' ht
  linarith

end GlobalTheory.LocalHeart
