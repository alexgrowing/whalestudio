import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeDecompSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

namespace KHFreeDecomp

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cellMon_monomial {I : ∀ k, Finset (ι k)} {t : MRingOver S ι} (ht : t ∈ KH.cellMon S I) :
    ∃ u : (Σ k, ι k) →₀ ℕ, t = monomial u 1 ∧ ∀ q ∈ u.support, q.2 ∈ I q.1 := by
  classical
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    refine ⟨Finsupp.single ⟨k, i⟩ 1, rfl, fun q hq => ?_⟩
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hq)]
    exact hi
  | one => exact ⟨0, by rw [← C_1, C_apply], by simp⟩
  | mul f g _ _ hf hg =>
    obtain ⟨u, rfl, hu⟩ := hf
    obtain ⟨v, rfl, hv⟩ := hg
    refine ⟨u + v, by rw [monomial_mul, one_mul], fun q hq => ?_⟩
    rcases Finset.mem_union.mp (Finsupp.support_add hq) with h | h
    · exact hu q h
    · exact hv q h

section Frac

variable {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

def overDen (T : Submonoid (MRingOver S ι)) (t : T) : M →ₗ[S] LocalizedModule T M where
  toFun m := LocalizedModule.mk m t
  map_add' x y := by
    simp only [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_add]
  map_smul' s m := by
    rw [RingHom.id_apply, LocalizedModule.smul'_mk]

theorem overDen_apply (T : Submonoid (MRingOver S ι)) (t : T) (m : M) :
    overDen T t m = LocalizedModule.mk m t := rfl

end Frac

theorem quot_mk_smul (s : S) (p : MRingOver S ι) :
    Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (s • p) = s • Ideal.Quotient.mk ⊥ p := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap]

theorem mk_monomial_eq (I : ∀ k, Finset (ι k)) (u v : (Σ k, ι k) →₀ ℕ) (hu : ∀ q ∈ u.support, q.2 ∈ I q.1)
    (ht : (monomial u (1 : S) : MRingOver S ι) ∈ KH.cellMon S I) :
    LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (monomial v 1)) ⟨monomial u 1, ht⟩ =
      monoFrac S I (fun q => (v q : ℤ) - u q) := by
  classical
  have hneg : ∀ k, negSet (fun q => (v q : ℤ) - u q) k ⊆ I k := by
    intro k i hi
    simp only [negSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hu ⟨k, i⟩ (Finsupp.mem_support_iff.mpr (by omega))
  have hexp : negExp (fun q => (v q : ℤ) - u q) + v = u + posExp (fun q => (v q : ℤ) - u q) := by
    ext q
    simp only [Finsupp.add_apply, posExp, negExp, Finsupp.coe_equivFunOnFinite_symm]
    omega
  rw [monoFrac, dif_pos hneg, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    monomial_mul, mul_one]
  rw [hexp]

theorem locPart_le (I : ∀ k, Finset (ι k)) (c d : K → ℤ) :
    KH.locPart ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) (KH.cellMon S I) c ≤
      Submodule.span S (monoFrac S I '' {a | blockSum a = c + d}) := by
  classical
  rcases subsingleton_or_nontrivial S with hS | hS
  · intro x _
    have hx : x = 0 := by rw [← one_smul S x, Subsingleton.elim (1 : S) 0, zero_smul]
    rw [hx]
    exact zero_mem _
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, ⟨t, ht⟩, b, htb, hm, rfl⟩
  obtain ⟨u, rfl, huI⟩ := cellMon_monomial ht
  have hub : ∀ k, ∑ i, u ⟨k, i⟩ = b k := by
    intro k
    refine htb u ?_ k
    rw [support_monomial, if_neg one_ne_zero]
    exact Finset.mem_singleton_self u
  have hle : KH.quotPart S (⊥ : Ideal (MRingOver S ι)) ((c + fun k => (b k : ℤ)) + d) ≤
      (Submodule.span S (monoFrac S I '' {a | blockSum a = c + d})).comap
        (overDen (KH.cellMon S I) ⟨monomial u 1, ht⟩) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, ⟨hpos, hp⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have hsum : p = ∑ v ∈ p.support, coeff v p • (monomial v 1 : MRingOver S ι) := by
      conv_lhs => rw [p.as_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hsum, map_sum, map_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    rw [quot_mk_smul, map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun q => (v q : ℤ) - u q, ?_, ?_⟩)
    · have hv' := hp v hv
      show blockSum _ = c + d
      funext k
      simp only [blockSum, Finset.sum_sub_distrib]
      have h1 : ∑ i, ((v ⟨k, i⟩ : ℕ) : ℤ) = ((((c + fun k => (b k : ℤ)) + d) k).toNat : ℤ) := by
        exact_mod_cast hv' k
      have h2 : ∑ i, ((u ⟨k, i⟩ : ℕ) : ℤ) = b k := by exact_mod_cast hub k
      have h3 := hpos k
      simp only [Pi.add_apply] at h1 h3 ⊢
      omega
    · rw [overDen_apply, mk_monomial_eq I u v huI ht]
  exact hle hm

theorem embed_apply_cell [LinearOrder K] [∀ k, LinearOrder (ι k)] (a : (Σ k, ι k) → ℤ) (n : ℕ)
    (F : KH.Cell K ι n → S) (I : KH.Cell K ι n) :
    embed S a n (fun J => F J.1) I = F I • monoFrac S I.1 a := by
  classical
  unfold embed
  rw [LinearMap.pi_apply]
  split_ifs with h
  · rfl
  · rw [LinearMap.zero_apply, monoFrac, dif_neg h, smul_zero]

end KHFreeDecomp

open KHFreeDecomp in

theorem KHFreeDecomp.full : KHFreeDecomp.Statement := by
  intro S _ K _ _ ι _ _ c d n φ hφ
  classical
  have hI : ∀ I : KH.Cell K ι n, ∃ l : ((Σ k, ι k) → ℤ) →₀ S,
      l ∈ Finsupp.supported S S {a | blockSum a = c + d} ∧
        Finsupp.linearCombination S (monoFrac S I.1) l = φ I := by
    intro I
    have hx : φ I ∈ KH.locPart ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d))
        (KH.cellMon S I.1) c := hφ I (Set.mem_univ _)
    exact (Finsupp.mem_span_image_iff_linearCombination S).mp (locPart_le I.1 c d hx)
  choose l hl hlφ using hI
  let _ : Fintype (KH.Cell K ι n) := by unfold KH.Cell; infer_instance
  refine ⟨Finset.univ.biUnion fun I => (l I).support, fun a J => l J.1 a, ?_, ?_⟩
  · intro a ha
    obtain ⟨I, -, haI⟩ := Finset.mem_biUnion.mp ha
    exact hl I haI
  · funext I
    rw [Finset.sum_apply, ← hlφ I, Finsupp.linearCombination_apply, Finsupp.sum]
    beta_reduce
    refine (Finset.sum_subset (s₁ := (l I).support) (s₂ := Finset.univ.biUnion fun I => (l I).support)
      (f := fun a => l I a • monoFrac S I.1 a) (fun a ha => Finset.mem_biUnion.mpr ⟨I, Finset.mem_univ _, ha⟩) ?_).trans
      (Finset.sum_congr rfl fun a _ => (embed_apply_cell a n (fun J => l J a) I).symm)
    intro a _ ha
    rw [Finsupp.mem_support_iff, not_not] at ha
    rw [ha, zero_smul]

end

end GroundTheory.Heights₂.Heights.Kleiman
