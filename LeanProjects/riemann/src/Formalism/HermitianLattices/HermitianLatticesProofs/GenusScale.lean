import Mathlib
import Formalism.HermitianLattices.DefsCS
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic

open NumberField

noncomputable section

namespace Formalism.HermitianLatticesTheory

section SlopeTestRemainingChoices

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem genusScale_span (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (c : K) (s : Set V)
    (hs : ∀ a ∈ s, ∀ b ∈ s, c * h a b ∈ (1 : Submodule R K)) :
    ∀ x ∈ Submodule.span R s, ∀ y ∈ Submodule.span R s, c * h x y ∈ (1 : Submodule R K) := by
  have key : ∀ a ∈ s, ∀ y ∈ Submodule.span R s, c * h a y ∈ (1 : Submodule R K) := by
    intro a ha y hy
    induction hy using Submodule.span_induction with
    | mem b hb => exact hs a ha b hb
    | zero => simp
    | add u w _ _ hu hw =>
        rw [map_add, mul_add]
        exact add_mem hu hw
    | smul r u _ hu =>
        rw [genusBasic_hsmul_right, mul_left_comm]
        exact genusBasic_mem_one_mul _ hu r
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem a ha => exact key a ha y hy
  | zero => simp
  | add u w _ _ hu hw =>
      rw [map_add, LinearMap.add_apply, mul_add]
      exact add_mem hu hw
  | smul r u _ hu =>
      rw [genusBasic_hsmul_left hinj hstar, mul_left_comm]
      exact genusBasic_mem_one_mul _ hu _

theorem genusScale_transfer (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (c : K) (L M : Submodule R V) (hLM : SameGenus h L M)
    (hL : ∀ x ∈ L, ∀ y ∈ L, c * h x y ∈ (1 : Submodule R K)) :
    ∀ x ∈ M, ∀ y ∈ M, c * h x y ∈ (1 : Submodule R K) := by
  intro x hx y hy
  refine genusBasic_lg (K := K) (1 : Submodule R K) (c * h x y) ?_
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  have hxM : x ∈ loc (K := K) p M := locBasic_le_locS (hcompl (K := K) p) M hx
  have hyM : y ∈ loc (K := K) p M := locBasic_le_locS (hcompl (K := K) p) M hy
  rw [← hgL, isomAct_mem_gmap] at hxM hyM
  obtain ⟨s, hsS, hsx⟩ := locBasic_mem_locS.mp hxM
  obtain ⟨t, htS, hty⟩ := locBasic_mem_locS.mp hyM
  have hg' : ∀ u v : V, h (g u) (g v) = h u v := hg
  have hiso : h (g.symm x) (g.symm y) = h x y := by
    have e := hg' (g.symm x) (g.symm y)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e
    exact e.symm
  have h1 := hL _ hsx _ hty
  rw [genusBasic_hsmul_left hinj hstar, genusBasic_hsmul_right, hiso] at h1
  refine locBasic_mem_locS.mpr ⟨locBasic_sigma hinj hstar s * t,
    (hcompl (K := K) p).mul_mem (genusBasic_sigma_mem hinj hstar p s hsS) htS, ?_⟩
  have e : (locBasic_sigma hinj hstar s * t) • (c * h x y) =
      c * (algebraMap R K (locBasic_sigma hinj hstar s) * (algebraMap R K t * h x y)) := by
    rw [Algebra.smul_def, map_mul]
    ring
  rw [e]
  exact h1

end SlopeTestRemainingChoices

private theorem exists_nat_pos_mul_mem_one {K : Type} [Field K] [NumberField K] (z : K) :
    ∃ n : ℕ, 0 < n ∧ (n : K) * z ∈ (1 : Submodule (𝓞 K) K) := by
  have hz : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsIntegral.isIntegral (R := ℚ) z).isAlgebraic
  obtain ⟨y, hy0, hy⟩ := hz.exists_integral_multiple
  have hw : IsIntegral ℤ ((y.natAbs : K) * z) := by
    rcases Int.natAbs_eq y with e | e
    · rw [← Int.cast_natCast, ← e, ← zsmul_eq_mul]
      exact hy
    · have e' : (y.natAbs : ℤ) = -y := by linarith
      rw [← Int.cast_natCast, e', Int.cast_neg, neg_mul, ← zsmul_eq_mul]
      exact hy.neg
  exact ⟨y.natAbs, Int.natAbs_pos.mpr hy0, Submodule.mem_one.mpr ⟨⟨_, hw⟩, rfl⟩⟩

theorem genusScale : GenusScale := by
  intro K V _ _ _ _ _ _ _ _ h _ L hL
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective _ _
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) := by
    intro r
    have hr : IsIntegral ℤ (algebraMap (𝓞 K) K r) := NumberField.RingOfIntegers.isIntegral_coe r
    exact ⟨⟨star (algebraMap (𝓞 K) K r), hr.map (starRingEnd K).toIntAlgHom⟩, rfl⟩
  obtain ⟨s, hs⟩ := hL.fg
  choose n hn0 hn using exists_nat_pos_mul_mem_one (K := K)
  refine ⟨∏ q ∈ s ×ˢ s, n (h q.1 q.2), Finset.prod_pos (fun q _ => hn0 _), ?_⟩
  have hLd : ∀ x ∈ L, ∀ y ∈ L,
      ((∏ q ∈ s ×ˢ s, n (h q.1 q.2) : ℕ) : K) * h x y ∈ (1 : Submodule (𝓞 K) K) := by
    rw [← hs]
    refine genusScale_span hinj hstar h _ _ ?_
    intro a ha b hb
    have hmem : (a, b) ∈ s ×ˢ s := Finset.mem_product.mpr ⟨ha, hb⟩
    obtain ⟨k, hk⟩ : n (h a b) ∣ ∏ q ∈ s ×ˢ s, n (h q.1 q.2) :=
      Finset.dvd_prod_of_mem (fun q : V × V => n (h q.1 q.2)) hmem
    rw [hk, Nat.cast_mul, mul_comm ((n (h a b) : ℕ) : K), mul_assoc]
    have hm := genusBasic_mem_one_mul _ (hn (h a b)) (k : 𝓞 K)
    rwa [map_natCast] at hm
  intro M hM x hx y hy
  have hM' : Submodule.IsLattice K M ∧ SameGenus h L M := hM
  exact genusScale_transfer hinj hstar h _ L M hM'.2 hLd x hx y hy

end Formalism.HermitianLatticesTheory
