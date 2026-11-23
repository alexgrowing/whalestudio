import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem tyFn_mul_of_mem {M : Type} [Group M] (J : Subgroup M) (ψ : J →* ℂˣ) (a b : M)
    (ha : a ∈ J) : tyFn J ψ a * tyFn J ψ b = tyFn J ψ (a * b) := by
  unfold tyFn
  by_cases hb : b ∈ J
  · have hab : a * b ∈ J := J.mul_mem ha hb
    rw [dif_pos ha, dif_pos hb, dif_pos hab]
    have e : (⟨a * b, hab⟩ : J) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, map_mul, mul_inv, Units.val_mul, mul_comm]
  · have hab : a * b ∉ J := fun h => hb (by simpa using J.mul_mem (J.inv_mem ha) h)
    rw [dif_neg hb, dif_neg hab, mul_zero]

private theorem mem_doubleCoset_loc_mul_of_mem_of_pr_eq_one {X M' : Type} [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X)
    (Kw : Subgroup M') (hF : L'.Fact K Kw)
    (hC : ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔
      L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧
        (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K)
    (t : M') (r g y : X) (hr : L'.pr r = 1) (hy : y ∈ DoubleCoset.doubleCoset r (K : Set X) K)
    (hz : y⁻¹ * g ∈ DoubleCoset.doubleCoset (L'.loc t) (K : Set X) K) :
    g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ∧
      y⁻¹ * ((L'.loc (L'.pr g))⁻¹ * g) ∈ K := by
  obtain ⟨hn, hk⟩ := (hC t 1 (map_one _) (y⁻¹ * g)).1 (by rw [mul_one]; exact hz)
  obtain ⟨ha, hy'⟩ := (hC 1 r hr y).1 (by rw [map_one, one_mul]; exact hy)
  have haK : L'.pr y ∈ Kw := by
    obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 ha
    rw [e, mul_one]
    exact Kw.mul_mem hu hv
  have hkK : (L'.loc (L'.pr (y⁻¹ * g)))⁻¹ * (y⁻¹ * g) ∈ K := by
    obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hk
    rw [e, mul_one]
    exact K.mul_mem hu hv
  generalize hkd : (L'.loc (L'.pr (y⁻¹ * g)))⁻¹ * (y⁻¹ * g) = k at hkK
  generalize hyd : (L'.loc (L'.pr y))⁻¹ * y = y' at hy'
  have hm : L'.pr g = L'.pr y * L'.pr (y⁻¹ * g) := by simp
  generalize had : L'.pr y = a at haK hm hyd
  generalize hnd : L'.pr (y⁻¹ * g) = n at hn hm hkd
  have hpy' : L'.pr y' = 1 := by
    rw [← hyd, map_mul, map_inv, L'.pr_loc, had, inv_mul_cancel]
  have hcomm : ∀ x, L'.loc x * y' = y' * L'.loc x := fun x => L'.comm x y' hpy'
  have hy1 : y = L'.loc a * y' := by rw [← hyd]; group
  have hg : g = L'.loc a * y' * (L'.loc n * k) := by
    rw [← hkd, ← hy1]; group
  have hy0 : (L'.loc (L'.pr g))⁻¹ * g = y' * k := by
    rw [hm, map_mul, hg, mul_assoc (L'.loc a), ← mul_assoc y', ← hcomm n]
    group
  refine ⟨(hC t r hr g).2 ⟨?_, ?_⟩, ?_⟩
  · rw [hm]
    obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hn
    exact DoubleCoset.mem_doubleCoset.2 ⟨a * u, Kw.mul_mem haK hu, v, hv, by rw [e]; group⟩
  · rw [hy0]
    obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hy'
    exact DoubleCoset.mem_doubleCoset.2 ⟨u, hu, v * k, K.mul_mem hv hkK, by rw [e]; group⟩
  · rw [hy0]
    have e : y⁻¹ * (y' * k) = (L'.loc a)⁻¹ * k := by
      calc y⁻¹ * (y' * k) = y'⁻¹ * ((L'.loc a)⁻¹ * y') * k := by rw [hy1]; group
        _ = y'⁻¹ * (y' * (L'.loc a)⁻¹) * k := by rw [← map_inv, hcomm]
        _ = (L'.loc a)⁻¹ * k := by group
    rw [e]
    exact K.mul_mem (K.inv_mem (hF.1 a haK)) hkK

private theorem mem_doubleCosets_of_dosetInd_mul_ne_zero {X : Type} [Group X] (K : Subgroup X) (a b : ℂ) (r s x g : X)
    (h : a * dosetInd ℂ K r x * (b * dosetInd ℂ K s (x⁻¹ * g)) ≠ 0) :
    x ∈ DoubleCoset.doubleCoset r (K : Set X) K ∧
      x⁻¹ * g ∈ DoubleCoset.doubleCoset s (K : Set X) K := by
  constructor
  · by_contra hn
    apply h
    simp [dosetInd, Set.indicator_apply, hn]
  · by_contra hn
    apply h
    simp [dosetInd, Set.indicator_apply, hn]

theorem UpperTheory.Gal.W2.Seed.pTfMulR :
    (∀ (X V : Type) [Group X] [AddCommGroup V] [Module ℂ V] (K K₀ : Subgroup X), K₀ ≤ K → K₀.relIndex K ≠ 0 → ∀ Ψ : X → V, (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ x : X ⧸ K₀, Ψ x.out = ((K₀.relIndex K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ K, Ψ y.out) → TfAdm → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔ L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧ (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K) → TfMulR := by
  intro hA hAdm hC X M M' _ _ _ T L' Kw hF hAp t r hr hr'
  funext g
  have hloc : T.L.pr (L'.loc t) = 1 := hAp.1 t
  have hinv : ∀ k ∈ T.K, ∀ x : X,
      T.tf r (x * k) * T.tf (L'.loc t) ((x * k)⁻¹ * g) = T.tf r x * T.tf (L'.loc t) (x⁻¹ * g) := by
    intro k hk x
    have h1 := ((hAdm X M T r hr).2 k hk x).2
    have h2 := ((hAdm X M T (L'.loc t) hloc).2 k⁻¹ (T.K.inv_mem hk) (x⁻¹ * g)).1
    rw [show (x * k)⁻¹ * g = k⁻¹ * (x⁻¹ * g) by group, h1, h2]
    generalize_proofs p1 p2
    have e : (⟨T.L.pr k⁻¹, p2⟩ : T.J) = (⟨T.L.pr k, p1⟩ : T.J)⁻¹ := Subtype.ext (map_inv _ _)
    rw [e, map_inv, inv_inv]
    have hu := Units.inv_mul (T.ψ ⟨T.L.pr k, p1⟩)
    linear_combination (T.tf r x * T.tf (L'.loc t) (x⁻¹ * g)) * hu
  have hsum := hA X ℂ T.K T.K₀ T.le T.idx (fun x => T.tf r x * T.tf (L'.loc t) (x⁻¹ * g)) hinv
  beta_reduce at hsum
  unfold conv
  rw [hsum]
  have hc : ((T.K₀.relIndex T.K : ℕ) : ℂ) ≠ 0 := by exact_mod_cast T.idx
  by_cases hg : g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (T.K : Set X) T.K
  · obtain ⟨hm, hy0⟩ := (hC X M' L' T.K Kw hF t r hr' g).1 hg
    obtain ⟨y₀, hy0d⟩ : ∃ y₀, y₀ = (L'.loc (L'.pr g))⁻¹ * g := ⟨_, rfl⟩
    rw [← hy0d] at hy0
    have hp0 : L'.pr y₀ = 1 := by rw [hy0d, map_mul, map_inv, L'.pr_loc, inv_mul_cancel]
    have hcomm : L'.loc (L'.pr g) * y₀ = y₀ * L'.loc (L'.pr g) := L'.comm _ _ hp0
    have hg0 : g = L'.loc (L'.pr g) * y₀ := by rw [hy0d]; group
    have hz0 : y₀⁻¹ * g = L'.loc (L'.pr g) := by
      calc y₀⁻¹ * g = y₀⁻¹ * (L'.loc (L'.pr g) * y₀) := by rw [← hg0]
        _ = L'.loc (L'.pr g) := by rw [hcomm]; group
    have hzK : y₀⁻¹ * g ∈ DoubleCoset.doubleCoset (L'.loc t) (T.K : Set X) T.K := by
      rw [hz0]
      obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hm
      exact DoubleCoset.mem_doubleCoset.2
        ⟨L'.loc u, hF.1 u hu, L'.loc v, hF.1 v hv, by rw [e, map_mul, map_mul]⟩
    have hJ : T.L.pr y₀ ∈ T.J := by
      obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hy0
      rw [e, map_mul, map_mul, hr, mul_one]
      exact T.J.mul_mem (T.fact.2 u hu) (T.fact.2 v hv)
    rw [finsum_eq_single _ (QuotientGroup.mk y₀ : X ⧸ T.K)]
    · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul T.K y₀
      rw [hk, hinv k k.2 y₀]
      have hτ := tyFn_mul_of_mem T.J T.ψ _ (T.L.pr (y₀⁻¹ * g)) hJ
      rw [← map_mul, mul_inv_cancel_left] at hτ
      simp only [TyLev.tf, dosetInd, Set.indicator_of_mem hy0, Set.indicator_of_mem hzK,
        Set.indicator_of_mem hg, Pi.one_apply]
      rw [smul_eq_mul, ← hτ]
      field_simp
    · intro q hq
      by_contra hne
      apply hq
      simp only [TyLev.tf] at hne
      have hm1 := mem_doubleCosets_of_dosetInd_mul_ne_zero T.K _ _ r (L'.loc t) q.out g hne
      have hK := (mem_doubleCoset_loc_mul_of_mem_of_pr_eq_one L' T.K Kw hF (hC X M' L' T.K Kw hF) t r g q.out hr' hm1.1 hm1.2).2
      rw [← hy0d] at hK
      have h := (QuotientGroup.eq (s := T.K)).2 hK
      rwa [QuotientGroup.out_eq'] at h
  · rw [finsum_eq_zero_of_forall_eq_zero]
    · simp [TyLev.tf, dosetInd, hg]
    · intro q
      by_contra hne
      apply hg
      simp only [TyLev.tf] at hne
      have hm1 := mem_doubleCosets_of_dosetInd_mul_ne_zero T.K _ _ r (L'.loc t) q.out g hne
      exact (mem_doubleCoset_loc_mul_of_mem_of_pr_eq_one L' T.K Kw hF (hC X M' L' T.K Kw hF) t r g q.out hr' hm1.1 hm1.2).1
