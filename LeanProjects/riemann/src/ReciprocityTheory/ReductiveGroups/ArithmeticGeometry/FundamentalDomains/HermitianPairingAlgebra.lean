import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

namespace HermitianPairingAlgebra

lemma cc_cc (a : E) : cc (cc a) = a := by
  exact IsCMField.complexConj_apply_apply E a

lemma cc_mul (a b : E) : cc (a * b) = cc a * cc b := by
  exact map_mul (IsCMField.complexConj E) a b

lemma cc_add (a b : E) : cc (a + b) = cc a + cc b := by
  exact map_add (IsCMField.complexConj E) a b

lemma cc_zero : cc (0 : E) = 0 := by
  exact map_zero (IsCMField.complexConj E)

lemma cc_sum {ι : Type*} (s : Finset ι) (f : ι → E) : cc (∑ i ∈ s, f i) = ∑ i ∈ s, cc (f i) := by
  exact map_sum (IsCMField.complexConj E) f s

lemma herm_add_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma herm_smul_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (a : E) (x y : Fin r → E) :
    herm G (a • x) y = a * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma herm_sub_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x - x') y = herm G x y - herm G x' y := by
  simp only [herm, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma herm_smul_right {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (a : E) (x y : Fin r → E) :
    herm G x (a • y) = cc a * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, cc_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma herm_symm {r : ℕ} {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a)
    (x y : Fin r → E) : cc (herm G x y) = herm G y x := by
  simp only [herm, cc_sum, cc_mul, cc_cc, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma smul_mem' {r : ℕ} {M : Submodule (𝓞 E) (Fin r → E)} {a : E} (ha : IsIntegral ℤ a)
    {y : Fin r → E} (hy : y ∈ M) : a • y ∈ M := by
  convert M.smul_mem (⟨a, ha⟩ : 𝓞 E) hy using 1
  rw [← algebraMap_smul E]
  rfl

noncomputable def pairL {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (ξ : Fin r → E) :
    (Fin r → E) →ₗ[𝓞 E] E where
  toFun y := herm G y ξ
  map_add' x y := herm_add_left G x y ξ
  map_smul' a y := by
    simp only [RingHom.id_apply]
    rw [← algebraMap_smul E a y, herm_smul_left, Algebra.smul_def]

lemma pairL_apply {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (ξ y : Fin r → E) :
    pairL G ξ y = herm G y ξ := rfl

end HermitianPairingAlgebra

open HermitianPairingAlgebra in
theorem hermitian_lattice_pairing_duality : PerpQuotientSelfDual (E := E) := by
  intro r X ξ _ x _ hx
  have hsym : ∀ u v, cc (herm X.Gm u v) = herm X.Gm v u := fun u v => herm_symm X.Gm_herm u v
  have hintcc : ∀ a : E, IsIntegral ℤ a → IsIntegral ℤ (cc a) := fun a ha =>
    ha.map (IsCMField.complexConj E).toAlgHom.toRingHom.toIntAlgHom
  suffices hP : ∃ c : E, ∀ y ∈ X.L', IsIntegral ℤ (herm X.Gm y x - c * herm X.Gm y ξ) by
    obtain ⟨c, hc⟩ := hP
    refine ⟨-cc c, X.L'_dual _ fun y hy => ?_⟩
    have h := hintcc _ (hc y hy)
    have e : cc (herm X.Gm y x - c * herm X.Gm y ξ) = herm X.Gm (x + (-cc c) • ξ) y := by
      rw [herm_add_left, herm_smul_left, ← hsym y x, ← hsym y ξ]
      simp only [cc, map_sub, map_mul, map_neg]
      ring
    rwa [e] at h
  by_cases hI : X.L'.map (pairL X.Gm ξ) = ⊥
  · refine ⟨0, fun y hy => ?_⟩
    have hy0 : herm X.Gm y ξ = 0 := by
      have hm : pairL X.Gm ξ y ∈ X.L'.map (pairL X.Gm ξ) := Submodule.mem_map_of_mem hy
      rw [hI, Submodule.mem_bot, pairL_apply] at hm
      exact hm
    rw [zero_mul, sub_zero, ← hsym x y]
    exact hintcc _ (hx y hy hy0)
  · let J : FractionalIdeal (𝓞 E)⁰ E :=
      ⟨X.L'.map (pairL X.Gm ξ), FractionalIdeal.isFractional_of_fg (X.L'_fg.map _)⟩
    have hJc : (J : Submodule (𝓞 E) E) = X.L'.map (pairL X.Gm ξ) := rfl
    have hJ0 : J ≠ 0 := by
      intro h
      apply hI
      rw [← hJc, h, FractionalIdeal.coe_zero]
    have h1 : (1 : E) ∈ (J : Submodule (𝓞 E) E) * ((J⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
      rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJ0]
      exact FractionalIdeal.one_mem_one _
    have key := Submodule.mul_induction_on
      (C := fun w => ∃ c : E, ∀ y ∈ X.L', IsIntegral ℤ (w * herm X.Gm y x - c * herm X.Gm y ξ)) h1
      (fun t ht u hu => by
        rw [hJc] at ht
        obtain ⟨yt, hyt, rfl⟩ := Submodule.mem_map.mp ht
        have hu' := (FractionalIdeal.mem_inv_iff hJ0).mp hu
        have hint : ∀ y ∈ X.L', IsIntegral ℤ (u * herm X.Gm y ξ) := fun y hy => by
          have hs : herm X.Gm y ξ ∈ J := by
            rw [← FractionalIdeal.mem_coe, hJc, ← pairL_apply]
            exact Submodule.mem_map_of_mem hy
          obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp (hu' _ hs)
          rw [← ha]
          exact a.isIntegral_coe
        refine ⟨u * herm X.Gm yt x, fun y hy => ?_⟩
        have hb := hint yt hyt
        have ha := hint y hy
        have hmem : (u * herm X.Gm yt ξ) • y - (u * herm X.Gm y ξ) • yt ∈ X.L' :=
          X.L'.sub_mem (smul_mem' hb hy) (smul_mem' ha hyt)
        have hz : herm X.Gm ((u * herm X.Gm yt ξ) • y - (u * herm X.Gm y ξ) • yt) ξ = 0 := by
          rw [herm_sub_left, herm_smul_left, herm_smul_left]
          ring
        have h2 := hintcc _ (hx _ hmem hz)
        rw [hsym, herm_sub_left, herm_smul_left, herm_smul_left] at h2
        rw [pairL_apply]
        convert h2 using 1
        ring)
      (fun w1 w2 ⟨c1, h1⟩ ⟨c2, h2⟩ => ⟨c1 + c2, fun y hy => by
        have h3 := (h1 y hy).add (h2 y hy)
        have e : (w1 + w2) * herm X.Gm y x - (c1 + c2) * herm X.Gm y ξ =
            (w1 * herm X.Gm y x - c1 * herm X.Gm y ξ) + (w2 * herm X.Gm y x - c2 * herm X.Gm y ξ) := by
          ring
        show IsIntegral ℤ ((w1 + w2) * herm X.Gm y x - (c1 + c2) * herm X.Gm y ξ)
        rw [e]
        exact h3⟩)
    obtain ⟨c, hc⟩ := key
    exact ⟨c, fun y hy => by simpa using hc y hy⟩

end ReciprocityTheory.ChartRestriction.G.FD
