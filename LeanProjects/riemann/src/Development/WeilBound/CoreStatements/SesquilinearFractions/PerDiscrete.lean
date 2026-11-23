import Development.WeilBound.CoreStatements.SesquilinearFractions.PrincipalRootReZeroImSq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {p q : ℕ} (hty : IsTypeFn H p q ty)

theorem blk_isLeft (k : Fin g) : (blk hty k).isLeft = true ↔ ty k (H.rt : E) = H.rt0 := by
  unfold blk
  split_ifs with h <;> simp [h]

theorem blk_inj {k k' : Fin g} (ht : ty k = ty k') (hb : blk hty k = blk hty k') : k = k' := by
  have key : ∀ (τ τ' : E →+* ℂ), τ = τ' → ∀ (h : τ (H.rt : E) = H.rt0) (h' : τ' (H.rt : E) = H.rt0)
      (a : {j : Fin g // ty j = τ}) (b : {j : Fin g // ty j = τ'}),
      eP hty τ h a = eP hty τ' h' b → (a : Fin g) = b := by
    rintro τ τ' rfl h h' a b hab
    exact congrArg Subtype.val ((eP hty τ h).injective hab)
  have key' : ∀ (τ τ' : E →+* ℂ), τ = τ' → ∀ (h : τ (H.rt : E) ≠ H.rt0) (h' : τ' (H.rt : E) ≠ H.rt0)
      (a : {j : Fin g // ty j = τ}) (b : {j : Fin g // ty j = τ'}),
      eQ hty τ h a = eQ hty τ' h' b → (a : Fin g) = b := by
    rintro τ τ' rfl h h' a b hab
    exact congrArg Subtype.val ((eQ hty τ h).injective hab)
  unfold blk at hb
  by_cases h : ty k (H.rt : E) = H.rt0
  · have h' : ty k' (H.rt : E) = H.rt0 := ht ▸ h
    rw [dif_pos h, dif_pos h'] at hb
    exact key _ _ ht h h' ⟨k, rfl⟩ ⟨k', rfl⟩ (Sum.inl.inj hb)
  · have h' : ty k' (H.rt : E) ≠ H.rt0 := ht ▸ h
    rw [dif_neg h, dif_neg h'] at hb
    exact key' _ _ ht h h' ⟨k, rfl⟩ ⟨k', rfl⟩ (Sum.inr.inj hb)

variable {D : Datum H} (x : Fin p ⊕ Fin q → D.La) (c : D.La →ₗ[𝓞 E] (Fin p ⊕ Fin q →₀ 𝓞 E)) (n : ℕ)

theorem per_bx (hn0 : 0 < n) (hcx : ∀ m, c (x m) = Finsupp.single m (n : 𝓞 E)) (b : 𝓞 E) (m : Fin p ⊕ Fin q)
    (k : Fin g) : per hty c n (b • x m) k = if blk hty k = m then ty k (b : E) else 0 := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  simp only [per, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul, hcx, Finsupp.smul_single, smul_eq_mul]
  rw [Finsupp.single_apply]
  by_cases h : blk hty k = m
  · rw [if_pos h.symm, if_pos h]
    push_cast
    rw [map_mul, map_natCast]
    field_simp
  · rw [if_neg (Ne.symm h), if_neg h]
    simp

def conjPerm : Equiv.Perm (E →+* ℂ) :=
  Function.Involutive.toPerm ComplexEmbedding.conjugate (fun σ => by ext x; simp)

theorem per_span (hn0 : 0 < n) (hcx : ∀ m, c (x m) = Finsupp.single m (n : 𝓞 E)) :
    Submodule.span ℝ (Set.range (per hty c n)) = ⊤ := by
  classical
  have side : ∀ k k' : Fin g, blk hty k = blk hty k' → ComplexEmbedding.conjugate (ty k) ≠ ty k' := by
    intro k k' hkk he
    have h1 := blk_isLeft hty k
    have h2 := blk_isLeft hty k'
    have h3 := conjugate_rt (H := H) (ty k)
    rw [he] at h3
    rw [hkk] at h1
    tauto
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  set l : Fin g → ℂ := fun k => ((f (Pi.single k (1 : ℂ)) : ℝ) : ℂ) -
    Complex.I * ((f (Pi.single k Complex.I) : ℝ) : ℂ) with hl
  have hsingle : ∀ (k : Fin g) (z : ℂ), f (Pi.single k z) = (l k * z).re := by
    intro k z
    have hz : (Pi.single k z : Fin g → ℂ) =
        z.re • (Pi.single k (1 : ℂ) : Fin g → ℂ) + z.im • (Pi.single k Complex.I : Fin g → ℂ) := by
      ext j
      rcases eq_or_ne j k with rfl | hj
      · simp [Complex.ext_iff]
      · simp [hj]
    rw [hz, map_add, map_smul, map_smul]
    simp [hl, Complex.mul_re, smul_eq_mul] <;> ring
  have hf : ∀ v : Fin g → ℂ, f v = (∑ k, l k * v k).re := by
    intro v
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum, Complex.re_sum]
    exact Finset.sum_congr rfl (fun k _ => hsingle k (v k))
  have hl0 : ∀ k0, l k0 = 0 := by
    intro k0
    set S := Finset.univ.filter (fun k => blk hty k = blk hty k0) with hS
    have hre : ∀ b : 𝓞 E, (∑ k ∈ S, l k * ty k (b : E)).re = 0 := by
      intro b
      have h1 : f (per hty c n (b • x (blk hty k0))) = 0 :=
        hle (Submodule.subset_span ⟨b • x (blk hty k0), rfl⟩)
      rw [hf] at h1
      simp only [per_bx hty x c n hn0 hcx, mul_ite, mul_zero] at h1
      rw [hS, Finset.sum_filter]
      exact h1
    set L : (E →+* ℂ) → ℂ := fun σ => ∑ k ∈ S, ((if ty k = σ then l k else 0) +
      (if ComplexEmbedding.conjugate (ty k) = σ then conj (l k) else 0)) with hL
    have hL0 : L = 0 := by
      apply emb_indep
      intro b
      have hterm : ∀ k, l k * ty k (b : E) + conj (l k) * conj (ty k (b : E)) =
          ((2 * (l k * ty k (b : E)).re : ℝ) : ℂ) := by
        intro k
        rw [← map_mul, Complex.add_conj]
      simp only [hL, Finset.sum_mul, add_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        ComplexEmbedding.conjugate_coe_eq]
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun k _ => hterm k)]
      rw [← Complex.ofReal_sum, ← Finset.mul_sum, ← Complex.re_sum, hre b]
      simp
    have h0 := congrFun hL0 (ty k0)
    simp only [hL, Pi.zero_apply] at h0
    rw [Finset.sum_eq_single k0] at h0
    · simpa [side k0 k0 rfl] using h0
    · intro k hk hne
      have hk' : blk hty k = blk hty k0 := by simpa [hS] using hk
      rw [if_neg (fun h => hne (blk_inj hty h hk')), if_neg (side k k0 hk'), add_zero]
    · intro h
      exact absurd (by simp [hS]) h
  apply hf0
  apply LinearMap.ext
  intro v
  rw [hf v]
  simp [hl0]

private theorem exists_blk_inl_of_rt_eq_rt0 (σ : E →+* ℂ) (h : σ (H.rt : E) = H.rt0) (i : Fin p) :
    ∃ k, ty k = σ ∧ blk hty k = Sum.inl i := by
  refine ⟨((eP hty σ h).symm i).1, ((eP hty σ h).symm i).2, ?_⟩
  have key : ∀ (τ : E →+* ℂ), τ = σ → ∀ (h1 : τ (H.rt : E) = H.rt0) (a : {j : Fin g // ty j = τ}),
      (a : Fin g) = ((eP hty σ h).symm i).1 → eP hty τ h1 a = i := by
    rintro τ rfl h1 a ha
    have ha' : a = (eP hty τ h).symm i := Subtype.ext ha
    rw [ha']
    exact (eP hty τ h).apply_symm_apply i
  have hk := ((eP hty σ h).symm i).2
  unfold blk
  rw [dif_pos (by rw [hk]; exact h)]
  exact congrArg Sum.inl (key _ hk _ ⟨_, rfl⟩ rfl)

private theorem exists_blk_inr_of_rt_ne_rt0 (σ : E →+* ℂ) (h : σ (H.rt : E) ≠ H.rt0) (j : Fin q) :
    ∃ k, ty k = σ ∧ blk hty k = Sum.inr j := by
  refine ⟨((eQ hty σ h).symm j).1, ((eQ hty σ h).symm j).2, ?_⟩
  have key : ∀ (τ : E →+* ℂ), τ = σ → ∀ (h1 : τ (H.rt : E) ≠ H.rt0) (a : {i : Fin g // ty i = τ}),
      (a : Fin g) = ((eQ hty σ h).symm j).1 → eQ hty τ h1 a = j := by
    rintro τ rfl h1 a ha
    have ha' : a = (eQ hty τ h).symm j := Subtype.ext ha
    rw [ha']
    exact (eQ hty τ h).apply_symm_apply j
  have hk := ((eQ hty σ h).symm j).2
  unfold blk
  rw [dif_neg (by rw [hk]; exact h)]
  exact congrArg Sum.inr (key _ hk _ ⟨_, rfl⟩ rfl)

theorem per_discrete (hn0 : 0 < n) (hc : ∀ y, c y = 0 → y = 0) : DiscreteTopology (per hty c n).range := by
  have hrt0 : H.rt0 ≠ 0 := by
    intro h0
    have h := H.sqrt_neg_disc_sq
    rw [h0] at h
    have hd : (H.d : ℂ) = 0 := by linear_combination h
    exact H.d_prime.ne_zero (by exact_mod_cast hd)
  have big : ∀ y : D.La, per hty c n y ≠ 0 → 1 / (n : ℝ) ≤ ‖per hty c n y‖ := by
    intro y hy
    have hcy : c y ≠ 0 := fun h => hy (by rw [hc y h, map_zero])
    obtain ⟨m, hm⟩ : ∃ m, c y m ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hcy (Finsupp.ext hcon)
    have hk : ∃ k, blk hty k = m ∧ 1 ≤ ‖ty k (c y m : E)‖ := by
      rcases m with i | j
      · obtain ⟨σ, hσ, hb⟩ := exists_big (H := H) (c y (Sum.inl i)) hm true
        simp only [if_true] at hσ
        obtain ⟨k, hk1, hk2⟩ := exists_blk_inl_of_rt_eq_rt0 hty σ hσ i
        exact ⟨k, hk2, by rw [hk1]; exact hb⟩
      · obtain ⟨σ, hσ, hb⟩ := exists_big (H := H) (c y (Sum.inr j)) hm false
        simp only [Bool.false_eq_true, if_false] at hσ
        have hne : σ (H.rt : E) ≠ H.rt0 := by
          rw [hσ]
          intro h
          apply hrt0
          linear_combination (-1 / 2 : ℂ) * h
        obtain ⟨k, hk1, hk2⟩ := exists_blk_inr_of_rt_ne_rt0 hty σ hne j
        exact ⟨k, hk2, by rw [hk1]; exact hb⟩
    obtain ⟨k, hk1, hk2⟩ := hk
    have hn : (0 : ℝ) < n := by exact_mod_cast hn0
    calc 1 / (n : ℝ) ≤ ‖ty k (c y m : E)‖ / n := by gcongr
      _ = ‖per hty c n y k‖ := by rw [per_apply, hk1, norm_div]; simp
      _ ≤ ‖per hty c n y‖ := norm_le_pi_norm _ k
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
  have hn : (0 : ℝ) < n := by exact_mod_cast hn0
  refine ⟨1 / (n : ℝ), by positivity, fun z hz => ?_⟩
  obtain ⟨z, hzmem⟩ := z
  obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.mp hzmem
  by_contra hne
  have hne' : per hty c n y ≠ 0 := fun h => hne (Subtype.ext h)
  have hb := big y hne'
  have hz' : ‖per hty c n y‖ < 1 / (n : ℝ) := by
    simpa [Subtype.dist_eq, dist_zero_right] using hz
  linarith

end PositivityTheory.Xgf.DPer

end
