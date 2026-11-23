import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.IsOpenOrbit

noncomputable section

open Matrix Topology GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Nil.BasePf

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem invV (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (h0 : dB0 Z = 0)
    (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) (hS : Supp ξ (Bz Z ×ˢ Set.univ)) (hI : Inv Z ξ)
    (g : GL (Fin n) k) (hg : g ∈ Gz Z) (h : Sp k n → ℂ) (hh : h ∈ TF (Sp k n)) :
    ξ (fun p => h (p.1, g.val *ᵥ p.2)) = ξ h := by
  have hc1 : ∀ g : GL (Fin n) k, Continuous fun p : Sp k n => (p.1, g.val *ᵥ p.2) := fun g =>
    continuous_fst.prodMk (continuous_const.matrix_mulVec continuous_snd)
  have hc2 : ∀ g : GL (Fin n) k, Continuous fun p : Sp k n => act g p := fun g =>
    ((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).prodMk
      (continuous_const.matrix_mulVec continuous_snd)
  have hT1 : (fun p : Sp k n => h (p.1, g.val *ᵥ p.2)) ∈ TF (Sp k n) := by
    refine ⟨hh.1.comp_continuous (hc1 g), HasCompactSupport.intro (hh.2.isCompact.image (hc1 g⁻¹)) fun p hp => ?_⟩
    by_contra hne
    refine hp ⟨(p.1, g.val *ᵥ p.2), subset_tsupport _ hne, ?_⟩
    simp [Matrix.mulVec_mulVec]
  have hT2 : (fun p : Sp k n => h (act g p)) ∈ TF (Sp k n) := by
    refine ⟨hh.1.comp_continuous (hc2 g), HasCompactSupport.intro (hh.2.isCompact.image (hc2 g⁻¹)) fun p hp => ?_⟩
    by_contra hne
    refine hp ⟨act g p, subset_tsupport _ hne, ?_⟩
    simp only [act, Matrix.mulVec_mulVec, inv_inv]
    refine Prod.ext ?_ ?_
    · simp only [← mul_assoc, Units.inv_mul, one_mul]
      rw [mul_assoc, Units.inv_mul, mul_one]
    · simp
  have h1 := hI g hg h ⟨hh, Set.subset_univ _⟩
  have hgZ : g.val ∈ Z := cent_le Z hZ h0 _ hg
  have h2 : ξ ((fun p : Sp k n => h (p.1, g.val *ᵥ p.2)) - fun p => h (act g p)) = 0 := by
    refine hS _ ⟨(TF (Sp k n)).sub_mem hT1 hT2, Set.subset_univ _⟩ fun p hp => ?_
    have hx : g.val * p.1 * g⁻¹.val = p.1 := by
      rw [hp.1 _ hgZ, mul_assoc, Units.mul_inv, mul_one]
    simp only [Pi.sub_apply, act, hx, sub_self]
  rw [map_sub, sub_eq_zero] at h2
  rw [h2, h1]

abbrev Wz (e : Matrix (Fin n) (Fin n) k) : Type := {w : Fin n → k // e *ᵥ w = 0}

theorem mainE (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (h0 : dB0 Z = 0)
    (e : Matrix (Fin n) (Fin n) k) (he : e ∈ Z) (hee : e * e = e)
    (hprim : ∀ u ∈ Z, u * e = u → u ≠ 0 → ∃ u' ∈ Z, u' * e = u' ∧ u' * u = e)
    (v0 : Fin n → k) (hv0 : e *ᵥ v0 ≠ 0)
    (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) (hS : Supp ξ (Bz Z ×ˢ Set.univ)) (hI : Inv Z ξ) :
    ∀ f ∈ supportedIn {q : Sp k n | e *ᵥ q.2 ≠ 0}, ξ f = 0 := by
  classical
  have he1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have h1e : (1 - e) * e = 0 := by rw [sub_mul, one_mul, hee, sub_self]
  have h11 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, he1, sub_zero]

  let Φ : Sp k n → (Matrix (Fin n) (Fin n) k × Wz e) × Wt e := fun p =>
    ((p.1, ⟨(1 - e) *ᵥ p.2, by rw [Matrix.mulVec_mulVec, he1, Matrix.zero_mulVec]⟩),
      ⟨e *ᵥ p.2, by rw [Matrix.mulVec_mulVec, hee]⟩)
  let Ψ : (Matrix (Fin n) (Fin n) k × Wz e) × Wt e → Sp k n := fun q => (q.1.1, q.1.2.1 + q.2.1)
  have hΨΦ : ∀ p, Ψ (Φ p) = p := fun p => by
    show ((p.1, (1 - e) *ᵥ p.2 + e *ᵥ p.2) : Sp k n) = p
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
  have hΦΨ : ∀ q, Φ (Ψ q) = q := fun q => by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      apply Subtype.ext
      show (1 - e) *ᵥ (q.1.2.1 + q.2.1) = q.1.2.1
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, q.1.2.2, q.2.2]
      abel
    · apply Subtype.ext
      show e *ᵥ (q.1.2.1 + q.2.1) = q.2.1
      rw [Matrix.mulVec_add, q.1.2.2, q.2.2, zero_add]
  have hΦc : Continuous Φ :=
    (continuous_fst.prodMk (Continuous.subtype_mk (continuous_const.matrix_mulVec continuous_snd) _)).prodMk
      (Continuous.subtype_mk (continuous_const.matrix_mulVec continuous_snd) _)
  have hΨc : Continuous Ψ :=
    (continuous_fst.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).add
        (continuous_subtype_val.comp continuous_snd))
  have hΦT : ∀ F ∈ TF ((Matrix (Fin n) (Fin n) k × Wz e) × Wt e), (fun p => F (Φ p)) ∈ TF (Sp k n) := by
    intro F hF
    refine ⟨hF.1.comp_continuous hΦc, HasCompactSupport.intro (hF.2.isCompact.image hΨc) fun p hp => ?_⟩
    by_contra hne
    exact hp ⟨Φ p, subset_tsupport _ hne, hΨΦ p⟩
  have hΨT : ∀ f ∈ TF (Sp k n), (fun q => f (Ψ q)) ∈ TF ((Matrix (Fin n) (Fin n) k × Wz e) × Wt e) := by
    intro f hf
    refine ⟨hf.1.comp_continuous hΨc, HasCompactSupport.intro (hf.2.isCompact.image hΦc) fun q hq => ?_⟩
    by_contra hne
    exact hq ⟨Ψ q, subset_tsupport _ hne, hΦΨ q⟩
  let D : ((Matrix (Fin n) (Fin n) k × Wz e) × Wt e → ℂ) →ₗ[ℂ] ℂ := ξ ∘ₗ LinearMap.funLeft ℂ ℂ Φ
  have hD : ∀ g : Gs Z e, ∀ F ∈ TF ((Matrix (Fin n) (Fin n) k × Wz e) × Wt e),
      D (fun q => F (q.1, g • q.2)) = D F := by
    intro g F hF
    have hg := Gs_mem g
    have hce : (1 - e) * (g : GL (Fin n) k).val = 1 - e :=
      calc (1 - e) * (g : GL (Fin n) k).val = (g : GL (Fin n) k).val * (1 - e) := by
            rw [sub_mul, mul_sub, one_mul, mul_one, hg.2.1]
        _ = 1 - e := hg.2.2
    have e1 : (fun p => (fun q : (Matrix (Fin n) (Fin n) k × Wz e) × Wt e => F (q.1, g • q.2)) (Φ p)) =
        fun p => (fun p => F (Φ p)) (p.1, (g : GL (Fin n) k).val *ᵥ p.2) := by
      funext p
      show F ((Φ p).1, g • (Φ p).2) = F (Φ (p.1, (g : GL (Fin n) k).val *ᵥ p.2))
      congr 1
      apply Prod.ext
      · apply Prod.ext
        · rfl
        apply Subtype.ext
        show (1 - e) *ᵥ p.2 = (1 - e) *ᵥ ((g : GL (Fin n) k).val *ᵥ p.2)
        rw [Matrix.mulVec_mulVec, hce]
      · apply Subtype.ext
        show (g : GL (Fin n) k).val *ᵥ (e *ᵥ p.2) = e *ᵥ ((g : GL (Fin n) k).val *ᵥ p.2)
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg.2.1]
    show ξ (fun p => (fun q : (Matrix (Fin n) (Fin n) k × Wz e) × Wt e => F (q.1, g • q.2)) (Φ p)) =
      ξ (fun p => F (Φ p))
    rw [e1]
    exact invV Z hZ h0 ξ hS hI _ hg.1 _ (hΦT F hF)

  let w0 : Wt e := ⟨e *ᵥ v0, by rw [Matrix.mulVec_mulVec, hee]⟩
  have hw0 : w0.1 ≠ 0 := hv0
  have htr : ∀ w ∈ {w : Wt e | w.1 ≠ 0}, ∃ g : Gs Z e, g • w0 = w := by
    intro w hw
    obtain ⟨u, hu, hue, huw⟩ := one_dim Z hZ h0 e he hee hprim w0.1 w.1 w0.2 hw0 w.2
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact hw (by rw [← huw, Matrix.zero_mulVec])
    obtain ⟨u', hu', hu'e, hu'u⟩ := hprim u hu hue hu0
    have heu' : e * u' = u' := by rw [hZ.1 e he u' hu', hu'e]
    have huu' : u * u' = e := by rw [hZ.1 u hu u' hu', hu'u]
    have hA : ((1 - e) + u) * ((1 - e) + u') = 1 := by
      have : ((1 - e) + u) * ((1 - e) + u') = (1 - e) * (1 - e) + ((u' - e * u') + (u - u * e)) + u * u' := by
        noncomm_ring
      rw [this, h11, heu', hue, huu', sub_self, sub_self, add_zero, add_zero, sub_add_cancel]
    have hB : ((1 - e) + u') * ((1 - e) + u) = 1 := by
      have heu : e * u = u := by rw [hZ.1 e he u hu, hue]
      have : ((1 - e) + u') * ((1 - e) + u) = (1 - e) * (1 - e) + ((u - e * u) + (u' - u' * e)) + u' * u := by
        noncomm_ring
      rw [this, h11, heu, hu'e, hu'u, sub_self, sub_self, add_zero, add_zero, sub_add_cancel]
    let U : GL (Fin n) k := ⟨(1 - e) + u, (1 - e) + u', hA, hB⟩
    have hUZ : (1 - e) + u ∈ Z := Z.add_mem (Z.sub_mem Z.one_mem he) hu
    have hU : U ∈ Gs Z e := by
      refine ⟨fun a ha => hZ.1 a ha _ hUZ, hZ.1 _ hUZ e he, ?_⟩
      show ((1 - e) + u) * (1 - e) = 1 - e
      rw [add_mul, h11, mul_sub, mul_one, hue, sub_self, add_zero]
    refine ⟨⟨U, hU⟩, Subtype.ext ?_⟩
    show ((1 - e) + u) *ᵥ w0.1 = w.1
    rw [Matrix.add_mulVec, huw, Matrix.sub_mulVec, Matrix.one_mulVec, w0.2, sub_self, zero_add]

  obtain ⟨t0, ht0v, ht0⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have ht00 : t0 ≠ 0 := by simpa using ht0v
  have hTT : ((1 - e) + t0 • e) * ((1 - e) + t0⁻¹ • e) = 1 := by
    simp only [add_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul, smul_smul, h1e, he1, hee, h11,
      mul_inv_cancel₀ ht00, inv_mul_cancel₀ ht00, one_smul, smul_zero, add_zero, zero_add, sub_add_cancel]
  have hTT' : ((1 - e) + t0⁻¹ • e) * ((1 - e) + t0 • e) = 1 := by
    simp only [add_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul, smul_smul, h1e, he1, hee, h11,
      mul_inv_cancel₀ ht00, inv_mul_cancel₀ ht00, one_smul, smul_zero, add_zero, zero_add, sub_add_cancel]
  let T : GL (Fin n) k := ⟨(1 - e) + t0 • e, (1 - e) + t0⁻¹ • e, hTT, hTT'⟩
  have hTZ : (1 - e) + t0 • e ∈ Z := Z.add_mem (Z.sub_mem Z.one_mem he) (Z.smul_mem he t0)
  have hT : T ∈ Gs Z e := by
    refine ⟨fun a ha => hZ.1 a ha _ hTZ, hZ.1 _ hTZ e he, ?_⟩
    show ((1 - e) + t0 • e) * (1 - e) = 1 - e
    rw [add_mul, h11, Matrix.smul_mul, he1, smul_zero, add_zero]
  let tG : Gs Z e := ⟨T, hT⟩
  have htinv : ∀ w : Wt e, (tG⁻¹ • w).1 = t0⁻¹ • w.1 := by
    intro w
    show ((1 - e) + t0⁻¹ • e) *ᵥ w.1 = t0⁻¹ • w.1
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, w.2, sub_self, zero_add, Matrix.smul_mulVec, w.2]

  let L : Set (Wt e) := {w | ∀ i, valuation k (w.1 i) ≤ 1}
  have hLK : ∀ γ, ∀ g ∈ Ks Z e γ, ∀ w ∈ L, g • w ∈ L := by
    intro γ g hg w hw i
    show valuation k (((g : GL (Fin n) k).val *ᵥ w.1) i) ≤ 1
    simp only [Matrix.mulVec, dotProduct]
    exact (valuation k).map_sum_le fun j _ => by
      rw [map_mul]
      exact mul_le_one' (int_of_sm hg.1 i j) (hw j)
  have htL : ∀ w : Wt e, tG⁻¹ • w ∈ L → w ∈ L := by
    intro w hw i
    have := hw i
    rw [htinv, Pi.smul_apply, smul_eq_mul] at this
    have e2 : w.1 i = t0 * (t0⁻¹ * w.1 i) := by rw [← mul_assoc, mul_inv_cancel₀ ht00, one_mul]
    rw [e2, map_mul]
    exact mul_le_one' ht0.le this
  have hLS : ∀ w ∈ L, tG⁻¹ • w ∉ L → w ∈ {w : Wt e | w.1 ≠ 0} := by
    intro w _ hw h
    apply hw
    intro i
    rw [htinv, h]
    simp
  have hne : ∃ w ∈ L, tG⁻¹ • w ∉ L := by
    obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hw0
    have : Nonempty (Fin n) := ⟨i0⟩
    obtain ⟨j, hj⟩ := Finite.exists_max fun i => valuation k (w0.1 i)
    have hc : w0.1 j ≠ 0 := by
      intro h
      have := hj i0
      rw [h, map_zero] at this
      exact hi0 ((valuation k).zero_iff.1 (le_antisymm this zero_le'))
    let w1 : Wt e := ⟨(w0.1 j)⁻¹ • w0.1, by rw [Matrix.mulVec_smul, w0.2]⟩
    refine ⟨w1, fun i => ?_, fun h => ?_⟩
    · show valuation k ((w0.1 j)⁻¹ * w0.1 i) ≤ 1
      rw [map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.2 ((valuation k).ne_zero_iff.2 hc)), mul_one]
      exact hj i
    · have := h j
      rw [htinv] at this
      change valuation k (t0⁻¹ * ((w0.1 j)⁻¹ * w0.1 j)) ≤ 1 at this
      rw [inv_mul_cancel₀ hc, mul_one] at this
      have h1 : valuation k t0 * valuation k t0⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ ht00, map_one]
      have h2 : valuation k t0 * valuation k t0⁻¹ ≤ valuation k t0 := mul_le_of_le_one_right' this
      rw [h1] at h2
      exact absurd (lt_of_le_of_lt h2 ht0) (lt_irrefl 1)
  have hcont : ∀ g : Gs Z e, Continuous fun w : Wt e => g • w := fun g =>
    Continuous.subtype_mk (continuous_const.matrix_mulVec continuous_subtype_val) _
  have hcore := core (Gs_comm Z hZ h0 e) hcont D hD {w : Wt e | w.1 ≠ 0} w0 htr (Ks Z e)
    (fun γ w hw => isOpen_orbit Z hZ h0 e he hee hprim γ w hw) (fun f hf => unif Z e hee f hf.1)
    tG L (isCompact_L e) (isOpen_L e) hLK htL hLS hne
  intro f hf
  have hF : (fun q => f (Ψ q)) ∈ supportedIn (Set.univ ×ˢ {w : Wt e | w.1 ≠ 0}) := by
    refine ⟨hΨT f hf.1, fun q hq => ⟨Set.mem_univ _, ?_⟩⟩
    have := hf.2 hq
    show q.2.1 ≠ 0
    intro h0'
    apply this
    show e *ᵥ (q.1.2.1 + q.2.1) = 0
    rw [Matrix.mulVec_add, q.1.2.2, q.2.2, h0', add_zero]
  have := hcore _ hF
  have e3 : D (fun q => f (Ψ q)) = ξ f := by
    show ξ (fun p => f (Ψ (Φ p))) = ξ f
    simp only [hΨΦ]
  rw [← e3]
  exact this

end PositivityTheory.RgUd.T.Nil.BasePf
