import Mathlib
open MeasureTheory Topology
open scoped ENNReal

namespace GlobalTheory

theorem lintegral_tsum_orbit_unfold (G G' V X : Type) [Group G] [Group G'] [MeasurableSpace G]
    [MeasurableSpace G'] [MeasurableMul₂ G] [MeasurableInv G] [MeasurableMul G'] [MulAction G V]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (μ' : Measure G') [SFinite μ']
    [μ'.IsMulLeftInvariant] (Γ : Subgroup G) (Γ' : Subgroup G') [Countable Γ] [Countable Γ']
    (𝓕 : Set G) (𝓕' : Set G') (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (h𝓕' : IsFundamentalDomain Γ' 𝓕' μ') (φ : G' →* G) (hφm : Measurable φ)
    (hφi : Function.Injective φ) (hΓ : ∀ g, φ g ∈ Γ ↔ g ∈ Γ') (x : V)
    (hst : φ.range = MulAction.stabilizer G x) (c : X → V) (hc : Function.Injective c)
    (hcr : ∀ y, y ∈ Set.range c ↔ ∃ γ ∈ Γ, γ • x = y) (u : G → ℝ≥0∞) (hu : Measurable u)
    (Φ : V → ℝ≥0∞) (hΦ : ∀ h : G, Φ (h⁻¹ • x) = ∫⁻ g, u ((φ g)⁻¹ * h) ∂μ') :
    ∫⁻ h in 𝓕, ∑' i, Φ (h⁻¹ • c i) ∂μ = μ' 𝓕' * ∫⁻ h, u h ∂μ := by
  haveI : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  haveI : MeasurableConstSMul Γ' G' := ⟨fun γ => measurable_const_mul (γ : G')⟩
  haveI : SMulInvariantMeasure Γ G μ :=
    ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  haveI : SMulInvariantMeasure Γ' G' μ' :=
    ⟨fun γ s _ => measure_preimage_mul μ' (γ : G') s⟩
  have hex : ∀ i, ∃ γ ∈ Γ, γ • x = c i := fun i => (hcr _).1 ⟨i, rfl⟩
  choose γ hγ hγx using hex
  have hfix : ∀ g, φ g • x = x := fun g => by
    have : φ g ∈ MulAction.stabilizer G x := hst ▸ ⟨g, rfl⟩
    exact this
  let f : X × Γ' → Γ := fun p => ⟨γ p.1 * φ p.2, Γ.mul_mem (hγ _) ((hΓ _).2 p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, a⟩ ⟨j, b⟩ hab
      have h1 : γ i * φ a = γ j * φ b := congrArg Subtype.val hab
      have h2 : i = j := by
        apply hc
        have := congrArg (· • x) h1
        simpa [mul_smul, hfix, hγx] using this
      subst h2
      have h3 : a = b := Subtype.ext (hφi (mul_left_cancel h1))
      rw [h3]
    · rintro ⟨δ, hδ⟩
      obtain ⟨i, hi⟩ := (hcr (δ • x)).2 ⟨δ, hδ, rfl⟩
      have h1 : (γ i)⁻¹ * δ ∈ φ.range := by
        rw [hst, MulAction.mem_stabilizer_iff, mul_smul, ← hi, ← hγx, inv_smul_smul]
      obtain ⟨a, ha⟩ := h1
      have ha' : a ∈ Γ' := (hΓ a).1 (ha ▸ Γ.mul_mem (Γ.inv_mem (hγ i)) hδ)
      refine ⟨(i, ⟨a, ha'⟩), Subtype.ext ?_⟩
      show γ i * φ a = δ
      rw [ha, mul_inv_cancel_left]
  let F : G → ℝ≥0∞ := fun h => ∫⁻ g in 𝓕', u ((φ g)⁻¹ * h) ∂μ'
  have hK : Measurable (fun p : G × G' => u ((φ p.2)⁻¹ * p.1)) :=
    hu.comp (((hφm.comp measurable_snd).inv).mul measurable_fst)
  have hF : Measurable F := hK.lintegral_prod_right'
  have step : ∀ h : G, ∑' i, Φ (h⁻¹ • c i) = ∑' δ : Γ, F (δ⁻¹ • h) := by
    intro h
    rw [← (Equiv.ofBijective f hf).tsum_eq, ENNReal.tsum_prod']
    refine tsum_congr fun i => ?_
    have h1 : h⁻¹ • c i = ((γ i)⁻¹ * h)⁻¹ • x := by
      rw [mul_inv_rev, inv_inv, mul_smul, hγx]
    rw [h1, hΦ, h𝓕'.lintegral_eq_tsum'']
    refine tsum_congr fun a => ?_
    refine lintegral_congr fun g => ?_
    congr 1
    show (φ ((a : G') * g))⁻¹ * ((γ i)⁻¹ * h) = (φ g)⁻¹ * ((γ i * φ a)⁻¹ * h)
    simp [mul_assoc]
  simp_rw [step]
  rw [lintegral_tsum (f := fun (δ : Γ) h => F (δ⁻¹ • h)) (fun δ => (hF.comp (measurable_const_smul δ⁻¹)).aemeasurable),
    ← h𝓕.lintegral_eq_tsum' F]
  show ∫⁻ h, ∫⁻ g in 𝓕', u ((φ g)⁻¹ * h) ∂μ' ∂μ = _
  rw [lintegral_lintegral_swap hK.aemeasurable]
  simp_rw [lintegral_mul_left_eq_self u]
  rw [setLIntegral_const, mul_comm]

end GlobalTheory
