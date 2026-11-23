import Development.AutomorphicSpectrum.Proofs.AdelicProofs.RelIndexInfEqOfMemMul
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.RelIndexRatioCocycle
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.EqOneOfPowEqLeExponent
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsFundamentalDomainOfRelIndexNeZero
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.IsIsotropicHermitianSetting

namespace PositivityTheory.EqVol

open MeasureTheory
open scoped ENNReal

variable {G : Type} [Group G]

theorem conjBy_mul (g h : G) (K : Subgroup G) : conjBy (g * h) K = conjBy g (conjBy h K) := by
  simp only [conjBy, Subgroup.map_map, map_mul]
  rfl

theorem relIndex_conjBy (g : G) (A B : Subgroup G) : (conjBy g A).relIndex (conjBy g B) = A.relIndex B :=
  Subgroup.relIndex_map_map_of_injective A B (MulAut.conj g).injective

theorem conjBy_eq_of {K : Subgroup G} {g : G} (h : ∀ x, x ∈ K ↔ g * x * g⁻¹ ∈ K) : conjBy g K = K := by
  ext x
  simp only [conjBy, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (h y).1 hy
  · intro hx
    refine ⟨g⁻¹ * x * g, (h _).2 (by simpa [mul_assoc] using hx), ?_⟩
    simp [mul_assoc]

theorem unimod (S Γ K : Subgroup G) (hc : ∀ g : G, K.relIndex (conjBy g K) ≠ 0 ∧ (conjBy g K).relIndex K ≠ 0)
    (hS : ∀ s ∈ S, ∃ γ ∈ Γ, ∃ k ∈ K, s = γ * k)
    (hΓ : Γ ≤ Subgroup.closure {x : G | ∀ n : ℕ, 0 < n → ∃ y : G, y ^ n = x})
    (hp : ∀ g : G, ∃ n : ℕ, 0 < n ∧ ∃ z ∈ Subgroup.center G, ∃ s ∈ S, g ^ n = z * s) (g : G) :
    K.relIndex (conjBy g K) = (conjBy g K).relIndex K := by
  let f : G → ℚ := fun g => ((conjBy g K).relIndex K : ℚ) / (K.relIndex (conjBy g K) : ℚ)
  have hpos : ∀ g, 0 < f g := fun g =>
    div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (hc g).2)) (Nat.cast_pos.2 (Nat.pos_of_ne_zero (hc g).1))
  have hmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    have h := (GlobalTheory.CompanionTheory.Ar.Cmp.relIndex_ratio_cocycle G K (conjBy a K) (conjBy a (conjBy b K)) (hc a).1 (hc a).2
      (by rw [relIndex_conjBy]; exact (hc b).1) (by rw [relIndex_conjBy]; exact (hc b).2)).2.2
    rw [relIndex_conjBy, relIndex_conjBy, ← conjBy_mul] at h
    have h' := congrArg (Nat.cast : ℕ → ℚ) h
    push_cast at h'
    have e1 : (K.relIndex (conjBy a K) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (hc a).1
    have e2 : (K.relIndex (conjBy b K) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (hc b).1
    have e3 : (K.relIndex (conjBy (a * b) K) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (hc (a * b)).1
    simp only [f]
    field_simp
    linear_combination -h'
  let c : G →* ℚˣ := MonoidHom.mk' (fun g => Units.mk0 (f g) (hpos g).ne') fun a b => Units.ext (hmul a b)
  have h1 : ∀ x, conjBy x K = K → c x = 1 := by
    intro x hx
    refine Units.ext ?_
    show f x = 1
    simp only [f, hx, Subgroup.relIndex_self]
    norm_num
  have hK : ∀ k ∈ K, c k = 1 := fun k hk => h1 k (conjBy_eq_of fun x =>
    ⟨fun hx => K.mul_mem (K.mul_mem hk hx) (K.inv_mem hk), fun hx => by
      simpa [mul_assoc] using K.mul_mem (K.mul_mem (K.inv_mem hk) hx) hk⟩)
  have hZ : ∀ z ∈ Subgroup.center G, c z = 1 := fun z hz => h1 z (conjBy_eq_of fun x => by
    rw [← Subgroup.mem_center_iff.1 hz x, mul_inv_cancel_right])
  have hG : ∀ γ ∈ Γ, c γ = 1 := by
    intro γ hγ
    have : Subgroup.closure {x : G | ∀ n : ℕ, 0 < n → ∃ y : G, y ^ n = x} ≤ c.ker := by
      rw [Subgroup.closure_le]
      intro x hx
      refine GlobalTheory.CompanionTheory.Ar.Cmp.ratUnit_eq_one_of_divisible (c x) fun n hn => ?_
      obtain ⟨y, hy⟩ := hx n hn
      exact ⟨c y, by rw [← map_pow, hy]⟩
    exact this (hΓ hγ)
  obtain ⟨n, hn, z, hz, s, hs, e⟩ := hp g
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hS s hs
  have h2 : c g ^ n = 1 := by rw [← map_pow, e, map_mul, map_mul, hZ z hz, hG γ hγ, hK k hk]; simp
  have h3 : f g ^ n = 1 := by
    have := congrArg Units.val h2
    rwa [Units.val_pow_eq_pow_val] at this
  have h4 : f g = 1 := (pow_eq_one_iff_of_nonneg (hpos g).le hn.ne').1 h3
  have e1 : (K.relIndex (conjBy g K) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (hc g).1
  exact_mod_cast ((div_eq_one_iff_eq e1).1 h4).symm

theorem master : ∀ (G : Type) [Group G] (S Γ : Subgroup G) (𝒦 : Set (Subgroup G)), (∀ K ∈ 𝒦, K ≤ S) → (∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, K ⊓ K' ∈ 𝒦) → (∀ K ∈ 𝒦, ∀ g : G, K.map (MulAut.conj g).toMonoidHom ∈ 𝒦) → (∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, K.relIndex K' ≠ 0) → (∀ K ∈ 𝒦, ∀ s ∈ S, ∃ γ ∈ Γ, ∃ k ∈ K, s = γ * k) → Γ ≤ Subgroup.closure {x : G | ∀ n : ℕ, 0 < n → ∃ y : G, y ^ n = x} → (∀ g : G, ∃ n : ℕ, 0 < n ∧ ∃ z ∈ Subgroup.center G, ∃ s ∈ S, g ^ n = z * s) → ∀ K ∈ 𝒦, ∀ g : G, (K ⊓ Γ).relIndex (K.map (MulAut.conj g).toMonoidHom ⊓ Γ) = (K.map (MulAut.conj g).toMonoidHom ⊓ Γ).relIndex (K ⊓ Γ) ∧ (K ⊓ Γ).relIndex (K.map (MulAut.conj g).toMonoidHom ⊓ Γ) ≠ 0 := by
  intro G _ S Γ 𝒦 h1 h2 h3 h4 h5 h6 h7 K hK g
  have hK' := h3 K hK g
  have e := unimod S Γ K (fun g => ⟨h4 _ hK _ (h3 K hK g), h4 _ (h3 K hK g) _ hK⟩) (h5 K hK) h6 h7 g
  have a := GlobalTheory.CompanionTheory.Ar.Cmp.relIndex_inf_eq_of_mem_mul G Γ K _ fun k hk => h5 _ (h2 _ hK _ hK') k (h1 _ hK' hk)
  have b := GlobalTheory.CompanionTheory.Ar.Cmp.relIndex_inf_eq_of_mem_mul G Γ _ K fun k hk => h5 _ (h2 _ hK' _ hK) k (h1 _ hK hk)
  rw [a, b]
  exact ⟨e, h4 _ hK _ hK'⟩

theorem fdEqual : ∀ (G X : Type) [Group G] [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X] (μ : Measure X) [SMulInvariantMeasure G X μ] (Γ₁ Γ₂ : Subgroup G) [Countable Γ₁] [Countable Γ₂] (s₁ s₂ : Set X), Γ₁.relIndex Γ₂ = Γ₂.relIndex Γ₁ → Γ₁.relIndex Γ₂ ≠ 0 → IsFundamentalDomain Γ₁ s₁ μ → IsFundamentalDomain Γ₂ s₂ μ → μ s₁ = μ s₂ := by
  intro G X _ _ _ _ μ _ Γ₁ Γ₂ _ _ s₁ s₂ he hne h₁ h₂
  have i1 : (Γ₁ ⊓ Γ₂).relIndex Γ₁ = Γ₂.relIndex Γ₁ := Subgroup.inf_relIndex_left _ _
  have i2 : (Γ₁ ⊓ Γ₂).relIndex Γ₂ = Γ₁.relIndex Γ₂ := Subgroup.inf_relIndex_right _ _
  obtain ⟨t₁, ht₁, m₁⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.exists_isFundamentalDomain_of_relIndex_ne_zero G X μ (Γ₁ ⊓ Γ₂) Γ₁ s₁ inf_le_left (by rw [i1, ← he]; exact hne) h₁
  obtain ⟨t₂, ht₂, m₂⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.exists_isFundamentalDomain_of_relIndex_ne_zero G X μ (Γ₁ ⊓ Γ₂) Γ₂ s₂ inf_le_right (by rw [i2]; exact hne) h₂
  have : Countable ↥(Γ₁ ⊓ Γ₂) := (Subgroup.inclusion_injective (inf_le_left : Γ₁ ⊓ Γ₂ ≤ Γ₁)).countable
  have e := ht₁.measure_eq ht₂
  rw [m₁, m₂, i1, i2, ← he] at e
  exact (ENNReal.mul_right_inj (Nat.cast_ne_zero.2 hne) (ENNReal.natCast_ne_top _)).1 e

end PositivityTheory.EqVol
