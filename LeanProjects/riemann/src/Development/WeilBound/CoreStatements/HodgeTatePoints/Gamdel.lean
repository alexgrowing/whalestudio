import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace PositivityTheory.HtPt.Gamdel

theorem mem_mulLat_iff {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {w : Ω} (hw : w ≠ 0)
    (L : AddSubgroup V) (v : V) : v ∈ mulLat w L ↔ w⁻¹ • v ∈ L := by
  unfold GlobalTheory.CompanionTheory.Ar.Num.mulLat
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨u, hu, huv⟩
    rw [← huv]
    simpa [inv_smul_smul₀ hw] using hu
  · intro h
    exact ⟨w⁻¹ • v, h, by simp [smul_inv_smul₀ hw]⟩

theorem smul_mem_stdLat {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    (ι : Type) {a : Ω} (ha : a ∈ R) {v : ι → Ω} (hv : v ∈ stdLat R ι) : a • v ∈ stdLat R ι := by
  unfold GlobalTheory.CompanionTheory.Ar.Num.stdLat at hv ⊢
  rw [AddSubgroup.mem_pi] at hv ⊢
  intro j hj
  have hvj : v j ∈ R := by simpa using hv j hj
  simpa [smul_eq_mul] using R.mul_mem ha hvj

def graphLat {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω V'] (w : Ω) (A : AddSubgroup V) (B : AddSubgroup V') (f : V →ₗ[Ω] V') :
    AddSubgroup (V × V') where
  carrier := {p | w • p.1 ∈ A ∧ p.2 - f p.1 ∈ B}
  zero_mem' := by
    refine ⟨by simp, by simp⟩
  add_mem' := by
    rintro p q ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, ?_⟩
    · have := A.add_mem h1 h3
      simpa [smul_add] using this
    · have := B.add_mem h2 h4
      convert this using 1
      simp only [Prod.snd_add, Prod.fst_add, map_add]
      abel
  neg_mem' := by
    rintro p ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := A.neg_mem h1
      simpa [smul_neg] using this
    · have := B.neg_mem h2
      convert this using 1
      simp only [Prod.snd_neg, Prod.fst_neg, map_neg]
      abel

theorem mem_graphLat {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω V'] (w : Ω) (A : AddSubgroup V) (B : AddSubgroup V') (f : V →ₗ[Ω] V') (a : V)
    (b : V') : (a, b) ∈ graphLat w A B f ↔ w • a ∈ A ∧ b - f a ∈ B := Iff.rfl

theorem smul_mem_graphLat {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    [AddCommGroup V'] [Module Ω V'] (w : Ω) (A : AddSubgroup V) (B : AddSubgroup V')
    (f : V →ₗ[Ω] V') (a : Ω) (hA : ∀ v ∈ A, a • v ∈ A) (hB : ∀ v ∈ B, a • v ∈ B)
    (v : V × V') (hv : v ∈ graphLat w A B f) : a • v ∈ graphLat w A B f := by
  have hv' := (PositivityTheory.HtPt.Gamdel.mem_graphLat w A B f v.1 v.2).1 hv
  refine (PositivityTheory.HtPt.Gamdel.mem_graphLat w A B f (a • v).1 (a • v).2).2 ⟨?_, ?_⟩
  · rw [Prod.smul_fst, smul_smul, mul_comm, ← smul_smul]
    exact hA _ hv'.1
  · rw [Prod.smul_snd, Prod.smul_fst, map_smul, ← smul_sub]
    exact hB _ hv'.2

theorem glue_gamdel : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (w : Ω), w ∈ R → w ≠ 0 → ∀ (r s n : ℕ) (W : AddSubgroup (Fin r → Ω)) (om : AddSubgroup (Fin s → Ω)), (∀ a ∈ R, ∀ v ∈ W, a • v ∈ W) → (∀ a ∈ R, ∀ v ∈ om, a • v ∈ om) → ∀ (i : (Fin r → Ω) →ₗ[Ω] (Fin n → Ω)) (q : (Fin n → Ω) →ₗ[Ω] (Fin s → Ω)), (∀ a ∈ W, i a ∈ stdLat R (Fin n)) → (∀ b ∈ stdLat R (Fin n), q b ∈ om) → (∀ a ∈ W, i a ∈ mulLat w (stdLat R (Fin n)) → a ∈ mulLat w W) → (∀ b ∈ stdLat R (Fin n), q b ∈ mulLat w om ↔ ∃ a ∈ W, b - i a ∈ mulLat w (stdLat R (Fin n))) → (∀ c ∈ om, ∃ b ∈ stdLat R (Fin n), c - q b ∈ mulLat w om) → ∃ (Gam : AddSubgroup ((Fin r → Ω) × (Fin n → Ω))) (Del : AddSubgroup ((Fin n → Ω) × (Fin s → Ω))), (∀ a b, (a, b) ∈ Gam ↔ w • a ∈ W ∧ b - i a ∈ stdLat R (Fin n)) ∧ (∀ b c, (b, c) ∈ Del ↔ w • b ∈ stdLat R (Fin n) ∧ c - q b ∈ om) ∧ (∀ a ∈ R, (∀ v ∈ Gam, a • v ∈ Gam) ∧ ∀ v ∈ Del, a • v ∈ Del) ∧ ((∀ a, (∃ b, (a, b) ∈ Gam) ↔ w • a ∈ W) ∧ (∀ b, (0, b) ∈ Gam ↔ b ∈ stdLat R (Fin n)) ∧ ∀ a, (a, 0) ∈ Gam ↔ a ∈ W) ∧ ((∀ b, (∃ c, (b, c) ∈ Del) ↔ w • b ∈ stdLat R (Fin n)) ∧ (∀ c, (∃ b, (b, c) ∈ Del) ↔ w • c ∈ om) ∧ (∀ c, (0, c) ∈ Del ↔ c ∈ om) ∧ ∀ b, (b, 0) ∈ Del ↔ ∃ a, (a, b) ∈ Gam) := by
  intro o Ω _ _ _ R w hwR hw r s n W om hW hom i q hiW hqS hexW hexS hsurj
  have hS : ∀ a ∈ R, ∀ v ∈ GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n),
      a • v ∈ GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n) :=
    fun a ha v hv => PositivityTheory.HtPt.Gamdel.smul_mem_stdLat R (Fin n) ha hv
  have hmem := fun {V : Type} [AddCommGroup V] [Module Ω V] (L : AddSubgroup V) (x : V) =>
    PositivityTheory.HtPt.Gamdel.mem_mulLat_iff hw L x
  refine ⟨PositivityTheory.HtPt.Gamdel.graphLat w W (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) i,
    PositivityTheory.HtPt.Gamdel.graphLat w (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) om q,
    fun a b => PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _, fun b c => PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _,
    fun a ha => ⟨PositivityTheory.HtPt.Gamdel.smul_mem_graphLat _ _ _ _ a (hW a ha) (hS a ha),
      PositivityTheory.HtPt.Gamdel.smul_mem_graphLat _ _ _ _ a (hS a ha) (hom a ha)⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro a
    constructor
    · rintro ⟨b, hb⟩
      exact ((PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).1 hb).1
    · intro ha
      refine ⟨i a, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨ha, ?_⟩⟩
      rw [sub_self]
      exact AddSubgroup.zero_mem _
  · intro b
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, smul_zero, map_zero, sub_zero]
    exact ⟨fun h => h.2, fun h => ⟨W.zero_mem, h⟩⟩
  · intro a
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, zero_sub, neg_mem_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : i (w • a) ∈ GlobalTheory.CompanionTheory.Ar.Num.mulLat w (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) := by
        rw [hmem, map_smul, inv_smul_smul₀ hw]
        exact h2
      have h4 := hexW _ h1 h3
      rwa [hmem, inv_smul_smul₀ hw] at h4
    · intro ha
      exact ⟨hW w hwR a ha, hiW a ha⟩
  · intro b
    constructor
    · rintro ⟨c, hc⟩
      exact ((PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).1 hc).1
    · intro hb
      refine ⟨q b, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨hb, ?_⟩⟩
      rw [sub_self]
      exact AddSubgroup.zero_mem _
  · intro c
    constructor
    · rintro ⟨b, hb⟩
      rw [PositivityTheory.HtPt.Gamdel.mem_graphLat] at hb
      have h1 := hom w hwR _ hb.2
      have h2 := hqS _ hb.1
      have hc : w • c = w • (c - q b) + q (w • b) := by
        rw [map_smul, smul_sub, sub_add_cancel]
      rw [hc]
      exact om.add_mem h1 h2
    · intro hc
      obtain ⟨b0, hb0, h⟩ := hsurj _ hc
      rw [hmem, smul_sub, inv_smul_smul₀ hw] at h
      refine ⟨w⁻¹ • b0, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨?_, ?_⟩⟩
      · rwa [smul_inv_smul₀ hw]
      · rwa [map_smul]
  · intro c
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, smul_zero, map_zero, sub_zero]
    exact ⟨fun h => h.2, fun h => ⟨AddSubgroup.zero_mem _, h⟩⟩
  · intro b
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, zero_sub, neg_mem_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : q (w • b) ∈ GlobalTheory.CompanionTheory.Ar.Num.mulLat w om := by
        rw [hmem, map_smul, inv_smul_smul₀ hw]
        exact h2
      obtain ⟨a0, ha0, h4⟩ := (hexS _ h1).1 h3
      rw [hmem, smul_sub, inv_smul_smul₀ hw] at h4
      refine ⟨w⁻¹ • a0, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨?_, ?_⟩⟩
      · rwa [smul_inv_smul₀ hw]
      · rwa [map_smul]
    · rintro ⟨a, ha⟩
      rw [PositivityTheory.HtPt.Gamdel.mem_graphLat] at ha
      obtain ⟨h1, h2⟩ := ha
      have hwb : w • b ∈ GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n) := by
        have e : w • b = w • (b - i a) + i (w • a) := by
          rw [map_smul, smul_sub, sub_add_cancel]
        rw [e]
        exact AddSubgroup.add_mem _ (hS w hwR _ h2) (hiW _ h1)
      refine ⟨hwb, ?_⟩
      have h3 : w • b - i (w • a) ∈ GlobalTheory.CompanionTheory.Ar.Num.mulLat w (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) := by
        rw [hmem, map_smul, ← smul_sub, inv_smul_smul₀ hw]
        exact h2
      have h4 := (hexS _ hwb).2 ⟨w • a, h1, h3⟩
      rwa [hmem, map_smul, inv_smul_smul₀ hw] at h4

end PositivityTheory.HtPt.Gamdel
