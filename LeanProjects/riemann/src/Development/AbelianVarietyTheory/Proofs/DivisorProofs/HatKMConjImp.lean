import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate

noncomputable section
namespace GlobalTheory.UCls.KGrp
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem isUA_mul (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) {g h : Matrix (Fin n) (Fin n) (RA F E)}
    (hg : IsUA c G g) (hh : IsUA c G h) : IsUA c G (g * h) :=
  ⟨by rw [det_mul]; exact hg.1.mul hh.1, fun x y => by rw [← mulVec_mulVec, ← mulVec_mulVec, hg.2, hh.2]⟩

theorem isUA_inv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) {g : Matrix (Fin n) (Fin n) (RA F E)}
    (hg : IsUA c G g) : IsUA c G g⁻¹ := by
  refine ⟨isUnit_nonsing_inv_det g hg.1, fun x y => ?_⟩
  rw [← hg.2, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv g hg.1, one_mulVec, one_mulVec]

theorem isKM_mul (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    {k k' : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) (hk' : IsKM c G L M k') :
    IsKM c G L M (k * k') := by
  refine ⟨isUA_mul c G hk.1 hk'.1, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y', hy', e'⟩ := hk'.2.1 x hx
    have hkx : k' *ᵥ x ∈ hat F L := by
      have : k' *ᵥ x = x + M • y' := by rw [← e']; abel
      rw [this]; exact add_mem hx (nsmul_mem hy' M)
    obtain ⟨y, hy, e⟩ := hk.2.1 _ hkx
    refine ⟨y + y', add_mem hy hy', ?_⟩
    rw [← mulVec_mulVec, smul_add, ← e, ← e']; abel
  · obtain ⟨y, hy, e⟩ := hk.2.2 x hx
    obtain ⟨z, hz, e'⟩ := hk'.2.2 y hy
    exact ⟨z, hz, by rw [← mulVec_mulVec, e', e]⟩

theorem isKM_inv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) : IsKM c G L M k⁻¹ := by
  have h1 : k * k⁻¹ = 1 := mul_nonsing_inv k hk.1.1
  have h2 : k⁻¹ * k = 1 := nonsing_inv_mul k hk.1.1
  refine ⟨isUA_inv c G hk.1, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hk.2.2 x hx
    obtain ⟨z, hz, e⟩ := hk.2.1 y hy
    refine ⟨-z, neg_mem hz, ?_⟩
    rw [mulVec_mulVec, h2, one_mulVec, smul_neg, ← e]; abel
  · obtain ⟨z, hz, e⟩ := hk.2.1 x hx
    refine ⟨k *ᵥ x, ?_, by rw [mulVec_mulVec, h2, one_mulVec]⟩
    have : k *ᵥ x = x + M • z := by rw [← e]; abel
    rw [this]; exact add_mem hx (nsmul_mem hz M)

theorem isKM_conj (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L Λ : Set (Fin n → E)) (M : ℕ)
    {g0 κ : Matrix (Fin n) (Fin n) (RA F E)} (hg0 : IsUA c G g0)
    (hL : (hat F L : Set (Fin n → RA F E)) = g0.mulVec '' (hat F Λ : Set (Fin n → RA F E)))
    (hκ : IsKM c G L M κ) : IsKM c G Λ M (g0⁻¹ * κ * g0) := by
  have h1 : g0 * g0⁻¹ = 1 := mul_nonsing_inv g0 hg0.1
  have h2 : g0⁻¹ * g0 = 1 := nonsing_inv_mul g0 hg0.1
  have mem : ∀ x, x ∈ hat F Λ → g0 *ᵥ x ∈ hat F L := fun x hx => by
    have : g0 *ᵥ x ∈ (hat F L : Set (Fin n → RA F E)) := by rw [hL]; exact ⟨x, hx, rfl⟩
    exact this
  have back : ∀ z, z ∈ hat F L → g0⁻¹ *ᵥ z ∈ hat F Λ := fun z hz => by
    have : z ∈ (hat F L : Set (Fin n → RA F E)) := hz
    rw [hL] at this
    obtain ⟨x, hx, rfl⟩ := this
    rw [mulVec_mulVec, h2, one_mulVec]; exact hx
  refine ⟨isUA_mul c G (isUA_mul c G (isUA_inv c G hg0) hκ.1) hg0, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, e⟩ := hκ.2.1 _ (mem x hx)
    refine ⟨g0⁻¹ *ᵥ y, back y hy, ?_⟩
    have hx' : g0⁻¹ *ᵥ (g0 *ᵥ x) = x := by rw [mulVec_mulVec, h2, one_mulVec]
    rw [← mulVec_smul, ← e, mulVec_sub, hx', ← mulVec_mulVec, ← mulVec_mulVec]
  · obtain ⟨y, hy, e⟩ := hκ.2.2 _ (mem x hx)
    refine ⟨g0⁻¹ *ᵥ y, back y hy, ?_⟩
    have hy' : g0 *ᵥ (g0⁻¹ *ᵥ y) = y := by rw [mulVec_mulVec, h1, one_mulVec]
    rw [← mulVec_mulVec, ← mulVec_mulVec, hy', e, mulVec_mulVec, h2, one_mulVec]

theorem hatKM_conj_imp {X Y : Set (Fin n → RA F E)} (M : ℕ) {A A' P : Matrix (Fin n) (Fin n) (RA F E)}
    (h2 : A' * A = 1) (hXY : X = A.mulVec '' Y)
    (hP : (∀ x ∈ X, ∃ y ∈ X, P *ᵥ x - x = M • y) ∧ ∀ x ∈ X, ∃ y ∈ X, P *ᵥ y = x) :
    (∀ x ∈ Y, ∃ y ∈ Y, (A' * P * A) *ᵥ x - x = M • y) ∧ ∀ x ∈ Y, ∃ y ∈ Y, (A' * P * A) *ᵥ y = x := by
  have back : ∀ y ∈ X, A' *ᵥ y ∈ Y := fun y hy => by
    rw [hXY] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [mulVec_mulVec, h2, one_mulVec]; exact hz
  have fwd : ∀ y ∈ Y, A *ᵥ y ∈ X := fun y hy => by rw [hXY]; exact ⟨y, hy, rfl⟩
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, e⟩ := hP.1 _ (fwd x hx)
    refine ⟨A' *ᵥ y, back y hy, ?_⟩
    have hx' : A' *ᵥ (A *ᵥ x) = x := by rw [mulVec_mulVec, h2, one_mulVec]
    rw [← mulVec_smul, ← e, mulVec_sub, hx', ← mulVec_mulVec, ← mulVec_mulVec]
  · obtain ⟨y, hy, e⟩ := hP.2 _ (fwd x hx)
    have hy2 := hy
    rw [hXY] at hy2
    obtain ⟨z, hz, rfl⟩ := hy2
    refine ⟨z, hz, ?_⟩
    rw [← mulVec_mulVec, ← mulVec_mulVec, e, mulVec_mulVec, h2, one_mulVec]

theorem hatKM_conj {X Y : Set (Fin n → RA F E)} (M : ℕ) {A A' P : Matrix (Fin n) (Fin n) (RA F E)}
    (h1 : A * A' = 1) (h2 : A' * A = 1) (hXY : X = A.mulVec '' Y) :
    ((∀ x ∈ X, ∃ y ∈ X, P *ᵥ x - x = M • y) ∧ ∀ x ∈ X, ∃ y ∈ X, P *ᵥ y = x) ↔
    ((∀ x ∈ Y, ∃ y ∈ Y, (A' * P * A) *ᵥ x - x = M • y) ∧ ∀ x ∈ Y, ∃ y ∈ Y, (A' * P * A) *ᵥ y = x) := by
  refine ⟨hatKM_conj_imp M h2 hXY, fun h => ?_⟩
  have hYX : Y = A'.mulVec '' X := by
    ext y
    constructor
    · intro hy
      refine ⟨A *ᵥ y, by rw [hXY]; exact ⟨y, hy, rfl⟩, by rw [mulVec_mulVec, h2, one_mulVec]⟩
    · rintro ⟨x, hx, rfl⟩
      rw [hXY] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      rw [mulVec_mulVec, h2, one_mulVec]; exact hz
  have := hatKM_conj_imp (P := A' * P * A) M h1 hYX h
  have e : A * (A' * P * A) * A' = P := by
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  rwa [e] at this

theorem isKM_image (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) :
    k.mulVec '' (hat F L : Set (Fin n → RA F E)) = (hat F L : Set (Fin n → RA F E)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, e⟩ := hk.2.1 y hy
    have : k *ᵥ y = y + M • z := by rw [← e]; abel
    show k *ᵥ y ∈ hat F L
    rw [this]; exact add_mem hy (nsmul_mem hz M)
  · intro hx
    obtain ⟨y, hy, e⟩ := hk.2.2 x hx
    exact ⟨y, hy, e⟩

end GlobalTheory.UCls.KGrp
