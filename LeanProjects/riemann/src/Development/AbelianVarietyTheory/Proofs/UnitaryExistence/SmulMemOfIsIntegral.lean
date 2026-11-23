import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOfFinOrderOfBounded
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceFiniteIndex

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FlagData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem transvMat_mulVec (G : Matrix (Fin r) (Fin r) E) (ξ x : Fin r → E) (α : E) :
    FD.transvMat G ξ α *ᵥ x = x + (α * FD.herm G x ξ) • ξ := by
  funext a
  simp only [FD.transvMat, FD.herm, Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul,
    Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem herm_add_smul_left (G : Matrix (Fin r) (Fin r) E) (x ξ y : Fin r → E) (c : E) :
    FD.herm G (x + c • ξ) y = FD.herm G x y + c * FD.herm G ξ y := by
  simp only [FD.herm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem herm_add_smul_right (G : Matrix (Fin r) (Fin r) E) (x ξ y : Fin r → E) (c : E) :
    FD.herm G x (y + c • ξ) = FD.herm G x y + FD.cc c * FD.herm G x ξ := by
  simp only [FD.herm, FD.cc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_add,
    map_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem cc_herm {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, FD.cc (G a b) = G b a)
    (x y : Fin r → E) : FD.cc (FD.herm G x y) = FD.herm G y x := by
  have hG' : ∀ a b, IsCMField.complexConj E (G a b) = G b a := hG
  simp only [FD.herm, FD.cc, map_sum, map_mul, hG', IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem transvMat_mul_neg (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : FD.herm G ξ ξ = 0)
    (α : E) : FD.transvMat G ξ α * FD.transvMat G ξ (-α) = 1 := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    transvMat_mulVec, transvMat_mulVec, herm_add_smul_left, hξ, mul_zero, add_zero, neg_mul,
    neg_smul, neg_add_cancel_right]

noncomputable def transv (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : FD.herm G ξ ξ = 0)
    (α : E) : GL (Fin r) E where
  val := FD.transvMat G ξ α
  inv := FD.transvMat G ξ (-α)
  val_inv := transvMat_mul_neg G hξ α
  inv_val := by simpa using transvMat_mul_neg G hξ (-α)

theorem herm_transvMat {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, FD.cc (G a b) = G b a)
    {ξ : Fin r → E} (hξ : FD.herm G ξ ξ = 0) {α : E} (hα : FD.cc α = -α) (x y : Fin r → E) :
    FD.herm G (FD.transvMat G ξ α *ᵥ x) (FD.transvMat G ξ α *ᵥ y) = FD.herm G x y := by
  have e : FD.cc (α * FD.herm G y ξ) = -α * FD.herm G ξ y := by
    rw [← hα, ← cc_herm hG y ξ]
    exact map_mul (IsCMField.complexConj E) _ _
  rw [transvMat_mulVec, transvMat_mulVec, herm_add_smul_left, herm_add_smul_right,
    herm_add_smul_right, hξ, e]
  ring

omit [NumberField E] [IsCMField E] in
theorem smul_mem_of_isIntegral (Λ : Submodule (𝓞 E) (Fin r → E)) {c : E} (hc : IsIntegral ℤ c)
    {v : Fin r → E} (hv : v ∈ Λ) : c • v ∈ Λ :=
  Λ.smul_mem (⟨c, hc⟩ : 𝓞 E) hv

theorem exists_data : (∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n → σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 M m : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (ξ0 κ0 : E), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ a b, FD.cc (Gm a b) = Gm b a) → Gm.det ≠ 0 → p0 ≤ r → (∀ τ ∈ Ψ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ))) → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → 3 ≤ M → FD.cc ξ0 = -ξ0 → ξ0 ≠ 0 → (κ0 = 2 * ξ0 ∨ κ0 = -(2 * ξ0)) → (∀ τ ∈ Ψ, (τ κ0).im < 0) → 0 < m → (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((m : E) / (M : E) * κ0 * FD.herm Gm x y)) → ∃ X : FD.Data E r, X.Ψ = Ψ ∧ X.Gm = Gm ∧ X.p0 = p0 ∧ X.Λ = Λ ∧ X.ξ0 = ξ0 ∧ X.κ0 = κ0 ∧ X.m = m ∧ (∀ γ, γ ∈ X.Γ ↔ FD.IsUStab Gm Λ γ ∧ (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w)) ∧ ∀ la γ, X.χ la γ = 1 := by
  intro hMink E _ _ _ r p0 M m Ψ Gm Λ ξ0 κ0 hΨ hG hdet hp hsig hfg hsp hM hξ hξ0 hκ hκs hm hint
  obtain ⟨Γ, hΓ, hidx⟩ :=
    GlobalTheory.CongruenceIndex.congruence_finiteIndex E r M Gm Λ hfg (by omega)
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hκ0 : κ0 ≠ 0 := by rcases hκ with h | h <;> simp [h, hξ0]
  have hξ' : IsCMField.complexConj E ξ0 = -ξ0 := hξ
  have hκc : IsCMField.complexConj E κ0 = -κ0 := by
    rcases hκ with h | h <;> simp [h, hξ', map_ofNat]
  have halg : IsAlgebraic ℤ (((m : E) / (M : E) * κ0)⁻¹) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
  refine ⟨{
    Ψ := Ψ, cmType := hΨ, Gm := Gm, Gm_herm := hG, Gm_det := hdet, p0 := p0, p0_le := hp
    signature := fun τ => hsig τ.1 τ.2
    Λ := Λ, Λ_fg := hfg, Λ_span := hsp
    den := (k : 𝓞 E), den_ne := Int.cast_ne_zero.2 hk
    Λ_int := fun x hx y hy => ?_
    Γ := Γ, Γ_stab := fun γ h => ((hΓ γ).1 h).1, Γ_index := hidx
    Γ_free := fun γ h => GlobalTheory.GamFree.gam_free hMink E r p0 M Ψ Gm Λ γ hΨ hG hfg hsp hM
      ((hΓ γ).1 h).1 ((hΓ γ).1 h).2
    χ := fun _ _ => 1
    χ_mul := fun _ _ _ _ _ => (mul_one _).symm
    χ_add := fun _ _ _ _ => (mul_one _).symm
    χ_fin := fun _ => ⟨1, one_pos, fun _ _ => one_pow _⟩
    ξ0 := ξ0, ξ0_im := hξ, ξ0_ne := hξ0, κ0 := κ0, κ0_xi := hκ
    κ0_sign := fun τ => hκs τ.1 τ.2
    m := m, m_pos := hm
    transv := fun ξ hξΛ hiso s hs hsi => ?_ },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, hΓ, fun _ _ => rfl⟩
  · have h := hki.mul (hint x hx y hy)
    have e : k • ((m : E) / (M : E) * κ0)⁻¹ * ((m : E) / (M : E) * κ0 * FD.herm Gm x y) =
        (((k : 𝓞 E) : 𝓞 E) : E) * FD.herm Gm x y := by
      rw [zsmul_eq_mul]
      simp only [map_intCast]
      field_simp
    rwa [e] at h
  · have hs' : IsCMField.complexConj E s = s := hs
    have hα : FD.cc ((m : E) * s * κ0) = -((m : E) * s * κ0) := by
      simp [FD.cc, hs', hκc]
    have hMi : IsIntegral ℤ (M : E) := isIntegral_natCast M
    have key : ∀ v ∈ Λ, (s * ((m : E) / (M : E) * κ0 * FD.herm Gm v ξ)) • ξ ∈ Λ := fun v hv =>
      smul_mem_of_isIntegral Λ (hsi.mul (hint v hv ξ hξΛ)) hξΛ
    have e : ∀ v, ((m : E) * s * κ0 * FD.herm Gm v ξ) • ξ =
        M • ((s * ((m : E) / (M : E) * κ0 * FD.herm Gm v ξ)) • ξ) := by
      intro v
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul]
      congr 1
      field_simp
    refine ⟨transv Gm hiso ((m : E) * s * κ0), (hΓ _).2 ⟨⟨herm_transvMat hG hiso hα, fun x => ?_⟩,
      fun v hv => ⟨_, key v hv, ?_⟩⟩, rfl⟩
    · change x ∈ Λ ↔ FD.transvMat Gm ξ ((m : E) * s * κ0) *ᵥ x ∈ Λ
      rw [transvMat_mulVec]
      refine ⟨fun hx => Λ.add_mem hx (by rw [e]; exact nsmul_mem (key x hx) M), fun hx => ?_⟩
      have h := nsmul_mem (key _ hx) M
      rw [← e, herm_add_smul_left, hiso, mul_zero, add_zero] at h
      simpa using Λ.sub_mem hx h
    · change FD.transvMat Gm ξ ((m : E) * s * κ0) *ᵥ v = _
      rw [transvMat_mulVec, e]

end GlobalTheory.FlagData
