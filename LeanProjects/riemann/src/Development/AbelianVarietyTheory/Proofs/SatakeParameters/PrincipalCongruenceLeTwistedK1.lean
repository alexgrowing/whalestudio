import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.ChainTwTopQ
import Formalism.LocalToGlobal.Columns.DiagUnitMemAndNormalizesKOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetTwist
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.PrincipalCongruenceLevelK1

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem intAt_shift {m c : ℕ} (hm : m ≤ c) {a d : E}
    (ha : IntAt P (((qOf P : E) ^ (m : ℤ))⁻¹ * a)) (hd : IntAt P d) :
    IntAt P (((qOf P : E) ^ (m : ℤ))⁻¹ * (a + (qOf P : E) ^ c * d)) := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero (P := P)
  have e : ((qOf P : E) ^ (m : ℤ))⁻¹ * (a + (qOf P : E) ^ c * d) =
      ((qOf P : E) ^ (m : ℤ))⁻¹ * a + (qOf P : E) ^ (c - m) * d := by
    rw [zpow_natCast]
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [Nat.add_sub_cancel_left, pow_add]
    field_simp
  rw [e]
  exact ha.add ((intAt_pow (P := P) (intAt_nat (P := P) (qOf P)) _).mul hd)

theorem prinCong_maps {N c : ℕ} {e : ℕ → ℤ} (he : ∀ l, 0 ≤ e l ∧ e l ≤ c) {k : GLint E N P}
    (hk : k ∈ prinCong N P c) {x : Sp E N} (hx : x ∈ LocE.sclLat P (qOf P) N e) :
    (k : Sp E N ≃ₗ[E] Sp E N) x ∈ LocE.sclLat P (qOf P) N e := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero (P := P)
  rw [ciMem_sclLat] at hx ⊢
  have hxs : x ∈ stdAt E N P := by
    rw [ciMem_stdAt]
    intro l
    obtain ⟨m, hm⟩ : ∃ m : ℕ, e l.1 = m := ⟨(e l.1).toNat, by have := he l.1; omega⟩
    have h1 := (intAt_pow (P := P) (intAt_nat (P := P) (qOf P)) m).mul (hx l)
    rw [hm, zpow_natCast] at h1
    rwa [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul] at h1
  have hd := mem_stdAt.1 (hk x hxs)
  intro l
  obtain ⟨m, hm⟩ : ∃ m : ℕ, e l.1 = m := ⟨(e l.1).toNat, by have := he l.1; omega⟩
  have hmc : m ≤ c := by have := he l.1; omega
  have e1 : (k : Sp E N ≃ₗ[E] Sp E N) x l = x l + (qOf P : E) ^ c * ((((qOf P : E) ^ c)⁻¹ • (k.1 x - x)) l) := by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul]
    show _ = x l + ((k : Sp E N ≃ₗ[E] Sp E N) x l - x l)
    ring
  rw [e1, hm]
  have hxl := hx l
  rw [hm] at hxl
  exact intAt_shift P hmc hxl (hd l)

theorem prinCong_stab {N c : ℕ} {e : ℕ → ℤ} (he : ∀ l, 0 ≤ e l ∧ e l ≤ c) {k : GLint E N P}
    (hk : k ∈ prinCong N P c) : (k : Sp E N ≃ₗ[E] Sp E N) ∈ stabL E N (LocE.sclLat P (qOf P) N e) := by
  intro x
  refine ⟨fun h => ?_, prinCong_maps P he hk⟩
  have h1 := prinCong_maps P he ((prinCong N P c).inv_mem hk) h
  have e2 : ((k⁻¹ : GLint E N P) : Sp E N ≃ₗ[E] Sp E N) ((k : Sp E N ≃ₗ[E] Sp E N) x) = x :=
    LinearEquiv.symm_apply_apply _ x
  rwa [e2] at h1

theorem principal_congruence_le_level_k1_at {N : ℕ} (r c : ℕ) (hc : 0 < c) : prinCong N P c ≤ twK1H P N r c := by
  intro k hk
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero (P := P)
  refine ⟨⟨k.2, ?_⟩, prinCong_stab P (fun l => ?_) hk, prinCong_stab P (fun l => ?_) hk, fun w hw => ?_⟩
  · exact prinCong_stab P (N := N + 0) (fun l => by split_ifs <;> omega) hk
  · unfold kOneLastExponents; split_ifs <;> omega
  · unfold twistedLevelExponent; split_ifs <;> omega
  · have hws : w ∈ stdAt E N P := by
      have h0 := prinCong_maps P (e := fun _ => 0) (fun _ => by omega) ((prinCong N P c).one_mem) (x := w) ?_
      · rw [ciMem_sclLat] at h0; rw [ciMem_stdAt]; intro l; simpa using h0 l
      · rw [ciMem_sclLat] at hw ⊢
        intro l
        have h1 := hw l
        unfold twistedLevelExponent at h1
        split_ifs at h1 with hl
        · simpa using h1
        · have h2 := (intAt_pow (P := P) (intAt_nat (P := P) (qOf P)) c).mul h1
          rw [zpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul] at h2
          simpa using h2
    have hd := mem_stdAt.1 (hk w hws)
    rw [ciMem_sclLat]
    intro l
    have := hd l
    simp only [Pi.smul_apply, smul_eq_mul, zpow_natCast] at this ⊢
    exact this

theorem principal_congruence_le_level_k1 : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (r c : ℕ),
    0 < c → prinCong N P c ≤ twK1H P N r c :=
  by
  intro E _ _ _ P N r c hc
  exact principal_congruence_le_level_k1_at P r c hc

end GlobalTheory.PrincipalCongruenceLevelK1
