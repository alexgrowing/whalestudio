import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.LabelNorm

variable {p : ℕ} [Fact p.Prime]

theorem sub_pos' {d : ℕ} (hd : 0 < d) : 0 < p ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)

theorem theta_gen_pow (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {x : Fbar p} (hx : x ^ (p ^ d - 1) = 1)
    (n : ℕ) : GlobalTheory.GLq.thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  have h : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m := ⟨n, rfl⟩
  unfold GlobalTheory.GLq.thetaOf
  rw [dif_pos h]
  have hp : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have hfin : IsOfFinOrder (L.gen d) := isOfFinOrder_iff_pow_eq_one.2 ⟨_, sub_pos' hd, hp.pow_eq_one⟩
  have hm : n ≡ h.choose [MOD p ^ d - 1] := by
    rw [← L.gen_order d hd]; exact hfin.pow_eq_pow_iff_modEq.1 h.choose_spec
  have h1 : L.teich x ^ (p ^ d - 1) = 1 := by rw [← map_pow, hx, map_one]
  rw [pow_eq_pow_mod h.choose h1, pow_eq_pow_mod n h1, hm]

theorem exists_pow (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {z : Fbar p} (hz : z ^ (p ^ d - 1) = 1) :
    ∃ n : ℕ, z = L.gen d ^ n := by
  haveI : NeZero (p ^ d - 1) := ⟨(sub_pos' hd).ne'⟩
  have hprim : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hz
  exact ⟨n, hn.symm⟩

theorem tor_pow {d : ℕ} (u : Tor p d) : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ d - 1) = 1 := by
  rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]

theorem base_pow (c : (ZMod p)ˣ) : algebraMap (ZMod p) (Fbar p) c ^ (p ^ 1 - 1) = 1 :=
  tor_pow (toTorOne p c)

theorem labels_norm_pow (L : GlobalTheory.GLq.LabelDatum p) {N : ℕ} (hN : 0 < N) (d : ℕ) (h : d ∣ N) (θ : Tor p d →* ℂˣ)
    (x : Fbar p) (n : ℕ) (hθ : LabelsChar L θ x) : LabelsChar L ((θ.comp (torNorm p h)) ^ n) (x ^ n) := by
  have hd : 0 < d := Nat.pos_of_dvd_of_pos h hN
  have hx : (x ^ n) ^ (p ^ N - 1) = 1 := by
    obtain ⟨k, hk⟩ := Nat.pow_sub_one_dvd_pow_sub_one p h
    rw [hk, ← pow_mul, mul_comm n, pow_mul, pow_mul, hθ.1, one_pow, one_pow]
  refine ⟨hx, fun u => ?_⟩
  obtain ⟨k, hk⟩ := exists_pow L hN (tor_pow u)
  have hn : (((torNorm p h u : Tor p d) : (Fbar p)ˣ) : Fbar p) = L.gen d ^ k := by
    have e : (((torNorm p h u : Tor p d) : (Fbar p)ˣ) : Fbar p) =
        ((u : (Fbar p)ˣ) : Fbar p) ^ ((p ^ N - 1) / (p ^ d - 1)) := Units.val_pow_eq_pow_val _ _
    obtain ⟨e', rfl⟩ := h
    rw [e, hk, ← pow_mul, mul_comm k, pow_mul, L.gen_norm d e' hd (Nat.pos_of_mul_pos_left hN)]
  rw [hk, theta_gen_pow L hN hx, MonoidHom.pow_apply, MonoidHom.comp_apply, Units.val_pow_eq_pow_val, hθ.2, hn,
    theta_gen_pow L hd hθ.1, map_pow, ← pow_mul, ← pow_mul, mul_comm]

theorem labels_base (L : GlobalTheory.GLq.LabelDatum p) {N : ℕ} (hN : 0 < N) (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ)
    (h : LabelsTame L χ a) :
    LabelsChar L (χ.comp (baseNorm p N)) (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) := by
  have h1 : LabelsChar L (χ.comp ((MulEquiv.ofBijective (toTorOne p) (toTorOne_bijective p)).symm :
      Tor p 1 →* (ZMod p)ˣ)) (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) := by
    refine ⟨base_pow a, fun u => ?_⟩
    obtain ⟨v, rfl⟩ := (MulEquiv.ofBijective (toTorOne p) (toTorOne_bijective p)).surjective u
    rw [MonoidHom.comp_apply, MonoidHom.coe_coe, MulEquiv.symm_apply_apply, ← h v]
    rfl
  have h2 := labels_norm_pow L hN 1 (one_dvd N) _ _ 1 h1
  rw [pow_one, pow_one] at h2
  exact h2

theorem labels_inv (L : GlobalTheory.GLq.LabelDatum p) (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ)
    (h : LabelsTame L χ a) : LabelsTame L χ⁻¹ a⁻¹ := by
  intro u
  obtain ⟨k, hk⟩ := exists_pow L one_pos (base_pow u)
  have h1 := h u
  rw [hk, theta_gen_pow L one_pos (base_pow a)] at h1
  rw [hk, theta_gen_pow L one_pos (base_pow a⁻¹), MonoidHom.inv_apply, Units.val_inv_eq_inv_val (χ u), ← h1,
    ← inv_pow]
  congr 1
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (N : ℕ), 0 < N → (∀ (d : ℕ) (h : d ∣ N) (θ : Tor p d →* ℂˣ) (x : Fbar p) (n : ℕ), LabelsChar L θ x → LabelsChar L ((θ.comp (torNorm p h)) ^ n) (x ^ n)) ∧ ∀ (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ), LabelsTame L χ a → LabelsChar L (χ.comp (baseNorm p N)) (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) ∧ LabelsTame L χ⁻¹ a⁻¹ :=
  fun _ _ L _ hN => ⟨labels_norm_pow L hN, fun χ a h => ⟨labels_base L hN χ a h, labels_inv L χ a h⟩⟩

end GlobalTheory.LabelNorm
