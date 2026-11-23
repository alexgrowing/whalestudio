import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.AnisoPeelAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.ExistsTraceNeZero

open Finset Module

noncomputable section

namespace DensInertW

section form
variable {L : Type} [Field L] {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}

theorem val_add_left (x x' y : Fin n → L) : hf q M (x + x') y = hf q M x y + hf q M x' y := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem val_smul_left (c : L) (x y : Fin n → L) : hf q M (c • x) y = c * hf q M x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem val_sub_left (x x' y : Fin n → L) : hf q M (x - x') y = hf q M x y - hf q M x' y := by
  simp only [hf, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem val_smul_right (x : Fin n → L) (c : L) (y : Fin n → L) :
    hf q M x (c • y) = c ^ q * hf q M x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

def valL (q : ℕ) (M : Matrix (Fin n) (Fin n) L) (y : Fin n → L) : (Fin n → L) →ₗ[L] L where
  toFun x := hf q M x y
  map_add' x x' := val_add_left x x' y
  map_smul' c x := by simp only [val_smul_left, smul_eq_mul, RingHom.id_apply]

theorem valL_apply (y x : Fin n → L) : valL q M y x = hf q M x y := rfl

def valPerp (q : ℕ) (M : Matrix (Fin n) (Fin n) L) (W : Submodule L (Fin n → L))
    (e : Fin n → L) : Submodule L (Fin n → L) :=
  (LinearMap.ker ((valL q M e).domRestrict W)).map W.subtype

theorem mem_valPerp {W : Submodule L (Fin n → L)} {e v : Fin n → L} :
    v ∈ valPerp q M W e ↔ v ∈ W ∧ hf q M v e = 0 := by
  simp only [valPerp, Submodule.mem_map, LinearMap.mem_ker, LinearMap.domRestrict_apply,
    valL_apply, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hv, h⟩
    exact ⟨⟨v, hv⟩, h, rfl⟩

theorem finrank_valPerp {W : Submodule L (Fin n → L)} {e : Fin n → L} (he : e ∈ W)
    (hb : hf q M e e ≠ 0) : finrank L (valPerp q M W e) + 1 = finrank L W := by
  have hsurj : LinearMap.range ((valL q M e).domRestrict W) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    refine ⟨⟨(t / hf q M e e) • e, W.smul_mem _ he⟩, ?_⟩
    simp only [LinearMap.domRestrict_apply, valL_apply, val_smul_left]
    exact div_mul_cancel₀ t hb
  have h := LinearMap.finrank_range_add_finrank_ker ((valL q M e).domRestrict W)
  rw [hsurj, finrank_top, finrank_self] at h
  rw [valPerp, Submodule.finrank_map_subtype_eq]
  omega

end form

section formK
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] {n : ℕ}
  {M : Matrix (Fin n) (Fin n) L}

theorem val_add_right (x y y' : Fin n → L) :
    hf (Fintype.card K) M x (y + y') =
      hf (Fintype.card K) M x y + hf (Fintype.card K) M x y' := by
  simp only [hf, Pi.add_apply, frob_add, mul_add, Finset.sum_add_distrib]

theorem val_symm [Fintype L] (h2 : finrank K L = 2) (hM : IsHerm (Fintype.card K) M)
    (x y : Fin n → L) : hf (Fintype.card K) M y x = (hf (Fintype.card K) M x y) ^ Fintype.card K := by
  unfold hf
  rw [frob_sum]
  simp_rw [frob_sum, mul_pow, frob_frob h2]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [← hM]
  ring

theorem val_fixed [Fintype L] (h2 : finrank K L = 2) (hM : IsHerm (Fintype.card K) M)
    (x : Fin n → L) : (hf (Fintype.card K) M x x) ^ Fintype.card K = hf (Fintype.card K) M x x :=
  (val_symm h2 hM x x).symm

theorem val_aniso [Fintype L] (h2 : finrank K L = 2) (hM : IsHerm (Fintype.card K) M)
    {W : Submodule L (Fin n → L)} (hW : NonDeg (Fintype.card K) M W) (hne : W ≠ ⊥) :
    ∃ e ∈ W, hf (Fintype.card K) M e e ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨v, hv, hwv⟩ : ∃ v ∈ W, hf (Fintype.card K) M w v ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (hW w hw h)
  obtain ⟨c, hc⟩ := exists_trace_ne_zero h2 _ (pow_ne_zero (Fintype.card K) hwv)
  apply hc
  have h := hcon (w + c • v) (W.add_mem hw (W.smul_mem c hv))
  simp only [val_add_left, val_add_right, val_smul_left, val_smul_right] at h
  rw [hcon w hw, hcon v hv, val_symm h2 hM w v] at h
  rw [mul_pow, frob_frob h2]
  linear_combination h

theorem val_expand [Fintype L] (h2 : finrank K L = 2) (hM : IsHerm (Fintype.card K) M)
    (e w : Fin n → L) (hwe : hf (Fintype.card K) M w e = 0) (l : L) :
    hf (Fintype.card K) M (l • e + w) (l • e + w) =
      l ^ (Fintype.card K + 1) * hf (Fintype.card K) M e e + hf (Fintype.card K) M w w := by
  have hq := one_lt_q (K := K)
  have hew : hf (Fintype.card K) M e w = 0 := by
    rw [val_symm h2 hM w e, hwe, zero_pow (by omega)]
  simp only [val_add_left, val_add_right, val_smul_left, val_smul_right, hwe, hew]
  ring

theorem nondeg_valPerp [Fintype L] (h2 : finrank K L = 2) (hM : IsHerm (Fintype.card K) M)
    {W : Submodule L (Fin n → L)} (hW : NonDeg (Fintype.card K) M W) {e : Fin n → L}
    (he : e ∈ W) (hb : hf (Fintype.card K) M e e ≠ 0) :
    NonDeg (Fintype.card K) M (valPerp (Fintype.card K) M W e) := by
  intro w hw hall
  rw [mem_valPerp] at hw
  apply hW w hw.1
  intro v hv
  have hv' : v - (hf (Fintype.card K) M v e / hf (Fintype.card K) M e e) • e ∈
      valPerp (Fintype.card K) M W e := by
    rw [mem_valPerp]
    refine ⟨W.sub_mem hv (W.smul_mem _ he), ?_⟩
    rw [val_sub_left, val_smul_left, div_mul_cancel₀ _ hb, sub_self]
  have h1 := hall _ hv'
  have hv2 : v = (hf (Fintype.card K) M v e / hf (Fintype.card K) M e e) • e +
      (v - (hf (Fintype.card K) M v e / hf (Fintype.card K) M e e) • e) := by abel
  rw [hv2, val_add_right, val_smul_right, hw.2, h1]
  ring

theorem val_fibre [Fintype L] [DecidableEq L] (h2 : finrank K L = 2) (b t : L) (hb : b ≠ 0)
    (hbq : b ^ Fintype.card K = b) (ht : t ^ Fintype.card K = t) :
    #{l : L | l ^ (Fintype.card K + 1) * b = t} = if t = 0 then 1 else Fintype.card K + 1 := by
  have e : (univ.filter fun l : L => l ^ (Fintype.card K + 1) * b = t) =
      univ.filter fun l : L => l ^ (Fintype.card K + 1) = t / b :=
    filter_congr (fun l _ => (eq_div_iff hb).symm)
  rw [e]
  split_ifs with h0
  · rw [h0, zero_div]
    exact card_norm_zero _
  · exact card_norm_fibre h2 _ (div_ne_zero h0 hb) (by rw [div_pow, ht, hbq])

end formK

end DensInertW
