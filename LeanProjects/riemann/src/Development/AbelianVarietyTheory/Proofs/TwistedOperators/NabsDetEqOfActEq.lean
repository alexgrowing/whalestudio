import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfPowerSpherical
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactMapsPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical GlobalTheory.LatPair GlobalTheory.StepData
open scoped Pointwise

noncomputable section
namespace GlobalTheory.IdealChain

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mem_idl {b : kˣ} {x : k} : x ∈ idl b ↔ valuation k x ≤ valuation k (b : k) := by
  have hb : valuation k (b : k) ≠ 0 := by simp
  rw [idl, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨s, rfl⟩
    change valuation k ((s : k) * b) ≤ _
    rw [map_mul]
    exact mul_le_of_le_one_left' s.2
  · intro h
    refine ⟨⟨x / b, ?_⟩, ?_⟩
    · change valuation k (x / b) ≤ 1
      rw [map_div₀]
      exact div_le_one_of_le₀ h zero_le
    · change x / b * b = x
      simp

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mem_idl_iff_int {b : kˣ} {x : k} : x ∈ idl b ↔ ((b⁻¹ : kˣ) : k) * x ∈ 𝒪[k] := by
  have hb : 0 < valuation k (b : k) := zero_lt_iff.2 (by simp)
  rw [mem_idl]
  change _ ↔ valuation k _ ≤ 1
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ hb, mul_one]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem idl_eq_iff {a b : kˣ} : idl a = idl b ↔ valuation k (a : k) = valuation k (b : k) := by
  constructor
  · intro h
    exact le_antisymm (mem_idl.1 (h ▸ mem_idl.2 le_rfl)) (mem_idl.1 (h ▸ mem_idl.2 le_rfl))
  · intro h
    ext x
    rw [mem_idl, mem_idl, h]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mem_monLat {n : Type} {c : ℕ} {L : Submodule 𝒪[k] (n → k)} {b : ℕ → kˣ} {v : n ⊕ Fin c → k} :
    v ∈ monLat c L b ↔ (fun r => v (Sum.inl r)) ∈ L ∧ ∀ i : Fin c, v (Sum.inr i) ∈ idl (b (i.val + 1)) := Iff.rfl

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem monLat_congr {n : Type} {c : ℕ} (L : Submodule 𝒪[k] (n → k)) {b b' : ℕ → kˣ}
    (h : ∀ i, 1 ≤ i → i ≤ c → idl (b i) = idl (b' i)) : monLat c L b = monLat c L b' := by
  ext v
  simp only [mem_monLat]
  exact and_congr_right' (forall_congr' fun i => by rw [h _ (by omega) i.2])

section Act
variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mem_act {g : GL ι k} {L : Submodule 𝒪[k] (ι → k)} {v : ι → k} : v ∈ act g L ↔ (g⁻¹).val *ᵥ v ∈ L := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · exact fun h => ⟨_, h, by simp⟩

theorem act_eq_smul (g : GL ι k) (L : Submodule 𝒪[k] (ι → k)) : act g L = g • L := by
  ext v
  rw [mem_act, mem_smul_iff]
  rfl

theorem isLattice_act (g : GL ι k) {L : Submodule 𝒪[k] (ι → k)} (h : L.IsLattice k) : (act g L).IsLattice k := by
  rw [act_eq_smul]
  infer_instance

theorem exists_act_stdLat {L : Submodule 𝒪[k] (ι → k)} (h : L.IsLattice k) : ∃ g : GL ι k, L = act g (stdLat k ι) := by
  obtain ⟨g, hg⟩ := exists_smul_lat (stdLat k ι) L
  exact ⟨g, by rw [act_eq_smul, hg]⟩

theorem act_stdLat_eq_iff {g : GL ι k} : act g (stdLat k ι) = stdLat k ι ↔ g ∈ KO k ι := by
  rw [mem_KO]
  constructor
  · intro h
    refine ⟨maps_stdLat_iff.1 fun y hy => ?_, maps_stdLat_iff.1 fun y hy => ?_⟩
    · rw [← h]
      exact ⟨y, hy, rfl⟩
    · rw [← h] at hy
      exact mem_act.1 hy
  · rintro ⟨h1, h2⟩
    ext v
    rw [mem_act]
    refine ⟨fun hv => ?_, fun hv => maps_stdLat_iff.2 h2 v hv⟩
    simpa using maps_stdLat_iff.2 h1 _ hv

theorem nabs_det_eq_of_act_eq {g h : GL ι k} {L : Submodule 𝒪[k] (ι → k)} (hL : L.IsLattice k)
    (e : act g L = act h L) :
    nabs k (Matrix.GeneralLinearGroup.det g) = nabs k (Matrix.GeneralLinearGroup.det h) := by
  obtain ⟨u, rfl⟩ := exists_act_stdLat hL
  have h1 : act ((h * u)⁻¹ * (g * u)) (stdLat k ι) = stdLat k ι := by
    rw [act_mul, act_mul g, e, ← act_mul h, ← act_mul, inv_mul_cancel, act_one]
  have h2 := valuation_det_of_mem_KO (act_stdLat_eq_iff.1 h1)
  rw [nabs_eq_iff]
  have : Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det h *
      Matrix.GeneralLinearGroup.det ((h * u)⁻¹ * (g * u)) := by
    simp only [map_mul, map_inv]
    rw [_root_.mul_inv_rev, mul_comm (Matrix.GeneralLinearGroup.det g)]
    group
    rw [mul_comm (Matrix.GeneralLinearGroup.det h)]
    group
  rw [this, Units.val_mul, map_mul, h2, mul_one]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype ι] [DecidableEq ι] [DecidableEq ι'] in
open Classical in
theorem sph_apply (α : kˣ) (L' : Submodule 𝒪[k] (ι' → k)) (L : Submodule 𝒪[k] (ι → k)) (x : Matrix ι ι' k) :
    sph α L' L x = if ∀ v ∈ L', (((α⁻¹ : kˣ) : k) • x) *ᵥ v ∈ L then 1 else 0 := by
  unfold sph
  refine if_congr (forall₂_congr fun v _ => ?_) rfl rfl
  rw [Matrix.smul_mulVec]
  constructor
  · rintro ⟨w, hw, e⟩
    rw [e, smul_smul]
    simpa using hw
  · exact fun h => ⟨_, h, by simp [smul_smul]⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem sph_act (α : kˣ) (g' : GL ι' k) (g : GL ι k) (L' : Submodule 𝒪[k] (ι' → k)) (L : Submodule 𝒪[k] (ι → k))
    (x : Matrix ι ι' k) : sph α (act g' L') (act g L) x = sph α L' L ((g⁻¹).val * x * g'.val) := by
  classical
  rw [sph_apply, sph_apply]
  refine if_congr ?_ rfl rfl
  simp only [mem_act, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul]
  refine ⟨fun H y hy => H _ (by simpa using hy), fun H y hy => ?_⟩
  simpa using H _ hy

omit [DecidableEq ι] [DecidableEq ι'] in
open Classical in
theorem sph_stdLat (α : kˣ) (x : Matrix ι ι' k) :
    sph α (stdLat k ι') (stdLat k ι) x = if IntM (((α⁻¹ : kˣ) : k) • x) then 1 else 0 := by
  rw [sph_apply]
  exact if_congr maps_stdLat_iff rfl rfl

omit [DecidableEq ι] [DecidableEq ι'] in
theorem sph_mem_SB (α : kˣ) {L' : Submodule 𝒪[k] (ι' → k)} {L : Submodule 𝒪[k] (ι → k)} (h' : L'.IsLattice k)
    (h : L.IsLattice k) : sph α L' L ∈ SB (Matrix ι ι' k) := by
  classical
  have : sph α L' L = latInd L' (α • L) := by
    funext x
    rw [sph, latInd]
    refine if_congr (forall₂_congr fun v _ => ?_) rfl rfl
    refine Iff.trans ?_ (Submodule.mem_smul_pointwise_iff_exists _ α L).symm
    exact exists_congr fun w => and_congr_right' eq_comm
  rw [this]
  exact latInd_mem_SB _ _

theorem om_sph (μ : kˣ →* ℂˣ) (h : GL ι k) (α : kˣ) (L' : Submodule 𝒪[k] (ι' → k)) (L : Submodule 𝒪[k] (ι → k))
    (x : Matrix ι ι' k) : om μ 1 h (sph α L' L) x = (((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) *
      ((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card ι' : ℝ) / 2) : ℝ) : ℂ) * sph α L' (act h L) x := by
  conv_rhs => rw [← act_one L', sph_act]
  simp [om, nabs_one]

end Act

section Half

theorem resCard_pos : (0 : ℝ) < resCard k := by exact_mod_cast (one_lt_resCard k).trans' one_pos

theorem isHalfPow_one : IsHalfPow k 1 := ⟨0, by simp⟩

theorem isHalfPow_mul {a b : ℝ} (ha : IsHalfPow k a) (hb : IsHalfPow k b) : IsHalfPow k (a * b) := by
  obtain ⟨e, rfl⟩ := ha
  obtain ⟨f, rfl⟩ := hb
  exact ⟨e + f, by rw [← Real.rpow_add resCard_pos]; push_cast; ring_nf⟩

theorem isHalfPow_inv {a : ℝ} (ha : IsHalfPow k a) : IsHalfPow k a⁻¹ := by
  obtain ⟨e, rfl⟩ := ha
  exact ⟨-e, by rw [← Real.rpow_neg resCard_pos.le]; push_cast; ring_nf⟩

theorem isHalfPow_pow {a : ℝ} (ha : IsHalfPow k a) (m : ℕ) : IsHalfPow k (a ^ m) := by
  induction m with
  | zero => simpa using isHalfPow_one
  | succ m ih => rw [pow_succ]; exact isHalfPow_mul ih ha

theorem exists_nabs_eq_zpow (x : kˣ) : ∃ e : ℤ, nabs k x = (resCard k : ℝ) ^ e := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have key : ∀ x : kˣ, (x : k) ∈ 𝒪[k] → ∃ e : ℤ, nabs k x = (resCard k : ℝ) ^ e := fun x hx => by
    obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨x, hx⟩ : 𝒪[k])) (fun h => x.ne_zero (congrArg Subtype.val h)) hϖ
    have hu' : (x : k) = ((u : 𝒪[k]) : k) * (ϖ : k) ^ m := by simpa using congrArg Subtype.val hu
    have hv : valuation k ((u : 𝒪[k]) : k) = 1 :=
      (Valuation.Integers.valuation_unit (Valuation.integer.integers (valuation k)) u)
    have : nabs k x = nabs k (Units.mk0 (ϖ : k) h0 ^ m) := by
      rw [nabs_eq_iff, hu', map_mul, hv, one_mul]
      simp
    refine ⟨-m, ?_⟩
    rw [this, OpELevi.nabs_pow, nabs_uniformiser hϖ rfl]
    simp
  rcases le_total (valuation k (x : k)) 1 with h | h
  · exact key x h
  · obtain ⟨e, he⟩ := key x⁻¹ (by
      change valuation k _ ≤ 1
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_le_one_of_one_le₀ h)
    rw [OpELevi.nabs_inv] at he
    exact ⟨-e, by rw [_root_.zpow_neg, ← he, inv_inv]⟩

theorem isHalfPow_nabs_rpow (x : kˣ) (m : ℤ) : IsHalfPow k (nabs k x ^ ((m : ℝ) / 2)) := by
  obtain ⟨e, he⟩ := exists_nabs_eq_zpow x
  refine ⟨e * m, ?_⟩
  rw [he, ← Real.rpow_intCast, ← Real.rpow_mul resCard_pos.le]
  push_cast
  ring_nf

theorem isHalfPow_nabs (x : kˣ) : IsHalfPow k (nabs k x) := by
  simpa using isHalfPow_nabs_rpow x 2

end Half

end GlobalTheory.IdealChain
