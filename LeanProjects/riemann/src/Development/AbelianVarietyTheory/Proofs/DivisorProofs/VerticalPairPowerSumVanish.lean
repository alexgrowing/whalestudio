import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData
open scoped Pointwise

noncomputable section
namespace GlobalTheory.CentreCpt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem val_eq_one_of_pow_eq_one (hN : N ≠ 0) {x : ValueGroupWithZero k} (h : x ^ N = 1) : x = 1 := by
  rcases lt_trichotomy x 1 with h1 | h1 | h1
  · exact absurd h (pow_lt_one₀ zero_le' h1 hN).ne
  · exact h1
  · exact absurd h (one_lt_pow₀ h1 hN).ne'

theorem mem_KO_of_mem_center {w : GL (Fin N) k} (hw : w ∈ Subgroup.center (GL (Fin N) k))
    (hv : valuation k (w : Matrix (Fin N) (Fin N) k).det = 1) : w ∈ KO k (Fin N) := by
  rw [GeneralLinearGroup.center_eq_range_scalar] at hw
  obtain ⟨a, rfl⟩ := hw
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [GlobalTheory.SplitFlip.mem_KO_iff]; exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  have hdet : ((GeneralLinearGroup.scalar (Fin N) a : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det =
      (a : k) ^ N := by
    simp [Matrix.det_diagonal]
  rw [hdet, map_pow] at hv
  have ha : valuation k (a : k) = 1 := val_eq_one_of_pow_eq_one hN.ne' hv
  have hai : valuation k ((a⁻¹ : kˣ) : k) = 1 := by simp [ha]
  have ent : ∀ b : kˣ, valuation k (b : k) = 1 → ∀ i j : Fin N,
      ((GeneralLinearGroup.scalar (Fin N) b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] := by
    intro b hb i j
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact (Valuation.mem_integer_iff _ _).2 hb.le
    · exact zero_mem _
  rw [GlobalTheory.SplitFlip.mem_KO_iff, ← map_inv]
  exact ⟨ent a ha, ent a⁻¹ hai⟩

def vdet (k : Type) [Field k] [ValuativeRel k] (N : ℕ) : GL (Fin N) k →* ValueGroupWithZero k :=
  (valuation k).toMonoidWithZeroHom.toMonoidHom.comp ((Units.coeHom k).comp GeneralLinearGroup.det)

theorem vdet_apply (g : GL (Fin N) k) : vdet k N g = valuation k (g : Matrix (Fin N) (Fin N) k).det := rfl

theorem vdet_eq_one_of_mem_KO {g : GL (Fin N) k} (hg : g ∈ KO k (Fin N)) : vdet k N g = 1 := by
  have hle : ∀ h ∈ KO k (Fin N), vdet k N h ≤ 1 := by
    rintro _ ⟨u, rfl⟩
    rw [vdet_apply]
    change valuation k ((algebraMap 𝒪[k] k).mapMatrix (u : Matrix (Fin N) (Fin N) 𝒪[k])).det ≤ 1
    rw [← RingHom.map_det]
    exact ((Valuation.mem_integer_iff _ _).1 (u.val.det).2)
  have h1 := hle g hg
  have h2 := hle g⁻¹ (inv_mem hg)
  have h3 : vdet k N g * vdet k N g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  refine le_antisymm h1 ?_
  calc (1 : ValueGroupWithZero k) = vdet k N g * vdet k N g⁻¹ := h3.symm
    _ ≤ vdet k N g * 1 := by gcongr
    _ = vdet k N g := mul_one _

theorem exists_compact_center_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (C : Set (GL (Fin N) k)), IsCompact C →
    ∃ D : Set (GL (Fin N) k), IsCompact D ∧ ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ c ∈ C,
      ValuativeRel.valuation k ((z * c : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det = 1 → z * c ∈ D := by
  intro k _ _ _ _ N C hC
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun c : GL (Fin N) k => c • (KO k (Fin N) : Set (GL (Fin N) k)))
    (fun c => GlobalTheory.SplitFlip.isOpen_KO.smul c)
    (fun c _ => Set.mem_iUnion.2 ⟨c, 1, one_mem _, mul_one c⟩)
  let f : GL (Fin N) k → GL (Fin N) k := fun i =>
    if h : ∃ z ∈ Subgroup.center (GL (Fin N) k), vdet k N (z * i) = 1 then h.choose * i else 1
  refine ⟨⋃ i ∈ t, f i • (KO k (Fin N) : Set (GL (Fin N) k)),
    t.isCompact_biUnion fun i _ => GlobalTheory.SplitFlip.isCompact_KO.smul (f i), ?_⟩
  intro z hz c hc hzc
  rw [← vdet_apply] at hzc
  obtain ⟨i, hi, hci⟩ := Set.mem_iUnion₂.1 (ht hc)
  obtain ⟨κ, hκ, rfl⟩ := hci
  change z * (i * κ) ∈ _
  change vdet k N (z * (i * κ)) = 1 at hzc
  have hvκ := vdet_eq_one_of_mem_KO hκ
  have hzi : vdet k N (z * i) = 1 :=
    calc vdet k N (z * i) = vdet k N (z * i) * vdet k N κ := by rw [hvκ, mul_one]
      _ = 1 := by rw [← map_mul, mul_assoc, hzc]
  have hex : ∃ z ∈ Subgroup.center (GL (Fin N) k), vdet k N (z * i) = 1 := ⟨z, hz, hzi⟩
  have hfi : f i = hex.choose * i := dif_pos hex
  obtain ⟨hzc', hv'⟩ := hex.choose_spec
  set zi := hex.choose
  set w := z * zi⁻¹ with hw
  have hwc : w ∈ Subgroup.center (GL (Fin N) k) := mul_mem hz (inv_mem hzc')
  have hwv : vdet k N w = 1 :=
    calc vdet k N w = vdet k N w * vdet k N (zi * i) := by rw [hv', mul_one]
      _ = vdet k N (z * i) := by rw [← map_mul, ← mul_assoc, hw, inv_mul_cancel_right]
      _ = 1 := hzi
  have hwK : w ∈ KO k (Fin N) := mem_KO_of_mem_center hwc (by rw [← vdet_apply]; exact hwv)
  refine Set.mem_iUnion₂.2 ⟨i, hi, ?_⟩
  rw [hfi]
  refine ⟨w * κ, mul_mem hwK hκ, ?_⟩
  have hz' : z = w * zi := by rw [hw, inv_mul_cancel_right]
  have hcomm := Subgroup.mem_center_iff.1 hwc
  change zi * i * (w * κ) = z * (i * κ)
  rw [hz', ← mul_assoc, hcomm (zi * i)]
  simp only [mul_assoc]

end GlobalTheory.CentreCpt
