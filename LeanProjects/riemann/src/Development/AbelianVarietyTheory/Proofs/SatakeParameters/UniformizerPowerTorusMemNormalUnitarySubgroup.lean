import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeB
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
open Formalism.UG Matrix

noncomputable section

namespace GlobalTheory.TorusNormal

open Formalism.UG.P

variable {L : Type} [Field L]

def pm {n : ℕ} (f g : Fin n → L) : Matrix (Fin n) (Fin n) L :=
  Matrix.of fun i j => (if j = i then f i else 0) + (if j = Fin.rev i then g i else 0)

theorem pm_mul {n : ℕ} (f g f' g' : Fin n → L) :
    pm f g * pm f' g' = pm (fun i => f i * f' i + g i * g' (Fin.rev i))
      (fun i => f i * g' i + g i * f' (Fin.rev i)) := by
  ext i k
  simp only [pm, Matrix.mul_apply, Matrix.of_apply, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  by_cases h1 : k = i <;> by_cases h2 : k = Fin.rev i <;> simp [h1, h2] <;>
    by_cases h3 : i = Fin.rev i <;>
    first
    | (simp only [if_pos h3, if_pos h3.symm]; ring)
    | (simp only [if_neg h3, if_neg (Ne.symm h3)]; ring)

theorem cT_pm {n : ℕ} (σ : L →+* L) (f g : Fin n → L) :
    cT σ (pm f g) = pm (fun i => σ (f i)) (fun i => σ (g (Fin.rev i))) := by
  ext i j
  simp only [cT, pm, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, map_add]
  have h2 : (i = Fin.rev j) ↔ (j = Fin.rev i) := by
    constructor <;> rintro rfl <;> simp
  by_cases h1 : j = i
  · subst h1; by_cases h3 : j = Fin.rev j
    · rw [if_pos rfl, if_pos rfl, if_pos h3, if_pos h3, ← h3]
    · rw [if_pos rfl, if_pos rfl, if_neg h3, if_neg h3, map_zero]
  · rw [if_neg (Ne.symm h1), if_neg h1, map_zero]
    by_cases h3 : j = Fin.rev i
    · rw [if_pos (h2.2 h3), if_pos h3, h3]
    · rw [if_neg (fun h => h3 (h2.1 h)), if_neg h3, map_zero]

theorem antiJ_pm {n : ℕ} : antiJ L n = pm 0 1 := by
  ext i j
  rw [fIwasawa_antiJ]
  simp [pm]

end GlobalTheory.TorusNormal

namespace GlobalTheory.TorusNormal

open Formalism.UG.P

variable {L : Type} [Field L]

theorem pm_supp_mul {n : ℕ} (u : Fin n → L) (hsupp : ∀ i, u i ≠ 0 → 2 * i.val + 1 < n) (i : Fin n) :
    u (Fin.rev i) * u i = 0 := by
  by_contra h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  have a := hsupp _ h1
  have b := hsupp _ h2
  rw [Fin.val_rev] at a
  omega

theorem un_pm {n : ℕ} (σ : L →+* L) (u : Fin n → L) (hσ : ∀ i, σ (u i) = -u i)
    (hsupp : ∀ i, u i ≠ 0 → 2 * i.val + 1 < n) : fIwasawaUn σ (pm 1 u) := by
  unfold fIwasawaUn
  rw [cT_pm, antiJ_pm, pm_mul, pm_mul]
  congr 1 <;> funext i
  · simp [hσ]
  · simp [hσ, pm_supp_mul u hsupp i]

theorem unip_pm {n : ℕ} (σ : L →+* L) (u : Fin n → L) (h : fIwasawaUn σ (pm 1 u))
    (hsupp : ∀ i, u i ≠ 0 → 2 * i.val + 1 < n) : IsUnipU (fIwasawaMk σ (pm 1 u) h) := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [fIwasawa_mk_val]
    simp only [pm, Matrix.of_apply, Pi.one_apply]
    rw [if_neg (ne_of_lt hji), zero_add]
    split_ifs with h1
    · by_contra hu
      have := hsupp i hu
      subst h1
      rw [Fin.lt_def, Fin.val_rev] at hji
      omega
    · rfl
  · rw [fIwasawa_mk_val]
    simp only [pm, Matrix.of_apply, Pi.one_apply]
    rw [if_pos trivial]
    split_ifs with h1
    · have : u i = 0 := by
        by_contra hu
        have := hsupp i hu
        have h' := congrArg Fin.val h1
        rw [Fin.val_rev] at h'
        omega
      rw [this, add_zero]
    · rw [add_zero]

theorem diagonal_pm {n : ℕ} (d : Fin n → L) : Matrix.diagonal d = pm d 0 := by
  ext i j
  simp only [Matrix.diagonal_apply, pm, Matrix.of_apply, Pi.zero_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]; simp

end GlobalTheory.TorusNormal

namespace GlobalTheory.TorusNormal

open Formalism.UG.P

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem idx_cases {n : ℕ} (i : Fin n) :
    (2 * i.val + 1 < n ∧ ¬ 2 * (Fin.rev i).val + 1 < n) ∨
    (¬ 2 * i.val + 1 < n ∧ 2 * (Fin.rev i).val + 1 < n) ∨
    (¬ 2 * i.val + 1 < n ∧ ¬ 2 * (Fin.rev i).val + 1 < n ∧ Fin.rev i = i) := by
  have := i.isLt
  rw [Fin.val_rev]
  by_cases h : 2 * i.val + 1 < n
  · left; omega
  · right
    by_cases h' : 2 * (n - (i.val + 1)) + 1 < n
    · left; omega
    · right; refine ⟨h, h', ?_⟩
      rw [Fin.ext_iff, Fin.val_rev]; omega

theorem exists_mem_pm (σ : L →+* L) {n : ℕ} (hσv : ∀ x, Valued.v (σ x) = Valued.v x)
    (N : Subgroup (GU σ n)) (hK : KU σ n ≤ N) (hU : ∀ u : GU σ n, IsUnipU u → u ∈ N)
    (y : Fin n → L) (hy0 : ∀ i, y i ≠ 0) (hyσ : ∀ i, σ (y i) = -y i) :
    ∃ g ∈ N, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      pm (fun i => if 2 * i.val + 1 < n ∨ 2 * (Fin.rev i).val + 1 < n then 0 else 1)
        (fun i => (if 2 * i.val + 1 < n then y i else 0) +
          (if 2 * (Fin.rev i).val + 1 < n then -(y (Fin.rev i))⁻¹ else 0)) := by
  set u : Fin n → L := fun i => if 2 * i.val + 1 < n then y i else 0 with hu
  set l : Fin n → L := fun i => if 2 * i.val + 1 < n then -(y i)⁻¹ else 0 with hl
  have hu1 : ∀ i, σ (u i) = -u i := by
    intro i; simp only [hu]; split_ifs <;> simp [hyσ]
  have hu2 : ∀ i, u i ≠ 0 → 2 * i.val + 1 < n := by
    intro i h; simp only [hu] at h; split_ifs at h with h'
    · exact h'
    · exact absurd rfl h
  have hl1 : ∀ i, σ (l i) = -l i := by
    intro i; simp only [hl]; split_ifs <;> simp [hyσ, map_inv₀, inv_neg]
  have hl2 : ∀ i, l i ≠ 0 → 2 * i.val + 1 < n := by
    intro i h; simp only [hl] at h; split_ifs at h with h'
    · exact h'
    · exact absurd rfl h
  have hW : fIwasawaUn σ (antiJ L n) := by
    unfold fIwasawaUn
    rw [antiJ_pm, cT_pm, pm_mul, pm_mul]
    congr 1 <;> funext i <;> simp
  have hWK : fIwasawaMk σ _ hW ∈ KU σ n := by
    refine fIwasawa_mk_mem_K σ hσv _ hW fun i j => ?_
    rw [fIwasawa_antiJ]
    split_ifs <;> simp
  have hA := hU _ (unip_pm σ u (un_pm σ u hu1 hu2) hu2)
  have hB := hU _ (unip_pm σ l (un_pm σ l hl1 hl2) hl2)
  refine ⟨fIwasawaMk σ _ (un_pm σ u hu1 hu2) * fIwasawaMk σ _ hW * fIwasawaMk σ _ (un_pm σ l hl1 hl2) *
    fIwasawaMk σ _ hW * fIwasawaMk σ _ (un_pm σ u hu1 hu2),
    mul_mem (mul_mem (mul_mem (mul_mem hA (hK hWK)) hB) (hK hWK)) hA, ?_⟩
  simp only [Subgroup.coe_mul, Units.val_mul, fIwasawa_mk_val]
  rw [antiJ_pm, pm_mul, pm_mul, pm_mul, pm_mul]
  congr 1 <;> funext i <;>
    rcases idx_cases i with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ <;>
    simp only [Fin.val_rev] at h1 h2 <;>
    simp [hu, hl, h1, h2, Fin.rev_rev, hy0]

end GlobalTheory.TorusNormal

namespace GlobalTheory

open Formalism.UG.P GlobalTheory.TorusNormal

theorem torus_mem_normal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ N : Subgroup (Formalism.UG.GU σ n), N.Normal →
    Formalism.UG.KU σ n ≤ N → (∀ u : Formalism.UG.GU σ n, Formalism.UG.IsUnipU u → u ∈ N) → ∀ (c : Fin n → ℤ),
    (∀ i : Fin n, c i.rev = -c i) → ∀ t : Formalism.UG.GU σ n,
    ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => ϖ ^ c i) → t ∈ N := by
  intro L _ _ ϖ σ q n hU N _ hK hUn c hc t ht
  obtain ⟨hσσ, hσv, hσϖ, hvϖ, ⟨x, -, hx⟩, -⟩ := hU
  set δ := σ x - x with hδ
  have hδ0 : δ ≠ 0 := by
    intro h; rw [h, map_zero] at hx; exact zero_ne_one hx
  have hδσ : σ δ = -δ := by
    rw [hδ, map_sub, hσσ]; ring
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  obtain ⟨g0, hg0, e0⟩ := exists_mem_pm σ hσv N hK hUn (fun _ => δ) (fun _ => hδ0) (fun _ => hδσ)
  obtain ⟨g1, hg1, e1⟩ := exists_mem_pm σ hσv N hK hUn (fun i => ϖ ^ c i * δ)
    (fun i => mul_ne_zero (zpow_ne_zero _ hϖ0) hδ0)
    (fun i => by rw [map_mul, map_zpow₀, hσϖ, hδσ, mul_neg])
  have key : t * g0 = g1 := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [ht, e0, e1, diagonal_pm, pm_mul]
    congr 1 <;> funext i <;>
      rcases idx_cases i with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · simp only [Fin.val_rev] at h1 h2; simp [h1, h2]
    · simp only [Fin.val_rev] at h1 h2; simp [h1, h2]
    · have hc0 : c i = 0 := by have := hc i; rw [h3] at this; omega
      simp only [Fin.val_rev] at h1 h2; simp [h1, h2, hc0]
    · simp only [Fin.val_rev] at h1 h2; simp [h1, h2]
    · simp only [Fin.val_rev] at h1 h2
      simp [h1, h2, hc i, _root_.zpow_neg]
      ring
    · simp only [Fin.val_rev] at h1 h2; simp [h1, h2]
  rw [eq_mul_inv_of_mul_eq key]
  exact mul_mem hg1 (inv_mem hg0)

end GlobalTheory
