import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RpowNegLeNormOfComponent

noncomputable section

namespace GlobalTheory.SatakeInv

open Matrix

variable {K : Type} [Field K] {r : ℕ}

def tinv : GL (Fin r) K →* GL (Fin r) K where
  toFun g := ⟨((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ, (g : Matrix (Fin r) (Fin r) K)ᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  map_one' := by ext i j; simp [Matrix.one_apply, eq_comm]
  map_mul' g h := by ext : 1; simp [_root_.mul_inv_rev, transpose_mul]

theorem tinv_val (g : GL (Fin r) K) :
    ((tinv g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ :=
  rfl

theorem tinv_inv_val (g : GL (Fin r) K) :
    (((tinv g)⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = (g : Matrix (Fin r) (Fin r) K)ᵀ :=
  rfl

theorem tinv_tinv (g : GL (Fin r) K) : tinv (tinv g) = g := by
  ext : 1
  rw [tinv_val, tinv_inv_val, transpose_transpose]

def scalGL (c : Kˣ) : GL (Fin r) K :=
  Units.map (Matrix.scalar (Fin r) : K →+* Matrix (Fin r) (Fin r) K).toMonoidHom c

theorem scalGL_val (c : Kˣ) :
    ((scalGL c : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = Matrix.scalar (Fin r) (c : K) := rfl

theorem scalGL_comm (c : Kˣ) (g : GL (Fin r) K) : scalGL c * g = g * scalGL c := by
  ext : 1
  simp only [Units.val_mul, scalGL_val]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _)

theorem tinv_scalGL (c : Kˣ) : tinv (scalGL c : GL (Fin r) K) = scalGL c⁻¹ := by
  ext : 1
  have h : (scalGL c : GL (Fin r) K)⁻¹ = scalGL c⁻¹ := (map_inv (Units.map (Matrix.scalar (Fin r) : K →+* Matrix (Fin r) (Fin r) K).toMonoidHom) c).symm
  rw [tinv_val, h, scalGL_val, Matrix.scalar_apply, Matrix.diagonal_transpose]

theorem tinv_scalGL' (c : Kˣ) : tinv (scalGL c : GL (Fin r) K) = (scalGL c)⁻¹ := by
  rw [tinv_scalGL]
  exact map_inv (Units.map (Matrix.scalar (Fin r) : K →+* Matrix (Fin r) (Fin r) K).toMonoidHom) c

theorem tinv_injective : Function.Injective (tinv : GL (Fin r) K → GL (Fin r) K) := fun a b h => by
  rw [← tinv_tinv a, h, tinv_tinv]

omit [Field K] in

theorem glMap_eq_glMap_iff {O : Type} [CommRing O] [Field K] [Algebra O K] (a b : GL (Fin r) K)
    (L : Submodule O (Fin r → K)) :
    GlobalTheory.LatHecke.glMap a L = GlobalTheory.LatHecke.glMap b L ↔ GlobalTheory.LatHecke.glMap (a⁻¹ * b) L = L := by
  constructor
  · intro h
    rw [GlobalTheory.LatHecke.glMap_mul, ← h, ← GlobalTheory.LatHecke.glMap_mul, inv_mul_cancel, GlobalTheory.LatHecke.glMap_one]
  · intro h
    conv_lhs => rw [← h, ← GlobalTheory.LatHecke.glMap_mul, mul_inv_cancel_left]

theorem esymm_inv_mul_esymm_card (β : Multiset ℂ) (hβ : ∀ b ∈ β, b ≠ 0) {k : ℕ} (hk : k ≤ β.card) :
    (β.map (·⁻¹)).esymm k * β.esymm β.card = β.esymm (β.card - k) := by
  obtain ⟨n, α, rfl⟩ : ∃ (n : ℕ) (α : Fin n → ℂ), β = Finset.univ.val.map α := by
    induction β using Quotient.inductionOn with
    | h l => exact ⟨l.length, l.get, by simp⟩
  have hα : ∀ i, α i ≠ 0 := fun i => hβ _ (Multiset.mem_map_of_mem _ (Finset.mem_univ_val i))
  have hn : (Finset.univ.val.map α).card = n := by simp
  rw [hn] at hk ⊢
  simp only [Multiset.map_map, Finset.esymm_map_val, Function.comp_def]
  have h1 : Finset.powersetCard n (Finset.univ : Finset (Fin n)) = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  rw [h1, Finset.sum_singleton, Finset.sum_mul]
  refine Finset.sum_nbij' compl compl (fun t ht => ?_) (fun t ht => ?_) (by simp) (by simp) fun t _ => ?_
  · simp only [Finset.mem_powersetCard_univ] at ht ⊢
    simp [Finset.card_compl, ht]
  · simp only [Finset.mem_powersetCard_univ] at ht ⊢
    rw [Finset.card_compl, ht, Fintype.card_fin]; omega
  · rw [← Finset.prod_mul_prod_compl t, ← mul_assoc, ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl (fun i _ => inv_mul_cancel₀ (hα i)), Finset.prod_const_one, one_mul]

end GlobalTheory.SatakeInv
