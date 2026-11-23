import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.JPred
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialOfConjTorus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermEqOneOfMonomialMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowUnifLeOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupBasisNhds

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
open GlobalTheory.CompanionTheory.LbElem.ConjMonomial GlobalTheory.CompanionTheory.LbElem.MonomialInJ GlobalTheory.CompanionTheory.LbElem.IwahoriLDU

namespace GlobalTheory.CompanionTheory.LbElem.JPredDom

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem entry_diag_mul {N : ℕ} {a b : GL (Fin N) k} (n : GL (Fin N) k) {α β : Fin N → k}
    (ha : (a : Matrix (Fin N) (Fin N) k) = Matrix.diagonal α)
    (hb : (b : Matrix (Fin N) (Fin N) k) = Matrix.diagonal β) (i j : Fin N) :
    ((a * n * b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      α i * (n : Matrix (Fin N) (Fin N) k) i j * β j := by
  rw [Units.val_mul, Units.val_mul, ha, hb, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem diag_ne_zero {N : ℕ} {x : GL (Fin N) k} {d : Fin N → k}
    (hx : (x : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d) (i : Fin N) : d i ≠ 0 := by
  have h := diag_ne_zero_of_offDiag x (fun i j hij => by rw [hx, Matrix.diagonal_apply_ne _ hij]) i
  rwa [hx, Matrix.diagonal_apply_eq] at h

theorem val_inv_diag {N : ℕ} {x : GL (Fin N) k} {d : Fin N → k}
    (hx : (x : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d) :
    ((x⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = Matrix.diagonal fun i => (d i)⁻¹ := by
  have h1 : (x : Matrix (Fin N) (Fin N) k) * Matrix.diagonal (fun i => (d i)⁻¹) = 1 := by
    rw [hx, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (diag_ne_zero hx i)
  calc ((x⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
      = ((x⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *
          ((x : Matrix (Fin N) (Fin N) k) * Matrix.diagonal (fun i => (d i)⁻¹)) := by rw [h1, mul_one]
    _ = Matrix.diagonal fun i => (d i)⁻¹ := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem val_pow_diag {N : ℕ} {x : GL (Fin N) k} {d : Fin N → k}
    (hx : (x : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d) (r : ℕ) :
    ((x ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = Matrix.diagonal fun i => d i ^ r := by
  rw [Units.val_pow_eq_pow_val, hx, Matrix.diagonal_pow]
  rfl

theorem val_conj_up (a b c : k) (r : ℕ) :
    valuation k (a ^ r * c * (b ^ r)⁻¹) = (valuation k a / valuation k b) ^ r * valuation k c := by
  rw [map_mul, map_mul, map_inv₀, map_pow, map_pow, div_pow, div_eq_mul_inv, mul_right_comm]

theorem val_conj_lo (a b c : k) (r : ℕ) :
    valuation k ((b ^ r)⁻¹ * c * a ^ r) = (valuation k a / valuation k b) ^ r * valuation k c := by
  rw [← val_conj_up]
  congr 1
  ring

theorem up_entries {N : ℕ} {t n : GL (Fin N) k} {d : Fin N → k}
    (ht : (t : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d)
    (h0 : ∀ i j : Fin N, j < i → (n : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i : Fin N, (n : Matrix (Fin N) (Fin N) k) i i = 1) (r : ℕ) :
    (∀ i j : Fin N, j < i → ((t ^ r * n * (t ^ r)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = 0) ∧
    (∀ i : Fin N, ((t ^ r * n * (t ^ r)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i i = 1) ∧
    ∀ i j : Fin N, valuation k (((t ^ r * n * (t ^ r)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) =
      (valuation k (d i) / valuation k (d j)) ^ r * valuation k ((n : Matrix (Fin N) (Fin N) k) i j) := by
  have hp := val_pow_diag ht r
  have hq := val_inv_diag hp
  have he := entry_diag_mul n hp hq
  refine ⟨fun i j hij => ?_, fun i => ?_, fun i j => ?_⟩
  · rw [he, h0 i j hij, mul_zero, zero_mul]
  · rw [he, h1, mul_one]
    exact mul_inv_cancel₀ (pow_ne_zero _ (diag_ne_zero ht i))
  · rw [he]
    exact val_conj_up _ _ _ r

theorem lo_entries {N : ℕ} {t n : GL (Fin N) k} {d : Fin N → k}
    (ht : (t : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d)
    (h0 : ∀ i j : Fin N, i < j → (n : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i : Fin N, (n : Matrix (Fin N) (Fin N) k) i i = 1) (r : ℕ) :
    (∀ i j : Fin N, i < j → (((t ^ r)⁻¹ * n * t ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = 0) ∧
    (∀ i : Fin N, (((t ^ r)⁻¹ * n * t ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i i = 1) ∧
    ∀ i j : Fin N, valuation k ((((t ^ r)⁻¹ * n * t ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) =
      (valuation k (d j) / valuation k (d i)) ^ r * valuation k ((n : Matrix (Fin N) (Fin N) k) i j) := by
  have hp := val_pow_diag ht r
  have hq := val_inv_diag hp
  have he := entry_diag_mul n hq hp
  refine ⟨fun i j hij => ?_, fun i => ?_, fun i j => ?_⟩
  · rw [he, h0 i j hij, mul_zero, zero_mul]
  · rw [he, h1, mul_one]
    exact inv_mul_cancel₀ (pow_ne_zero _ (diag_ne_zero ht i))
  · rw [he]
    exact val_conj_lo _ _ _ r

theorem ratio_lt_one {a b : ValueGroupWithZero k} (h : a < b) : a / b < 1 :=
  (div_lt_one₀ (lt_of_le_of_lt zero_le' h)).2 h

theorem exists_contract {N : ℕ} {d : Fin N → k} (hd : ∀ i, d i ≠ 0)
    (hinc : ∀ i j : Fin N, i < j → valuation k (d i) < valuation k (d j))
    {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) :
    ∃ r : ℕ, ∀ i j : Fin N, i < j → (valuation k (d i) / valuation k (d j)) ^ r < γ := by
  classical
  have h : ∀ p : Fin N × Fin N, ∃ r : ℕ, p.1 < p.2 → ∀ r' : ℕ, r ≤ r' →
      (valuation k (d p.1) / valuation k (d p.2)) ^ r' < γ := by
    intro p
    by_cases hp : p.1 < p.2
    · have h1 := ratio_lt_one (hinc _ _ hp)
      have h2 : valuation k (d p.1) / valuation k (d p.2) ≠ 0 :=
        div_ne_zero ((Valuation.ne_zero_iff _).2 (hd _)) ((Valuation.ne_zero_iff _).2 (hd _))
      obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.CongruenceBasis.exists_pow_succ_lt h2 h1 hγ
      exact ⟨m + 1, fun _ r' hr' => lt_of_le_of_lt (pow_le_pow_of_le_one zero_le' h1.le hr') hm⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose f hf using h
  exact ⟨Finset.univ.sup f, fun i j hij => hf (i, j) hij _ (Finset.le_sup (Finset.mem_univ _))⟩

theorem levi_comm {N : ℕ} (s x : Levi k (Bl (ones N))) : s * x = x * s := by
  funext a
  haveI : Subsingleton (Fin (ones N a)) := by
    show Subsingleton (Fin 1)
    infer_instance
  apply Units.ext
  ext i j
  obtain rfl : i = j := Subsingleton.elim i j
  simp only [Units.val_mul, Matrix.mul_apply, Pi.mul_apply]
  rw [Fintype.sum_subsingleton _ i, Fintype.sum_subsingleton _ i, mul_comm]

theorem torEmb_diag {N : ℕ} (s : Levi k (Bl (ones N))) :
    ((torEmb k N s : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => ((torEmb k N s : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i i := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ h]
    exact tor_offDiag (⟨s, rfl⟩ : torEmb k N s ∈ Tor k N) h

theorem sub_one_le {N : ℕ} {x : GL (Fin N) k} {γ : ValueGroupWithZero k}
    (h1 : ∀ i, (x : Matrix (Fin N) (Fin N) k) i i = 1)
    (h2 : ∀ i j, i ≠ j → valuation k ((x : Matrix (Fin N) (Fin N) k) i j) ≤ γ) (i j : Fin N) :
    valuation k ((x : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ γ := by
  by_cases h : i = j
  · subst h
    rw [h1, Matrix.one_apply_eq, sub_self, map_zero]
    exact zero_le'
  · rw [Matrix.one_apply_ne h, sub_zero]
    exact h2 i j h

theorem exists_value_subset {N : ℕ} {U : Set (GL (Fin N) k)} (hU : IsOpen U) (h1 : (1 : GL (Fin N) k) ∈ U) :
    ∃ γ : ValueGroupWithZero k, γ ≠ 0 ∧ ∀ g : GL (Fin N) k, (∀ i j,
      valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ γ) → g ∈ U := by
  have hne : algebraMap 𝒪[k] k (Zls.unif k) ≠ 0 :=
    (map_ne_zero_iff (algebraMap 𝒪[k] k) (IsFractionRing.injective 𝒪[k] k)).2 Zls.irreducible_unif.ne_zero
  obtain ⟨M, -, hsub⟩ := GlobalTheory.CompanionTheory.CongruenceBasis.exists_congruence_subset k N _ hne
    GlobalTheory.CompanionTheory.CongruenceBasis.val_unif_lt_one GlobalTheory.CompanionTheory.CongruenceBasis.val_le_val_unif U (hU.mem_nhds h1)
  exact ⟨_, (Valuation.ne_zero_iff _).2 (pow_ne_zero M hne), fun g hg => hsub hg⟩

end GlobalTheory.CompanionTheory.LbElem.JPredDom

end
