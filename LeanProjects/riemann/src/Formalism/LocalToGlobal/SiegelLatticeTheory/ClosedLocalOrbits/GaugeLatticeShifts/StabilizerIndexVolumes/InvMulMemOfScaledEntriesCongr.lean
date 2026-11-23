import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StClosed

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem inv_mul_mem_of_scaled_entries_congr (W : Matrix (Fin n) (Fin n) E) (H K : Subgroup (Matrix.GeneralLinearGroup (Fin n) E))
    (hHS : (H : Set (Matrix.GeneralLinearGroup (Fin n) E)) ⊆ StSet W) (N0 : ℕ) (hN0 : N0 ≠ 0)
    (hbd : ∀ h ∈ H, ∀ i j, IntE ((N0 : E) * (h : Matrix (Fin n) (Fin n) E) i j)) (N1 : ℕ) (hN1 : N1 ≠ 0)
    (hcg : ∀ a : Matrix.GeneralLinearGroup (Fin n) E, a ∈ StSet W →
      (∀ i j, IntE (((a : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) / (N1 : E))) → a ∈ K)
    (h1 h2 : Matrix.GeneralLinearGroup (Fin n) E) (hh1 : h1 ∈ H) (hh2 : h2 ∈ H)
    (c : Fin n → Fin n → 𝓞 E)
    (hc : ∀ k j, ((c k j : 𝓞 E) : E) * ((N0 * N0 * N1 : ℕ) : E) =
      (N0 : E) * (h2 : Matrix (Fin n) (Fin n) E) k j - (N0 : E) * (h1 : Matrix (Fin n) (Fin n) E) k j) :
    h1⁻¹ * h2 ∈ K := by
  have hN0E : (N0 : E) ≠ 0 := by exact_mod_cast hN0
  have hN1E : (N1 : E) ≠ 0 := by exact_mod_cast hN1
  apply hcg _ (hHS (H.mul_mem (H.inv_mem hh1) hh2))
  intro i j
  have hinv := hbd _ (H.inv_mem hh1)
  choose p hp using hinv
  refine ⟨∑ k, p i k * c k j, ?_⟩
  have hsub : ((h1⁻¹ * h2 : Matrix.GeneralLinearGroup (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1 =
      ((h1⁻¹ : Matrix.GeneralLinearGroup (Fin n) E) : Matrix (Fin n) (Fin n) E) *
        ((h2 : Matrix (Fin n) (Fin n) E) - (h1 : Matrix (Fin n) (Fin n) E)) := by
    rw [Matrix.mul_sub, Units.val_mul, Units.inv_mul]
  have hent := congrFun (congrFun hsub i) j
  rw [Matrix.sub_apply] at hent
  have hcast : ((∑ k, p i k * c k j : 𝓞 E) : E) = ∑ k, (p i k : E) * (c k j : E) := by push_cast; rfl
  rw [hent, Matrix.mul_apply, Finset.sum_div, hcast]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hpk := hp i k
  have hck := hc k j
  push_cast at hck
  have hX : ((h1⁻¹ : Matrix.GeneralLinearGroup (Fin n) E) : Matrix (Fin n) (Fin n) E) i k =
      (p i k : E) / N0 := by
    rw [hpk]; field_simp
  have hD : (h2 : Matrix (Fin n) (Fin n) E) k j - (h1 : Matrix (Fin n) (Fin n) E) k j =
      (c k j : E) * (N0 * N1) := by
    have : (N0 : E) * ((h2 : Matrix (Fin n) (Fin n) E) k j - (h1 : Matrix (Fin n) (Fin n) E) k j) =
        (N0 : E) * ((c k j : E) * (N0 * N1)) := by rw [mul_sub, ← hck]; ring
    exact mul_left_cancel₀ hN0E this
  rw [hX, Matrix.sub_apply, hD]
  field_simp

theorem commens : Commens := by
  intro E _ _ n W H K hHS ⟨N0, hN0, hbd⟩ ⟨N1, hN1, hcg⟩
  have hM0 : ((N0 * N0 * N1 : ℕ) : 𝓞 E) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (Nat.mul_ne_zero hN0 hN0) hN1)
  have hI : Ideal.span {((N0 * N0 * N1 : ℕ) : 𝓞 E)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hM0
  have : Finite (𝓞 E ⧸ Ideal.span {((N0 * N0 * N1 : ℕ) : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ hI
  choose o ho using hbd
  let φ : H → Fin n → Fin n → 𝓞 E ⧸ Ideal.span {((N0 * N0 * N1 : ℕ) : 𝓞 E)} :=
    fun h i j => Ideal.Quotient.mk _ (o h h.2 i j)
  have key : ∀ h1 h2 : H, φ h1 = φ h2 → h1⁻¹ * h2 ∈ K.subgroupOf H := by
    intro h1 h2 hq
    have hc : ∀ k j, ∃ c : 𝓞 E, c * ((N0 * N0 * N1 : ℕ) : 𝓞 E) = o h2 h2.2 k j - o h1 h1.2 k j := by
      intro k j
      have := congrFun (congrFun hq k) j
      simp only [φ] at this
      exact Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp this.symm)
    choose c hc using hc
    rw [Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine inv_mul_mem_of_scaled_entries_congr W H K hHS N0 hN0 (fun h hh i j => ⟨o h hh i j, ho h hh i j⟩) N1 hN1 hcg _ _ h1.2 h2.2 c
      fun k j => ?_
    have h3 := congrArg (fun x : 𝓞 E => (x : E)) (hc k j)
    have e1 : ((c k j * ((N0 * N0 * N1 : ℕ) : 𝓞 E) : 𝓞 E) : E) = (c k j : E) * ((N0 * N0 * N1 : ℕ) : E) := by
      push_cast; rfl
    have e2 : ((o h2 h2.2 k j - o h1 h1.2 k j : 𝓞 E) : E) = (o h2 h2.2 k j : E) - (o h1 h1.2 k j : E) := by
      push_cast; rfl
    rw [← e1, h3, e2, ho, ho]
  have : Finite (H ⧸ K.subgroupOf H) := by
    refine Finite.of_injective (fun q : H ⧸ K.subgroupOf H => φ (Quotient.out q)) ?_
    intro q1 q2 hq
    have := (QuotientGroup.eq (s := K.subgroupOf H)).mpr (key _ _ hq)
    simpa [QuotientGroup.out_eq'] using this
  exact Subgroup.index_ne_zero_of_finite

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
