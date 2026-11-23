import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.GlobalDual

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem pre_rowvec (Λ : Submodule (𝓞 E) S.V) (hint : IntLat Λ) (Tn : ℕ) (F : LFlag S r ((Tn : ℕ) : E))
    (hz : F.fl.z ∈ Λ) (g : 𝓞 E)
    (hdual : ∀ c : Fin r, ∃ y ∈ Λ, (∀ i, i ≠ c → S.hT y (F.fl.e i) = 0) ∧
      ∃ q : 𝓞 E, S.hT y (F.fl.e c) = ((1 + g * q : 𝓞 E) : E))
    (hTg : ∃ x y : 𝓞 E, x * (Tn : 𝓞 E) + y * g = 1) (a : Fin r) (t : Fin (r + 1) → 𝓞 E) :
    ∃ v ∈ Λ, (∀ i, i ≤ a → S.hT v (F.fl.e i) = 0) ∧
      ∀ c, Fin.castSucc a < c → ∃ q : 𝓞 E, S.hT v (frame F c) = ((t c + g * q : 𝓞 E) : E) := by
  choose y hy h0 q hq using hdual
  let v₀ : S.V := ∑ c : Fin r, (if a < c then cj (t c.castSucc) else 0) • y c
  have hv₀ : v₀ ∈ Λ := Λ.sum_mem fun c _ => Λ.smul_mem _ (hy c)
  have hv0e : ∀ i, S.hT v₀ (F.fl.e i) =
      if a < i then (t i.castSucc : E) * ((1 + g * q i : 𝓞 E) : E) else 0 := by
    intro i
    rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single i]
    · by_cases hai : a < i
      · rw [if_pos hai, if_pos hai, hT_cj_left, hq]
      · rw [if_neg hai, if_neg hai, zero_smul, map_zero, LinearMap.zero_apply]
    · intro c _ hci
      by_cases hac : a < c
      · rw [if_pos hac, hT_cj_left, h0 c i (Ne.symm hci), mul_zero]
      · rw [if_neg hac, zero_smul, map_zero, LinearMap.zero_apply]
    · intro h; exact absurd (Finset.mem_univ i) h
  obtain ⟨ζ, hζ⟩ := hint v₀ hv₀ F.fl.z hz
  obtain ⟨x, y', hxy⟩ := hTg
  have hxyE : (x : E) * (Tn : E) + (y' : E) * (g : E) = 1 := by
    have := congrArg (fun o : 𝓞 E => (o : E)) hxy
    simpa using this
  let m : 𝓞 E := x * (ζ - t (Fin.last r))
  let v : S.V := v₀ + cj m • F.fl.z
  have hze : ∀ i, S.hT F.fl.z (F.fl.e i) = 0 := by
    intro i; rw [herm_eq, F.fl.z_orth i, star_zero]
  have hve : ∀ i, S.hT v (F.fl.e i) = S.hT v₀ (F.fl.e i) := by
    intro i; simp only [v, map_add, LinearMap.add_apply, hT_cj_left, hze, mul_zero, add_zero]
  refine ⟨v, Λ.add_mem hv₀ (Λ.smul_mem _ hz), fun i hi => ?_, fun c hc => ?_⟩
  · rw [hve, hv0e, if_neg (not_lt.mpr hi)]
  · induction c using Fin.lastCases with
    | last =>
      refine ⟨y' * (ζ - t (Fin.last r)), ?_⟩
      have hfz : frame F (Fin.last r) = F.fl.z := by simp [frame, FlagG.fvec]
      rw [hfz]
      simp only [v, map_add, LinearMap.add_apply, hT_cj_left, F.fl.z_norm, hζ, m]
      push_cast
      linear_combination (-((ζ : E) - (t (Fin.last r) : E))) * hxyE
    | cast i =>
      have hai : a < i := Fin.castSucc_lt_castSucc_iff.mp hc
      refine ⟨t i.castSucc * q i, ?_⟩
      have hfi : frame F (Fin.castSucc i) = F.fl.e i := by simp [frame, FlagG.fvec]
      rw [hfi, hve, hv0e, if_pos hai]
      push_cast; ring

theorem coe_nat (N : ℕ) : ((N : 𝓞 E) : E) = (N : E) := map_natCast (algebraMap (𝓞 E) E) N

theorem trace_fix (Λ : Submodule (𝓞 E) S.V) (hint : IntLat Λ) {n : ℕ} (f : Fin n → S.V) (g : 𝓞 E)
    (htr : (∃ k : ℕ, (g : E) = 2 * (k : E) + 1) ∨ ∃ ω : 𝓞 E, (ω : E) + star (ω : E) = 1)
    (Z : Set (Fin n)) (t : Fin n → 𝓞 E) (v : S.V) (hv : v ∈ Λ)
    (hZ : ∀ c ∈ Z, S.hT v (f c) = 0) (hc : ∀ c ∉ Z, ∃ q : 𝓞 E, S.hT v (f c) = ((t c + g * q : 𝓞 E) : E)) :
    ∃ v' ∈ Λ, ∃ l : 𝓞 E, (l : E) + star (l : E) = -S.hT v' v' ∧ (∀ c ∈ Z, S.hT v' (f c) = 0) ∧
      ∀ c ∉ Z, ∃ q : 𝓞 E, S.hT v' (f c) = ((t c + g * q : 𝓞 E) : E) := by
  obtain ⟨o, ho⟩ := hint v hv v hv
  have hself : star (o : E) = (o : E) := by rw [← ho, ← herm_eq]
  rcases htr with ⟨k, hk⟩ | ⟨ω, hω⟩
  · obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 2 * (k + 1) := ⟨_, rfl⟩
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = 2 * (k + 1) * (k + 1) := ⟨_, rfl⟩
    have hmE : (M : E) = 2 * ((k : E) + 1) := by rw [hM]; push_cast; ring
    have hNE : (N : E) = 2 * ((k : E) + 1) * ((k : E) + 1) := by rw [hN]; push_cast; ring
    have hmg : (M : E) = (g : E) + 1 := by rw [hmE, hk]; ring
    refine ⟨cj (M : 𝓞 E) • v, Λ.smul_mem _ hv, -((N : 𝓞 E) * o), ?_, fun c hcZ => ?_, fun c hcZ => ?_⟩
    · rw [hT_cj_left, hT_osmul_right, coe_cj, ho]
      simp only [coe_nat, map_neg, map_mul, map_natCast, star_neg, star_mul', hself, star_natCast]
      rw [hNE, hmE]; ring
    · rw [hT_cj_left, hZ c hcZ, mul_zero]
    · obtain ⟨q, hq⟩ := hc c hcZ
      refine ⟨t c + (M : 𝓞 E) * q, ?_⟩
      rw [hT_cj_left, hq]
      simp only [coe_nat, map_add, map_mul, map_natCast]
      linear_combination ((t c : E) + (g : E) * (q : E) - (g : E) * (q : E)) * hmg
  · refine ⟨v, hv, -(ω * o), ?_, hZ, hc⟩
    rw [ho]
    simp only [map_neg, map_mul, star_neg, star_mul', hself]
    linear_combination (-(o : E)) * hω

end PI.NRL
