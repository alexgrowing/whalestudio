import Formalism.WachLatticeTwists.WachProductBases.NontrivialWachExample
import Formalism.WachLatticeTwists.WachProductBases.WachProductProofs.SaturationIntersectionHolds

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

open Finset

theorem consequence_four_local : LocalValuationConsequence := by
  intro L R _ _ _ P _ _ _ _ t π' r₀ u ϖ γR γ d κ _ n a c y Sx hγt hγs hmod hbij hπu hπ' hd hc hn hS
    x hx
  classical
  have hbijm := pow_smul_bij t hbij
  choose wv hwv using fun (k : κ) (m : ℕ) => (hbijm m).2 (n k)
  simp only at hwv
  obtain ⟨πi, hπi⟩ := hπu.exists_left_inv
  have hstep : ∀ k m, t • wv k (m + 1) = wv k m := by
    intro k m
    apply (hbijm m).1
    simp only
    rw [smul_smul, ← pow_succ, hwv, hwv]
  have heig : ∀ k (m : ℕ), γ (wv k m) = ((u ^ (-(a k + m)) : Lˣ) : L) • wv k m := by
    intro k m
    apply (hbijm m).1
    simp only
    have h1 : γ (t ^ m • wv k m) = ((u : L) ^ m) • (t ^ m • γ (wv k m)) := by
      rw [hγs, map_pow, hγt, smul_pow, smul_assoc]
    rw [hwv, hn] at h1
    rw [smul_comm (t ^ m), hwv]
    have h2 : t ^ m • γ (wv k m) =
        ((u ^ (-(m : ℤ)) : Lˣ) : L) • (((u : L) ^ m) • (t ^ m • γ (wv k m))) := by
      rw [smul_smul]
      have : ((u ^ (-(m : ℤ)) : Lˣ) : L) * (u : L) ^ m = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, zpow_neg, zpow_natCast, inv_mul_cancel,
          Units.val_one]
      rw [this, one_smul]
    rw [h2, ← h1, smul_smul, ← Units.val_mul, ← zpow_add]
    congr 3
    ring
  have hdv : ∀ v, d v = πi • (γ v - v) := by
    intro v
    rw [← hd, smul_smul, hπi, one_smul]

  have key1 : ∀ k m (b : ℤ) (r : R), ∃ r' : R, d (r • wv k m) - c b • (r • wv k m) = r' • wv k m := by
    intro k m b r
    refine ⟨πi * (γR r * algebraMap L R ((u ^ (-(a k + m)) : Lˣ) : L) - r) - algebraMap L R (c b) * r,
      ?_⟩
    rw [hdv, hγs, heig, ← algebraMap_smul R (((u ^ (-(a k + m)) : Lˣ) : L)) (wv k m),
      ← algebraMap_smul R (c b) (r • wv k m)]
    module

  have key2 : ∀ k (m : ℕ) (r : R), ∃ r' : R,
      d (r • wv k (m + 1)) - c (a k + ((m + 1 : ℕ) : ℤ)) • (r • wv k (m + 1)) = r' • wv k m := by
    intro k m r
    obtain ⟨r', hr'⟩ := hmod r
    set μ : L := ((u ^ (-(a k + ((m + 1 : ℕ) : ℤ))) : Lˣ) : L) with hμ
    set cc : L := c (a k + ((m + 1 : ℕ) : ℤ)) with hcc
    have hcμ : algebraMap L R (ϖ : L) * algebraMap L R cc = algebraMap L R μ - 1 := by
      rw [← map_mul, hc, map_sub, map_one]
    refine ⟨πi * (r' * algebraMap L R μ - r₀ * algebraMap L R cc * r), ?_⟩
    rw [← hstep k m]
    have e1 : c (a k + ((m + 1 : ℕ) : ℤ)) • (r • wv k (m + 1)) =
        (πi * π') • (algebraMap L R cc • (r • wv k (m + 1))) := by
      rw [hπi, one_smul, algebraMap_smul]
    have e2 : γR r = r + t * r' := by rw [← hr']; ring
    rw [e1, hdv, hγs, heig, ← hμ, ← algebraMap_smul R μ (wv k (m + 1)), e2, hπ']
    have e3 : algebraMap L R μ = algebraMap L R (ϖ : L) * algebraMap L R cc + 1 := by
      rw [hcμ]; ring
    have : ∀ w : P, πi • ((r + t * r') • algebraMap L R μ • w - r • w) -
        (πi * (algebraMap L R (ϖ : L) + t * r₀)) • algebraMap L R cc • r • w =
        (πi * (r' * algebraMap L R μ - r₀ * algebraMap L R cc * r)) • t • w +
        (πi * r * (algebraMap L R μ - (algebraMap L R (ϖ : L) * algebraMap L R cc + 1))) • w := by
      intro w; module
    rw [this, ← e3, sub_self, mul_zero, zero_smul, add_zero]
  have pres : ∀ k m (T : Finset ℤ) (r : R), ∃ r' : R,
      Polynomial.aeval d (∏ b ∈ T, (Polynomial.X - Polynomial.C (c b))) (r • wv k m) =
        r' • wv k m := by
    intro k m T
    induction T using Finset.induction_on with
    | empty => intro r; exact ⟨r, by simp⟩
    | insert b T hb ih =>
      intro r
      obtain ⟨r₁, h1⟩ := ih r
      obtain ⟨r₂, h2⟩ := key1 k m b r₁
      refine ⟨r₂, ?_⟩
      rw [Finset.prod_insert hb, map_mul, Module.End.mul_apply, h1, ← h2]
      simp [Module.algebraMap_end_apply]
  have main : ∀ k (m : ℕ) (T : Finset ℤ), (∀ j ∈ Finset.Icc (1 : ℤ) m, a k + j ∈ T) → ∀ r : R,
      ∃ r' : R, Polynomial.aeval d (∏ b ∈ T, (Polynomial.X - Polynomial.C (c b))) (r • wv k m) =
        r' • wv k 0 := by
    intro k m
    induction m with
    | zero => intro T _ r; exact pres k 0 T r
    | succ m ih =>
      intro T hT r
      have hb₀ : a k + ((m + 1 : ℕ) : ℤ) ∈ T :=
        hT _ (Finset.mem_Icc.2 ⟨by push_cast; omega, le_refl _⟩)
      obtain ⟨r₁, h1⟩ := key2 k m r
      obtain ⟨r₂, h2⟩ := ih (T.erase (a k + ((m + 1 : ℕ) : ℤ))) (by
        intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
        refine Finset.mem_erase.2 ⟨by push_cast; omega, hT j (Finset.mem_Icc.2 ⟨hj1, ?_⟩)⟩
        push_cast; omega) r₁
      refine ⟨r₂, ?_⟩
      rw [← Finset.prod_erase_mul T _ hb₀, map_mul, Module.End.mul_apply, ← h2, ← h1]
      simp [Module.algebraMap_end_apply]
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hx
  have hxsum : x = ∑ k, r k • wv k y := by
    apply (hbijm y).1
    simp only
    rw [← hr, smul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [smul_comm, hwv]
  rw [hxsum, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  obtain ⟨r', h'⟩ := main k y Sx (hS k) (r k)
  rw [h']
  have h0 : wv k 0 = n k := by simpa using hwv k 0
  rw [h0]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end Formalism.RepresentationBoundsCohomology.N1
