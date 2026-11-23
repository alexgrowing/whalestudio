import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelCharpoly.IrreducibleCharpolyInv

open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace PI.GreenLabelMapW

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem galois_clause (Cv : LabelConv K) (hC : CuspParam K Cv) (d : ℕ) (α : ℂ ≃+* ℂ) (a : ℕ)
    (hα : ∀ ζ : ℂ, ζ ^ (∏ e ∈ Finset.Icc 1 d, (q K ^ e - 1)) = 1 → α ζ = ζ ^ a)
    (τ τ' : FDRep ℂ (GL (Fin d) K)) (hd : 1 ≤ d) (hs : Simple τ) (hc : IsCuspidal K τ)
    (hs' : Simple τ') (hc' : IsCuspidal K τ')
    (htr : ∀ γ, LinearMap.trace ℂ τ' (τ'.ρ γ) = α (LinearMap.trace ℂ τ (τ.ρ γ))) :
    rootsBar K (greenLab Cv d τ') = (rootsBar K (greenLab Cv d τ)).map (· ^ a) := by
  obtain ⟨hm, hi, hX, hdeg, hval⟩ := greenLab_spec Cv hC hd hs hc
  rw [Fintype.card_fin] at hdeg
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) (greenLab Cv d τ)
    (by rw [degree_eq_natDegree hm.ne_zero, hdeg]; exact_mod_cast (show d ≠ 0 by omega))
  have hunit : ∀ r, aeval r (greenLab Cv d τ) = 0 →
      Cv.ι r ^ (∏ e ∈ Finset.Icc 1 d, (q K ^ e - 1)) = 1 := by
    intro r hr
    have h1 := root_pow_card hm hi hX hr
    rw [hdeg] at h1
    obtain ⟨k, hk⟩ : (q K ^ d - 1) ∣ ∏ e ∈ Finset.Icc 1 d, (q K ^ e - 1) :=
      Finset.dvd_prod_of_mem (fun e => q K ^ e - 1) (Finset.mem_Icc.2 ⟨hd, le_rfl⟩)
    rw [hk, pow_mul, ← map_pow, h1, map_one, one_pow]
  have hinj : ∀ r₁ r₂ : AlgebraicClosure K, aeval r₁ (greenLab Cv d τ) = 0 →
      aeval r₂ (greenLab Cv d τ) = 0 → r₁ ^ a = r₂ ^ a → r₁ = r₂ := by
    intro r₁ r₂ h₁ h₂ h
    apply Cv.ι_inj r₁ r₂ (root_ne_zero hm hi hX h₁) (root_ne_zero hm hi hX h₂)
    apply α.injective
    rw [hα _ (hunit r₁ h₁), hα _ (hunit r₂ h₂), ← map_pow, ← map_pow, h]
  have hf : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure K),
      (σ x) ^ a = σ (x ^ a) := fun σ x => (map_pow σ x a).symm
  have hint : IsIntegral K (w ^ a) := Algebra.IsIntegral.isIntegral _
  have hlab : HasCuspLabel Cv τ' (minpoly K (w ^ a)) := by
    refine ⟨minpoly.monic hint, minpoly.irreducible hint, ?_, ?_, ?_⟩
    · intro h
      have h0 := minpoly.aeval K (w ^ a)
      rw [h, aeval_X] at h0
      exact pow_ne_zero a (root_ne_zero hm hi hX hw) h0
    · have hdeg' : (minpoly K (w ^ a)).natDegree = (greenLab Cv d τ).natDegree :=
        natDegree_minpoly_eq hm hi hw (fun x => x ^ a) hf hinj
      rw [hdeg', hdeg, Fintype.card_fin]
    · intro y hy γ hγ z hz m hm'
      obtain ⟨r, hr, rfl⟩ := (conj_roots hm hi hw (fun x => x ^ a) hf y).1 hy
      rw [htr γ, hval r hr γ hγ z hz m hm', map_mul, map_pow, map_neg, map_one, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have hu : (Cv.ι r ^ (m * Fintype.card K ^ i)) ^ (∏ e ∈ Finset.Icc 1 d, (q K ^ e - 1)) = 1 := by
        rw [pow_right_comm, hunit r hr, one_pow]
      rw [hα _ hu, map_pow, ← pow_mul, ← pow_mul]
      congr 1
      ac_rfl
  rw [greenLab_eq Cv hC hd hs' hc' hlab]
  exact aroots_eq_map hm hi hw (fun x => x ^ a) hf hinj

theorem dual_clause (Cv : LabelConv K) (hC : CuspParam K Cv) (d : ℕ)
    (τ τ' : FDRep ℂ (GL (Fin d) K)) (hd : 1 ≤ d) (hs : Simple τ) (hc : IsCuspidal K τ)
    (hs' : Simple τ') (hc' : IsCuspidal K τ')
    (htr : ∀ γ, LinearMap.trace ℂ τ' (τ'.ρ γ) = LinearMap.trace ℂ τ (τ.ρ γ⁻¹)) :
    rootsBar K (greenLab Cv d τ') = (rootsBar K (greenLab Cv d τ)).map (·⁻¹) := by
  obtain ⟨hm, hi, hX, hdeg0, hval⟩ := greenLab_spec Cv hC hd hs hc
  have hdeg : (greenLab Cv d τ).natDegree = d := by rw [hdeg0, Fintype.card_fin]
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) (greenLab Cv d τ)
    (by rw [degree_eq_natDegree hm.ne_zero, hdeg]; exact_mod_cast (show d ≠ 0 by omega))
  have hf : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure K),
      (σ x)⁻¹ = σ x⁻¹ := fun σ x => (map_inv₀ σ x).symm
  have hinj : ∀ r₁ r₂ : AlgebraicClosure K, aeval r₁ (greenLab Cv d τ) = 0 →
      aeval r₂ (greenLab Cv d τ) = 0 → r₁⁻¹ = r₂⁻¹ → r₁ = r₂ := fun _ _ _ _ h => inv_injective h
  have hint : IsIntegral K w⁻¹ := Algebra.IsIntegral.isIntegral _
  have hlab : HasCuspLabel Cv τ' (minpoly K w⁻¹) := by
    refine ⟨minpoly.monic hint, minpoly.irreducible hint, ?_, ?_, ?_⟩
    · intro h
      have h0 := minpoly.aeval K w⁻¹
      rw [h, aeval_X] at h0
      exact inv_ne_zero (root_ne_zero hm hi hX hw) h0
    · have hdeg' : (minpoly K w⁻¹).natDegree = (greenLab Cv d τ).natDegree :=
        natDegree_minpoly_eq hm hi hw (fun x => x⁻¹) hf hinj
      rw [hdeg', hdeg0]
    · intro y hy γ hγ z hz m hm'
      obtain ⟨r, hr, rfl⟩ := (conj_roots hm hi hw (fun x => x⁻¹) hf y).1 hy
      have hD : 1 ≤ Fintype.card (Fin d) := by rw [Fintype.card_fin]; exact hd
      have hn := card_pow_sub_one_pos (K := K) hD
      have hgen := gen_pow Cv hD
      have hz0 : z ≠ 0 := by rw [← hm']; exact pow_ne_zero _ (gen_ne_zero Cv hD)
      have hzi : Cv.gen (Fintype.card (Fin d)) ^
          (m * (Fintype.card K ^ Fintype.card (Fin d) - 1 - 1)) = z⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← hm', ← pow_add, ← mul_add_one, Nat.sub_add_cancel hn, mul_comm, pow_mul, hgen,
          one_pow]
      have hirr := irreducible_charpoly_inv γ hγ hz0 hz
      have hroot := root_inv γ hz0 hz
      have key := hval r hr γ⁻¹ hirr z⁻¹ hroot _ hzi
      rw [htr γ, key]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have hr1 : r ^ (Fintype.card K ^ Fintype.card (Fin d) - 1) = 1 := by
        have h5 := root_pow_card hm hi hX hr
        rwa [hdeg0] at h5
      have hrinv : r⁻¹ = r ^ (Fintype.card K ^ Fintype.card (Fin d) - 1 - 1) := by
        symm
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, Nat.sub_add_cancel hn, hr1]
      rw [hrinv, map_pow, ← pow_mul]
      congr 1
      ac_rfl
  rw [greenLab_eq Cv hC hd hs' hc' hlab]
  exact aroots_eq_map hm hi hw (fun x => x⁻¹) hf hinj

theorem labelMapGreen : LabelMapGreen K := by
  intro C hC
  refine ⟨{ lab := greenLab C
            lab_iso := greenLab_iso C
            lab_spec := ?_
            lab_inj := ?_
            lab_one := ?_ }, ⟨?_, ?_⟩, ?_⟩
  · intro d τ hd hs hc
    obtain ⟨h1, h2, h3, h4, -⟩ := greenLab_spec C hC hd hs hc
    exact ⟨h1, h2, h3, by simpa using h4⟩
  · intro d τ τ' hd hs hc hs' hc' heq
    have h' : HasCuspLabel C τ' (greenLab C d τ) := by
      rw [heq]
      exact greenLab_spec C hC hd hs' hc'
    exact (hC d hd).2.2 τ τ' (greenLab C d τ) hs hc hs' hc' (greenLab_spec C hC hd hs hc) h'
  · intro τ x hs hx htr
    exact greenLab_one C hC τ x hs hx htr
  · intro d α a hα τ τ' hd hs hc hs' hc' htr
    exact galois_clause C hC d α a hα τ τ' hd hs hc hs' hc' htr
  · intro d τ τ' hd hs hc hs' hc' htr
    exact dual_clause C hC d τ τ' hd hs hc hs' hc' htr
  · intro d τ hd hs hc
    exact greenLab_spec C hC hd hs hc

end PI.GreenLabelMapW
