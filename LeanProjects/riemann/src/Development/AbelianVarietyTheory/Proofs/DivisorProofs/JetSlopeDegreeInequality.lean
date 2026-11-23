import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpanIntersectionSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankInfKerAddOneOfNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLemmaSmallVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLineLatticeEqLogIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogIndexSubLogNormEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeNormMulPowIdealStatement

open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

namespace GlobalTheory.SlopeFilt

theorem nrm_pos {K : Type} [Field K] {m : ℕ} (h : HermFam K (Fin m → K)) (σ : K →+* ℂ) {x : Fin m → K}
    (hx : x ≠ 0) : 0 < h.nrm σ x := by
  have hpd := h.posDef σ 1 ![x] (linearIndependent_unique_iff.2 (by simpa using hx))
  have h0 := hpd.diag_pos (i := 0)
  simp only [Matrix.diag_apply, Matrix.of_apply, Matrix.cons_val_fin_one] at h0
  unfold HermFam.nrm
  exact Real.sqrt_pos.2 (by simpa using (Complex.lt_def.1 h0).1)

theorem slope_filt : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (h : HermFam K (Fin m → K))
    (L : Submodule (𝓞 K) (Fin m → K)) (x : Fin m → K) (n : ℕ) (ν : ℝ) (β : ℕ → (K →+* ℂ) → ℝ),
    Full L → x ≠ 0 → (∀ i σ, i ≤ n → 0 < β i σ) → JetSys h L x n ν β →
    ((n : ℝ) + 1) * ν ≤ ∑ i ∈ Finset.range (n + 1), (-(i : ℝ) * deg h (lineLat L x) + meanLog K (β i)) := by
  intro K _ _ m h L x n ν β hL hx hβ hJS
  obtain ⟨r, hE, E, Vf, j, hEfull, hmu, hdeg, hV0, hst⟩ := hJS
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have fgle : ∀ {p : ℕ} {M N : Submodule (𝓞 K) (Fin p → K)}, N.FG → M ≤ N → M.FG := by
    intro p M N hN hMN
    haveI : IsNoetherian (𝓞 K) N := isNoetherian_of_fg_of_noetherian N hN
    exact isNoetherian_submodule.1 inferInstance M hMN
  have hmemJ : ∀ b : K, b ∈ L.comap ((LinearMap.toSpanSingleton K (Fin m → K) x).restrictScalars (𝓞 K)) ↔
      b • x ∈ L := fun b => by simp
  obtain ⟨a, haL, ha0⟩ : ∃ a : K, a • x ∈ L ∧ a ≠ 0 := by
    by_contra hno
    push_neg at hno
    have hsp := GlobalTheory.T.lattice_span_intersection_subspace K m L (Submodule.span K {x}) hL.2
    have hbot : Submodule.span K ((L ⊓ (Submodule.span K {x}).restrictScalars (𝓞 K) :
        Submodule (𝓞 K) (Fin m → K)) : Set (Fin m → K)) = ⊥ := by
      rw [Submodule.span_eq_bot]
      intro y hy
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy.2
      rw [hno b hy.1, zero_smul]
    rw [hsp] at hbot
    exact hx (by simpa using hbot)
  have hJfg : (L.comap ((LinearMap.toSpanSingleton K (Fin m → K) x).restrictScalars (𝓞 K))).FG := by
    have hinj : Function.Injective ((LinearMap.toSpanSingleton K (Fin m → K) x).restrictScalars (𝓞 K)) :=
      fun b b' hbb => smul_left_injective K hx (by simpa using hbb)
    exact Submodule.fg_of_fg_map_injective _ hinj (fgle hL.1 (Submodule.map_comap_le _ _))
  have hnrm : ∀ σ, 0 < h.nrm σ x := fun σ => nrm_pos h σ hx
  have step : ∀ i ≤ n, deg hE (E ⊓ (Vf i).restrictScalars (𝓞 K)) - deg hE (E ⊓ (Vf (i + 1)).restrictScalars (𝓞 K)) ≤
      -(i : ℝ) * deg h (lineLat L x) + meanLog K (β i) := by
    intro i hi
    obtain ⟨hVs, ⟨v, hvV, hjv⟩, hint, hbd⟩ := hst i hi
    obtain ⟨u, huE, huV, hu⟩ : ∃ u ∈ E, u ∈ Vf i ∧ j i u ≠ 0 := by
      by_contra hno
      push_neg at hno
      have hsp := GlobalTheory.T.lattice_span_intersection_subspace K r E (Vf i) hEfull.2
      have hle : Submodule.span K ((E ⊓ (Vf i).restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin r → K)) :
          Set (Fin r → K)) ≤ LinearMap.ker (j i) := by
        rw [Submodule.span_le]
        intro w hw
        exact LinearMap.mem_ker.2 (hno w hw.1 hw.2)
      rw [hsp] at hle
      exact hjv (LinearMap.mem_ker.1 (hle hvV))
    have hB : ∀ σ, 0 < β i σ * h.nrm σ x ^ i := fun σ => mul_pos (hβ i σ hi) (pow_pos (hnrm σ) i)
    have hs := GlobalTheory.T.siegel_lemma_small_vector K r hE E (Vf i) (j i) u (fun σ => β i σ * h.nrm σ x ^ i) hEfull.1 hEfull.2 huE huV hu hB
      (fun σ q w c hw => hbd σ q w c hw)
    rw [← hVs] at hs
    have hIfg : ((E ⊓ (Vf i).restrictScalars (𝓞 K)).map ((j i).restrictScalars (𝓞 K))).FG :=
      (fgle hEfull.1 inf_le_left).map _
    have hcI : j i u ∈ (E ⊓ (Vf i).restrictScalars (𝓞 K)).map ((j i).restrictScalars (𝓞 K)) :=
      ⟨u, ⟨huE, huV⟩, rfl⟩
    have hIint : ∀ y ∈ (E ⊓ (Vf i).restrictScalars (𝓞 K)).map ((j i).restrictScalars (𝓞 K)),
        ∀ b ∈ L.comap ((LinearMap.toSpanSingleton K (Fin m → K) x).restrictScalars (𝓞 K)),
        IsIntegral ℤ (b ^ i * y) := by
      rintro y ⟨w, ⟨hwE, hwV⟩, rfl⟩ b hb
      exact hint w hwE hwV b ((hmemJ b).1 hb)
    have hI0 : (E ⊓ (Vf i).restrictScalars (𝓞 K)).map ((j i).restrictScalars (𝓞 K)) ≠ ⊥ := by
      intro h0; rw [h0] at hcI; exact hu (by simpa using hcI)
    have haJ := (hmemJ a).2 haL
    have hJ0 : L.comap ((LinearMap.toSpanSingleton K (Fin m → K) x).restrictScalars (𝓞 K)) ≠ ⊥ := by
      intro h0; rw [h0] at haJ; exact ha0 (by simpa using haJ)
    have e1 := GlobalTheory.T.log_index_sub_log_norm_eq K _ hIfg (j i u) hcI hu
    have e2 := GlobalTheory.T.log_index_sub_log_norm_eq K _ hJfg a haJ ha0
    have n2 := GlobalTheory.T.one_le_norm_mul_pow_ideal K _ _ hIfg hJfg i hI0 hJ0 hIint
    have hl := GlobalTheory.T.degree_line_lattice_eq_log_index K m h L x a hL.1 hx ha0 haL
    have n2' : (1 : ℝ) ≤ (FractionalIdeal.absNorm (⟨_, FractionalIdeal.isFractional_of_fg hIfg⟩ :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) * (FractionalIdeal.absNorm
        (⟨_, FractionalIdeal.isFractional_of_fg hJfg⟩ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) ^ i := by
      exact_mod_cast n2
    generalize (FractionalIdeal.absNorm (⟨_, FractionalIdeal.isFractional_of_fg hIfg⟩ :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) = NI at e1 n2'
    generalize (FractionalIdeal.absNorm (⟨_, FractionalIdeal.isFractional_of_fg hJfg⟩ :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) = NJ at e2 n2'
    have hlog : 0 ≤ Real.log NI + i * Real.log NJ := by
      have hpos : 0 < NI * NJ ^ i := lt_of_lt_of_le one_pos n2'
      have h1 : NI ≠ 0 := by rintro rfl; simp at hpos
      have h2 : NJ ^ i ≠ 0 := by intro h0; rw [h0] at hpos; simp at hpos
      have := Real.log_nonneg n2'
      rwa [Real.log_mul h1 h2, Real.log_pow] at this
    have hsumB : ∑ σ : K →+* ℂ, Real.log (β i σ * h.nrm σ x ^ i) =
        ∑ σ : K →+* ℂ, Real.log (β i σ) + i * ∑ σ : K →+* ℂ, Real.log (h.nrm σ x) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Real.log_mul (hβ i σ hi).ne' (pow_ne_zero _ (hnrm σ).ne'), Real.log_pow]
    rw [hsumB, e1] at hs
    rw [e2] at hl
    unfold meanLog
    have hl' : (i : ℝ) * ((Module.finrank ℚ K : ℝ) * deg h (lineLat L x)) + i * ∑ σ : K →+* ℂ, Real.log (h.nrm σ x)
        = -(i * Real.log NJ) := by
      rw [← mul_add, hl]; ring
    have key : (-Real.log NI + (∑ σ : K →+* ℂ, Real.log (β i σ) + i * ∑ σ : K →+* ℂ, Real.log (h.nrm σ x))) /
        (Module.finrank ℚ K : ℝ) ≤ -(i : ℝ) * deg h (lineLat L x) +
          (∑ σ : K →+* ℂ, Real.log (β i σ)) / (Module.finrank ℚ K : ℝ) := by
      rw [div_le_iff₀ hd, add_mul, div_mul_cancel₀ _ hd.ne']
      have : -(i : ℝ) * deg h (lineLat L x) * (Module.finrank ℚ K : ℝ) =
          -((i : ℝ) * ((Module.finrank ℚ K : ℝ) * deg h (lineLat L x))) := by ring
      rw [this]
      linarith
    exact hs.trans key
  have hrank : ∀ i ≤ n + 1, Module.finrank K (Vf i) + i = r := by
    intro i
    induction i with
    | zero => intro _; rw [hV0]; simp
    | succ k ih =>
      intro hk
      obtain ⟨hVs, ⟨v, hvV, hjv⟩, -, -⟩ := hst k (by omega)
      have h1 := GlobalTheory.T.finrank_inf_ker_add_one_of_exists_ne_zero K r (Vf k) (j k) ⟨v, hvV, hjv⟩
      rw [← hVs] at h1
      have h2 := ih (by omega)
      omega
  have hlast : deg hE (E ⊓ (Vf (n + 1)).restrictScalars (𝓞 K)) ≤ ((r : ℝ) - (n + 1)) * ν := by
    have h1 := hmu (E ⊓ (Vf (n + 1)).restrictScalars (𝓞 K)) inf_le_left
    have h2 : latRank K (E ⊓ (Vf (n + 1)).restrictScalars (𝓞 K)) = Module.finrank K (Vf (n + 1)) := by
      unfold latRank; rw [GlobalTheory.T.lattice_span_intersection_subspace K r E (Vf (n + 1)) hEfull.2]
    have h3 := hrank (n + 1) le_rfl
    rw [h2] at h1
    have h4 : (Module.finrank K (Vf (n + 1)) : ℝ) = r - (n + 1) := by
      have h5 : ((Module.finrank K (Vf (n + 1)) + (n + 1) : ℕ) : ℝ) = r := by rw [h3]
      push_cast at h5; linarith
    rwa [h4] at h1
  have htel := Finset.sum_range_sub' (fun i => deg hE (E ⊓ (Vf i).restrictScalars (𝓞 K))) (n + 1)
  have hsum_le : ∑ i ∈ Finset.range (n + 1), (deg hE (E ⊓ (Vf i).restrictScalars (𝓞 K)) -
      deg hE (E ⊓ (Vf (i + 1)).restrictScalars (𝓞 K))) ≤
      ∑ i ∈ Finset.range (n + 1), (-(i : ℝ) * deg h (lineLat L x) + meanLog K (β i)) :=
    Finset.sum_le_sum fun i hi => step i (by simp at hi; omega)
  rw [htel] at hsum_le
  simp only [hV0, Submodule.restrictScalars_top, inf_top_eq] at hsum_le
  rw [hdeg] at hsum_le
  have e : ((n : ℝ) + 1) * ν = r * ν - ((r : ℝ) - (n + 1)) * ν := by ring
  rw [e]
  linarith

end GlobalTheory.SlopeFilt
