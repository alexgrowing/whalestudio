import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescent

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped WithZero

namespace GlobalTheory.TraceSmall

theorem valV_le_one_of_ext {T T' : CDVR} (i : T.Fr →+* T'.Fr) {e' : ℕ} (he' : 0 < e')
    (hv : ∀ z : T.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T.V z) (z : T.Fr) :
    valV T'.V (i z) ≤ 1 ↔ valV T.V z ≤ 1 := by
  by_cases hz : z = 0
  · subst hz; simp
  have h1 : valV T'.V (i z) ≠ 0 := valV_ne_zero ((map_ne_zero i).2 hz)
  have h2 : valV T.V z ≠ 0 := valV_ne_zero hz
  have h := hv z hz
  have he : (0 : ℤ) < e' := by exact_mod_cast he'
  rw [← WithZero.log_le_log h1 one_ne_zero, ← WithZero.log_le_log h2 one_ne_zero, WithZero.log_one]
  unfold vV at h
  constructor <;> intro h' <;> nlinarith

theorem exists_bound {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (p : HeightOneSpectrum (𝓞 K)) {m : ℕ} (y : Fin m → L) :
    ∃ N : ℕ, ∀ la' : HeightOneSpectrum (𝓞 L), la'.asIdeal.under (𝓞 K) = p.asIdeal → ∀ k,
      la'.valuation L (y k) ≤ WithZero.exp (N : ℤ) := by
  have hS : {la' : HeightOneSpectrum (𝓞 L) | la'.asIdeal.under (𝓞 K) = p.asIdeal}.Finite := by
    refine (Set.Finite.preimage (f := fun la' : HeightOneSpectrum (𝓞 L) => la'.asIdeal)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
      (IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 L))).subset fun la' h => ?_
    exact ⟨la'.isPrime, ⟨h.symm⟩⟩
  obtain ⟨B, hB⟩ := ((hS.prod (Set.finite_univ (α := Fin m))).image
    fun q : HeightOneSpectrum (𝓞 L) × Fin m => WithZero.log (q.1.valuation L (y q.2))).bddAbove
  refine ⟨B.toNat, fun la' h k => ?_⟩
  by_cases hy : y k = 0
  · simp [hy]
  have h0 : la'.valuation L (y k) ≠ 0 := by simpa using hy
  have := hB ⟨(la', k), ⟨h, Set.mem_univ _⟩, rfl⟩
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
  simp only at this
  omega

theorem valuation_le_of_mem {L : Type} [Field L] [NumberField L] (la' : HeightOneSpectrum (𝓞 L)) {N : ℕ}
    {b : 𝓞 L} (hb : b ∈ la'.asIdeal ^ N) : la'.valuation L (b : L) ≤ WithZero.exp (-(N : ℤ)) :=
  (la'.valuation_of_algebraMap b).trans_le ((la'.intValuation_le_pow_iff_mem b N).2 hb)

theorem trace_le_one : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L)), la.asIdeal.under (𝓞 K) = p.asIdeal → ∀ (m : ℕ) (y : Fin m → L), ∃ N : ℕ, ∀ b : 𝓞 L, (∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la → la'.asIdeal.under (𝓞 K) = p.asIdeal → b ∈ la'.asIdeal ^ N) → ∀ (T : CDVR), T.FinRes → ∀ (io : K →+* T.Fr) (e : ℕ), OverLa p T.V io e → ∀ x : Fin m → T.Fr, (∀ k, valV T.V (x k) ≤ 1) → (∀ (T' : CDVR) (i : T.Fr →+* T'.Fr) (e' : ℕ) (τ : L →+* T'.Fr) (e'' : ℕ), 0 < e' → (∀ z : T.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T.V z) → T'.FinRes → (∀ z : K, τ (algebraMap K L z) = i (io z)) → OverLa la T'.V τ e'' → valV T'.V (∑ k, τ (y k) * i (x k)) ≤ 1) → valV T.V (∑ k, io (Algebra.trace K L ((b : L) * y k)) * x k) ≤ 1 := by
  intro K L _ _ _ _ _ p la hla m y
  obtain ⟨N, hN⟩ := exists_bound p y
  refine ⟨N, fun b hb T hT io e ho x hx H => ?_⟩
  let Ω := AlgebraicClosure L
  let F := IntermediateField.normalClosure K L Ω
  obtain ⟨T', i, e', σ₀, he', hv, hT', hσ₀⟩ := GlobalTheory.SupDescent.exists_ext (L := F) T hT io
  have hv' : ∀ a : T.Fr, vV T'.V (i a) = (e' : ℤ) * vV T.V a := fun a => by
    by_cases h : a = 0
    · subst h; simp [vV]
    · exact hv a h
  have ho' := ho.bc i he' hv'
  have hF : ∀ (ρ : L →ₐ[K] Ω) (z : L), ρ z ∈ F := fun ρ z =>
    AlgHom.fieldRange_le_normalClosure ρ ⟨z, rfl⟩
  let τ : (L →ₐ[K] Ω) → L →+* T'.Fr := fun ρ =>
    σ₀.comp ((ρ.codRestrict F.toSubalgebra (hF ρ)).toRingHom)
  have hτ : ∀ ρ z, τ ρ z = σ₀ ⟨ρ z, hF ρ z⟩ := fun _ _ => rfl
  have hτK : ∀ ρ (a : K), τ ρ (algebraMap K L a) = i (io a) := fun ρ a => by
    rw [hτ, ← hσ₀ a]
    congr 1
    exact Subtype.ext (ρ.commutes a)
  have htr : ∀ z : L, i (io (Algebra.trace K L z)) = ∑ ρ : L →ₐ[K] Ω, τ ρ z := fun z => by
    have h1 := trace_eq_sum_embeddings Ω (K := K) (L := L) (x := z)
    have h2 : algebraMap K F (Algebra.trace K L z) = ∑ ρ : L →ₐ[K] Ω, (⟨ρ z, hF ρ z⟩ : F) := by
      apply Subtype.val_injective
      rw [IntermediateField.coe_sum]
      exact h1
    rw [← hσ₀, h2, map_sum]
    exact Finset.sum_congr rfl fun ρ _ => (hτ ρ z).symm
  rw [← valV_le_one_of_ext i he' hv]
  have hsum : i (∑ k, io (Algebra.trace K L ((b : L) * y k)) * x k) =
      ∑ ρ : L →ₐ[K] Ω, ∑ k, τ ρ (b : L) * (τ ρ (y k) * i (x k)) := by
    simp only [map_sum, map_mul (f := i), htr, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, mul_assoc]
  rw [hsum]
  refine Valuation.map_sum_le _ fun ρ _ => ?_
  obtain ⟨la', e'', hol⟩ := GlobalTheory.AlgLawsCompare.exists_overLa T' (τ ρ) hT'
  have hunder : la'.asIdeal.under (𝓞 K) = p.asIdeal := Ideal.ext fun a => by
    rw [Ideal.under_def, Ideal.mem_comap, ← GlobalTheory.SupDescent.val_lt_one_iff_mem hol,
      ← GlobalTheory.SupDescent.val_lt_one_iff_mem ho']
    exact Iff.of_eq (congrArg (fun t => valV T'.V t < 1) (hτK ρ a))
  rcases eq_or_ne la' la with rfl | hne
  · rw [← Finset.mul_sum, map_mul]
    exact mul_le_one' ((GlobalTheory.SupDescent.val_le_one_iff hol _).2 (la'.valuation_le_one b))
      (H T' i e' (τ ρ) e'' he' hv hT' (hτK ρ) hol)
  · refine Valuation.map_sum_le _ fun k _ => ?_
    rw [← mul_assoc, ← map_mul, map_mul]
    refine mul_le_one' ((GlobalTheory.SupDescent.val_le_one_iff hol _).2 ?_) ((valV_le_one_of_ext i he' hv _).2 (hx k))
    rw [map_mul]
    calc la'.valuation L (b : L) * la'.valuation L (y k)
        ≤ WithZero.exp (-(N : ℤ)) * WithZero.exp (N : ℤ) :=
          mul_le_mul' (valuation_le_of_mem la' (hb la' hne hunder)) (hN la' hunder k)
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]

end GlobalTheory.TraceSmall
