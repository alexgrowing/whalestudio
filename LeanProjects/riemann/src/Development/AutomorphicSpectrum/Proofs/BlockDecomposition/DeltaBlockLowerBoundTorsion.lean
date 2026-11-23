import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumCompBoundedFibresLeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndexStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamIsLatticeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeQuotientTorsionNonzeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeOfDualPairingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorIndexBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorNormQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPrincipalElementNormBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeNormCmAbsNormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmConjugationPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionOrthogonalityIntegralSolutionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockMatrixMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockQuotientInjectionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionNormZetaBoundStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound

section
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem blk_mulVec_castSucc {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y : Fin m → E) (s : E) (a : Fin m) :
    (blk σ c u d *ᵥ (Fin.snoc (α := fun _ => E) y s)) a.castSucc = (c *ᵥ y) a + u a * s := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, blk]

theorem blk_mulVec_last {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y : Fin m → E) (s : E) :
    (blk σ c u d *ᵥ (Fin.snoc (α := fun _ => E) y s)) (Fin.last m) =
      ∑ j, σ (u j) * y j + d * s := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, blk]

variable [NumberField E]

theorem mem_lastFib_blk {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y l : Fin m → 𝓞 E) (s : 𝓞 E)
    (h : ∀ a, (c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) a + u a * algebraMap (𝓞 E) E s =
      algebraMap (𝓞 E) E (l a)) :
    (∑ j, σ (u j) * algebraMap (𝓞 E) E (y j) + d * algebraMap (𝓞 E) E s) ∈
      lastFib (blk σ c u d) := by
  have hvI : (Fin.snoc (α := fun _ => E) (fun j => algebraMap (𝓞 E) E (y j))
      (algebraMap (𝓞 E) E s) : Fin (m + 1) → E) ∈ intVec E (m + 1) := by
    intro i
    refine Fin.lastCases ?_ (fun a => ?_) i
    · exact ⟨s, by simp⟩
    · exact ⟨y a, by simp⟩
  have h1 := Submodule.mem_sup_right (S := intVec E (m + 1))
    (Submodule.mem_map_of_mem (f := (blk σ c u d).mulVecLin.restrictScalars (𝓞 E)) hvI)
  have h2 : (Fin.snoc (α := fun _ => E) (fun j => algebraMap (𝓞 E) E (l j)) 0 :
      Fin (m + 1) → E) ∈ lam (blk σ c u d) := by
    refine Submodule.mem_sup_left ?_
    intro i
    refine Fin.lastCases ?_ (fun a => ?_) i
    · exact ⟨0, by simp⟩
    · exact ⟨l a, by simp⟩
  have h3 := (lam (blk σ c u d)).sub_mem h1 h2
  show LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m) _ ∈ lam (blk σ c u d)
  convert h3 using 1
  ext i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simp [blk_mulVec_last]
  · have hne : a.castSucc ≠ Fin.last m := Fin.castSucc_ne_last a
    simp [blk_mulVec_castSucc, h a, hne]

theorem one_le_lastFib {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    (1 : Submodule (𝓞 E) E) ≤ lastFib C := by
  intro x hx
  obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hx
  refine Submodule.mem_sup_left (show _ ∈ intVec E (m + 1) from ?_)
  intro i
  by_cases hi : i = Fin.last m
  · subst hi
    exact ⟨o, by simp⟩
  · exact ⟨0, by simp [hi]⟩

theorem lastFib_fg {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    (lastFib C).FG := by
  have hfg : (lam C).FG := (GlobalTheory.T.lam_is_lattice E (m + 1) C).1
  have hmap : ((lastFib C).map
      (LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m))).FG :=
    Submodule.FG.of_le hfg (Submodule.map_comap_le _ _)
  exact Submodule.fg_of_fg_map_injective (LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m))
    (fun a b h => by simpa using congrFun h (Fin.last m)) hmap

theorem tor_decomp {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (t : 𝓞 E)
    (ht : t ∈ tor c u) :
    ∃ yo lo : Fin m → 𝓞 E, ∀ a, (c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) a +
      u a * algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E (lo a) := by
  have h : t • u ∈ lam c := by
    have h0 := (Ideal.mem_torsionOf_iff _ _).1 ht
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨l, hl, z, ⟨y, hy, rfl⟩, hz⟩ := Submodule.mem_sup.1 h
  choose lo hlo using hl
  choose yo hyo using hy
  refine ⟨-yo, lo, fun a => ?_⟩
  have h1 := congrFun hz a
  have hy' : (fun j => algebraMap (𝓞 E) E ((-yo) j)) = -y := by
    funext j
    simp [hyo j]
  rw [hy', Matrix.mulVec_neg, hlo a]
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Pi.add_apply, Pi.smul_apply,
    Algebra.smul_def] at h1
  simp only [Pi.neg_apply]
  linear_combination -h1
end

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound

open GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (t : 𝓞 E), t ∈ tor c u → t ≠ 0 → ∃ f : F, ∀ d : F, delta c * Ideal.absNorm (tor c u) ^ 2 * Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2 ≤ delta (blk σ c u (algebraMap F E d)) := by
  intro F E _ _ _ _ _ σ hCM m c hc u t ht ht0
  obtain ⟨hinv, hfix, hsO, hN⟩ := GlobalTheory.T.cm_conjugation_properties F E σ hCM
  obtain ⟨yo, lo, hyl⟩ := LocalBound.tor_decomp c u t ht
  have hf0 : σ (-∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j)) =
      -∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j) := by
    have hs : ∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j) =
        ∑ j, (c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j * σ (algebraMap (𝓞 E) E (yo j)) := by
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [hc]
      ring
    rw [map_neg, map_sum]
    simp only [map_mul, hinv]
    rw [hs]
  obtain ⟨f, hf⟩ := hfix _ hf0
  refine ⟨f, fun d => ?_⟩
  have hT : tor c u ≠ ⊥ := fun h => ht0 (by simpa [h] using ht)
  have hsOt : sO σ t ≠ 0 := by
    intro h0
    apply ht0
    have h1 : σ (algebraMap (𝓞 E) E t) = 0 := by
      have := hsO t
      rw [h0] at this
      simpa using this.symm
    have h2 : algebraMap (𝓞 E) E t = 0 := by
      rw [← hinv (algebraMap (𝓞 E) E t), h1, map_zero]
    exact (map_eq_zero_iff _ (RingOfIntegers.coe_injective)).1 h2
  have hmem : ∀ t' ∈ tor c u, sO σ t' ∈ (tor c u).map (sO σ) :=
    fun t' h' => Ideal.mem_map_of_mem _ h'
  have h𝔱 : (tor c u).map (sO σ) ≠ ⊥ := by
    intro h0
    have := hmem t ht
    rw [h0] at this
    exact hsOt (by simpa using this)
  have hw := LocalBound.mem_lastFib_blk σ c u (algebraMap F E d) yo lo t hyl
  have hinvb : ∀ b : E, (∀ a ∈ (tor c u).map (sO σ), (a : E) * b ∈ (1 : Submodule (𝓞 E) E)) →
      b ∈ lastFib (blk σ c u (algebraMap F E d)) := by
    intro b hb
    obtain ⟨y, hy, hby⟩ := GlobalTheory.T.torsion_orthogonality_integral_solution F E σ hCM m c hc u b (fun t' h' => by
      have := hb _ (hmem t' h')
      rwa [show ((sO σ t' : 𝓞 E) : E) = σ (t' : E) from hsO t'] at this)
    choose lo' hlo' using hy
    have h1 := LocalBound.mem_lastFib_blk σ c u (algebraMap F E d) y lo' 0 (fun a => by
      rw [hlo' a]
      simp)
    have h2 := LocalBound.one_le_lastFib (blk σ c u (algebraMap F E d)) hby
    have h3 := Submodule.add_mem _ h1 h2
    have h4 : (∑ j, σ (u j) * algebraMap (𝓞 E) E (y j) + algebraMap F E d * algebraMap (𝓞 E) E 0) +
        (b - ∑ j, σ (u j) * (y j : E)) = b := by
      simp only [map_zero, mul_zero, add_zero]
      exact add_sub_cancel _ _
    rwa [h4] at h3
  have hnorm := (GlobalTheory.T.relative_norm_cm_absNorm F E σ hCM t).1
  have hkey : ((sO σ t : 𝓞 E) : E) * (∑ j, σ (u j) * algebraMap (𝓞 E) E (yo j) +
      algebraMap F E d * algebraMap (𝓞 E) E t) -
      algebraMap F E (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d) ∈ (1 : Submodule (𝓞 E) E) := by
    refine Submodule.mem_one.2 ⟨∑ j, sO σ (lo j) * yo j, ?_⟩
    have hsum : σ (algebraMap (𝓞 E) E t) * ∑ j, σ (u j) * algebraMap (𝓞 E) E (yo j) =
        ∑ j, σ (algebraMap (𝓞 E) E (lo j)) * algebraMap (𝓞 E) E (yo j) -
          ∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hyl j, map_add, map_mul]
      ring
    have hs2 : algebraMap (𝓞 E) E (∑ j, sO σ (lo j) * yo j) =
        ∑ j, σ (algebraMap (𝓞 E) E (lo j)) * algebraMap (𝓞 E) E (yo j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]
      exact congrArg (· * _) (hsO (lo j))
    rw [hs2, show ((sO σ t : 𝓞 E) : E) = σ (algebraMap (𝓞 E) E t) from hsO t, map_add, map_mul,
      hf, hnorm]
    have hnorm' : (t : E) = algebraMap (𝓞 E) E t := rfl
    rw [hnorm']
    linear_combination -hsum
  have hmain := GlobalTheory.T.denominator_index_bound E ((tor c u).map (sO σ)) h𝔱
    (lastFib (blk σ c u (algebraMap F E d))) (LocalBound.lastFib_fg _)
    (LocalBound.one_le_lastFib _) hinvb (sO σ t) _ _ (hmem t ht) hw hkey
  rw [hN, GlobalTheory.T.denominator_norm_quadratic_extension F E hCM.2.2.1] at hmain
  rw [GlobalTheory.T.delta_block_matrix_multiplicative F E σ m c u (algebraMap F E d)]
  calc delta c * Ideal.absNorm (tor c u) ^ 2 *
        Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2
      = delta c * Ideal.absNorm (tor c u) * (Ideal.absNorm (tor c u) *
        Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hmain
