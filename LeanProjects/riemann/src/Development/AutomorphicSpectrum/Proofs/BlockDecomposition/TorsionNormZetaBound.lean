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
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

theorem summable_absNorm_rpow_neg (K : Type) [Field K] [NumberField K] {r : ℝ} (hr : 1 < r) :
    Summable (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-r)) := by
  have h := (GlobalTheory.Mem.summable_norm_absNorm_cpow K (s := (r : ℂ)) (by simpa using hr))
  refine h.congr fun I => ?_
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
    Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

theorem sum_torsion_le (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)) (hL : IsLat L) {r : ℝ} (hr : 1 < r)
    (S : Finset ((Fin m → K) ⧸ L)) :
    ∑ x ∈ S, (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))
      ≤ zetaR K r := by
  classical
  set τ : (Fin m → K) ⧸ L → Ideal (𝓞 K) := fun x => Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x
    with hτ
  have hg := summable_absNorm_rpow_neg K hr
  have hfib : ∀ 𝔞 ∈ S.image τ,
      ∑ x ∈ S.filter (fun x => τ x = 𝔞), (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r))
        ≤ (Ideal.absNorm 𝔞 : ℝ) ^ (-r) := by
    intro 𝔞 h𝔞
    obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.mp h𝔞
    have hne : τ x₀ ≠ ⊥ := GlobalTheory.T.lattice_quotient_torsion_nonzero K m L hL x₀
    obtain ⟨hfin, hcard⟩ := GlobalTheory.T.torsion_card_le_absNorm_pow K m L hL (τ x₀) hne
    have hN : (0 : ℝ) < (Ideal.absNorm (τ x₀) : ℝ) := by
      have : Ideal.absNorm (τ x₀) ≠ 0 := fun h => hne (Ideal.absNorm_eq_zero_iff.mp h)
      exact_mod_cast Nat.pos_of_ne_zero this
    have hc : ((S.filter (fun x => τ x = τ x₀)).card : ℝ) ≤ (Ideal.absNorm (τ x₀) : ℝ) ^ m := by
      have hinj : (S.filter (fun x => τ x = τ x₀)).card ≤
          Nat.card {x : (Fin m → K) ⧸ L // ∀ a ∈ τ x₀, a • x = 0} := by
        haveI := Fintype.ofFinite {x : (Fin m → K) ⧸ L // ∀ a ∈ τ x₀, a • x = 0}
        rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
        refine Fintype.card_le_of_injective (fun x => ⟨x.1, fun a ha => ?_⟩) (fun x y h => ?_)
        · have hx := (Finset.mem_filter.mp x.2).2
          rw [← hx] at ha
          exact (Ideal.mem_torsionOf_iff _ _).mp ha
        · have h' : (x : (Fin m → K) ⧸ L) = y :=
            congrArg (fun z : {x : (Fin m → K) ⧸ L // ∀ a ∈ τ x₀, a • x = 0} => z.1) h
          exact Subtype.ext h'
      exact_mod_cast hinj.trans hcard
    have hsum : ∑ x ∈ S.filter (fun x => τ x = τ x₀), (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r))
        = ((S.filter (fun x => τ x = τ x₀)).card : ℝ) *
          (Ideal.absNorm (τ x₀) : ℝ) ^ (-((m : ℝ) + r)) := by
      rw [Finset.sum_congr rfl (g := fun _ => (Ideal.absNorm (τ x₀) : ℝ) ^ (-((m : ℝ) + r)))
        (fun x hx => by rw [(Finset.mem_filter.mp hx).2])]
      simp
    rw [hsum]
    calc _ ≤ (Ideal.absNorm (τ x₀) : ℝ) ^ m * (Ideal.absNorm (τ x₀) : ℝ) ^ (-((m : ℝ) + r)) :=
          mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hN.le _)
      _ = (Ideal.absNorm (τ x₀) : ℝ) ^ (-r) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hN]
          congr 1
          ring
  calc ∑ x ∈ S, (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r))
      = ∑ 𝔞 ∈ S.image τ, ∑ x ∈ S.filter (fun x => τ x = 𝔞),
          (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r)) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem τ hx) _).symm
    _ ≤ ∑ 𝔞 ∈ S.image τ, (Ideal.absNorm 𝔞 : ℝ) ^ (-r) := Finset.sum_le_sum hfib
    _ ≤ zetaR K r :=
        hg.sum_le_tsum _ (fun I _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem sum_torsion (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)) (hL : IsLat L) (r : ℝ) (hr : 1 < r) :
    Summable (fun x : (Fin m → K) ⧸ L =>
      (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))) ∧
    ∑' x : (Fin m → K) ⧸ L,
      (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))
        ≤ zetaR K r := by
  have hnn : ∀ x : (Fin m → K) ⧸ L,
      0 ≤ (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r)) :=
    fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hs := summable_of_sum_le hnn (sum_torsion_le K m L hL hr)
  exact ⟨hs, hs.tsum_le_of_sum_le (sum_torsion_le K m L hL hr)⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
