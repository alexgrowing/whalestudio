import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.WhittakerHecke.FiniteNatIdeleArchValuationSupport
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem val_nat (n : ℕ) (v : H.P ℚ) : Valued.v (n : H.Kv v) = v.intValuation (n : 𝓞 ℚ) := by
  have e : (n : H.Kv v) = FinitePlace.embedding v (algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ)) := by simp
  rw [e, ← HeightOneSpectrum.valuation_of_algebraMap (K := ℚ)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ))

private theorem val_le (N : ℕ) (v : H.P ℚ) : Valued.v (N : H.Kv v) ≤ 1 := by
  rw [val_nat]
  exact HeightOneSpectrum.intValuation_le_one v _

private theorem cp_iy {y : ℝ} (h : y ≠ 0) (v : H.P ℚ) : H.cp v ((iy y : (A ℚ)ˣ) : A ℚ) = 1 := by
  have : ((iy y : (A ℚ)ˣ) : A ℚ).2 = 1 := by
    unfold iy
    rw [dif_neg h]
    show (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) - 0 + 0 = 1
    simp
  exact (congrArg (pLoc ℚ v) this).trans (map_one _)

theorem UpperTheory.ideleCongruence_archIdele_mul_finiteNatIdele :
    ∀ N : ℕ, 0 < N → ∀ (n : ℕ) (r : ℝ), 0 < n → n.Coprime N → r ≠ 0 → ((∀ v, Bad N v → Dv N v (((iy r * pin n : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((iy r * pin n : (A ℚ)ˣ) : A ℚ)) ≤ 1) := by
  intro N _ n r hn hc hr
  obtain ⟨-, h2, h3⟩ := UpperTheory.finiteNatIdele_arch_valuation_support n hn
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · have hb : ¬ Bad n v := fun hb => by
      have h1 : IsCoprime (n : 𝓞 ℚ) (N : 𝓞 ℚ) := Nat.Coprime.cast hc
      obtain ⟨a, b, e⟩ := h1
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (e ▸ add_mem (Ideal.mul_mem_left _ _ hb) (Ideal.mul_mem_left _ _ hv)))
    unfold Dv
    rw [map_sub, Units.val_mul, map_mul, cp_iy hr, h3 v hb, map_one]
    simp
  · rw [Units.val_mul, map_mul, cp_iy hr, one_mul, h2]
    exact val_le n v
