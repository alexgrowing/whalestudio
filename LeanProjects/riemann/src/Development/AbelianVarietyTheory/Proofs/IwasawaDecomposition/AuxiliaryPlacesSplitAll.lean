import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.SplitPrimeAuxiliary

open scoped Pointwise

theorem eq_one_of_smul_eq (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] {p : ℕ} (hp : p.Prime)
    (h : ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E)
    (P : Ideal (𝓞 E)) [P.IsPrime] (hP : (p : 𝓞 E) ∈ P) (σ : Gal(E/ℚ)) (hσ : σ • P = P) : σ = 1 := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpz.ne_zero).2 hpz).isMaximal (by simpa using hp.ne_zero)
  have hlo : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using hP
  have horb := Algebra.IsInvariant.orbit_eq_primesOver ℤ (𝓞 E) Gal(E/ℚ) (Ideal.span {(p : ℤ)}) P
  have hidx := MulAction.index_stabilizer Gal(E/ℚ) P
  rw [horb, h, ← IsGalois.card_aut_eq_finrank] at hidx
  have hmul := (MulAction.stabilizer Gal(E/ℚ) P).card_mul_index
  rw [hidx] at hmul
  have h1 : Nat.card (MulAction.stabilizer Gal(E/ℚ) P) = 1 :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [hmul, one_mul])
  have hb := Subgroup.card_eq_one.1 h1
  have hm : σ ∈ MulAction.stabilizer Gal(E/ℚ) P := hσ
  rwa [hb, Subgroup.mem_bot] at hm

theorem conj_ne_one {R : Ranks} (H : Host R) : H.conj ≠ 1 := by
  have : IsCMField H.E := H.isCMField_hostE
  intro h
  apply IsCMField.complexConj_ne_one H.E
  ext z
  have : IsCMField.complexConj H.E z = H.conj z := by
    apply H.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  rw [this, h]
  rfl

theorem isSplitPl_of_split {R : Ranks} (H : Host R) {p : ℕ} (hp : p.Prime)
    (h : ((Ideal.span {(p : ℤ)}).primesOver (𝓞 H.E)).ncard = Module.finrank ℚ H.E)
    (v : HeightOneSpectrum (𝓞 H.E)) (hv : v ∈ placesOver H.E p) : IsSplitPl H v := by
  have : IsGalois ℚ H.E := H.hostE_isGalois
  have := v.isPrime
  by_contra hs
  apply conj_ne_one H
  rw [← inv_eq_one]
  refine eq_one_of_smul_eq H.E hp h v.asIdeal hv _ (Eq.symm ?_)
  refine v.isMaximal.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
  intro x hx
  rw [Ideal.mem_inv_pointwise_smul_iff]
  by_contra hx'
  refine hs ⟨x, hx, fun y hy => ?_⟩
  have : y = H.conj • x := RingOfIntegers.ext hy
  rwa [this]

theorem auxiliary_primes_split : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ _ x => ∀ _ : LC hL x, ∀ v, v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  intro _ hL
  refine StepW.of_all fun K B f T w _ _ _ P x _ v hv => ?_
  rcases hv with hv | hv
  · exact isSplitPl_of_split B.host B.host.pde_prime B.toPre.pde_split.1 v hv
  · exact isSplitPl_of_split B.host B.host.pde'_prime B.toPre.pde_split.2 v hv

end GlobalTheory.SplitPrimeAuxiliary
