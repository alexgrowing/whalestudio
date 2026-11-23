import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatTuple
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanFormStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatTest

theorem trace_tmul_eq {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] (r : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] e) = r * algebraMap F R (Algebra.trace F E e) := by
  have h1 : (r ⊗ₜ[F] e : R ⊗[F] E) = r • ((1 : R) ⊗ₜ[F] e) := by
    simp [TensorProduct.smul_tmul']
  have h2 : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e)
      = LinearMap.baseChange R (Algebra.lmul F E e) := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s y => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [h1, map_smul, Algebra.trace_apply, h2, LinearMap.trace_baseChange, Algebra.trace_apply]
  simp

theorem inNOh_tmul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (N : ℕ) {α : Af F} (hα : α ∈ Oh F) (k : Fin d) :
    InNOh b N (((N : Af F) * α) ⊗ₜ[F] b k) := by
  intro j
  by_cases h : j = k
  · subst h
    exact ⟨α, hα, by simp [Algebra.TensorProduct.basis_repr_tmul]⟩
  · refine ⟨0, fun v => zero_mem _, ?_⟩
    simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.single_apply, Ne.symm h]

theorem exists_common_denom {E : Type} [Field E] [NumberField E] {d : ℕ} (ε : Fin d → E) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ k, IsIntegral ℤ ((y : E) * ε k) := by
  have hex : ∀ k, ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * ε k) := by
    intro k
    obtain ⟨y, hy, h⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic (ε k)))
    exact ⟨y, hy, by simpa [zsmul_eq_mul] using h⟩
  choose y hy hint using hex
  refine ⟨∏ k, y k, Finset.prod_ne_zero_iff.mpr fun k _ => hy k, fun k => ?_⟩
  have h1 : (((∏ j, y j : ℤ)) : E) * ε k
      = ((∏ j ∈ Finset.univ.erase k, y j : ℤ) : E) * ((y k : E) * ε k) := by
    rw [← mul_assoc, ← Int.cast_mul, mul_comm (∏ j ∈ Finset.univ.erase k, y j) (y k),
      Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  rw [h1]
  have h2 : IsIntegral ℤ (((∏ j ∈ Finset.univ.erase k, y j : ℤ)) : E) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (∏ j ∈ Finset.univ.erase k, y j : ℤ))
  exact h2.mul (hint k)

theorem rat_test : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ),
    IsCharAF F ψ → ∀ N : ℕ, 0 < N → ∀ D : ℕ, 0 < D → (∀ f : F,
      (∀ r : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F (f * (r : F)) = m) → ∃ o : 𝓞 F, (o : F) = (D : F) * f) →
    ∃ t : F, t ≠ 0 ∧ ∀ w : E, (∀ x : Af F ⊗[F] E, InNOh b N x →
        psiFin F ψ (Algebra.trace (Af F) (Af F ⊗[F] E) (sigR (Af F) σ x * inclR (Af F) w)) = 1) →
      ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = t • w := by
  intro F E _ _ _ _ _ σ hCM d b ψ hψ N hN D hD hDint
  have hF : IsTotallyReal F := hCM.1
  obtain ⟨ρ, e, h1, h2, h3, -, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hF
  obtain ⟨a, ha, -, ψf, hstd, hpsi⟩ := GlobalTheory.T.adelic_character_archimedean_form F hF ρ e h1 h2 h3 ψ hψ
  have hbeta := ((GlobalTheory.T.standard_adelic_character F).2 ψf hstd).2.2
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  let τ : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  let b' : Module.Basis (Fin d) F E := b.map τ.toLinearEquiv
  have hb' : ∀ k, b' k = σ (b k) := fun k => by simp [b', τ]
  let ε := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b'
  obtain ⟨y, hy, hyint⟩ := exists_common_denom (fun k => ε k)
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hDF : (D : F) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  have hyF : (y : F) ≠ 0 := Int.cast_ne_zero.mpr hy
  refine ⟨(y : F) * ((D : F) * (a * (N : F))), mul_ne_zero hyF (mul_ne_zero hDF (mul_ne_zero ha hNF)), ?_⟩
  intro w hw

  have hcoord : ∀ k, ∃ o : 𝓞 F, (o : F) = (D : F) * (a * (N : F) * ε.repr w k) := by
    intro k
    have hrepr : ε.repr w k = Algebra.trace F E (σ (b k) * w) := by
      rw [LinearMap.BilinForm.dualBasis_repr_apply, hb', Algebra.traceForm_apply, mul_comm]
    refine hDint _ ((hbeta _).mp fun α hα => ?_)
    have hx := hw (((N : Af F) * α) ⊗ₜ[F] b k) (inNOh_tmul b N hα k)
    have e1 : sigR (Af F) σ (((N : Af F) * α) ⊗ₜ[F] b k) * inclR (Af F) w
        = ((N : Af F) * α) ⊗ₜ[F] (σ (b k) * w) := by
      change (((N : Af F) * α) ⊗ₜ[F] σ (b k)) * ((1 : Af F) ⊗ₜ[F] w) = _
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [e1, trace_tmul_eq] at hx
    change ψ (pairA F 0 _) = 1 at hx
    rw [hpsi] at hx
    rw [hrepr, ← hx]
    congr 1
    simp only [map_mul, map_natCast]
    ring
  choose o ho using hcoord
  rw [← IsIntegralClosure.isIntegral_iff (A := 𝓞 E) (R := ℤ), ← ε.sum_repr w, Finset.smul_sum]
  refine IsIntegral.sum _ fun k _ => ?_
  have e2 : ((y : F) * ((D : F) * (a * (N : F)))) • (ε.repr w k • ε k)
      = algebraMap F E (o k : F) * ((y : E) * ε k) := by
    have e3 : (y : F) * ((D : F) * (a * (N : F))) * ε.repr w k
        = (y : F) * ((D : F) * (a * (N : F) * ε.repr w k)) := by ring
    rw [smul_smul, Algebra.smul_def, e3, ho k, map_mul, map_intCast]
    ring
  rw [e2]
  exact (IsIntegral.algebraMap (RingOfIntegers.isIntegral_coe (o k))).mul (hyint k)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatTest
