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
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNatMulMem
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem

theorem exists_nat_mul_mem (F : Type) [Field F] [NumberField F] (x : F) :
    ∃ m : ℕ, 0 < m ∧ ∃ r : 𝓞 F, (r : F) = (m : F) * x :=
  _root_.UpperTheory.Reformulated.B.ExistsNatMulMem.exists_nat_mul_mem F x

theorem repr_inclR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (x : E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Af F) b).repr (inclR (Af F) x) k
      = algebraMap F (Af F) (b.repr x k) := by
  have h : inclR (Af F) x = (1 : Af F) ⊗ₜ[F] x := rfl
  rw [h, Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem natCast_mul_eq_smul {F E : Type} [Field F] [Field E] [Algebra F E] (n : ℕ) (z : E) :
    (n : E) * z = (n : F) • z := by
  rw [Algebra.smul_def, map_natCast]

theorem intCast_mul_eq_smul {F E : Type} [Field F] [Field E] [Algebra F E] (n : ℤ) (z : E) :
    (n : E) * z = (n : F) • z := by
  rw [Algebra.smul_def, map_intCast]

theorem exists_clear_family {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E) {ι : Type} [Fintype ι] (e : ι → E) :
    ∃ D : ℕ, 0 < D ∧ ∀ (t : ι) (o : 𝓞 E) (k : Fin d),
      ∃ r : 𝓞 F, (r : F) = b.repr ((D : E) * (e t * (o : E))) k := by
  classical
  let B := RingOfIntegers.basis E
  choose m hm hr using fun p : ι × Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin d =>
    exists_nat_mul_mem F (b.repr (e p.1 * (B p.2.1 : E)) p.2.2)
  refine ⟨∏ p, m p, Finset.prod_pos fun p _ => hm p, fun t o k => ?_⟩
  set D : ℕ := ∏ p, m p with hDdef
  have hterm : ∀ l, ∃ r : 𝓞 F, (r : F) = b.repr ((D : E) * (e t * (B l : E))) k := by
    intro l
    obtain ⟨c, hc⟩ : m (t, l, k) ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    obtain ⟨r, hr1⟩ := hr (t, l, k)
    refine ⟨(c : 𝓞 F) * r, ?_⟩
    rw [natCast_mul_eq_smul (F := F), map_smul, Finsupp.smul_apply, smul_eq_mul, hc]
    simp only [map_mul, map_natCast, Nat.cast_mul]
    have hr2 : (r : F) = (m (t, l, k) : F) * b.repr (e t * (B l : E)) k := hr1
    change (c : F) * (r : F) = _
    rw [hr2]
    ring
  choose r hr' using hterm
  refine ⟨∑ l, (B.repr o l) • r l, ?_⟩
  have ho : (o : E) = ∑ l, ((B.repr o l : ℤ) : E) * (B l : E) := by
    have h3 := congrArg (algebraMap (𝓞 E) E) (B.sum_repr o)
    rw [map_sum] at h3
    rw [show (o : E) = algebraMap (𝓞 E) E o from rfl, ← h3]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [zsmul_eq_mul]
  have hsum : (D : E) * (e t * (o : E))
      = ∑ l, ((B.repr o l : ℤ) : F) • ((D : E) * (e t * (B l : E))) := by
    rw [ho, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← intCast_mul_eq_smul]
    ring
  rw [hsum, map_sum, Finsupp.finsetSum_apply]
  have h4 : ((∑ l, (B.repr o l) • r l : 𝓞 F) : F) = ∑ l, ((B.repr o l : ℤ) : F) * (r l : F) := by
    rw [show ((∑ l, (B.repr o l) • r l : 𝓞 F) : F)
      = algebraMap (𝓞 F) F (∑ l, (B.repr o l) • r l) from rfl, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [zsmul_eq_mul]
  rw [h4]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hr']

theorem ratTuple_mem_latN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n N : ℕ), 0 < N →
    ∃ s : ℕ, 0 < s ∧ ∀ ρ : Fin M → Fin n → 𝓞 E, ratTuple J s ρ ∈ latN b n M N := by
  intro F E _ _ _ _ _ d b M J n N hN
  obtain ⟨D, hD0, hD⟩ := exists_clear_family b (fun p : Fin M × Fin M => J⁻¹ p.1 p.2)
  refine ⟨N * D, Nat.mul_pos hN hD0, fun ρ => ?_⟩
  show ∀ a i, InNOh b N (ratTuple J (N * D) ρ a i)
  intro a j k
  choose r hr using fun i => hD (j, i) (ρ i a) k
  refine ⟨algebraMap F (Af F) (((∑ i, r i : 𝓞 F)) : F), ?_, ?_⟩
  · exact ((GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.1 _).2 ⟨_, rfl⟩
  · show (Algebra.TensorProduct.basis (Af F) b).repr
      (inclR (Af F) (((N * D : ℕ) : E) *
        (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a)) j)) k = _
    rw [repr_inclR]
    have h1 : ((N * D : ℕ) : E) * (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a)) j
        = (N : F) • ∑ i, (D : E) * (J⁻¹ j i * (ρ i a : E)) := by
      rw [← natCast_mul_eq_smul, Nat.cast_mul, Matrix.mulVec, dotProduct, ← Finset.mul_sum,
        mul_assoc]
    rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul, map_sum, Finsupp.finsetSum_apply,
      map_mul, map_natCast]
    congr 2
    rw [show ((∑ i, r i : 𝓞 F) : F) = algebraMap (𝓞 F) F (∑ i, r i) from rfl, map_sum]
    exact Finset.sum_congr rfl fun i _ => (hr i).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem
