import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem span_cocycles_ext {G F E : Type} [Group G] [TopologicalSpace G] [Field F]
    [TopologicalSpace F] [IsTopologicalRing F] [Field E] [Algebra F E] [TopologicalSpace E]
    [FiniteDimensional F E] [IsModuleTopology F E] [IsTopologicalRing E] (χ : G → F)
    (H : ∃ z0 : G × G → F, (Continuous z0 ∧ ∀ g h k,
        χ g * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧
      ∀ z : G × G → F, Continuous z →
        (∀ g h k, χ g * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) →
        ∃ x : F, ∃ f : G → F, Continuous f ∧
          ∀ g h, χ g * f h - f (g * h) + f g = z (g, h) - x * z0 (g, h)) :
    ∃ z0 : G × G → E, (Continuous z0 ∧ ∀ g h k,
        algebraMap F E (χ g) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧
      ∀ z : G × G → E, Continuous z →
        (∀ g h k, algebraMap F E (χ g) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) →
        ∃ x : E, ∃ f : G → E, Continuous f ∧
          ∀ g h, algebraMap F E (χ g) * f h - f (g * h) + f g = z (g, h) - x * z0 (g, h) := by
  obtain ⟨z0, ⟨hc0, hz0⟩, H⟩ := H
  haveI : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E
  have hA : Continuous (algebraMap F E) := by
    have : (algebraMap F E : F → E) = fun a => a • (1 : E) := by
      funext a; rw [Algebra.algebraMap_eq_smul_one]
    rw [this]; fun_prop
  refine ⟨fun p => algebraMap F E (z0 p), ⟨hA.comp hc0, fun g h k => ?_⟩, fun z hc hz => ?_⟩
  · have := congrArg (algebraMap F E) (hz0 g h k)
    simpa using this
  · let b := Module.finBasis F E
    have hb : ∀ i, Continuous (b.coord i) := fun i =>
      IsModuleTopology.continuous_of_linearMap (b.coord i)
    have key : ∀ i, ∃ x : F, ∃ f : G → F, Continuous f ∧
        ∀ g h, χ g * f h - f (g * h) + f g = b.coord i (z (g, h)) - x * z0 (g, h) := by
      intro i
      refine H (fun p => b.coord i (z p)) ((hb i).comp hc) (fun g h k => ?_)
      have := congrArg (b.coord i) (hz g h k)
      rw [← Algebra.smul_def, map_sub, map_add, map_sub, map_smul, map_zero, smul_eq_mul] at this
      exact this
    choose x f hf hxf using key
    refine ⟨∑ i, x i • b i, fun g => ∑ i, f i g • b i, ?_, fun g h => ?_⟩
    · exact continuous_finsetSum _ (fun i _ => (hf i).smul continuous_const)
    · have hs : z (g, h) = ∑ i, b.coord i (z (g, h)) • b i := by
        simp [b.sum_repr]
      rw [hs, ← Algebra.smul_def, mul_comm, ← Algebra.smul_def, Finset.smul_sum, Finset.smul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_smul, smul_smul, ← sub_smul, ← add_smul, ← sub_smul, hxf i g h, mul_comm (x i)]

theorem span_cocycles_cyc_ext : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∃ z0 : ↥(GK K) × ↥(GK K) → ℚ_[l], (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → ℚ_[l], Continuous z → (∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : ℚ_[l], CobL (P.PD K) (z - x • z0)) → ∃ z0 : ↥(GK K) × ↥(GK K) → LL, (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → LL, Continuous z → (∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : LL, CobL (P.PD K) (z - x • z0) := by
  intro l _ P K LL _ _ _ O _ _ hO H
  obtain ⟨-, hfd, hmt, htr, -⟩ := hO
  obtain ⟨z0, hz0, H⟩ := H
  have := span_cocycles_ext (F := ℚ_[l]) (E := LL)
    (fun g : ↥(GK K) => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l])) ⟨z0, hz0, fun z hc hz => by
      obtain ⟨x, f, hf, hd⟩ := H z hc hz
      refine ⟨x, f, hf, fun g h => ?_⟩
      have := congrFun hd (g, h)
      simpa [ReciprocityTheory.Def.d1, Formalism.WeaklyAdmissibleFiltrations.charRep] using this⟩
  have e : ∀ g : ↥(GK K), algebraMap ℚ_[l] LL ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l])
      = ((cycLL (P.PD K) LL g : LLˣ) : LL) := fun g => by simp [cycLL]
  simp only [e] at this
  obtain ⟨w0, hw0, H'⟩ := this
  refine ⟨w0, hw0, fun z hc hz => ?_⟩
  obtain ⟨x, f, hf, hd⟩ := H' z hc hz
  refine ⟨x, f, hf, ?_⟩
  funext ⟨g, h⟩
  simpa [ReciprocityTheory.Def.d1, Formalism.WeaklyAdmissibleFiltrations.charRep] using hd g h

end GlobalTheory
