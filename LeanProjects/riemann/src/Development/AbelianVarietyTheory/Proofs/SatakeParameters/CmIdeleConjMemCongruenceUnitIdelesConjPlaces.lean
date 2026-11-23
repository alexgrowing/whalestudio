import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfMemLev

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj finiteCompletionMap)

namespace GlobalTheory.HeckeConjLev

theorem ideleMap_mem_levT (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (T : Set (HeightOneSpectrum (𝓞 K))) (T' : Set (HeightOneSpectrum (𝓞 L)))
    (hT : ∀ w ∈ T', w.under (𝓞 K) ∈ T) (N : ℕ) (y : Ideles K) (hy : y ∈ levT K T N) :
    ideleMap K L y ∈ levT L T' N := by
  have hc : ∀ w : HeightOneSpectrum (𝓞 L), (ideleMap K L y).val.2 w =
      finiteCompletionMap K L w (y.val.2 (w.under (𝓞 K))) := fun w => rfl
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · show Valued.v ((ideleMap K L y).val.2 w) = 1
    have h : Valued.v (y.val.2 (w.under (𝓞 K))) = 1 := hy.1 _
    rw [hc, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, h, one_pow]
  · show Valued.v ((ideleMap K L y).val.2 w - 1) ≤ Valued.v (N : w.adicCompletion L)
    rw [hc, ← map_one (finiteCompletionMap K L w), ← map_sub, ← map_natCast (finiteCompletionMap K L w),
      GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap]
    exact pow_le_pow_left₀ zero_le (hy.2 _ (hT w hw)) _

theorem under_under (F K L : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra F K] [Algebra K L] [Algebra F L]
    (h : ∀ x : F, algebraMap K L (algebraMap F K x) = algebraMap F L x) (w : HeightOneSpectrum (𝓞 L)) :
    (w.under (𝓞 K)).under (𝓞 F) = w.under (𝓞 F) := by
  haveI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun x => (h x).symm
  exact HeightOneSpectrum.ext (Ideal.under_under w.asIdeal)

theorem ideleConj_mem_levT (E : Type) [Field E] [NumberField E] [IsCMField E]
    (T : Set (HeightOneSpectrum (𝓞 E))) (N : ℕ) (u : Ideles E) (hu : u ∈ levT E T N) :
    ideleConj (maximalRealSubfield E) E u ∈ levT E {w | ∀ w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → w' ∈ T} N :=
  @ideleMap_mem_levT E E _ _ _ _
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra T
    {w | ∀ w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → w' ∈ T}
    (fun w hw => hw _ (@under_under (maximalRealSubfield E) E E _ _ _ _ _ _ _
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra _
      (fun x => (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).commutes x) w)) N u hu

end GlobalTheory.HeckeConjLev
