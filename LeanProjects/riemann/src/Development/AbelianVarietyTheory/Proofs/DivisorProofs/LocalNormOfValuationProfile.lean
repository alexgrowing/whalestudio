import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinHeightSmulInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsEvEqProdNormZpow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.EisMidHt

open GroundTheory.Global.SemiLocal

theorem normFin_eq_prod_absNorm_of_valAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Fv F v ⊗[F] E)
    (e : HeightOneSpectrum (𝓞 E) → ℤ),
    (∀ c : Fv F v ⊗[F] E, c • y ∈ latLoc F L v ↔
        ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → GlobalTheory.UnrTate.valAt v w c ≤ WithZero.exp (-e w)) →
      (GlobalTheory.EisMidHt.normFin F L v y : ℝ) =
        ∏ w ∈ Formalism.L2.Host.aboveF (L := E) F v, (Ideal.absNorm w.asIdeal : ℝ) ^ e w := by
  intro F E _ _ _ _ _ n L v y e hy
  classical
  have hN1 : ∀ w : HeightOneSpectrum (𝓞 E), (1 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := by
    intro w
    have : Ideal.absNorm w.asIdeal ≠ 0 :=
      (Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors (I := w.asIdeal)).2
        (mem_nonZeroDivisors_of_ne_zero w.ne_bot)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hunder : ∀ w : HeightOneSpectrum (𝓞 E),
      w ∈ Formalism.L2.Host.aboveF (L := E) F v ↔ w.under (𝓞 F) = v := by
    intro w
    rw [GlobalTheory.UnrTate.completion_norms.mem_aboveF_iff]
    constructor
    · intro h; exact HeightOneSpectrum.ext h
    · intro h; rw [← h]; rfl
  have hmem : ∀ l : (Fv F v ⊗[F] E)ˣ, ((l⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • y ∈ latLoc F L v ↔
      ∀ w ∈ Formalism.L2.Host.aboveF (L := E) F v, GlobalTheory.UnrTate.ordAt v w l ≤ -e w := by
    intro l
    rw [hy]
    refine forall_congr' fun w => ?_
    rw [hunder, GlobalTheory.UnrTate.valAt_eq_exp, GlobalTheory.UnrTate.ordAt_inv, neg_neg, WithZero.exp_le_exp]
  choose π hπ using fun w : HeightOneSpectrum (𝓞 E) => w.valuation_exists_uniformizer E
  have hπ0 : ∀ w : HeightOneSpectrum (𝓞 E), algebraMap E (w.adicCompletion E) (π w) ≠ 0 := by
    intro w h
    have := congrArg Valued.v h
    rw [Formalism.UG.P.levelaf_valued_algebraMap, hπ w, map_zero] at this
    exact WithZero.coe_ne_zero this
  let z : CompletionsOver E v := fun w => (algebraMap E (w.1.adicCompletion E) (π w.1)) ^ (-e w.1)
  have hz : IsUnit z := Pi.isUnit_iff.2 fun w => (zpow_ne_zero _ (hπ0 w.1)).isUnit
  let l0 : (Fv F v ⊗[F] E)ˣ := (hz.map (tensorEquiv E v).symm).unit
  have hl0z : tensorEquiv E v (l0 : Fv F v ⊗[F] E) = z := by
    simp [l0]
  have hl0 : ∀ w ∈ Formalism.L2.Host.aboveF (L := E) F v, GlobalTheory.UnrTate.ordAt v w l0 = -e w := by
    intro w hw
    have h := (hunder w).1 hw
    haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← h]; rfl⟩
    have hv := GlobalTheory.UnrTate.valAt_eq_exp v w l0
    rw [GlobalTheory.UnrTate.valAt_of_under h, GlobalTheory.UnrTate.completion_norms.toCompl_eq v ⟨w, inferInstance⟩ h, hl0z] at hv
    change Valued.v ((algebraMap E (w.adicCompletion E) (π w)) ^ (-e w)) = _ at hv
    rw [map_zpow₀, Formalism.UG.P.levelaf_valued_algebraMap, hπ w] at hv
    rw [← WithZero.exp_zsmul] at hv
    have := WithZero.exp_injective hv
    rw [smul_eq_mul] at this
    linarith
  have hleast : IsLeast {c | ∃ l : (Fv F v ⊗[F] E)ˣ, ((l⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • y ∈ latLoc F L v ∧
      c = GlobalTheory.Doubling.absEv F E v l} (GlobalTheory.Doubling.absEv F E v l0) := by
    refine ⟨⟨l0, (hmem l0).2 fun w hw => (hl0 w hw).le, rfl⟩, ?_⟩
    rintro c ⟨l, hl, rfl⟩
    rw [← NNReal.coe_le_coe, GlobalTheory.UnrTate.absEv_eq_prod_absNorm, GlobalTheory.UnrTate.absEv_eq_prod_absNorm]
    refine Finset.prod_le_prod (fun w _ => zpow_nonneg (zero_le_one.trans (hN1 w)) _) fun w hw => ?_
    rw [hl0 w hw, neg_neg]
    exact zpow_le_zpow_right₀ (hN1 w) (by have := (hmem l).1 hl w hw; omega)
  have hinf : normFin F L v y = GlobalTheory.Doubling.absEv F E v l0 := hleast.csInf_eq
  rw [hinf, GlobalTheory.UnrTate.absEv_eq_prod_absNorm]
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [hl0 w hw, neg_neg]

end GlobalTheory.EisMidHt

end
