import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CharpolyEqOfIsNilpotentSub
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFrobSSWdRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitOfStableLine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DmulMulDRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamCharacterTwistIffLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBalancedBilinearTensorProductMapStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodProductCommutesFrobeniusZpowStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPeriodProductEqOfInvertibleCharacterStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvertibleDPstPotSemistableCharacterStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Pst.TwistLetters

set_option maxHeartbeats 4000000 in

theorem wdSpace_twist_equiv : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {L : FinExt l} {a : ℕ} (s : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1) (m : ↥(Dec (F := E) A) →* GL (Fin 1) ↥L.1) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L s))] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L m))] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))))], IsPst P (Bw.repE L s) → IsPst P (Bw.repE L m) → IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) → ∃ e : WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m) ≃ₗ[ℂ] WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))), (∀ (σ : ↥(Weil h)) x, e (TensorProduct.map (wdRho P ι Bw h hj (Bw.repE L s) σ) (wdRho P ι Bw h hj (Bw.repE L m) σ) x) = wdRho P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) σ (e x)) ∧ ∀ x, e (((wdN P ι (Bw.repE L s)).rTensor (WDSpace P ι (Bw.repE L m)) + (wdN P ι (Bw.repE L m)).lTensor (WDSpace P ι (Bw.repE L s)) : Module.End ℂ (WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m))) x) = wdN P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (e x) := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj L a s m _ _ _ hs hm ht
  let χ : ↥(GK Bw.Kw) → ↥L.1 := fun g => ((GlobalTheory.TwistAbove.chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1)
  have hχm : ∀ g v, Bw.repE L m g v = χ g • v := fun g v => GlobalTheory.TwistAbove.repE_rank_one Bw m g v
  have hχt : ∀ g v, Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)) g v = χ g • Bw.repE L s g v := by
    intro g v
    rw [GlobalTheory.TwistBridgeDR.twGL_eq]
    exact GlobalTheory.TwistBridgeDR.repE_twGL' Bw _ s g v
  clear_value χ
  have hl := dmul_mulD_left P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt
  have hr := dmul_mulD_right P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt
  have hL1 := @GlobalTheory.T.exists_balancedBilinear_tensorProduct_map _ _ _ _ _ _ _ _ _ _ _ _ _ (mulD P (Bw.repE L s)) (mulD P (Bw.repE L m)) (mulD P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))) ℂ _ (algC ι L) (urC ι) _ hl hr
  obtain ⟨Φ, hΦ'⟩ : ∃ Φ : WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m) →ₗ[ℂ] WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))), ∀ x y, Φ (wdMk P ι (Bw.repE L s) x ⊗ₜ wdMk P ι (Bw.repE L m) y) = wdMk P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) ((dmul P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt) x y) := hL1
  have hsurj : Function.Surjective Φ := by
    have h2b := GlobalTheory.T.exists_invertible_dPst_potSemistableCharacter P AI hT (Bw.repE L m) χ hχm hm
    obtain ⟨y, hy, y', hyy'⟩ := h2b
    let y₀ : ↥(Dpst P (Bw.repE L m)) := ⟨y, hy⟩
    have h2 := GlobalTheory.T.exists_periodProduct_eq_of_invertible_character P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt y₀ y' hyy'
    have hspan : Submodule.span ℂ (Set.range (wdMk P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))))) = ⊤ := span_wdMk P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))
    have hle : Submodule.span ℂ (Set.range (wdMk P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))))) ≤ LinearMap.range Φ := by
      rw [Submodule.span_le]
      rintro _ ⟨z, rfl⟩
      obtain ⟨x, hx⟩ := h2 z
      exact ⟨_, (hΦ' x y₀).trans (by rw [hx])⟩
    intro z
    exact LinearMap.mem_range.mp (hle (Submodule.eq_top_iff'.mp hspan z))
  have hdim : Module.finrank ℂ (WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m)) =
      Module.finrank ℂ (WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))) := by
    rw [Module.finrank_tensorProduct, GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι _ L _ _ hs,
      GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι _ L _ _ hm, GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι _ L _ _ ht]
    simp
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  have key : ∀ {f g : WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m) →ₗ[ℂ] WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))},
      (∀ x y, f (wdMk P ι (Bw.repE L s) x ⊗ₜ wdMk P ι (Bw.repE L m) y) =
        g (wdMk P ι (Bw.repE L s) x ⊗ₜ wdMk P ι (Bw.repE L m) y)) → f = g := by
    intro f g H
    apply TensorProduct.ext
    apply LinearMap.ext_on_range (span_wdMk P ι (Bw.repE L s))
    intro x
    apply LinearMap.ext_on_range (span_wdMk P ι (Bw.repE L m))
    intro y
    exact H x y
  have hW : ∀ σ x y, weilD Bw h P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) σ ((dmul P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt) x y) =
      (dmul P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt) (weilD Bw h P (Bw.repE L s) σ x) (weilD Bw h P (Bw.repE L m) σ y) := by
    intro σ x y
    simp only [weilD_apply, Module.End.mul_apply, GlobalTheory.T.periodProduct_commutes_frobenius_zpow P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt, actD_dmul]
  refine ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun σ x => ?_, fun x => ?_⟩
  · have e : Φ ∘ₗ TensorProduct.map (wdRho P ι Bw h hj (Bw.repE L s) σ) (wdRho P ι Bw h hj (Bw.repE L m) σ) =
        wdRho P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) σ ∘ₗ Φ := by
      apply key
      intro x y
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, wdRho_mk, hΦ', hW]
    exact LinearMap.congr_fun e x
  · have e : Φ ∘ₗ ((wdN P ι (Bw.repE L s)).rTensor (WDSpace P ι (Bw.repE L m)) +
        (wdN P ι (Bw.repE L m)).lTensor (WDSpace P ι (Bw.repE L s))) = wdN P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) ∘ₗ Φ := by
      apply key
      intro x y
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        wdN_mk, map_add, hΦ', monD_dmul, wdMk_add]
    exact LinearMap.congr_fun e x

end GlobalTheory.Pst.TwistLetters
