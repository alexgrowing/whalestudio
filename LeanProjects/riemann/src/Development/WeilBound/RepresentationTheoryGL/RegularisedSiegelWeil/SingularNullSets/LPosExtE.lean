import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LPosExtB
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LPosExtD

noncomputable section

open Set MeasureTheory CompactlySupported

namespace PositivityTheory.Rg.Rsw.L.LPosExt

variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

theorem exist (A : Submodule ℂ (X → ℂ)) (hA : ∀ f ∈ A, Continuous f ∧ HasCompactSupport f)
    (hstar : ∀ f ∈ A, star f ∈ A)
    (hbump : ∀ C, IsCompact C → ∃ f ∈ A, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) ∧ ∀ x ∈ C, f x = 1)
    (L : A →ₗ[ℂ] ℂ) (hpos : ∀ f : A, (∀ x, 0 ≤ (f.1 x).re ∧ (f.1 x).im = 0) → 0 ≤ (L f).re ∧ (L f).im = 0) :
    ∃ ν : Measure X, IsFiniteMeasureOnCompacts ν ∧ ∀ f : A, L f = ∫ x, f.1 x ∂ν := by
  obtain ⟨Λ, hΛ⟩ := extend A hA hbump L hpos
  set ν := RealRMK.rieszMeasure Λ
  have rep : ∀ a : AR A, ∫ x, (a.1 x).re ∂ν = (L ⟨a.1, a.2.1⟩).re := fun a =>
    (RealRMK.integral_rieszMeasure Λ (reC A hA a)).trans (hΛ a)
  refine ⟨ν, inferInstance, fun f => ?_⟩
  let u : X → ℂ := (1 / 2 : ℂ) • (f.1 + star f.1)
  let v : X → ℂ := (-(Complex.I / 2)) • (f.1 - star f.1)
  have hux : ∀ x, u x = ((f.1 x).re : ℂ) := fun x => by
    apply Complex.ext <;> simp [u] <;> ring
  have hvx : ∀ x, v x = ((f.1 x).im : ℂ) := fun x => by
    apply Complex.ext <;> simp [v] <;> ring
  have huA : u ∈ A := A.smul_mem _ (A.add_mem f.2 (hstar _ f.2))
  have hvA : v ∈ A := A.smul_mem _ (A.sub_mem f.2 (hstar _ f.2))
  let uR : AR A := ⟨u, huA, fun x => by simp [hux x]⟩
  let vR : AR A := ⟨v, hvA, fun x => by simp [hvx x]⟩
  have hsplit : f = (⟨uR.1, uR.2.1⟩ : A) + Complex.I • (⟨vR.1, vR.2.1⟩ : A) := by
    apply Subtype.ext; funext x
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, uR, vR,
      hux, hvx]
    rw [mul_comm]; exact (Complex.re_add_im _).symm
  have iu := im_L A hA hbump L hpos uR
  have iv := im_L A hA hbump L hpos vR
  have ru : (L ⟨uR.1, uR.2.1⟩).re = ∫ x, (f.1 x).re ∂ν := by
    rw [← rep uR]; congr 1; funext x; simp [uR, hux]
  have rv : (L ⟨vR.1, vR.2.1⟩).re = ∫ x, (f.1 x).im ∂ν := by
    rw [← rep vR]; congr 1; funext x; simp [vR, hvx]
  have hint : Integrable f.1 ν := (hA _ f.2).1.integrable_of_hasCompactSupport (hA _ f.2).2
  have hre : (∫ x, f.1 x ∂ν).re = ∫ x, (f.1 x).re ∂ν := (integral_re hint).symm
  have him : (∫ x, f.1 x ∂ν).im = ∫ x, (f.1 x).im ∂ν := (integral_im hint).symm
  rw [hsplit, map_add, map_smul, ← hsplit]
  apply Complex.ext
  · rw [hre, Complex.add_re, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im, iv, ru]; ring
  · rw [him, Complex.add_im, smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im, iu, rv]; ring

theorem main [SecondCountableTopology X] (A : Submodule ℂ (X → ℂ)) (hA : ∀ f ∈ A, Continuous f ∧ HasCompactSupport f)
    (hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A) (hstar : ∀ f ∈ A, star f ∈ A)
    (hsep : ∀ x y, x ≠ y → ∃ f ∈ A, f x ≠ f y)
    (hbump : ∀ C, IsCompact C → ∃ f ∈ A, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) ∧ ∀ x ∈ C, f x = 1) :
    (∀ L : A →ₗ[ℂ] ℂ, (∀ f : A, (∀ x, 0 ≤ (f.1 x).re ∧ (f.1 x).im = 0) → 0 ≤ (L f).re ∧ (L f).im = 0) →
      ∃ ν : Measure X, IsFiniteMeasureOnCompacts ν ∧ ∀ f : A, L f = ∫ x, f.1 x ∂ν) ∧
    ∀ ν ν' : Measure X, IsFiniteMeasureOnCompacts ν → IsFiniteMeasureOnCompacts ν' →
      (∀ f ∈ A, ∫ x, f x ∂ν = ∫ x, f x ∂ν') → ν = ν' :=
  ⟨fun L hpos => exist A hA hstar hbump L hpos,
    fun ν ν' hν hν' heq => uniq' A hA hmul hstar hsep hbump ν ν' hν hν' heq⟩

end PositivityTheory.Rg.Rsw.L.LPosExt
