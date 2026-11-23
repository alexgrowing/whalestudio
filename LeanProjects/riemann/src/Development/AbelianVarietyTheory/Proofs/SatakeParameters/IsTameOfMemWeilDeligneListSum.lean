import Mathlib
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NoMonodromyOfMemWeilDeligneListSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaAndZelevinskyPolynomialRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BernsteinZelevinskyFinitenessHolds

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TameSum

theorem isTameWD_of_lpSum {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {x y : WD h}
    (hxy : IsTameWD (x.lpSum y)) : IsTameWD x ∧ IsTameWD y := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  obtain ⟨m, b, rfl⟩ := WD.exists_rep y
  obtain ⟨k, c, hc, hw⟩ := hxy
  rw [WD.lpSum_mk, WD.mk_eq_mk] at hc
  have H : ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → (a.ρ σ).prodMap (b.ρ σ) = 1 :=
    fun σ hσ => hc.ρ_eq_one (hw σ hσ)
  refine ⟨⟨n, a, rfl, fun σ hσ => LinearMap.ext fun u => ?_⟩, ⟨m, b, rfl, fun σ hσ => LinearMap.ext fun u => ?_⟩⟩
  · simpa using congrArg Prod.fst (LinearMap.congr_fun (H σ hσ) (u, 0))
  · simpa using congrArg Prod.snd (LinearMap.congr_fun (H σ hσ) (0, u))

theorem isTameWD_of_mem_sumList : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (l : List (WD h)), IsTameWD (sumList l) → ∀ y ∈ l, IsTameWD y := by
  intro E Ω _ _ _ _ _ A w h l
  induction l with
  | nil => intro _ y hy; simp at hy
  | cons z l ih =>
    intro H y hy
    have H2 := isTameWD_of_lpSum (x := z) (y := sumList l) H
    rcases List.mem_cons.1 hy with rfl | hy
    · exact H2.1
    · exact ih H2.2 y hy

end GlobalTheory.TameSum
