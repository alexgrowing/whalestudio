import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContractNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralAndGoodOfIsSpherical
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjEqOfNormalises
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeOneOfIsCuspidalMultiProd

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SphHyp

theorem isSpherical_of_hypOutside : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → ∀ (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), NG.HypOutside J χ B → ∀ f ∈ NG.isoTyp a.ρ S, f ∈ NG.TypeSp a.ρ J χ → f ≠ 0 → ∀ (s : SplitPlace L), s.v ∉ B → ∀ (σ : IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → IsSpherical (GlobalTheory.LocLanglands.cls σ).rep := by
  intro L _ _ _ n a S hS J χ hlev B hB f hfiso hfT hf0 s hsB σ hσ
  classical
  obtain ⟨i, T₀, hi, hic, -, -, -⟩ := id hσ
  have hrt : ∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc n κ ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring,
      NG.rt L n κ f = (((1 : (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) →* ℂˣ) ⟨s.loc n κ, h⟩ : ℂˣ) : ℂ) • f := by
    intro κ hκ h
    have hU := (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hκ).1 h
    have hκB : TrivOutside Bᶜ κ := fun w hw => hκ w (by
      intro hm
      rw [Set.mem_singleton_iff] at hm
      rw [hm] at hw
      exact hsB (by simpa using hw))
    obtain ⟨hJ, hχ⟩ := hB κ hκB
    have hκJ := hJ.2 hU
    rw [hfT.2 ⟨κ, hκJ⟩, hχ hκJ]
    simp
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.LocVec.main L n a S hS s σ hσ i hi hic
    (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) 1 (fun g hg => hg)
    (by simp) f hfiso hf0 hrt
  have key : ∀ y, i y ∈ Formalism.UG.Ov L s.w → Valued.v y ≤ 1 := fun y hy =>
    (GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff s.v y).1 (GlobalTheory.SphLoc.le_one_of_map i.toRingHom hi
      ((GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff s.w _).2 hy))
  have hfix : ∀ g ∈ KO (s.w.adicCompletion L) (Fin n), σ.ρ g u = u := by
    intro g hg
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion s.w n, GlobalTheory.HeckeScalarSph.mem_GLint_iff] at hg
    let g' := Matrix.GeneralLinearGroup.map i.symm.toRingHom g
    have hg' : g' ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
      rw [GlobalTheory.HeckeScalarSph.mem_GLint_iff]
      refine ⟨fun p q => ?_, fun p q => ?_⟩
      · show Valued.v (i.symm (g.1 p q)) ≤ 1
        exact key _ (by rw [RingEquiv.apply_symm_apply]; exact hg.1 p q)
      · rw [← map_inv]
        show Valued.v (i.symm ((g⁻¹).1 p q)) ≤ 1
        exact key _ (by rw [RingEquiv.apply_symm_apply]; exact hg.2 p q)
    have e : Matrix.GeneralLinearGroup.map i.toRingHom g' = g :=
      Units.ext (Matrix.ext fun p q => i.apply_symm_apply _)
    have := hu g' hg'
    rw [e] at this
    simpa using this
  have hsph : IsSpherical σ.ρ := by
    intro h
    apply hu0
    have hm : u ∈ fixed σ.ρ (KO (s.w.adicCompletion L) (Fin n)) := fun g => by
      simpa using hfix g.1 g.2
    rw [h] at hm
    exact hm
  exact GlobalTheory.BCOffT.isSpherical_of_equiv (equivRep σ) hsph
end GlobalTheory.SphHyp
