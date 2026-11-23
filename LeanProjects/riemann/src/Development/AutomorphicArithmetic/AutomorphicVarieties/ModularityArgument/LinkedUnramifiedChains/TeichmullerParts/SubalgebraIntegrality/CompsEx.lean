import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocCompSplit

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D

theorem compsEx : CompsEx := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V hV σ hσ
  have hund : ∀ {A : ValuationSubring Ω} {w : Plc L}, IsPlaceOver A w → IsPlaceOver A (w.under (𝓞 (Lp L))) :=
    fun hA y => hA (algebraMap (𝓞 (Lp L)) (𝓞 L) y)
  have hwv : ∀ v, (s.w v).under (𝓞 (Lp L)) = v := fun v =>
    HeightOneSpectrum.ext (Ideal.ext fun y => (hund (s.hw v) y).symm.trans (s.hA v y))
  have hsp : ∀ v ∈ s.S, IsSplitAt (s.w v) := fun v hv =>
    UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA v) (s.split v hv) _ (hwv v)
  have hex : ∀ w : Plc L, IsSplitAt w → ∃ τ : SmIrr (GLw n w), Cp σ w τ := fun w hw => by
    obtain ⟨τ, -, h1, -⟩ := GlobalTheory.DefU.exists_locComp_split L n ⟨σ, hσ⟩ w hw
    exact ⟨τ, h1⟩
  have hl : ∀ v : V.frame.Vl, v.1 ∈ s.S := fun v => Or.inl v.2
  have hu : ∀ u : s.St, u.1 ∈ s.S := fun u => Or.inr (Or.inl u.2)
  have ho : s.v0 ∈ s.S := Or.inr (Or.inr rfl)
  choose f hf using fun v (hv : v ∈ s.S) => hex (s.w v) (hsp v hv)
  exact ⟨⟨fun v => f _ (hl v), fun u => f _ (hu u), f _ ho, fun v => hf _ (hl v), fun u => hf _ (hu u), hf _ ho⟩⟩

end UpperTheory.V.Z.J.D
