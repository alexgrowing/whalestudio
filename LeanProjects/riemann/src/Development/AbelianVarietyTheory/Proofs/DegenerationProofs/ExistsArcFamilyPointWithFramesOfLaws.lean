import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsExtendValuation
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuationSubring
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraitsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemRangeIffOfFinite
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFramePull

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex

theorem arcFam : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt →
    ThetaUnifAV → GlobalTheory.LN.ArcFamSt := by
  intro h₁ h₂ h₃ h₄ h₅ h₆ h₇ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hb m hm hmu
  have pt := GlobalTheory.ArcPoint.exists_point h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have bad := GlobalTheory.Ex.Trait.hasArcData_at_trait h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have good := GlobalTheory.Ex.GoodTrait.range_subset_abLocus h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have fr₁ := GlobalTheory.T.exists_single_polarisation_generator_all_traits h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have frm := GlobalTheory.OneBasis.exists_isFrame_pow_sq h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have mono := GlobalTheory.Ex.Mono.mono h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  obtain ⟨R₁, _, _, g, y₁, gi, gf, n₁, hy, hr, ht⟩ := pt
  have td : GlobalTheory.LN.TraitData Y a g y₁ := ⟨hy, fun W _ _ _ hW φ gam hg χ hχ =>
    ⟨good R₁ g y₁ gi gf n₁ ht hy W hW φ gam hg χ hχ, bad R₁ g y₁ gi gf n₁ hr hy W hW φ gam hg χ hχ⟩⟩
  obtain ⟨R₂, _, _, h, h', hi, hf, n₂, hh, hθ⟩ := fr₁ R₁ g y₁ gi gf n₁ td ht
  obtain ⟨td₂, hr₂, -⟩ := mono R₁ g y₁ gi gf n₁ R₂ h h' hf hh
  have gi₂ : Function.Injective (h.comp g) := hi.comp gi
  have gf₂ : (h.comp g).Finite := hf.comp gf
  obtain ⟨R₃, _, _, k, k', ki, kf, n₃, kk, hfm⟩ :=
    frm R₂ (h.comp g) (spMap h' ≫ y₁) gi₂ gf₂ n₂ (td₂ td) (hr₂ hr) hθ m hm hmu
  obtain ⟨td₃, -, hfr⟩ := mono R₂ (h.comp g) (spMap h' ≫ y₁) gi₂ gf₂ n₂ R₃ k k' kf kk
  obtain ⟨θ, hθ⟩ := hθ
  obtain ⟨f', hf'⟩ := hfr 1 1 _ hθ
  refine ⟨R₃, inferInstance, inferInstance, k.comp (h.comp g), spMap k' ≫ spMap h' ≫ y₁, ki.comp gi₂, kf.comp gf₂, n₃,
    td₃ (td₂ td), ⟨f' 0, ?_⟩, hfm⟩
  have e : (fun _ : Fin 1 => f' 0) = f' := funext fun i => by rw [Subsingleton.elim i 0]
  rw [e]; exact hf'
end GlobalTheory.Ex
