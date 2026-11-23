import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactBlockLeviSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormBlockEmbLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfIsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KinfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZfinOfKnownTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspBlockConstantTermVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspBlockConstantTermFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BlockForms

theorem exists_isCuspForm_comp_blockEmb : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        ∃ f : GlobalTheory.CuspRep.Sm E d, (∀ x, f.1 x = ψ (ι x * g₀)) ∧ GlobalTheory.CuspRep.IsCuspForm f := by
  intro hP F E _ _ _ _ _ _ σ hσ n J hJ r Xf Yf hW K hK S l d h ι hι hd h1 h2 h3 ψ hψ g₀ hg₀
  let f : GlobalTheory.CuspRep.Sm E d := ⟨fun x => ψ (ι x * g₀), GlobalTheory.T.isCuspOn_translate_mem_sm F E σ hσ n J hJ r Xf Yf hW K hK S l d h ι hι hd h1 h2 h3 ψ hψ g₀ hg₀⟩
  refine ⟨f, fun _ => rfl, ⟨⟨GlobalTheory.CuspBlockLeft.cuspForm_blockEmb_left_invariant F E σ hσ n J hJ r Xf Yf hW K hK S l d h ι hι hd h1 h2 h3 ψ hψ g₀ hg₀, ?_, ?_, GlobalTheory.CuspBlockZfin.zfin_of_classicalTheorems hP F E σ hσ n J hJ r Xf Yf hW K hK S l d h ι hι hd h1 h2 h3 ψ hψ g₀ hg₀ f (fun _ => rfl), GlobalTheory.T.cusp_block_constant_term_vanishing F E σ hσ n J hJ r Xf Yf hW K hK S l d h ι hι hd h1 h2 h3 ψ hψ g₀ hg₀⟩, GlobalTheory.T.cusp_block_constant_term_formula F E σ hσ n J hJ r Xf Yf hW K hK S l d h ι hι hd h1 h2 h3 ψ hψ g₀ hg₀⟩⟩
  · have e : {k | GlobalTheory.CuspRep.finRep E d k f = f} = {k : GL (Fin d) (GlobalTheory.CuspRep.Af E) | ∀ g, ψ (ι (g * GlobalTheory.CuspRep.finGL E d k) * g₀) = ψ (ι g * g₀)} :=
      Set.ext fun k => ⟨fun e g => congrFun (congrArg Subtype.val e) g, fun e => Subtype.ext (funext e)⟩
    rw [e]
    exact GlobalTheory.BlockLevel.isOpen_rightInv_finGL F E σ hσ n J hJ r Xf Yf hW K hK S l d h ι hι hd h1 h2 h3 ψ hψ g₀ hg₀
  · have e : (Submodule.span ℂ (Set.range fun k => GlobalTheory.CuspRep.cptRep E d k f)).map (GlobalTheory.CuspRep.Sm E d).subtype =
        Submodule.span ℂ (Set.range fun k : GlobalTheory.CuspRep.Kinf E d => fun g : GlobalTheory.CuspRep.GA E d => ψ (ι (g * GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀)) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    have := GlobalTheory.CuspKinfFin.kinf_finite F E σ hσ n J hJ r Xf Yf hW K hK S l d h ι hι hd h1 h2 h3 ψ hψ g₀ hg₀
    rw [← e] at this
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective (GlobalTheory.CuspRep.Sm E d).subtype Subtype.val_injective
      (Submodule.span ℂ (Set.range fun k => GlobalTheory.CuspRep.cptRep E d k f))).symm

end GlobalTheory.BlockForms
