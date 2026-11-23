import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweInj
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweEx
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.WhitOne
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.ConvolutionTheory.Loc.howeLine :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π → π.IsIrreducible → GlobalTheory.LocGL.IsGeneric π → ∀ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E → ∀ c : ℤ, ∃ a₀ : ℤ, ∀ a ≥ a₀,
      ∀ ψ : AddChar E Circle, HasConductor ψ (ϖ ^ (2 * a - c)) → Module.finrank ℂ (howeSpace π ψ (howeSet n ϖ a c)) = 1 := by
  intro E _ _ _ _ n V _ _ π hs hi hg ϖ hϖ c
  obtain ⟨a₀, h⟩ := howeEx E n V π hs ϖ hϖ hg c
  refine ⟨max 1 a₀, fun a ha ψ hψ => ?_⟩
  have h1 := whitOne E n V π hs hi ψ hψ.continuous hψ.ne_one
  let f := (twKer π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n)).mkQ ∘ₗ (howeSpace π ψ (howeSet n ϖ a c)).subtype
  have hf : Function.Injective f := (injective_iff_map_eq_zero f).2 fun v hv =>
    Subtype.ext (howeInj E n V π hs ϖ hϖ a c (le_trans (le_max_left _ _) ha) ψ hψ v.1 v.2 ((Submodule.Quotient.mk_eq_zero _).1 hv))
  have h2 : Module.rank ℂ (howeSpace π ψ (howeSet n ϖ a c)) ≤ 1 := (LinearMap.rank_le_of_injective f hf).trans h1
  have h3 := Submodule.nontrivial_iff_ne_bot.2 (h a (le_trans (le_max_right _ _) ha) ψ hψ)
  exact Module.finrank_eq_of_rank_eq (le_antisymm (by simpa using h2) (by simpa using Cardinal.one_le_iff_pos.2 rank_pos))
