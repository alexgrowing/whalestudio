import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TripleWeilTransfer

variable {D : D7}

theorem isThetaFunO_of_mem_algF {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (ε : Bool) {M X : HSp D} (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) {Φ : WO M X → ℂ}
    (hΦ : Φ ∈ algF ψ θ ε A B) : IsThetaFunO ψ (GlobalTheory.Grid.sgn ε M) X Φ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, P, hf, rfl⟩ := hx
    exact GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P
  | zero => exact GlobalTheory.OrientedHeis.theta_zero
  | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
  | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx

theorem eq_on_theta {ψ : AddChar (AF D.host.F) ℂ} (ε : Bool) {M X : HSp D} {χ χ' : (AE D)ˣ →* Circle}
    {ω ω' : GlobalTheory.Grid.WRep M X} (h : GlobalTheory.Grid.IsWeil ψ ε M X χ χ' ω) (h' : GlobalTheory.Grid.IsWeil ψ ε M X χ χ' ω')
    (p : GA D M × GA D X) (f : WO M X → ℂ) (hf : IsThetaFunO ψ (GlobalTheory.Grid.sgn ε M) X f) : ω p f = ω' p f := by
  have e := GlobalTheory.WeilUniq.weilDatum_unique D ψ h.std _ X χ χ' _ _ h h' ((GlobalTheory.Grid.ofSgn ε M).symm p.1, p.2) f hf
  simpa [GlobalTheory.Grid.WRep.toSgn] using e

theorem isCoinvMap_congr {θ : InfFam D} {M X : HSp D} {ω ω' : GlobalTheory.Grid.WRep M X} {S : Submodule ℂ (WO M X → ℂ)}
    {Pi : ModuleCat.{0} ℂ} {rf : GA D X → Module.End ℂ Pi}
    {rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi} {p : (WO M X → ℂ) →ₗ[ℂ] Pi}
    (he : ∀ q, ∀ Φ ∈ S, ω q Φ = ω' q Φ) (h : GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsCoinvMap θ ω S Pi rf rl p) : GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsCoinvMap θ ω' S Pi rf rl p := by
  obtain ⟨⟨sM1, sM2⟩, ⟨sX1, sX2⟩, onto, invf, invl, eqf, eql⟩ := h
  refine ⟨⟨fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ => ?_⟩, ⟨fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ => ?_⟩, onto,
    fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ Φ' hΦ' hd => ?_, fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ Φ' hΦ' hd => ?_⟩
  · rw [← he _ Φ hΦ]; exact sM1 g hg Φ hΦ
  · obtain ⟨Φ', h1, h2⟩ := sM2 τ Y hY Φ hΦ
    refine ⟨Φ', h1, fun z => ?_⟩
    simpa only [he _ Φ hΦ] using h2 z
  · rw [← he _ Φ hΦ]; exact sX1 g hg Φ hΦ
  · obtain ⟨Φ', h1, h2⟩ := sX2 τ Y hY Φ hΦ
    refine ⟨Φ', h1, fun z => ?_⟩
    simpa only [he _ Φ hΦ] using h2 z
  · rw [← he _ Φ hΦ]; exact invf g hg Φ hΦ
  · exact invl τ Y hY Φ hΦ Φ' hΦ' (fun z => by simpa only [he _ Φ hΦ] using hd z)
  · rw [← he _ Φ hΦ]; exact eqf g hg Φ hΦ
  · exact eql τ Y hY Φ hΦ Φ' hΦ' (fun z => by simpa only [he _ Φ hΦ] using hd z)

theorem exists_isMatch : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β → (∃ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p') → ∀ (ωA : GlobalTheory.Grid.WRep W X) (ωB : GlobalTheory.Grid.WRep W₁ X), GlobalTheory.Grid.IsWeil ψ true W X β (β / α) ωA → GlobalTheory.Grid.IsWeil ψ false W₁ X α (α / β) ωB → ∃ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' := by
  intro _ _ _ _ D ψ θ hψ hθ W W₁ X A A₁ B α β _ ⟨ωA₀, ωB₀, Pi, rf, rl, p, p', hm⟩ ωA ωB hA hB
  refine ⟨Pi, rf, rl, p, p', hA, hB, hm.irred, ?_, ?_⟩
  · exact isCoinvMap_congr (fun q Φ hΦ => eq_on_theta true hm.weilA hA q Φ (isThetaFunO_of_mem_algF hψ hθ true A B hΦ))
      hm.mapA
  · exact isCoinvMap_congr (fun q Φ hΦ => eq_on_theta false hm.weilB hB q Φ (isThetaFunO_of_mem_algF hψ hθ false A₁ B hΦ))
      hm.mapB

end GlobalTheory.TripleWeilTransfer

end
