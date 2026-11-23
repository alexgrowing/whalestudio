import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFrameCol
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseRowFourierTransformMemSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierInversionInverseRowTransformNegOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionCompSkewAdjointSimilitudeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SkewAdjointSimilitudeExchangesHalvesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFormHalfSkewAdjointImageStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KappaModel
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

theorem kappa_model : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (L S L'' : HSp D) (ζ : Fin L.rank → D.host.E) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), L''.rank = 1 → τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ (s : k) (z₀ : Fin L''.rank → k), s ≠ 0 → τ.map p.pr *ᵥ z₀ = (-(p.xi * s)) • (fun i => p.pr (ζ i)) → ∀ (n : Type) [Fintype n] [DecidableEq n] (FS : Frame k S.rank n) (FL : Frame k L.rank Unit), (∀ r, FL.β r () = s * p.pr (ζ r)) → ∀ TLS, p.IsModel ψ FL FS TLS → ∃ FL'' : Frame k L''.rank Unit, (∀ r, FL''.β r () = z₀ r) ∧ ∃ TL, p.IsModel ψ FS FL'' TL ∧ ∀ (c : SB (Matrix n Unit k)) (Φ : SB (Matrix Unit n k)), (∀ η, Φ.1 η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (η ())) → ∀ w, TL Φ w = TLS c (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * w)) := by
  intro D k _ _ _ _ _ _ p ν hν ψ hψ ψk hk L S L'' ζ τ hrk hτ s z₀ hs hz n _ _ FS FL hFL TLS hTLS
  obtain ⟨-, hk2, hxi, -, -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨hcont, hne⟩ := hk2 ψk hk
  have hz0 : z₀ ≠ 0 := by
    intro h0
    rw [h0, Matrix.mulVec_zero] at hz
    have h1 := congrFun (congrFun FL.γβ ()) ()
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    have h2 : ∀ r, FL.β r () = 0 := fun r => by
      have h3 := congrFun hz r
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at h3
      have hx : p.xi * s ≠ 0 := mul_ne_zero hxi hs
      have h4 : p.pr (ζ r) = 0 := by
        rcases mul_eq_zero.1 h3.symm with h | h
        · exact absurd (neg_eq_zero.1 h) hx
        · exact h
      rw [hFL, h4, mul_zero]
    simp [h2] at h1
  obtain ⟨FL'', hFL''⟩ := exists_frame_col hrk z₀ hz0
  refine ⟨FL'', hFL'', ?_⟩
  set κ : WO S L'' → WO L S := fun w => ofAdj L S ((rat τ : Mx D L.rank L''.rank) * w) with hκdef
  have hτ' : τᴴ * (L.gram * τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L''.gram := by
    rw [hτ]; congr 1; push_cast; ring
  obtain ⟨hadd, -, -, -, hsy, -⟩ := GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1) hτ' κ (fun _ => rfl)
  have hsy' : ∀ w w', symplO L S (κ w) (κ w') = symplO S L'' w w' := fun w w' => by
    rw [hsy]; push_cast; ring
  obtain ⟨C, hC⟩ := GlobalTheory.T.fourierInversion_inverseRowTransform_negOne k n ψk ν hcont hne hν
  haveI := hν
  let H : SB (Matrix Unit n k) →ₗ[ℂ] SB (Matrix n Unit k) :=
    { toFun := fun Φ => ⟨finv ψk ν C Φ.1, GlobalTheory.T.inverseRowFourierTransform_mem_schwartzBruhat k n ψk ν hcont hne hν C Φ.1 Φ.2⟩
      map_add' := fun Φ Ψ => Subtype.ext (finv_add ψk hcont ν C Φ.2 Ψ.2)
      map_smul' := fun a Φ => Subtype.ext (finv_smul ψk ν C a Φ.1) }
  let TL : SB (Matrix Unit n k) →ₗ[ℂ] (WO S L'' → ℂ) := (LinearMap.funLeft ℂ ℂ κ) ∘ₗ TLS ∘ₗ H
  have hTL : ∀ Φ w, TL Φ w = TLS (H Φ) (κ w) := fun _ _ => rfl
  obtain ⟨-, -, -, hpsi, -⟩ := GlobalTheory.LocSympl.halves_at_split D k p n Unit L S FL FS ψ ψk hk
  have hhalf : ∀ x, IsHalf (cA D p.e) (κ (p.up FS FL'' x)) := fun x =>
    (GlobalTheory.T.skewAdjointSimilitude_exchanges_halves D L S L'' τ p.e _).2 (Witness.up_half p FS FL'' x)
  have hkey : ∀ x a, ψ (symplO L S (p.up FL FS a) (κ (p.up FS FL'' x))) = (ψk (-(∑ r, x () r * a r ())) : ℂ) := by
    intro x a
    rw [hpsi a _ (hhalf x)]
    exact congrArg (fun u => ((ψk u : Circle) : ℂ)) (GlobalTheory.T.splitPlace_hermitianForm_half_skewAdjointImage D k p L S L'' ζ τ s z₀ hs hz n FS FL FL'' hFL hFL'' x a)
  refine ⟨TL, ⟨fun Φ => ?_, fun x Φ Φ' h => ?_, fun y hy Φ Φ' h => ?_⟩, fun c Φ hΦ w => ?_⟩
  · exact GlobalTheory.T.isThetaFunction_comp_skewAdjointSimilitude D ψ L S L'' τ hτ _ (hTLS.theta _)
  · funext w
    show TLS (H Φ') (κ w) = heisO ψ S L'' (p.up FS FL'' x) (fun w => TLS (H Φ) (κ w)) w
    rw [← heis_comp ψ L S L'' κ hadd hsy']
    rw [hTLS.modul (κ (p.up FS FL'' x)) (hhalf x) (H Φ) (H Φ') (fun t => ?_)]
    show finv ψk ν C Φ'.1 t = _ * finv ψk ν C Φ.1 t
    rw [finv_trans ψk ν C x h t, hkey]
  · have hy' : IsHalf p.e (κ y) := (GlobalTheory.T.skewAdjointSimilitude_exchanges_halves D L S L'' τ p.e y).1 hy
    set t₀ := p.down FL FS (κ y) with ht₀
    have hup : p.up FL FS t₀ = κ y := Witness.up_down p FL FS hy'
    have hmod : ∀ t, Φ'.1 t = (ψk (∑ r, t () r * t₀ r ()) : ℂ) * Φ.1 t := fun t => by
      rw [h t, ← hsy', ← hup, GlobalTheory.OrientedHeis.symplO_skew, AddChar.map_neg_eq_inv, hkey, AddChar.map_neg_eq_inv,
        Circle.coe_inv, inv_inv]
    funext w
    show TLS (H Φ') (κ w) = heisO ψ S L'' y (fun w => TLS (H Φ) (κ w)) w
    rw [← heis_comp ψ L S L'' κ hadd hsy', ← hup]
    rw [hTLS.trans t₀ (H Φ) (H Φ') (fun t => finv_mod ψk ν C t₀ hmod t)]
  · show TLS (H Φ) (κ w) = _
    have : H Φ = c := Subtype.ext (hC c.1 c.2 Φ.1 hΦ)
    rw [this]
end GlobalTheory.KappaModel

end
