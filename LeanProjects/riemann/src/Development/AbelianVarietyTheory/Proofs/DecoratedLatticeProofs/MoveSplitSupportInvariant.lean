import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairAlongChainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLatticesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DeltaNeZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedFamilyLatticeHypAndSmooth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedThetaFamilyVectorsLatticesThetaZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LeviFactorCharactersSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationSplitSupportProjectsVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicTranslateStandardLatticeIsSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionMovesByTranslatePairStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFinitePartMemHomLatticeCompletionIffStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDetRootCharMulStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlacePairMovesLatticeVacuumReadingStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.SplitMove

open Formalism.L2.Th1.H

theorem inter_ne_zero {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {α : V → ℂ} {A₁ A₂ : AddSubgroup V} {F : V → ℂ}
    (h : inter H α A₁ A₂ F ≠ 0) : relIdx A₁ A₂ ≠ 0 := by
  intro h0
  apply h
  funext z
  simp [inter, h0]

theorem inter_zero {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A₁ A₂ : AddSubgroup V) :
    inter H α A₁ A₂ 0 = 0 := by
  funext z
  simp [inter, opU]

theorem inter_const_mul {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A₁ A₂ : AddSubgroup V)
    (c : ℂ) (F : V → ℂ) (z : V) : inter H α A₁ A₂ (fun w => c * F w) z = c * inter H α A₁ A₂ F z := by
  unfold inter
  have e : ∀ q : A₂ ⧸ A₁.addSubgroupOf A₂, α ((Quotient.out q : A₂) : V) * opU H ((Quotient.out q : A₂) : V) (fun w => c * F w) z =
      c * (α ((Quotient.out q : A₂) : V) * opU H ((Quotient.out q : A₂) : V) F z) := fun q => by
    simp only [opU]; ring
  simp only [e]
  rw [← mul_finsum]
  ring

theorem mem_LamC_toHom {D : D7} (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (z : VCx D.what₂.Tau a b) (hz : z ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :
    ∃ γ, z = embH (tauE D) δ (toHom S T hS hT γ) := by
  obtain ⟨x, -, rfl⟩ := hz
  refine ⟨(LinearMap.toMatrix' x).reindex (finCongr hT).symm (finCongr hS).symm, ?_⟩
  congr 1
  subst hS hT
  simp [toHom]

end GlobalTheory.AdForm.SplitMove

namespace GlobalTheory.AdForm.SplitMove

open GlobalTheory.ThetaMove Formalism.L2.Th1.H

set_option maxHeartbeats 1600000 in

theorem moveAt_split : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word) (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → A.MoveAt θ i hi c₀ g h → ∀ e, IsSplitIdem (I.rec7 l Z) e → ∀ s s', SuppAt e _ s → SuppAt e _ s' → A.MoveAt θ i hi c₀ (s * g) (s' * h) := by
  intro B X I l Z w u A ψ θ hA i hi c₀ g h hg hh hmv e he s s' hs hs'
  intro N₁ N₁' hN₁ hN₁' x₁ y₁ hx₁ hy₁
  have hi0 : i ≤ B.R.m := Nat.le_of_succ_le hi
  obtain ⟨hstd, hAA, hemb, hroot⟩ := GlobalTheory.T.standard_pair_along_chain I l Z w u A ψ θ hA i hi
  have hSr := rankN (I.rec7 l Z) i hi0
  have hTr := rankN (I.rec7 l Z) (i + 1) hi
  obtain ⟨N, hN⟩ := (GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual _ _ _ hSr hstd.gS).1 g
  obtain ⟨N', hN'⟩ := (GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual _ _ _ hTr hstd.gT).1 h
  obtain ⟨x, hx⟩ := hroot i hi0 g
  obtain ⟨y, hy⟩ := hroot (i + 1) hi h
  have key := hmv N N' hN hN' x y hx hy
  have hW := hA.om i hi
  have hvac := hA.vac i hi
  have hsG : s ∈ GfC _ := GlobalTheory.WeilProduct.mem_GfC_of_suppAt he hs
  have hs'G : s' ∈ GfC _ := GlobalTheory.WeilProduct.mem_GfC_of_suppAt he hs'
  have xv := fun g₀ (hg₀ : g₀ ∈ GfC _) h₀ (hh₀ : h₀ ∈ GfC _) M M' (hM : Moves _ hSr g₀ M) (hM' : Moves _ hTr h₀ M') =>
    GlobalTheory.T.movedWeilVacuum_eq_vacuum_of_movedLattices (I.rec7 l Z) ψ θ _ _ _ _ hSr hTr I.A.δ I.A.sc hstd (A.chr (i + 1)) (A.om i) hW (A.vac i) hvac g₀ hg₀ h₀ hh₀ M M' hM hM'

  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal (I.rec7 l Z) ⊤ := ⟨top_ne_bot, by simp⟩
  have hδ := ((I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 w.ok.amb_ok).1
  have hχ := GlobalTheory.Mem.ChiIdeal.isChi_chiId (I.rec7 l Z) I.C.chiPsi I.C.isChi
  have hE := (GlobalTheory.Core.Ht2.family_laws I w.ok hX l Z).1
  have hfam := GlobalTheory.NatFamily.family (I.rec7 l Z) ⊤ I.J.δ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ
  have ha : Even (B.R.N i) := hSr ▸ hstd.rk.2.2.1
  have hb : Even (B.R.N (i + 1)) := hTr ▸ hstd.rk.2.2.2
  have hMv : GlobalTheory.ThetaMove.Moves I.A (B.R.N i) (B.R.N (i + 1)) := by
    show GlobalTheory.ThetaMove.Moves (I.J.amb B I.chi) _ _
    rw [AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G]
    exact GlobalTheory.ThetaMove.SeamMoves.moves_ambOf B.fields _ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
      (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD _ _ hX (seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G) hcc hχ hE
      hfam.2.1 (hfam.2.2 _ _) ha hb
  have hemb' : B.fields.embC I.A.σ₀ = tauE (I.rec7 l Z) := funext hemb
  have hlam : ∀ M M', lam I.A (a := B.R.N i) (b := B.R.N (i + 1)) M M' =
      LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M' := by
    intro M M'
    show LamC (B.fields.embC I.A.σ₀) I.A.δ I.A.AA M M' = _
    rw [hemb', hAA]
    rfl
  have hvacT : ∀ M M', Formalism.L2.Col.IsSdLat M → Formalism.L2.Col.IsSdLat M' →
      vac I.A (a := B.R.N i) (b := B.R.N (i + 1)) M M' = I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) M M' := by
    intro M M' hM hM'
    funext z
    exact inv_mul_cancel_left₀ (hMv.2.2.2.2.1 M M' hM hM').1 _
  obtain ⟨hNsd, ΛS, hcS, hΛS⟩ := (GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual _ _ _ hSr hstd.gS).2 g N hN
  obtain ⟨hN'sd, ΛT, hcT, hΛT⟩ := (GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual _ _ _ hTr hstd.gT).2 h N' hN'
  obtain ⟨hN₁sd, ΛS₁, hcS₁, hΛS₁⟩ := (GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual _ _ _ hSr hstd.gS).2 (s * g) N₁ hN₁
  obtain ⟨hN₁'sd, ΛT₁, hcT₁, hΛT₁⟩ := (GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual _ _ _ hTr hstd.gT).2 (s' * h) N₁' hN₁'
  have v0 := xv g hg h hh N N' hN hN'
  have v1 := xv (s * g) (mul_mem hsG hg) h hh N₁ N' hN₁ hN'
  have v2 := xv (s * g) (mul_mem hsG hg) (s' * h) (mul_mem hs'G hh) N₁ N₁' hN₁ hN₁'
  have hc1 : A.om i (s, 1) (A.om i (g, h) (A.vac i)) = A.om i (s * g, h) (A.vac i) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hc2 : A.om i (1, s') (A.om i (s * g, h) (A.vac i)) = A.om i (s * g, s' * h) (A.vac i) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hth0 : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N N' ≠ 0 := by
    intro h0
    apply v0.2.2
    refine key.trans (funext fun z => ?_)
    show _ = (0 : ℂ)
    rw [h0, Pi.zero_apply, mul_zero]
  have hv1 : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N' ≠ 0 := by
    intro h0
    apply hth0
    rw [← hvacT N N' hNsd hN'sd, hMv.2.2.2.2.2.2 N₁ N N' hN₁sd hNsd hN'sd, hvacT N₁ N' hN₁sd hN'sd, h0, inter_zero]
  have hv2 : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N₁' ≠ 0 := by
    intro h0
    apply hv1
    rw [← hvacT N₁ N' hN₁sd hN'sd, hMv.2.2.2.2.2.1 N₁ N₁' N' hN₁sd hN₁'sd hN'sd, hvacT N₁ N₁' hN₁sd hN₁'sd, h0, inter_zero]
  have hrel1 : relIdx (lam I.A (a := B.R.N i) (b := B.R.N (i + 1)) N N') (lam I.A N₁ N') ≠ 0 := by
    apply inter_ne_zero (H := HV I.A.sc) (α := alV I.A.d I.A.sc) (F := vac I.A (a := B.R.N i) (b := B.R.N (i + 1)) N N')
    rw [← hMv.2.2.2.2.2.2 N N₁ N' hNsd hN₁sd hN'sd, hvacT N₁ N' hN₁sd hN'sd]
    exact hv1
  have hrel2 : relIdx (lam I.A (a := B.R.N i) (b := B.R.N (i + 1)) N₁ N') (lam I.A N₁ N₁') ≠ 0 := by
    apply inter_ne_zero (H := HV I.A.sc) (α := alV I.A.d I.A.sc) (F := vac I.A (a := B.R.N i) (b := B.R.N (i + 1)) N₁ N')
    rw [← hMv.2.2.2.2.2.1 N₁ N' N₁' hN₁sd hN'sd hN₁'sd, hvacT N₁ N₁' hN₁sd hN₁'sd]
    exact hv2
  rw [hlam N N', hlam N₁ N'] at hrel1
  rw [hlam N₁ N', hlam N₁ N₁'] at hrel2
  have hfacts : ∀ (M : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin (B.R.N i) → (I.rec7 l Z).host.E)) (M' : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin (B.R.N (i + 1)) → (I.rec7 l Z).host.E)), Formalism.L2.Col.IsSdLat M → Formalism.L2.Col.IsSdLat M' →
      IsSelfDual (HV I.A.sc) (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M') ∧
      IsSemiChar (HV I.A.sc) (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M')
        (alV (I.rec7 l Z).host.d I.A.sc) := by
    intro M M' hM hM'
    have := (hMv.2.2.2.2.1 M M' hM hM').2.2
    rw [← hlam M M']
    exact this
  haveI : Nonempty (I.rec7 l Z).what₂.Tau := Fintype.card_pos_iff.1 hX.f_pos
  have hinj := GlobalTheory.ThetaMove.embH_injective (a := B.R.N i) (b := B.R.N (i + 1)) (tauE (I.rec7 l Z)) hstd.ne
  have memL : ∀ (M : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin (B.R.N i) → (I.rec7 l Z).host.E)) (M' : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin (B.R.N (i + 1)) → (I.rec7 l Z).host.E)) x, embH (tauE (I.rec7 l Z)) I.A.δ x ∈
      LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M' ↔
      x ∈ perO ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M' := by
    intro M M' x
    exact ⟨fun ⟨y, hy, e⟩ => hinj e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.AdTh.SplitClass.exists_detAt _ he.1 s
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.AdTh.SplitClass.exists_detAt _ he.1 s'
  have st1 := GlobalTheory.T.splitPlacePair_moves_latticeVacuumReading (I.rec7 l Z) ψ θ _ _ _ _ hSr hTr I.A.δ I.A.sc hstd (A.chr (i + 1)) (A.om i) hW ΛS ΛS₁ ΛT ΛT hΛS hΛS₁
    hΛT hΛT e he s 1 hs (GlobalTheory.LeviSplitChar.suppAt_one e _) x₀ 1 hx₀ (GlobalTheory.LeviSplitChar.isDetAt_one e _)
    (by rw [hcS, hcS₁, hcT]; exact GlobalTheory.T.homLatticeCompletion_moves_by_translatePair _ _ _ _ _ hSr hTr g s h 1 N N' N₁ N' hN hN' hN₁ (by rwa [one_mul]))
    _ _ (fun γ v hv => by rw [hcS, hcT]; exact (GlobalTheory.T.rationalFinitePart_mem_homLatticeCompletion_iff _ ψ θ _ _ _ _ hSr hTr _ _ hstd ΛS ΛT N N' hcS hcT hΛS hΛT γ v hv).trans (memL N N' _).symm)
    (fun γ v hv => by rw [hcS₁, hcT]; exact (GlobalTheory.T.rationalFinitePart_mem_homLatticeCompletion_iff _ ψ θ _ _ _ _ hSr hTr _ _ hstd ΛS₁ ΛT N₁ N' hcS₁ hcT hΛS₁ hΛT γ v hv).trans (memL N₁ N' _).symm)
    (mem_LamC_toHom _ _ hSr hTr _ N₁ N') (hfacts N₁ N' hN₁sd hN'sd).1 (hfacts N N' hNsd hN'sd).2 (hfacts N₁ N' hN₁sd hN'sd).2 hrel1
    (A.om i (g, h) (A.vac i)) (by rw [hcS, hcT]; exact v0.1) v0.2.1.2 (by rw [hc1]; exact v1.2.1.2) (by rw [hc1]; exact v1.2.2)
  have mv1 : inter (HV I.A.sc) (alV (I.rec7 l Z).host.d I.A.sc)
      (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) N N')
      (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) N₁ N')
      (I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N N') = I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N' := by
    have c7 := hMv.2.2.2.2.2.2 N N₁ N' hNsd hN₁sd hN'sd
    rw [hvacT N N' hNsd hN'sd, hvacT N₁ N' hN₁sd hN'sd, hlam N N', hlam N₁ N'] at c7
    exact c7.symm
  have mv2 : inter (HV I.A.sc) (alV (I.rec7 l Z).host.d I.A.sc)
      (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) N₁ N')
      (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) N₁ N₁')
      (I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N') = I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N₁' := by
    have c6 := hMv.2.2.2.2.2.1 N₁ N' N₁' hN₁sd hN'sd hN₁'sd
    rw [hvacT N₁ N' hN₁sd hN'sd, hvacT N₁ N₁' hN₁sd hN₁'sd, hlam N₁ N', hlam N₁ N₁'] at c6
    exact c6.symm
  have e1 : xiN θ _ _ hSr hTr I.A.δ I.A.sc (A.om i (s * g, h) (A.vac i)) = fun z =>
      ((A.chr (i + 1) x₀ : ℂ))⁻¹ * (c₀ * ((A.chr (i + 1) x : ℂ))⁻¹ * (A.chr (i + 1) y : ℂ)) * I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N' z := by
    rw [← hc1]
    refine st1.trans (funext fun z => ?_)
    rw [show xiN θ _ _ hSr hTr I.A.δ I.A.sc (A.om i (g, h) (A.vac i)) = _ from key]
    erw [inter_const_mul]
    erw [mv1]
    simp only [map_one, Circle.coe_one, mul_one]
    ring
  have st2 := GlobalTheory.T.splitPlacePair_moves_latticeVacuumReading (I.rec7 l Z) ψ θ _ _ _ _ hSr hTr I.A.δ I.A.sc hstd (A.chr (i + 1)) (A.om i) hW ΛS₁ ΛS₁ ΛT ΛT₁ hΛS₁ hΛS₁
    hΛT hΛT₁ e he 1 s' (GlobalTheory.LeviSplitChar.suppAt_one e _) hs' 1 y₀ (GlobalTheory.LeviSplitChar.isDetAt_one e _) hy₀
    (by rw [hcS₁, hcT, hcT₁]; exact GlobalTheory.T.homLatticeCompletion_moves_by_translatePair _ _ _ _ _ hSr hTr (s * g) 1 h s' N₁ N' N₁ N₁' hN₁ hN' (by rwa [one_mul]) hN₁')
    _ _ (fun γ v hv => by rw [hcS₁, hcT]; exact (GlobalTheory.T.rationalFinitePart_mem_homLatticeCompletion_iff _ ψ θ _ _ _ _ hSr hTr _ _ hstd ΛS₁ ΛT N₁ N' hcS₁ hcT hΛS₁ hΛT γ v hv).trans (memL N₁ N' _).symm)
    (fun γ v hv => by rw [hcS₁, hcT₁]; exact (GlobalTheory.T.rationalFinitePart_mem_homLatticeCompletion_iff _ ψ θ _ _ _ _ hSr hTr _ _ hstd ΛS₁ ΛT₁ N₁ N₁' hcS₁ hcT₁ hΛS₁ hΛT₁ γ v hv).trans (memL N₁ N₁' _).symm)
    (mem_LamC_toHom _ _ hSr hTr _ N₁ N₁') (hfacts N₁ N₁' hN₁sd hN₁'sd).1 (hfacts N₁ N' hN₁sd hN'sd).2
    (hfacts N₁ N₁' hN₁sd hN₁'sd).2 hrel2
    (A.om i (s * g, h) (A.vac i)) (by rw [hcS₁, hcT]; exact v1.1) v1.2.1.2 (by rw [hc2]; exact v2.2.1.2) (by rw [hc2]; exact v2.2.2)
  have rx := GlobalTheory.T.splitPlace_detRootChar_mul _ _ (A.chr (i + 1)) _ hstd.rk.2.2.1 hW.resS e he s g hs x₀ x x₁ hx₀ hx hx₁
  have ry := GlobalTheory.T.splitPlace_detRootChar_mul _ _ (A.chr (i + 1)) _ hstd.rk.2.2.2 hW.resT e he s' h hs' y₀ y y₁ hy₀ hy hy₁
  rw [← hc2]
  refine st2.trans (funext fun z => ?_)
  rw [e1]
  erw [inter_const_mul]
  erw [mv2]
  rw [rx, ry]
  simp only [map_one, Circle.coe_one, inv_one, one_mul, Circle.coe_mul, mul_inv]
  ring

end GlobalTheory.AdForm.SplitMove
