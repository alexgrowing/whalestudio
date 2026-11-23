import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTuple
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StpTopIdxEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChiPowOfLevG
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemGinfCOfFinM
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem rd_emb_evz : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ θ, IsInfFam θ → ∀ emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m), IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) emb → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ β, ((∃ n : ℕ, 0 < n ∧ ∀ κ, K.lev.chi κ ^ n = 1) → ∀ h (κ : K.lev.U), GlobalTheory.Core.Rk.Top.HasMat h κ.1 → ∃ hU : emb h ∈ A.U B.R.m β, A.chi B.R.m β ⟨emb h, hU⟩ = K.lev.chi κ ∧ ‖((K.lev.chi κ : ℂˣ) : ℂ)‖ = 1) ∧ ∀ φ ∈ (I.fm l u a).Fi B.R.m, ∀ c h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 → ∀ y, A.rd θ B.R.m le_rfl β φ y (emb h) = (I.per l u a).evz φ c y := by
  intro B X I hI hP l Z u a Ch₀ A hA θ hθ emb hemb bad K hK β
  refine ⟨fun hfin => GlobalTheory.AdForm.LevChiTop.emb_mem_chi I hI hP l Z u a Ch₀ A hA emb hemb bad K hK hfin β, ?_⟩
  intro φ hφ c h hh y
  have hβ := GlobalTheory.AdForm.TwDat.Is.chOf_top_eq I hI hP l Z u a Ch₀ A hA ((I.perIn u a).tilC c) β
  subst hβ
  obtain ⟨γ, hγ, k, hk, κ, he, hv⟩ := GlobalTheory.AdForm.TwDat.Is.evz_decomp I hI hP l Z u a Ch₀ A hA θ hθ emb hemb bad K hK c h hh
  obtain ⟨y', hy', hval⟩ := hv φ hφ y
  rw [he, (GlobalTheory.AdForm.rd_charts I hI hP l Z u a Ch₀ A hA θ hθ B.R.m le_rfl φ hφ).2 _ y γ hγ ⟨(I.perIn u a).tilC c, rfl⟩ k hk κ y' hy']
  exact hval

end GlobalTheory.AdForm
