import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoeLatFrameOfEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoCptOfIsAnisoOrPosDef
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiTContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactGinfCOfOntoUni

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.AdForm.PinInhab
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def stdSp {D : D7} (V : HSp D) : DefSp V :=
  ⟨fun _ => 1, fun _ => 1, GlobalTheory.PlaceModel.latFrame V, (GlobalTheory.Unf.VolExist.nonempty_vol V).some⟩

theorem gramAt_one {D : D7} {V : HSp D} (h : V.gram = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  rw [gramAt, h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem stdSp_is {D : D7} {V : HSp D} (hs : V.SigOK) (h : V.gram = 1) : (stdSp V).Is where
  sig := hs
  cpt := (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D V).2 fun τ => by rw [gramAt_one h]; exact Matrix.PosDef.one
  cart := fun τ => VacStd.cartan_of_gram h τ
  pm := fun _ => Or.inl rfl
  onb := fun τ => ⟨V.rank, fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, by simp [gramAt_one h, stdSp], by simp [stdSp]⟩
  sd := GlobalTheory.PlaceModel.isSelfDualC_latFrame V

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}

theorem gram_X (hI : I.Ok) (j : ℕ) : ((I.rec7 l Z).sp.X j).gram = 1 := by
  obtain ⟨hs, hX, -⟩ := hI.spaces
  exact VacStd.gram_of_eq _ hs _ (hX j)

theorem lat_X (hI : I.Ok) (j : ℕ) :
    (GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X j) : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) =
      GlobalTheory.AdForm.intVec (I.rec7 l Z) _ := by
  obtain ⟨hs, hX, -⟩ := hI.spaces
  exact VacStd.coe_latFrame_of_eq _ hs _ (hX j)

theorem exists_vac (hI : I.Ok) {ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ} {θ : InfFam (I.rec7 l Z)}
    (hψ : IsStdChar (I.rec7 l Z) ψ (-1)) (hθ : IsInfFam θ) (i : ℕ) :
    ∃ f, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) f := by
  obtain ⟨f, hf⟩ := GlobalTheory.Member.vacuum_oriented_exists (I.rec7 l Z) ψ θ hψ hθ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))
    (fun _ => 1) (fun _ => 1) ((I.rec7 l Z).sp.X_sig _) ((I.rec7 l Z).sp.X_sig _)
    (fun τ => VacStd.cartan_of_gram (gram_X hI _) τ) (fun τ => VacStd.cartan_of_gram (gram_X hI _) τ)
    _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame _) (GlobalTheory.PlaceModel.isSelfDualC_latFrame _)
  rw [lat_X hI i, lat_X hI (i + 1)] at hf
  exact ⟨f, hf⟩

theorem volLev_ne_zero (hI : I.Ok) {θ : InfFam (I.rec7 l Z)} (hθ : IsInfFam θ) {Ch : ℕ → Type}
    {A : TwDat I l Z u a Ch} (j : ℕ) (v : GlobalTheory.Unf.Vol ((I.rec7 l Z).sp.X j)) (β : Ch j)
    (hr : IsReps ((I.rec7 l Z).sp.X j) (A.U j β) (A.h j β)) : volLev v (A.U j β) ≠ 0 := by
  have hu := GlobalTheory.SeeSaw.ontoUni_inB _ θ ((I.rec7 l Z).sp.X j) (fun _ => 1) hθ fun τ => by
    rw [gramAt_one (gram_X hI j)]; simp
  obtain ⟨-, -, -, ν, -, -, h⟩ := GlobalTheory.SeeSaw.integral_eq_classSum _ θ _ _ hθ hu
  letI : Fintype {c : (I.stp u a j).Cl // A.chOf j c = β} := @Subtype.fintype _ _ _ ((I.chain l u a).clsFin j)
  exact (h v _ _ _ hr).1.ne'

end GlobalTheory.AdForm.PinInhab
