import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtOfFactors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdDifferent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem unfIsAll_of_same {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {O O' : GL3Theta.LiftObj D C}
    (hf : O.frm = O'.frm) (hd : O.dgen = O'.dgen) (hT : O.Th = O'.Th) {i : ℕ} (h : UnfIsAll O i) : UnfIsAll O' i := by
  have e1 : ∀ n, frPoly O n = frPoly O' n := fun n => LinearMap.ext fun Q => by
    funext y
    show GL3Theta.evFr D Q (O.frm n y) = GL3Theta.evFr D Q (O'.frm n y)
    rw [hf]
  have e2 : frInv O i = frInv O' i := by
    unfold frInv
    simp only [e1]
  have e3 : ∀ Θ, unfC O i Θ = unfC O' i Θ := fun Θ => by
    unfold unfC
    rw [e1 (i + 1), e2, hd]
  intro c c' Q
  have h1 := h c c' Q
  rw [e1 i, e3, hT] at h1
  exact h1

theorem isSel_of_heq {X' X₀ : Fields} (h : X' = X₀) {s' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)}
    {s : HeightOneSpectrum (𝓞 X₀.F) → HeightOneSpectrum (𝓞 X₀.E)} (hs : HEq s' s) (H : IsSel X₀ s) : IsSel X' s' := by
  subst h
  obtain rfl := eq_of_heq hs
  exact H

theorem kernel_inputs : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → t.TopPinned → I.IsTw → t.AAUnit ∧ t.UnfAll := by
  intro B X I hok hp l Z L hT Gi Gl K Y cX ex t hS _ _
  refine ⟨fun u μ P hP => ?_, fun u μ i hi => ?_⟩
  · have hsel : IsSel t.X t.sel := isSel_of_heq hS.X_eq hS.sel hok.sel_ok
    have hXok : t.X.Ok := hS.X_eq ▸ FieldsLaws.fields_ok B
    have hTS : t.Pr.T (t.word u) ∈ t.S := by
      rw [t.T_rec, hS.S]
      exact hok.T_mem u
    have hgS : ∀ k, t.Pr.g k ∈ t.S := fun k => by
      rw [t.g_rec, hS.S]
      exact hok.g_mem k
    have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes t.X t.Pr t.sel t.S (t.tup μ) (t.word u) hXok t.pr_ok hsel hTS hgS P hP
    have hcop : Nat.Coprime (Ideal.absNorm t.cc) (Ideal.absNorm P.asIdeal) := by
      have h1 : t.cc = ⊤ := t.cc_rec.trans B.toPre.ccK_top
      rw [h1, Ideal.absNorm_top]
      exact Nat.coprime_one_left _
    exact GlobalTheory.PeriodIdealUnit.locP_AA_eq_one t.X _ t.seam t.cc t.δ t.B t.χ t.cD P bad.2.1 bad.2.2.1 hcop
  · obtain ⟨O₀, h0, hU⟩ := lift_objects I hok hp l Z Y.Qp
    have hO := hS.O
    refine unfIsAll_of_same (O := O₀ u μ) ?_ ?_ ?_ (hU u μ i hi)
    · funext n y
      rw [h0.frm, hO.frm]
    · rw [h0.dgen, hO.dgen]
    · funext n c c'
      rw [h0.Th, hO.Th]

end GlobalTheory.Mem.Col2.TC

end
