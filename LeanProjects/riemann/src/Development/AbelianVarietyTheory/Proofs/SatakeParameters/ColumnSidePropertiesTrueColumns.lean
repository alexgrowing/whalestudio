import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetIdStdBot
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

namespace GlobalTheory.Pdv

theorem colSide_of_choices {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts}
    {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hN : GlobalTheory.Pdv.ColNorm I)
    (hX_eq : t.X = B.fields) (hseam : HEq t.seam (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)) (hPr : HEq t.Pr (B.primes X))
    (hCh : HEq t.Ch I.Ch) (hsel : HEq t.sel I.sel) (hS : t.S = I.S) (htup : HEq t.tup I.tup) (hcst : HEq t.cst I.cst)
    (hidx : HEq t.idx I.idx) (hm2 : t.m2 = B.R.m - 2) (hglob : HEq t.glob I.glob) : GlobalTheory.KerJ.ColSide t := by
  have hb := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have kCst : ∀ (X' : Fields) (Pr' : Primes X') (sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)) (S' : Set ℕ)
      (tup' : (I.rec7 l Z).what₂.Tup → Tup X'.F X'.E X'.K S') (cst' : ∀ μ, LocCst X' (rowSG Pr' sel' (tup' μ))),
      X' = B.fields → HEq Pr' (B.primes X) → HEq sel' I.sel → S' = I.S → HEq tup' I.tup → HEq cst' I.cst →
      ∀ μ, (cst' μ).sharp = true ∧ (I.rec7 l Z).R.m ≤ (cst' μ).A ∧ 2 * (cst' μ).M ≤ twTopDepth (I.rec7 l Z).R := by
    rintro X' Pr' sel' S' tup' cst' rfl h1 h2 rfl h3 h4
    obtain rfl := eq_of_heq h1
    obtain rfl := eq_of_heq h2
    obtain rfl := eq_of_heq h3
    obtain rfl := eq_of_heq h4
    intro μ
    have h5 := (hN μ)
    refine ⟨hI.sharp μ, h5.1, ?_⟩
    show 2 * (I.cst μ).M ≤ 4 * B.R.m + 1
    omega
  refine ⟨?fields, ?sel, ?bad, ?chOk, ?chars, ?sharp, ?deep, ?repOne⟩
  case fields => exact hX_eq ▸ hb.1
  case sel =>
    have key : ∀ (X' : Fields) (sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)),
        X' = B.fields → HEq sel' I.sel → IsSel X' sel' := by
      rintro X' sel' rfl h
      obtain rfl := eq_of_heq h
      exact hI.sel_ok
    exact key _ _ hX_eq hsel
  case bad =>
    have key : ∀ (X' : Fields) (Pr' : Primes X'), X' = B.fields → HEq Pr' (B.primes X) → ∀ v, Pr'.T v ∈ I.S := by
      rintro X' Pr' rfl h
      obtain rfl := eq_of_heq h
      exact hI.T_mem
    rw [hS]
    refine ⟨fun i => ?_, key _ _ hX_eq hPr, fun _ hl => hI.small_mem hl, hI.two_q_d_mem.2.1⟩
    rw [t.g_rec]
    exact hI.g_mem i
  case chOk =>
    have key : ∀ (X' : Fields) (Pr' : Primes X') (Ch' : Chars X' Pr' (I.rec7 l Z).R.m), X' = B.fields → HEq Pr' (B.primes X) →
        HEq Ch' I.Ch → Ch'.Ok := by
      rintro X' Pr' Ch' rfl h1 h2
      obtain rfl := eq_of_heq h1
      obtain rfl := eq_of_heq h2
      exact hI.ch_ok
    exact key _ _ _ hX_eq hPr hCh
  case chars =>
    have key : ∀ (X' : Fields) (Pr' : Primes X') (Ch' : Chars X' Pr' (I.rec7 l Z).R.m) (glob' : ChGlob X' (I.rec7 l Z).R.m)
        (seam' : Seam (I.rec7 l Z) X'), X' = B.fields → HEq Pr' (B.primes X) →
        HEq Ch' I.Ch → HEq glob' I.glob → HEq seam' (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) →
        ∃ eta, Ch'.Tied glob'.σ₀ (fun j τ => ((I.rec7 l Z).hc (seam'.iT τ)).e j) glob'.mu0 eta := by
      rintro X' Pr' Ch' glob' seam' rfl h1 h2 h3 h4
      obtain rfl := eq_of_heq h1
      obtain rfl := eq_of_heq h2
      obtain rfl := eq_of_heq h3
      obtain rfl := eq_of_heq h4
      exact ⟨I.C.eta, hI.ch_tied⟩
    exact key _ _ _ _ _ hX_eq hPr hCh hglob hseam
  case sharp => exact fun μ => (kCst _ _ _ _ _ _ hX_eq hPr hsel hS htup hcst μ).1
  case deep => exact fun μ => (kCst _ _ _ _ _ _ hX_eq hPr hsel hS htup hcst μ).2
  case repOne =>
    have key : ∀ (X' : Fields) (Pr' : Primes X') (sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)) (S' : Set ℕ)
        (tup' : (I.rec7 l Z).what₂.Tup → Tup X'.F X'.E X'.K S')
        (idx' : ∀ μ, ChIdx X' Pr' (I.rec7 l Z).R (QE sel' (tup' μ : Chr X'.F X'.E X'.K))),
        X' = B.fields → HEq Pr' (B.primes X) → HEq sel' I.sel → S' = I.S → HEq tup' I.tup → HEq idx' I.idx →
        ∀ μ j, j ≤ B.R.m - 2 + 1 → ∀ (b : (idx' μ).β j) (P : rowSG Pr' sel' (tup' μ)), P.1 ∈ Pr'.vGs → (idx' μ).h j b P = 1 := by
      rintro X' Pr' sel' S' tup' idx' rfl h1 h2 rfl h3 h4
      obtain rfl := eq_of_heq h1
      obtain rfl := eq_of_heq h2
      obtain rfl := eq_of_heq h3
      obtain rfl := eq_of_heq h4
      intro μ
      exact (hN μ).2.2
    rw [hm2]
    exact key _ _ _ _ _ _ hX_eq hPr hsel hS htup hidx

theorem colSide_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → I.StdKer l Z t → GlobalTheory.KerJ.ColSide t := by
  intro B X I hI _ l Z L hT Gi Gl K Y cX ex t hN hS
  exact colSide_of_choices I hI l Z t hN hS.X_eq hS.seam hS.Pr hS.Ch hS.sel hS.S hS.tup hS.cst hS.idx hS.m2 hS.glob

end GlobalTheory.Pdv
