import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCombAtReN
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.TopLocData
section Gen
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
end Gen
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} {f : _root_.GlobalTheory.Fam.FamilyCharacter W u}
  {v : VCom f.c}
theorem s_eq_alt (G : GLoc v) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) : G.s = j := by
  have := G.hs; omega
def frameOfSuccessor (G : GLoc v) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) :
    Frame G.k (Yc D (j + 1)).rank (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) ⊕ Fin 0) :=
  reN (congrArg (fun s => (Yc D (s + 1)).rank) (_root_.GlobalTheory.TopLocData.s_eq_alt G h)) (G.FY (G.s + 1) 0 rfl)
def successorFrameMatrix (G : GLoc v) : SB (Matrix (Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (G.s + 2))
    (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) ⊕ Fin 0) G.k) :=
  ⟨(G.S.T (Fin D.R.t)).PhiTop, (GModel.phi_sb G).2⟩
def eigenvectorAtPlace {n : ℕ} {G : Fin n → GLoc v} (hGP : GPin G) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) (i : Fin n) :
    WO (Yc D (j + 1)) D.sp.X' →₀ ℂ :=
  Classical.choose (hGP.eGT j h) i
theorem eGT_comb_eq_foldr_eigenvectorAtPlace {n : ℕ} {G : Fin n → GLoc v} (hGP : GPin G) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) :
    (∀ i, HEq (_root_.GlobalTheory.TopLocData.eigenvectorAtPlace hGP h i) (G i).egT) ∧ ∀ F, IsThetaFunO f.c.ψ _ _ F →
      comb f.c.ψ _ _ (v.eGT j h) F = (List.finRange n).foldr (fun i g => comb f.c.ψ _ _ (_root_.GlobalTheory.TopLocData.eigenvectorAtPlace hGP h i) g) F :=
  Classical.choose_spec (hGP.eGT j h)
theorem eigenvectorAtPlace_isCombAt {n : ℕ} {G : Fin n → GLoc v} (hGP : GPin G) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) (i : Fin n) :
    (ofSplit (G i).q).IsCombAt f.c.ψ (_root_.GlobalTheory.TopLocData.frameOfSuccessor (G i) h) (G i).FT (_root_.GlobalTheory.TopLocData.eigenvectorAtPlace hGP h i) (_root_.GlobalTheory.TopLocData.successorFrameMatrix (G i)).1 :=
  isCombAt_reN (G i).q f.c.ψ (G i).FT _ (_root_.GlobalTheory.TopLocData.s_eq_alt (G i) h) ((G i).FY ((G i).s + 1) 0 rfl) (G i).egT _
    ((_root_.GlobalTheory.TopLocData.eGT_comb_eq_foldr_eigenvectorAtPlace hGP h).1 i) (G i).egT_is
def localLatticeAtPlace (hψ : IsStdChar D f.c.ψ (-1)) {n : ℕ} {G : Fin n → GLoc v} (hGP : GPin G) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m)
    {M : GlobalTheory.FinPl.Lat (Yc D (j + 1))} (hM : IsSelfDualC (Yc D (j + 1)) M) (hLT : IsSelfDualC D.sp.X' f.g.LT) (i : Fin n) :
    LocPl f.c.ψ (Yc D (j + 1)) D.sp.X' M f.g.LT :=
  mkPl hψ (G i).q (G i).unit (_root_.GlobalTheory.TopLocData.frameOfSuccessor (G i) h) (G i).FT (_root_.GlobalTheory.TopLocData.successorFrameMatrix (G i)) (_root_.GlobalTheory.TopLocData.eigenvectorAtPlace hGP h i) (_root_.GlobalTheory.TopLocData.eigenvectorAtPlace_isCombAt hGP h i) hM hLT
end GlobalTheory.TopLocData
end
end
