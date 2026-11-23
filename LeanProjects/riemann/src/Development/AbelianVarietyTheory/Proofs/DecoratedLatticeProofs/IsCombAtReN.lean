import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocPlOff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsFoldr
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

def reN {N N' : ℕ} (h : N = N') (F : Frame k N Y) : Frame k N' Y := h ▸ F

@[simp] theorem reN_rfl {N : ℕ} (F : Frame k N Y) : reN rfl F = F := rfl

theorem exists_o {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (q : GlobalTheory.FinPl.SplitPt D k)
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}
    (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') :
    ∃ o : WO S T →₀ ℂ, (∀ x ∈ o.support, IsHalf (q.e + cA D q.e) x) ∧
      ∀ Tm, (ofSplit q).IsModel ψ FS FT Tm → ∀ Φ₀ Φ₁ : SB (Matrix Y Y' k), IsOne Φ₁ →
        Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) →
        Tm Φ₁ = comb ψ S T o (Tm Φ₀) := by
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  obtain ⟨Φ₀, h1, h2⟩ := LocPlInhab.exists_latInd q FS FT hS hT
  obtain ⟨o, o1, o2⟩ := GlobalTheory.LocComb.exists_comb D k (ofSplit q) Y Y' S T FS FT ψ hψ Φ₀ O (by rintro rfl; simp at h1)
  refine ⟨o, o1, fun Tm hT a b hb ha => ?_⟩
  obtain rfl : b = O := Subtype.ext (hb.trans hO.symm)
  obtain rfl : a = Φ₀ := Subtype.ext (ha.trans h2.symm)
  exact o2 Tm hT

def mkPl {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (q : GlobalTheory.FinPl.SplitPt D k) (hu : q.UnitAA)
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : SB (Matrix Y Y' k)) (e : WO S T →₀ ℂ)
    (he : (ofSplit q).IsCombAt ψ FS FT e Φ.1) {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}
    (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') : LocPl ψ S T M M' :=
  ⟨k, q, hu, Y, Y', FS, FT, Φ, e, he, Classical.choose (exists_o hψ q FS FT hS hT),
    (Classical.choose_spec (exists_o hψ q FS FT hS hT)).1, (Classical.choose_spec (exists_o hψ q FS FT hS hT)).2⟩

end Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} {f : FamCh W u}
  {v : VCom f.c}

theorem s_eq (G : GLoc v) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) : G.s = j := by
  have := G.hs; omega

def frS (G : GLoc v) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) :
    Frame G.k (Yc D (j + 1)).rank (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) ⊕ Fin 0) :=
  reN (congrArg (fun s => (Yc D (s + 1)).rank) (s_eq G h)) (G.FY (G.s + 1) 0 rfl)

def phiT (G : GLoc v) : SB (Matrix (Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (G.s + 2))
    (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) ⊕ Fin 0) G.k) :=
  ⟨(G.S.T (Fin D.R.t)).PhiTop, (GModel.phi_sb G).2⟩

theorem isCombAt_reN {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (q : GlobalTheory.FinPl.SplitPt D k)
    (ψ : AddChar (AF D.host.F) ℂ) (FT : Frame k D.sp.X'.rank Y) (Ξ : Matrix Y Y' k → ℂ) :
    ∀ {s j : ℕ} (hs : s = j) (F : Frame k (Yc D (s + 1)).rank Y') (e : WO (Yc D (s + 1)) D.sp.X' →₀ ℂ)
      (e' : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ), HEq e' e → (ofSplit q).IsCombAt ψ F FT e Ξ →
      (ofSplit q).IsCombAt ψ (reN (congrArg (fun s => (Yc D (s + 1)).rank) hs) F) FT e' Ξ := by
  rintro s j rfl F e e' he h
  cases he
  exact h

theorem intIn_reN {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y' : Type} [Fintype Y'] [DecidableEq Y'] (q : GlobalTheory.FinPl.SplitPt D k) (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) :
    ∀ {s j : ℕ} (hs : s = j) (F : Frame k (Yc D (s + 1)).rank Y'), IntIn q (Yc D (s + 1)) F (N (s + 1)) →
      IntIn q (Yc D (j + 1)) (reN (congrArg (fun s => (Yc D (s + 1)).rank) hs) F) (N (j + 1)) := by
  rintro s j rfl F h
  exact h

def eT {n : ℕ} {G : Fin n → GLoc v} (hGP : GPin G) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) (i : Fin n) :
    WO (Yc D (j + 1)) D.sp.X' →₀ ℂ :=
  Classical.choose (hGP.eGT j h) i

theorem eT_spec {n : ℕ} {G : Fin n → GLoc v} (hGP : GPin G) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) :
    (∀ i, HEq (eT hGP h i) (G i).egT) ∧ ∀ F, IsThetaFunO f.c.ψ _ _ F →
      comb f.c.ψ _ _ (v.eGT j h) F = (List.finRange n).foldr (fun i g => comb f.c.ψ _ _ (eT hGP h i) g) F :=
  Classical.choose_spec (hGP.eGT j h)

theorem eT_is {n : ℕ} {G : Fin n → GLoc v} (hGP : GPin G) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) (i : Fin n) :
    (ofSplit (G i).q).IsCombAt f.c.ψ (frS (G i) h) (G i).FT (eT hGP h i) (phiT (G i)).1 :=
  isCombAt_reN (G i).q f.c.ψ (G i).FT _ (s_eq (G i) h) ((G i).FY ((G i).s + 1) 0 rfl) (G i).egT _
    ((eT_spec hGP h).1 i) (G i).egT_is

def lp (hψ : IsStdChar D f.c.ψ (-1)) {n : ℕ} {G : Fin n → GLoc v} (hGP : GPin G) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m)
    {M : GlobalTheory.FinPl.Lat (Yc D (j + 1))} (hM : IsSelfDualC (Yc D (j + 1)) M) (hLT : IsSelfDualC D.sp.X' f.g.LT) (i : Fin n) :
    LocPl f.c.ψ (Yc D (j + 1)) D.sp.X' M f.g.LT :=
  mkPl hψ (G i).q (G i).unit (frS (G i) h) (G i).FT (phiT (G i)) (eT hGP h i) (eT_is hGP h i) hM hLT

end GlobalTheory.TopLocData

end
