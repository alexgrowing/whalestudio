import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocPlOff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsFoldr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCombAtReN
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentTopStandardCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.TopLocData

theorem main : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GPin G → GRead f G pl → ∀ j (h : j + 2 * 0 + 2 = D.R.m) d₀, IsDG W (j + 1) (pk W).MX (pk W).ΛX (pk W).βX (vacT (pk W) j h) d₀ → IsSelfDualC (Yc D (j + 1)) ((pk W).ΛY (j + 1)) → IsSelfDualC D.sp.X' (pk W).ΛX → ∀ M : GlobalTheory.FinPl.Lat (Yc D (j + 1)), IsSelfDualC (Yc D (j + 1)) M → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((pk W).ΛY (j + 1)) M P) → ∃ (Lp : Fin n → LocPl f.c.ψ (Yc D (j + 1)) D.sp.X' M f.g.LT) (κ : ℂ), κ ≠ 0 ∧ (∀ i, (Lp i).q.v = (G i).q.v) ∧ (∀ i, IntIn (Lp i).q (Yc D (j + 1)) (Lp i).FS (v.N (j + 1)) ∧ IntIn (Lp i).q D.sp.X' (Lp i).FT v.NT) ∧ (∀ F, IsThetaFunO f.c.ψ (Yc D (j + 1)) D.sp.X' F → comb f.c.ψ _ _ (v.eGT j h) F = (List.finRange n).foldr (fun i g => comb f.c.ψ _ _ (Lp i).e g) F) ∧ ∀ d, IsDG W (j + 1) (pk W).MX (pk W).ΛX (pk W).βX (vacT (pk W) j h) d → ∃ F, IsThetaAt f.c.ψ (symplO (Yc D (j + 1)) D.sp.X') (heisO f.c.ψ (Yc D (j + 1)) D.sp.X') (∑ i, (Lp i).q.e) (latO (Yc D (j + 1)) D.sp.X' (M : Set _) (f.g.LT : Set _) fun _ => True) 1 (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h)) (prodDat Lp) F ∧ IsThetaFunO f.c.ψ (Yc D (j + 1)) D.sp.X' F ∧ omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (vacT (pk W) j h)) = κ • F := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hGP hGR j h d₀ hd₀ hΛ hΛX M hM hMv
  have hψ : IsStdChar D f.c.ψ (-1) := hd₀.2.1.1
  have hLT : IsSelfDualC D.sp.X' f.g.LT := hVT.bT.2 ▸ hv.sdT
  obtain ⟨κ, hκ, hdat⟩ := GlobalTheory.T.descent_top_standard_character D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hGP hGR j h hψ d₀ hd₀ hΛ hΛX M hM hLT hMv
  refine ⟨lp hψ hGP h hM hLT, κ, hκ, fun i => rfl, fun i => ⟨?_, ?_⟩, fun F hF => (eT_spec hGP h).2 F hF, hdat⟩
  · exact intIn_reN (G i).q v.N (s_eq (G i) h) _ ((G i).latY ((G i).s + 1) 0 rfl)
  · have := (G i).latT
    rw [hVT.bT.2] at this ⊢
    exact this

end GlobalTheory.TopLocData

end
