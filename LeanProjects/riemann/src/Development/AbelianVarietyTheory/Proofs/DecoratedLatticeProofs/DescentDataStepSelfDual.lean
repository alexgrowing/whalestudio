import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesIffPlaceSetProd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.Fam.OffLevel

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit

variable {D : D7}

theorem mem_latV_at_iff_all (S : HSp D) (L : Lat S) (p : Pl D) {z : Fin S.rank → AE D}
    (hz : ∀ i, z i ∈ idAt D (· = p)) : z ∈ latV S L (· = p) ↔ z ∈ latV S L (fun _ => True) := by
  constructor
  · exact fun h => latV_mono S L (fun _ _ => trivial) h
  · intro h
    have h1 := ((mem_latV_iff_parts S L (fun _ => True) {p}
      (fun i => idAt_mono (fun _ _ => trivial) (hz i))).1 h).1
    have e : eQ {p} • z = z := funext fun i =>
      eQ_mul_of_in (P := fun _ => True) {p}
        (idAt_mono (fun w hw => ⟨trivial, Finset.mem_singleton.2 hw⟩) (hz i))
    rw [e] at h1
    exact latV_mono S L (fun w hw => Finset.mem_singleton.1 hw.2) h1

theorem latV_eq_of_moves (S : HSp D) (g : GA D S) (Λ N M : Lat S) (p : Pl D)
    (hN : Moves S g Λ N (· = p)) (hM : Moves S g Λ M (fun _ => True)) :
    latV S N (· = p) = latV S M (· = p) := by
  have key : ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = p)) →
      (z ∈ latV S N (· = p) ↔ z ∈ latV S M (· = p)) := by
    intro z hz
    set y := mt S g⁻¹ *ᵥ z with hy
    have hys : ∀ i, y i ∈ idAt D (· = p) := mulVec_mem S _ hz
    have hgy : mt S g *ᵥ y = z := by
      rw [hy, Matrix.mulVec_mulVec, ← KSplit.mt_mul, mul_inv_cancel]
      exact Matrix.one_mulVec z
    rw [← hgy, ← hN y hys, mem_latV_at_iff_all S M p (by rw [hgy]; exact hz),
      ← hM y (fun i => idAt_mono (fun _ _ => trivial) (hys i)), mem_latV_at_iff_all S Λ p hys]
  ext z
  constructor
  · intro h; exact (key z (GlobalTheory.FinPlLoc.latV_idAt h)).1 h
  · intro h; exact (key z (GlobalTheory.FinPlLoc.latV_idAt h)).2 h

end GlobalTheory.Fam.OffLevel

end

open GlobalTheory.Fam.OffLevel in
theorem GlobalTheory.Fam.latV_N_eq_off_level : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GPin G → GRead f G pl → ∀ j, j + 1 < D.R.m → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((pk W).ΛY j) M (fun _ => True) → GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((pk W).ΛY (j + 1)) M' (fun _ => True) → ∀ p, p ∉ v.gP → GlobalTheory.FinPl.latV (Yc D j) (v.N j) (· = p) = GlobalTheory.FinPl.latV (Yc D j) M (· = p) ∧ GlobalTheory.FinPl.latV (Yc D (j + 1)) (v.N (j + 1)) (· = p) = GlobalTheory.FinPl.latV (Yc D (j + 1)) M' (· = p) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f _ _ v _ hv n G pl _ _ j hj M M' hM hM' p hp
  have hP : ∀ q, (· = p) q → q ∉ v.gP := fun q hq => hq ▸ hp
  exact ⟨latV_eq_of_moves _ _ _ _ _ p (hv.moves j (by omega) _ hP) hM,
    latV_eq_of_moves _ _ _ _ _ p (hv.moves (j + 1) hj _ hP) hM'⟩
