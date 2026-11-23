import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianBlockSpans
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate
open Matrix

set_option linter.dupNamespace false

namespace Formalism.L2.SG.RealObj.FlagExtensionRegularity

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.RealObj.HermitianBlockSpans Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem flag_ext {D : D7} {T : D.host.E} (F1 F2 : FlagG (VS D) D.R.rS T)
    (he : F1.e = F2.e) (hz : F1.z = F2.z) : F1 = F2 := by
  cases F1; cases F2
  simp only at he hz
  subst he; subst hz; rfl

theorem fam_castLE {n r l : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (hl : l ≤ r) (h : l ≤ r + 1) (b : Fin l) :
    fam e z (Fin.castLE h b) = e (Fin.castLE hl b) := by
  have : Fin.castLE h b = Fin.castSucc (Fin.castLE hl b) := Fin.ext rfl
  rw [this, fam, Fin.snoc_castSucc]

theorem famSc_one {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : famSc 1 e z = fam e z := by
  funext a
  simp [famSc]

theorem span_map {n r : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (e : Fin r → Fin n → ℂ) (a : ℕ) {y : Fin n → ℂ}
    (hy : y ∈ spanLt e a) : g *ᵥ y ∈ spanLt (fun c => g *ᵥ e c) a := by
  unfold spanLt at *
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, hb, rfl⟩ := hw
    exact Submodule.subset_span ⟨b, hb, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add w1 w2 _ _ h1 h2 => rw [Matrix.mulVec_add]; exact add_mem h1 h2
  | smul c w _ h1 => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ h1

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem uMat_mul_inv' {n : ℕ} {ε : Fin n → Bool} (a : Formalism.REAL.UJ ε) : uMat a * uMat a⁻¹ = 1 := by
  simp [uMat]

theorem dl_eq (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) {l : ℕ} (hl : l ≤ D.R.rS) :
    Dl (ZX X u u' 1 γ v) l =
      (HermitianBlockSpans.blk (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => uMat (γ v) *ᵥ rv X.B.I v (X.eR a)) hl).det := by
  have h : l ≤ D.R.rS + 1 := hl.trans (Nat.le_succ _)
  unfold Dl
  rw [dif_pos h]
  congr 1
  ext b c
  simp only [Matrix.submatrix_apply, ZX, Zhat, frm, famSc_one, HermitianBlockSpans.blk, Matrix.of_apply]
  rw [fam_castLE _ _ hl h, fam_castLE _ _ hl h]

variable {X} {u u' : D.what₂.Word} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem ro_triv (t : GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') (hreg : RegX X u u' t.pt.1) :
    ∀ y ∈ ROinf t, y = 1 := by
  rintro y ⟨x, m, hx, rfl, hm, hm'⟩
  have hN := Formalism.L2.SG.Pf.nLamNinf_holds D X u t.lam x m hx hm
  have hγ : RatLink X t.pt t.lin := t.rep.2.1
  have hx' : RatLink X (t.pt⁻¹ * x * t.pt) (t.lin⁻¹ * m * t.lin) :=
    Vanish.ratLink_mul X (Vanish.ratLink_mul X (Vanish.ratLink_inv X hγ) hx) hγ
  have hN' := Formalism.L2.SG.Pf.nLamNinf_holds D X u' t.lam' _ _ hx' hm'
  funext v
  apply Subtype.ext
  apply Units.ext
  show uMat (x.1 v) = 1
  set g := uMat (t.pt.1 v) with hg
  set gi := uMat (t.pt.1⁻¹ v) with hgi
  have hgg : g * gi = 1 := uMat_mul_inv' (t.pt.1 v)
  have hv := hN v
  have hv' := hN' v
  have hconj : uMat ((t.pt⁻¹ * x * t.pt).1 v) = gi * uMat (x.1 v) * g := by
    simp [uMat, hg, hgi]
  rw [hconj] at hv'
  set e := fun a => rv X.B.I v (X.eR a) with he
  have hkey : ∀ y, (uMat (x.1 v) - 1) *ᵥ (g *ᵥ y) = g *ᵥ ((gi * uMat (x.1 v) * g - 1) *ᵥ y) := by
    intro y
    have hm : g * (gi * uMat (x.1 v) * g - 1) = (uMat (x.1 v) - 1) * g := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc, hgg]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm]
  refine st_triv (X.B.I.ε v) e (fun a => g *ᵥ e a) (uMat (x.1 v)) (hJ_map _ (x.1 v).2) hv.1.1
    (fun a => ?_) hv.2 (fun l hl h1 => ?_)
  · rw [hkey]
    exact span_map g e a.1 (hv'.1.1 a)
  · have := (hreg v).1 l h1 hl
    rwa [dl_eq X u u' t.pt.1 v hl] at this

theorem fundOf_univ (t : GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') (hreg : RegX X u u' t.pt.1) :
    FundOf t = Set.univ := by
  have htriv := ro_triv t hreg
  have h1 : (1 : X.B.I.Ginf) ∈ ROinf t := (Vanish.ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin).one_mem
  have hex : ∃ Ω, IsSFund X.B.I (ROinf t) Ω :=
    ⟨Set.univ, MeasurableSet.univ, fun x => ⟨1, h1, trivial⟩, fun x _ s hs _ => htriv s hs⟩
  unfold FundOf
  rw [dif_pos hex]
  ext x
  simp only [Set.mem_univ, iff_true]
  obtain ⟨s, hs1, hs2⟩ := hex.choose_spec.2.1 x
  rwa [htriv s hs1, one_mul] at hs2

variable (X u u')

theorem OOtReg_holds (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)) :
    OOtReg X u u' F0 F0' what₂ rows' := by
  intro hFT
  obtain ⟨he, hz, he', hz'⟩ := hFT
  obtain rfl : F0 = X.Fu u := flag_ext _ _ ((funext he).trans (X.Fu_e u).symm) (hz.trans (X.flagZVector u).symm)
  obtain rfl : F0' = X.Fu u' := flag_ext _ _ ((funext he').trans (X.Fu_e u').symm) (hz'.trans (X.flagZVector u').symm)
  intro t hreg
  unfold TermOp.OOt OOinf
  rw [fundOf_univ t hreg]

end Formalism.L2.SG.RealObj.FlagExtensionRegularity
