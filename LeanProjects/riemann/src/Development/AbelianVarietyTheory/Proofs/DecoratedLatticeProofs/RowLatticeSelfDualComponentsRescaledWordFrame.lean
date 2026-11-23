import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramEqOfInst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameCoordsMemSelfDualLatticeCoordsIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

def basY (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Module.Basis (Fin (D.sp.Y 0).rank) D.host.E (VS D).V :=
  X.bas.reindex (finCongr (rank_eq X h)).symm

theorem cY_eq_basY (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (z : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h z = (basY X h).equivFun z := by
  funext k
  simp [GlobalTheory.Core.SBesEx.cY, HidaSetting.crd, crdOf, basY, Module.Basis.repr_reindex]

theorem mem_hermitianCoordinateLattice_iff (S : HSp D) (y : Fin S.rank → D.host.E) :
    y ∈ Formalism.L2.Herm.crdLat S S.L0 ↔ S.frame.equivFun.symm y ∈ S.L0 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [Formalism.L2.Herm.crd] using hw
  · intro hy
    exact ⟨_, hy, S.frame.equivFun.apply_symm_apply y⟩

theorem mem_rowLatticeYZeroFrame_iff_basis_sum (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (hId : ∀ x : I.E, HEq (ιE x) x) (bas : Module.Basis (Fin I.n) D.host.E (VS D).V)
    (hL : ∀ x : Fin I.n → I.E, x ∈ I.L ↔ (∑ i, ιE (x i) • bas i) ∈ (VS D).L0) (hn : (D.sp.Y 0).rank = I.n)
    (y : Fin (D.sp.Y 0).rank → D.host.E) :
    y ∈ latS D ↔ (∑ k, y k • bas (Fin.cast hn k)) ∈ (VS D).L0 := by
  subst hI
  have hι : ∀ x, ιE x = x := fun x => eq_of_heq (hId x)
  have e1 := hL y
  have e2 : (∑ i, ιE (y i) • bas i) = ∑ k, y k • bas (Fin.cast hn k) :=
    Finset.sum_congr rfl fun i _ => congrArg (· • bas i) (hι (y i))
  refine Iff.trans ?_ (e1.trans (Eq.to_iff (congrArg (· ∈ (VS D).L0) e2)))
  rw [mem_hermitianCoordinateLattice_iff]
  show _ ↔ y ∈ Formalism.L2.SG.InstExistsPf.Lv D
  rw [Formalism.L2.SG.InstExistsPf.mem_Lv, Module.Basis.equivFun_symm_apply]

theorem mem_latS (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : IdE X)
    (y : Fin (D.sp.Y 0).rank → D.host.E) :
    y ∈ latS D ↔ (basY X h).equivFun.symm y ∈ (VS D).L0 := by
  rw [mem_rowLatticeYZeroFrame_iff_basis_sum X.B.I h X.ιE hId X.bas X.L_eq (rank_eq X h), Module.Basis.equivFun_symm_apply]
  simp [basY]

theorem cY_mem_latS (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : IdE X) (z : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h z ∈ latS D ↔ z ∈ (VS D).L0 := by
  rw [mem_latS X h hId, cY_eq_basY, LinearEquiv.symm_apply_apply]

theorem hT_swap (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := by
  have := (VS D).herm.eq x y
  rw [← this]
  rfl

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

theorem hT_fY_mem (X : HidaSetting D) (i : Fin D.R.rS) {Y : (VS D).V} (hY : Y ∈ (VS D).L0) :
    (VS D).hT (X.fY i) Y ∈ aaD D i := by
  have key : (VS D).L0 ≤ (aaD D i : Submodule (𝓞 D.host.E) D.host.E).comap
      (((VS D).hT (X.fY i)).restrictScalars (𝓞 D.host.E)) := by
    rw [X.Lam_split]
    refine sup_le (sup_le ?_ ?_) ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      show (VS D).hT (X.fY i) (x • X.eX a) ∈ (aaD D i : Submodule (𝓞 D.host.E) D.host.E)
      rw [map_smul, smul_eq_mul, hT_swap, X.ef]
      by_cases hai : a = i
      · subst hai; simpa using hx
      · simp [hai]
    · intro x hx
      show (VS D).hT (X.fY i) x ∈ (aaD D i : Submodule (𝓞 D.host.E) D.host.E)
      rw [((X.Lb_perp x hx) i).2]; exact zero_mem _
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      show (VS D).hT (X.fY i) (x • X.fY a) ∈ (aaD D i : Submodule (𝓞 D.host.E) D.host.E)
      rw [map_smul, X.ff, smul_zero]; exact zero_mem _
  exact key hY

theorem hT_eX_mem (X : HidaSetting D) (i : Fin D.R.rS) {Y : (VS D).V} (hY : Y ∈ (VS D).L0) :
    (VS D).hT (X.eX i) Y ∈ (aaD D i)⁻¹ := by
  have key : (VS D).L0 ≤ (((aaD D i)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E).comap (((VS D).hT (X.eX i)).restrictScalars (𝓞 D.host.E)) := by
    rw [X.Lam_split]
    refine sup_le (sup_le ?_ ?_) ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      show (VS D).hT (X.eX i) (x • X.eX a) ∈ (((aaD D i)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E)
      rw [map_smul, X.ee, smul_zero]; exact zero_mem _
    · intro x hx
      show (VS D).hT (X.eX i) x ∈ (((aaD D i)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E)
      rw [((X.Lb_perp x hx) i).1]; exact zero_mem _
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      show (VS D).hT (X.eX i) (x • X.fY a) ∈ (((aaD D i)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E)
      rw [map_smul, smul_eq_mul, X.ef]
      by_cases hai : i = a
      · subst hai; simpa using hx
      · simp [hai]
  exact key hY

theorem smul_eX_mem_iff (X : HidaSetting D) (i : Fin D.R.rS) (c : D.host.E) :
    c • X.eX i ∈ (VS D).L0 ↔ c ∈ aaD D i := by
  constructor
  · intro hc
    have := hT_fY_mem X i hc
    rwa [map_smul, smul_eq_mul, hT_swap, X.ef, if_pos rfl, star_one, mul_one] at this
  · intro hc
    rw [X.Lam_split]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨i, c, hc, rfl⟩))

theorem smul_fY_mem_iff (X : HidaSetting D) (i : Fin D.R.rS) (c : D.host.E) :
    c • X.fY i ∈ (VS D).L0 ↔ c ∈ (aaD D i)⁻¹ := by
  constructor
  · intro hc
    have := hT_eX_mem X i hc
    rwa [map_smul, smul_eq_mul, X.ef, if_pos rfl, mul_one] at this
  · intro hc
    rw [X.Lam_split]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, c, hc, rfl⟩)

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

theorem star_smul_dotProduct {n : ℕ} (c : D.host.E) (v w : Fin n → D.host.E) :
    star (c • v) ⬝ᵥ w = star c * (star v ⬝ᵥ w) := by
  simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum, mul_assoc]

theorem qX_mulVec_apply {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (y : Fin S.rank → D.host.E) (i : Fin ρ) :
    (d.qX *ᵥ y) i = star (fun r => d.e' r i) ⬝ᵥ (S.gram *ᵥ y) := by
  rw [HypDec.qX, ← Matrix.mulVec_mulVec]; rfl

theorem qY_mulVec_apply {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (y : Fin S.rank → D.host.E) (i : Fin ρ) :
    (d.qY *ᵥ y) i = star (fun r => d.e r i) ⬝ᵥ (S.gram *ᵥ y) := by
  rw [HypDec.qY, ← Matrix.mulVec_mulVec]; rfl

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem latS_rescaled_frame : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μ lam : D.host.E), GlobalTheory.Core.Mi.IdE X → B.FrameAt μ lam → IsSelfDualC (D.sp.Y 0) (latS D) ∧ (∀ y ∈ latS D, ∀ i, (fun r => (B.d.qX *ᵥ y) i * B.d.e r i) ∈ latS D ∧ (fun r => (B.d.qY *ᵥ y) i * B.d.e' r i) ∈ latS D) ∧ (∀ (i : Fin D.R.rS) (t : D.host.E), t • (fun r => B.d.e r i) ∈ latS D ↔ GlobalTheory.Core.SBesEx.scl μ lam i * t ∈ aaD D i) ∧ ∀ (i : Fin D.R.rS) (t : D.host.E), t • (fun r => B.d.e' r i) ∈ latS D ↔ (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹ * t ∈ (aaD D i)⁻¹ := by
  intro D X h u ψ A B μ lam hId hF
  have hcY_smul : ∀ (c : D.host.E) (z : (VS D).V), c • GlobalTheory.Core.SBesEx.cY X h z = GlobalTheory.Core.SBesEx.cY X h (c • z) := by
    intro c z; rw [cY_eq_basY, cY_eq_basY, map_smul]
  have hcol_e : ∀ i, (fun r => B.d.e r i) = GlobalTheory.Core.SBesEx.scl μ lam i • GlobalTheory.Core.SBesEx.cY X h (X.eX i) := by
    intro i; funext r; rw [hF.e]; rfl
  have hcol_e' : ∀ i, (fun r => B.d.e' r i) =
      (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹ • GlobalTheory.Core.SBesEx.cY X h (X.fY i) := by
    intro i; funext r; rw [hF.e']; rfl
  have colE : ∀ i (t : D.host.E), t • (fun r => B.d.e r i) ∈ latS D ↔ GlobalTheory.Core.SBesEx.scl μ lam i * t ∈ aaD D i := by
    intro i t
    rw [hcol_e, smul_smul, hcY_smul, cY_mem_latS X h hId, smul_eX_mem_iff, mul_comm]
  have colE' : ∀ i (t : D.host.E), t • (fun r => B.d.e' r i) ∈ latS D ↔
      (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹ * t ∈ (aaD D i)⁻¹ := by
    intro i t
    rw [hcol_e', smul_smul, hcY_smul, cY_mem_latS X h hId, smul_fY_mem_iff, mul_comm]
  have hdot := @star_smul_dotProduct D (D.sp.Y 0).rank
  have hqX := qX_mulVec_apply B.d
  have hqY := qY_mulVec_apply B.d
  refine ⟨GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D (D.sp.Y 0), ?_, colE, colE'⟩
  intro y hy i
  have hY : (basY X h).equivFun.symm y ∈ (VS D).L0 := (mem_latS X h hId y).1 hy
  have hyY : y = GlobalTheory.Core.SBesEx.cY X h ((basY X h).equivFun.symm y) := by
    rw [cY_eq_basY, LinearEquiv.apply_symm_apply]
  set Y := (basY X h).equivFun.symm y
  constructor
  · have hq : (B.d.qX *ᵥ y) i = (GlobalTheory.Core.SBesEx.scl μ lam i)⁻¹ * (VS D).hT (X.fY i) Y := by
      rw [hqX, hcol_e', hdot, hyY, GlobalTheory.Core.SBesEx.cY_isom D X h hId Y (X.fY i), star_inv₀, star_star]
    show (B.d.qX *ᵥ y) i • (fun r => B.d.e r i) ∈ latS D
    rw [colE, hq]
    by_cases hs : GlobalTheory.Core.SBesEx.scl μ lam i = 0
    · rw [hs, zero_mul]; exact FractionalIdeal.mem_coe.mp (zero_mem _)
    · rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]; exact hT_fY_mem X i hY
  · have hq : (B.d.qY *ᵥ y) i = star (GlobalTheory.Core.SBesEx.scl μ lam i) * (VS D).hT (X.eX i) Y := by
      rw [hqY, hcol_e, hdot, hyY, GlobalTheory.Core.SBesEx.cY_isom D X h hId Y (X.eX i)]
    show (B.d.qY *ᵥ y) i • (fun r => B.d.e' r i) ∈ latS D
    rw [colE', hq]
    by_cases hs : star (GlobalTheory.Core.SBesEx.scl μ lam i) = 0
    · rw [hs, _root_.inv_zero, zero_mul]; exact FractionalIdeal.mem_coe.mp (zero_mem _)
    · rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]; exact hT_eX_mem X i hY

end GlobalTheory.Core.Mi.LatMatch

end
