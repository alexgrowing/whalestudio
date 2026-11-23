import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.StabilizerSymmMapsOrthogonal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsOrbCard

open GlobalTheory.RowsOrb

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem frF_Xa' (F : FlagG S r T) (hT : T ≠ 0) (k : ℕ) : (GlobalTheory.TypeAsm.frF F hT).Xa k = F.Xa k := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.Xa FlagG.Xa
  have h : (fun b : Fin r => (GlobalTheory.TypeAsm.frF F hT).e b.castSucc) = F.e := funext fun b => GlobalTheory.TypeAsm.fv_cast F b
  rw [h]

theorem frF_X' (F : FlagG S r T) (hT : T ≠ 0) : (GlobalTheory.TypeAsm.frF F hT).X = F.X := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.X
  rw [frF_Xa']
  unfold FlagG.Xa FlagG.X
  congr 1
  ext x; simp

end Gen

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem fixedFrameOfWord_X : (GlobalTheory.TypeAsm.F0 X u).X = (X.Fu u).X := frF_X' _ _

theorem FuX_eq : (X.Fu u).X = Submodule.span D.host.E (Set.range X.eX) := by
  rw [FlagG.X, X.Fu_e]

theorem Wb_le (w : Wb X) : (w : (VS D).V) ∈ perpS (VS D) (X.Fu u).X := by
  intro y hy
  rw [FuX_eq] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact (w.2 a).1
  | zero => simp
  | add y v _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

def iotaL : Wb X →ₗ[D.host.E] WbQ D (X.Fu u) :=
  (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.nX D (X.Fu u)).mkQ ∘ₗ
    Submodule.inclusion (fun v hv => Wb_le X u ⟨v, hv⟩)

theorem iotaL_apply (w : Wb X) :
    iotaL X u w = Submodule.Quotient.mk ⟨(w : (VS D).V), Wb_le X u w⟩ := rfl

theorem iotaL_bij : Function.Bijective (iotaL X u) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker, iotaL_apply, Submodule.Quotient.mk_eq_zero] at hw
    have hwX : (w : (VS D).V) ∈ Submodule.span D.host.E (Set.range X.eX) := by
      rw [← FuX_eq]; exact hw
    have h1 := Formalism.L2.SG.Pf.pj_X (f := X.fY) X.ee X.ef _ hwX
    rw [Formalism.L2.SG.Pf.pj_perp _ (fun a => w.2 a)] at h1
    exact Subtype.ext h1
  · intro q
    induction q using Submodule.Quotient.induction_on with | H a => ?_
    refine ⟨⟨Formalism.L2.SG.Pf.pj X.eX X.fY (a : (VS D).V), fun b =>
      ⟨Formalism.L2.SG.Pf.hT_e_pj X.ee X.ef _ b, Formalism.L2.SG.Pf.hT_f_pj X.ff X.ef _ b⟩⟩, ?_⟩
    rw [iotaL_apply, PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.mk_eq_mk]
    show Formalism.L2.SG.Pf.pj X.eX X.fY (a : (VS D).V) - (a : (VS D).V) ∈ (X.Fu u).X
    have h := Formalism.L2.SG.Pf.pj_sub_mem (e := X.eX) (f := X.fY) (a : (VS D).V)
      (fun b => a.2 _ (by rw [FuX_eq]; exact Submodule.subset_span ⟨b, rfl⟩))
    rw [← FuX_eq] at h
    exact h

def iota : Wb X ≃ₗ[D.host.E] WbQ D (X.Fu u) := LinearEquiv.ofBijective (iotaL X u) (iotaL_bij X u)

theorem iota_apply (w : Wb X) : iota X u w = Submodule.Quotient.mk ⟨(w : (VS D).V), Wb_le X u w⟩ := rfl

theorem iota_h (x y : Wb X) : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u) (iota X u x) (iota X u y) = hb X x y := rfl

theorem definiteInclusion_orthogonal_negativeVector : iota X u (zb X u) = PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar D (X.Fu u) := by
  rw [iota_apply, PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar]
  congr 1
  apply Subtype.ext
  exact (X.flagZVector u).symm

theorem iota_mem (Λ : Submodule (𝓞 D.host.E) (VS D).V) (w : Wb X) :
    iota X u w ∈ PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ ↔ w ∈ Lmap X u Λ := by
  rw [PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.mem_Mof, mem_Lmap, fixedFrameOfWord_X]
  constructor
  · rintro ⟨a, haΛ, hmk⟩
    rw [iota_apply, PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.mk_eq_mk] at hmk
    refine Submodule.mem_sup.2 ⟨a, haΛ, (w : (VS D).V) - a, ?_, by abel⟩
    have := Submodule.neg_mem _ hmk
    rw [neg_sub] at this
    exact this
  · intro hw
    obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.1 hw
    have hxX : x ∈ (X.Fu u).X := hx
    have hlp : l ∈ perpS (VS D) (X.Fu u).X := by
      have : l = (w : (VS D).V) - x := by rw [← hlx]; abel
      rw [this]
      exact Submodule.sub_mem _ (Wb_le X u w) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.X_le_perp D (X.Fu u) hxX)
    refine ⟨⟨l, hlp⟩, hl, ?_⟩
    rw [iota_apply, PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.mk_eq_mk]
    have : l - (w : (VS D).V) = -x := by rw [← hlx]; abel
    show l - (w : (VS D).V) ∈ _
    rw [this]
    exact Submodule.neg_mem _ hxX

end GlobalTheory.RowsOrbCard

namespace GlobalTheory.RowsOrbCard

open GlobalTheory.RowsOrb

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def conj (g : Wb X ≃ₗ[D.host.E] Wb X) : WbQ D (X.Fu u) ≃ₗ[D.host.E] WbQ D (X.Fu u) :=
  (iota X u).symm.trans (g.trans (iota X u))

def unconj (σ : WbQ D (X.Fu u) ≃ₗ[D.host.E] WbQ D (X.Fu u)) : Wb X ≃ₗ[D.host.E] Wb X :=
  (iota X u).trans (σ.trans (iota X u).symm)

theorem conj_iota (g : Wb X ≃ₗ[D.host.E] Wb X) (w : Wb X) : conj X u g (iota X u w) = iota X u (g w) := by
  simp [conj]

theorem conj_unconj (σ : WbQ D (X.Fu u) ≃ₗ[D.host.E] WbQ D (X.Fu u)) : conj X u (unconj X u σ) = σ := by
  ext q; simp [conj, unconj]

theorem unconj_conj (g : Wb X ≃ₗ[D.host.E] Wb X) : unconj X u (conj X u g) = g := by
  ext w; simp [conj, unconj]

theorem conj_isom (g : Wb X ≃ₗ[D.host.E] Wb X) (hg : ∀ x y, hb X (g x) (g y) = hb X x y)
    (x y : WbQ D (X.Fu u)) :
    PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u) (conj X u g x) (conj X u g y) =
      PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u) x y := by
  have e : ∀ q, conj X u g q = iota X u (g ((iota X u).symm q)) := fun q => rfl
  have e2 : ∀ q, iota X u ((iota X u).symm q) = q := fun q => (iota X u).apply_symm_apply q
  rw [e, e, iota_h, hg, ← iota_h, e2, e2]

theorem gmap_conj (Λ : Submodule (𝓞 D.host.E) (VS D).V) (g : Wb X ≃ₗ[D.host.E] Wb X) :
    Formalism.HermitianLatticesTheory.gmap (conj X u g) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ) =
              PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ ↔
      Formalism.HermitianLatticesTheory.gmap g (Lmap X u Λ) = Lmap X u Λ := by
  have key : ∀ w, iota X u w ∈ Formalism.HermitianLatticesTheory.gmap (conj X u g) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ) ↔
      w ∈ Formalism.HermitianLatticesTheory.gmap g (Lmap X u Λ) := by
    intro w
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨y, hy, h⟩
      refine ⟨(iota X u).symm y, (iota_mem X u Λ _).1 (by simpa using hy), ?_⟩
      apply (iota X u).injective
      rw [← h, ← conj_iota]
      simp
    · rintro ⟨y, hy, h⟩
      refine ⟨iota X u y, (iota_mem X u Λ y).2 hy, ?_⟩
      rw [conj_iota, h]
  constructor
  · intro h
    ext w
    rw [← key, h, iota_mem]
  · intro h
    ext q
    rw [← (iota X u).apply_symm_apply q, key, h, iota_mem]

theorem conj_mem (Λ : Submodule (𝓞 D.host.E) (VS D).V) (g : MulAction.stabilizer (Gz X u) (Lmap X u Λ)) :
    conj X u (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) ∈
      PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.stabZ (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u))
        (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar D (X.Fu u)) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ) := by
  have hz : (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) (zb X u) = zb X u :=
    MulAction.mem_stabilizer_iff.1 (g : Gz X u).2
  have hL : Formalism.HermitianLatticesTheory.gmap (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) (Lmap X u Λ) =
      Lmap X u Λ := MulAction.mem_stabilizer_iff.1 g.2
  have hg : ∀ x y, hb X ((((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) x)
      ((((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) y) = hb X x y :=
    ((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)).2
  refine ⟨⟨conj_isom X u _ hg, ?_⟩, (gmap_conj X u Λ _).2 hL⟩
  have e := conj_iota X u (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) (zb X u)
  rw [hz, definiteInclusion_orthogonal_negativeVector] at e
  exact e

theorem unconj_mem (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (σ : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.stabZ (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u))
        (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar D (X.Fu u)) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ)) :
    ∃ (h1 : unconj X u σ.1 ∈ Formalism.HermitianLatticesTheory.isom (hb X)) (h2 : (⟨unconj X u σ.1, h1⟩ : Formalism.HermitianLatticesTheory.isom (hb X)) ∈ Gz X u),
      (⟨⟨unconj X u σ.1, h1⟩, h2⟩ : Gz X u) ∈ MulAction.stabilizer (Gz X u) (Lmap X u Λ) := by
  obtain ⟨⟨hi, hz⟩, hM⟩ := σ.2
  have h1 : unconj X u σ.1 ∈ Formalism.HermitianLatticesTheory.isom (hb X) := by
    intro x y
    rw [← iota_h, ← iota_h]
    have e : ∀ w, iota X u (unconj X u σ.1 w) = σ.1 (iota X u w) := fun w => by simp [unconj]
    rw [e, e]
    exact hi _ _
  refine ⟨h1, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff]
    show unconj X u σ.1 (zb X u) = zb X u
    apply (iota X u).injective
    simp only [unconj, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, definiteInclusion_orthogonal_negativeVector]
    exact hz
  · rw [MulAction.mem_stabilizer_iff]
    show Formalism.HermitianLatticesTheory.gmap (unconj X u σ.1) (Lmap X u Λ) = Lmap X u Λ
    rw [← gmap_conj, conj_unconj]
    exact hM

theorem card_stab (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Nat.card (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.stabZ (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u))
        (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar D (X.Fu u)) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ)) =
      Nat.card (MulAction.stabilizer (Gz X u) (Lmap X u Λ)) := by
  refine (Nat.card_congr
    { toFun := fun g => ⟨conj X u (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X), conj_mem X u Λ g⟩
      invFun := fun σ => ⟨⟨⟨unconj X u σ.1, (unconj_mem X u Λ σ).1⟩, (unconj_mem X u Λ σ).2.1⟩,
        (unconj_mem X u Λ σ).2.2⟩
      left_inv := fun g => by
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
        exact unconj_conj X u _
      right_inv := fun σ => by
        apply Subtype.ext
        exact conj_unconj X u _ }).symm

end GlobalTheory.RowsOrbCard

namespace GlobalTheory.RowsOrb

theorem card_autLz : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ →
    ∀ Λ ∈ Y.what₂ u, Nat.card (autLz D (X.Fu u) Λ) =
      Nat.card (MulAction.stabilizer (GlobalTheory.RowsOrb.Gz X u) (GlobalTheory.RowsOrb.Lmap X u Λ)) := by
  intro D large₂ X Y u _ Λ hΛ
  rw [PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_weight_formula D u (X.Fu u) Λ ((Y.rowsOK u).1 Λ hΛ)]
  exact GlobalTheory.RowsOrbCard.card_stab X u Λ

end GlobalTheory.RowsOrb
