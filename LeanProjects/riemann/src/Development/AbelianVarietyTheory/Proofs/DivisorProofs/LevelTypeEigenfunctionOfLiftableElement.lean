import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.RowsOfLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.LevelRows

variable {D : D7}

theorem levelType_eigenfunction_of_liftable_element {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {P : LevelP L.Pg L.r ℂ} {F : GA D V → ℂ} (hF : HasType V β (withP L P) F) (p : P.H)
    (hex : ∃ κ, IsLevelLift V β L p.1 κ) :
    actG0 V β L p.1 F = fun h => ((P.chi p : ℂˣ) : ℂ) * F h := by
  have hκ : IsLevelLift V β L p.1 hex.choose := hex.choose_spec
  have hp : rTup β L (finE V hex.choose) ∈ P.H := by rw [hκ.2.2]; exact p.2
  have hmem : hex.choose ∈ levG V β (withP L P) := ⟨hκ.1, hκ.2.1, hp⟩
  have hc : levChi V β (withP L P) hex.choose = ((P.chi p : ℂˣ) : ℂ) * levChi V β (flagL L) hex.choose := by
    unfold levChi
    rw [levFn_withP, extendOne_of_mem _ hp, Units.val_mul]
    congr 3
    exact Subtype.ext hκ.2.2
  have ha := levChi_ne_zero (β := β) (flagL L) hex.choose
  funext h
  unfold actG0
  rw [dif_pos hex, hF _ hmem h, hc]
  field_simp

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_lift_of_ne_zero (R : RealDat D A Ks) (hinj : Function.Injective R.HE.e) (hg : R.models_gE)
    {x : R.HE.H} (hx : x ≠ 0) (g : G) : ∃ κ, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) κ := by
  by_contra hk
  apply hx
  have h0 : R.gE g x = 0 := by
    apply hinj
    rw [hg g x, map_zero]
    ext v h
    show actG0 _ _ _ _ _ h = 0
    unfold actG0
    rw [dif_neg hk]
    rfl
  have : R.gE g⁻¹ (R.gE g x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, h0, map_zero]

theorem rowsOfLevel_of_models (R : RealDat D A Ks) (F : Face D A) (hE : R.models_HE) (hg : R.models_gE) :
    GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows.RowsOfLevel R F := by
  intro b x
  have hx : R.HE.e x ∈ R.EEat R.triv := hE.2.1 ▸ LinearMap.mem_range_self _ x
  unfold RealDat.EEat at hx ⊢
  rw [mem_goodPart, GlobalTheory.MultMem.mem_mult_iff] at hx ⊢
  constructor
  · rintro ⟨h1, -⟩ g
    by_cases h0 : x = 0
    · simp [h0]
    apply hE.1
    rw [hg, map_smul]
    ext v h
    have hmem : R.eG g ∈ (R.levR F b).H := by
      show R.eG.symm (R.eG g) ∈ (F.lvl b).P
      rw [MulEquiv.symm_apply_apply]; exact g.2
    have h2 := levelType_eigenfunction_of_liftable_element (V := Yc D 0) (β := R.βY 0) (L := R.dat0 R.triv) (P := R.levR F b)
      (F := R.HE.e x v) (fun κ hκ h => h1.lev v κ hκ h) ⟨R.eG g, hmem⟩ (exists_lift_of_ne_zero R hE.1 hg h0 g)
    have h3 : (R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P) ⟨R.eG g, hmem⟩ = g :=
      Subtype.ext (R.eG.symm_apply_apply g)
    refine (congrFun h2 h).trans ?_
    show D.what₂.embLL (((F.lvl b).ψ ((R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P) ⟨R.eG g, hmem⟩) : D.what₂.LLˣ) : D.what₂.LL) * _ = _
    rw [h3]
    rfl
  · intro h
    refine ⟨⟨hx.1.aut, hx.1.cusp, fun v => ?_, hx.1.equiv, hx.1.cont⟩, hx.2⟩
    have hP : IsPLevel (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.levR F b) (R.HE.e x v) := by
      refine ⟨fun κ hκ y => hx.1.lev v κ hκ y, fun p => ?_⟩
      have h1 := congrArg (fun z => R.HE.e z v) (h ⟨R.eG.symm p.1, p.2⟩)
      simp only [hg _ x, map_smul] at h1
      have h2 : R.eG (R.eG.symm p.1) = p.1 := R.eG.apply_symm_apply p.1
      rw [h2] at h1
      exact h1
    exact fun κ hκ y => hP.hasType κ hκ y

end GlobalTheory.LevelRows

end
