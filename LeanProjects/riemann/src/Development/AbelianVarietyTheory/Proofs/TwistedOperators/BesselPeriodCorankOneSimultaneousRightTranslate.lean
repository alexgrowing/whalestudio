import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
noncomputable section

namespace GlobalTheory.BplusShift

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem embTop_mul (a b : GA D (G.V (.top 0))) : embTop G (a * b) = embTop G a * embTop G b := by
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D _ _ _
    (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have e : ∀ h, embTop G h = s h := fun h => ((embRel_iff _ h _).1 ((hs h _).2 rfl)).symm
  rw [e, e, e, map_mul]

theorem inner_left (W : G.Weil) (M : Vol G) (hM : M.IsRow) {φ : Fn G (.top 0)} {F : Fn G (.grid D.R.m 0)}
    (hφ : φ ∈ contLeft (G.V (.top 0))) (hF : F ∈ contLeft (G.V (.grid D.R.m 0))) {γ : GA D (G.V (.top 0))}
    (hγ : γ ∈ GQ (G.V (.top 0))) (h : GA D (G.V (.top 0))) :
    ∫ n in M.fdN, besInt W φ F (γ * h) n ∂M.νN = ∫ n in M.fdN, besInt W φ F h n ∂M.νN := by
  obtain ⟨_, _, _, _⟩ := GlobalTheory.Per.Inhab.flag_topology _ G.besTop.e_iso
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid D.R.m 0))
  obtain ⟨s, -, hs, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D _ _ _
    (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have e : ∀ h, embTop G h = s h := fun h => ((embRel_iff _ h _).1 ((hs h _).2 rfl)).symm
  have r1 := (hs γ (s γ)).2 rfl
  have r2 := (hs γ⁻¹ (s γ)⁻¹).2 (map_inv s _).symm
  have hδ : s γ ∈ GQ (G.V (.grid D.R.m 0)) := hq _ hγ
  let c : NFlag (G.V (.grid D.R.m 0)) G.besTop.e ≃ₜ* NFlag (G.V (.grid D.R.m 0)) G.besTop.e :=
    { toFun := fun n => ⟨s γ * n * (s γ)⁻¹, (GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop _ _ r1 n n.2).1⟩
      invFun := fun n => ⟨(s γ)⁻¹ * n * (s γ)⁻¹⁻¹, (GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop _ _ r2 n n.2).1⟩
      left_inv := fun n => Subtype.ext (by simp [mul_assoc])
      right_inv := fun n => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hc : ∀ n, c n ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e ↔ n ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e := fun n => by
    change s γ * n.1 * (s γ)⁻¹ ∈ GQ (G.V (.grid D.R.m 0)) ↔ n.1 ∈ GQ (G.V (.grid D.R.m 0))
    rw [Subgroup.mul_mem_cancel_right _ (inv_mem hδ), Subgroup.mul_mem_cancel_left _ hδ]
  have hl : ∀ γ' ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e, ∀ n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e,
      besInt W φ F (γ * h) (γ' * n) = besInt W φ F (γ * h) n := fun γ' hγ' n => by
    have hq' := Subgroup.mem_subgroupOf.1 hγ'
    simp only [besInt, Subgroup.coe_mul]
    rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop _ _ γ'.2 n.2, GlobalTheory.BesselChar.besChar_rat W.ψ W.ψ_std.1 G.besTop _ γ'.2 hq',
      one_mul, mul_assoc γ'.1, hF.2 _ hq']
  refine (GlobalTheory.Mem.TrueRecord.integral_aut _ hM.unip.1 hM.unip.2.1 hM.unip.2.2 c hc _ hl).symm.trans ?_
  congr 1
  funext n
  change φ (γ * h) * F ((s γ * n * (s γ)⁻¹) * embTop G (γ * h)) * star (besChar W.ψ G.besTop (s γ * n * (s γ)⁻¹)) =
    φ h * F (n * embTop G h) * star (besChar W.ψ G.besTop n)
  rw [(GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop _ _ r1 n n.2).2, hφ.2 γ hγ h, e, e, map_mul,
    show s γ * n * (s γ)⁻¹ * (s γ * s h) = s γ * (n * s h) by group, hF.2 _ hδ]

end GlobalTheory.BplusShift

open GlobalTheory.BplusShift in

theorem GlobalTheory.BplusShift.bplus_rTr : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ φ ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ a : GA D (G.V (.top 0)),
      Bplus W M (rTr _ a φ) (rTr _ (embTop G a) F) = Bplus W M φ F := by
  intro D T L sc G W M hM φ hφ F hF a
  have hshift : ∀ h n, besInt W (rTr _ a φ) (rTr _ (embTop G a) F) h n = besInt W φ F (h * a) n := fun h n => by
    simp only [besInt, rTr]
    rw [embTop_mul, mul_assoc (n : GA D (G.V (.grid D.R.m 0)))]
  simp only [Bplus, hshift]
  obtain ⟨hμ, h𝓕⟩ := hM.top.haar_fund
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  haveI := hμ
  haveI : (M.ν (.top 0)).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hμ
  have hmp : MeasurePreserving (· * a) (M.ν (.top 0)) (M.ν (.top 0)) := measurePreserving_mul_right _ a
  have hmp' : MeasurePreserving (· * a⁻¹) (M.ν (.top 0)) (M.ν (.top 0)) := measurePreserving_mul_right _ a⁻¹
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight a)
    (fun h => ∫ n in M.fdN, besInt W φ F h n ∂M.νN) (M.fd (.top 0)), Set.image_mul_right]
  have hF' : IsFundamentalDomain (GQ (G.V (.top 0))) ((· * a⁻¹) ⁻¹' M.fd (.top 0)) (M.ν (.top 0)) :=
    h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (h𝓕.setIntegral_eq hF' fun γ x => inner_left W M hM hφ hF γ.2 x).symm
