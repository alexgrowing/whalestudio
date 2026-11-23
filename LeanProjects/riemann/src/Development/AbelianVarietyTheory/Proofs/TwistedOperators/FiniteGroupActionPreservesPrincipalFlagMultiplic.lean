import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagAction

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem conj_mem_flag1 {g0 : G0 L.Pg L.r} {κ k : GA D V} (hκ : IsLevelLift V β L g0 κ)
    (hk : k ∈ levG V β (flag1L L)) :
    κ⁻¹ * (k * κ) ∈ levG V β (flag1L L) ∧
      levChi V β (flag1L L) (κ⁻¹ * (k * κ)) = levChi V β (flag1L L) k := by
  obtain ⟨hκf, hκp, hκr⟩ := hκ
  rw [levG, mem_levA, Formalism.L2.DIV.mem_lev] at hk
  obtain ⟨hkf, hkp, hkr⟩ := hk

  have hxp : finE V k ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := hkp
  have hx1 : Formalism.L2.DIV.rTup β L (finE V k) = 1 := Subgroup.mem_bot.mp hkr
  have hfin : finE V (κ⁻¹ * (k * κ)) = (finE V κ)⁻¹ * (finE V k * finE V κ) := by
    rw [map_mul, map_mul, map_inv]
  have hcp : (finE V κ)⁻¹ * (finE V k * finE V κ) ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hκp) (Subgroup.mul_mem _ hxp hκp)
  refine ⟨?_, ?_⟩
  · rw [levG, mem_levA, Formalism.L2.DIV.mem_lev, hfin]
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hκf) (Subgroup.mul_mem _ hkf hκf), hcp, ?_⟩
    have hr : Formalism.L2.DIV.rTup β L ((finE V κ)⁻¹ * (finE V k * finE V κ)) = 1 := by
      rw [Formalism.L2.DIV.rTup_mul (Subgroup.inv_mem _ hκp) (Subgroup.mul_mem _ hxp hκp),
        Formalism.L2.DIV.rTup_inv hκp, Formalism.L2.DIV.rTup_mul hxp hκp, hx1, one_mul, inv_mul_cancel]
    exact Subgroup.mem_bot.mpr hr
  ·
    show ((Formalism.L2.DIV.levFn β (flag1L L) (finE V (κ⁻¹ * (k * κ))) : ℂˣ) : ℂ) =
      ((Formalism.L2.DIV.levFn β (flag1L L) (finE V k) : ℂˣ) : ℂ)
    rw [levFn_flag1, levFn_flag1, hfin]
    have hA : finE V κ ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) :=
      Formalism.L2.DIV.mem_lev.mpr ⟨hκp, Subgroup.mem_top _⟩
    have hX : finE V k ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) :=
      Formalism.L2.DIV.mem_lev.mpr ⟨hxp, Subgroup.mem_top _⟩
    let A : Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) := ⟨finE V κ, hA⟩
    let X : Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) := ⟨finE V k, hX⟩
    have hc : Formalism.L2.DIV.levChar D.sp.cm V.gram β (flagL L) (A⁻¹ * (X * A)) =
        Formalism.L2.DIV.levChar D.sp.cm V.gram β (flagL L) X := by
      rw [map_mul, map_mul, map_inv]
      exact inv_mul_cancel_comm_assoc _ _
    have e1 := Formalism.L2.DIV.levChar_apply (A⁻¹ * (X * A))
    have e2 := Formalism.L2.DIV.levChar_apply X
    exact congrArg (fun u : ℂˣ => (u : ℂ)) (e1.symm.trans (hc.trans e2))

theorem finiteGroupAction_preserves_principalFlagMultiplicity : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), IsInfFam θ → ∀ (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (g0 : G0 L.Pg L.r), ∀ T ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)), ∀ U : MMap M, (∀ v, U v = actG0 V β L g0 (T v)) → U ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) := by
  intro D V S θ M _ β L g0 T hT U hU
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
  by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
  ·
    have hκ : IsLevelLift V β L g0 hk.choose := hk.choose_spec
    have hEq : U = (levChi V β (flagL L) hk.choose)⁻¹ • heckeOn M {hk.choose} T := by
      ext v h
      rw [hU v, MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      unfold actG0
      rw [dif_pos hk]
      congr 1
      show T v (h * hk.choose) = ∑ γ ∈ ({hk.choose} : Finset (GA D V)), T v (h * γ)
      rw [Finset.sum_singleton]
    rw [hEq]
    refine GlobalTheory.MultMem.isMultMap_smul _ (GlobalTheory.SphericalOps.isMultMap_heckeOn hT ?_ ?_)
    · intro k hk'
      rw [Finset.mem_singleton.mp hk']
      exact hκ.1
    · intro v k hkJ g
      show ∑ γ ∈ ({hk.choose} : Finset (GA D V)), T v (g * k * γ) =
        levChi V β (flag1L L) k * ∑ γ ∈ ({hk.choose} : Finset (GA D V)), T v (g * γ)
      rw [Finset.sum_singleton, Finset.sum_singleton]
      obtain ⟨hmem, hchi⟩ := conj_mem_flag1 hκ hkJ
      have hl := hT.lev v _ hmem (g * hk.choose)
      rw [hchi] at hl
      rw [← hl]
      congr 1
      simp [mul_assoc]
  ·
    have hEq : U = 0 := by
      ext v h
      rw [hU v]
      unfold actG0
      rw [dif_neg hk]
      rfl
    rw [hEq]
    exact GlobalTheory.MultMem.isMultMap_zero

end GlobalTheory.FlagAction

end
