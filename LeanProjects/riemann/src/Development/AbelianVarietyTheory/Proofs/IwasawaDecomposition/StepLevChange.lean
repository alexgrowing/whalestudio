import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IoUniq
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RightInv
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodGA
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.DTheta

theorem stepLev_change : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (b : Bool) (t : T) (k : ℕ), k + 1 < D.R.m → ∀ (κ : GA D (Yc D k)), ∀ κ' ∈ levS (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)), ∀ c : ℂ, (∀ φ, R.ωY t k (κ, κ') (R.toRealDat.ptY t k φ) = c • R.toRealDat.ptY t k φ) → ∀ y : R.CC t (k + 1), y.1 ∈ MultT R.θ (R.MY (k + 1)) (levS (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))) (levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))) → ∀ φ w g, (R.ioY t k y).1 (R.ItY k φ w) (g * κ) = c * levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) κ' * (R.ioY t k y).1 (R.ItY k φ w) g := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH b t k hk κ κ' hκ' c hc y hy φ w g
  have hch : R.toRealDat.IsChain := RealDat.chain_of_weak hP.char.base.chain hH.aux.ex
  have hio := hch.ioY t k (by omega)
  have e1 := hio.eq y φ w (g * κ)
  have e2 := hio.eq y φ w g
  rw [← e1, ← e2]
  unfold Lift.liftInt

  have hm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hy)
  set χ1 := levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) with hχ1
  have hlev : ∀ (u : SmT (R.MY (k + 1))) h, y.1 u (h * κ') = χ1 κ' * y.1 u h := by
    intro u h
    induction u using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := hm.lev v κ' hκ' h
      simp only [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply] at this
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, this]
      ring
    | add a a' ha ha' =>
      simp only [map_add, Pi.add_apply, ha, ha']
      ring
  have hleft : ∀ (u : SmT (R.MY (k + 1))), ∀ γ ∈ GQ (Yc D (k + 1)), ∀ h, y.1 u (γ * h) = y.1 u h := by
    intro u γ hγ h
    induction u using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := (hm.aut v).left γ hγ h
      simp only [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply] at this
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, this]
    | add a a' ha ha' =>
      simp only [map_add, Pi.add_apply, ha, ha']
  have hω := hch.ωY t k hk
  have hpt := hch.ptY t k hk φ
  have hθ1 : ∀ h, thetaKO (R.ωY t k) (g * κ) h (R.toRealDat.ptY t k φ) =
      c * thetaKO (R.ωY t k) g (h * κ'⁻¹) (R.toRealDat.ptY t k φ) := by
    intro h
    unfold thetaKO
    have e : ((g * κ, h) : GA D (Yc D k) × GA D (Yc D (k + 1))) = (g, h * κ'⁻¹) * (κ, κ') := by
      ext <;> simp [mul_assoc]
    rw [e, map_mul, Module.End.mul_apply, hc φ, map_smul, Pi.smul_apply, smul_eq_mul]
  have hθ2 : ∀ γ ∈ GQ (Yc D (k + 1)), ∀ h, thetaKO (R.ωY t k) g (γ * h) (R.toRealDat.ptY t k φ) =
      thetaKO (R.ωY t k) g h (R.toRealDat.ptY t k φ) := by
    intro γ hγ h
    unfold thetaKO
    have e : ((g, γ * h) : GA D (Yc D k) × GA D (Yc D (k + 1))) = (1, γ) * (g, h) := by
      ext <;> simp
    rw [e, map_mul, Module.End.mul_apply]
    exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ hpt)
  have hmod := hP.char.base.models
  have hHF : (R.νY t (k + 1)).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D (k + 1))) (R.fdY t (k + 1)) (R.νY t (k + 1)) := by
    by_cases h2 : k + 1 + 1 < D.R.m
    · have h3 := hmod.νY t (k + 1) h2
      exact ⟨h3.1.1, h3.2⟩
    · have h3 := hmod.νY' t
      have e : D.R.m - 1 = k + 1 := by omega
      rw [e] at h3
      exact ⟨h3.1.1, h3.2⟩
  haveI := Formalism.IndefR.Eqv.measurableMul_GA D (Yc D (k + 1))
  haveI := Formalism.IndefR.Eqv.gQ_countable D (Yc D (k + 1))
  haveI := hHF.1
  haveI : (R.νY t (k + 1)).IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds _ _ hHF.1
  set Ψ : GA D (Yc D (k + 1)) → ℂ := fun h => thetaKO (R.ωY t k) g h (R.toRealDat.ptY t k φ) * y.1 w h with hΨ
  have hRI := Formalism.IndefR.Eqv.rightInv_holds (GA D (Yc D (k + 1))) (GQ (Yc D (k + 1))) (R.νY t (k + 1))
    (R.fdY t (k + 1)) hHF.2 Ψ (fun γ hγ h => by simp only [hΨ, hθ2 γ hγ h, hleft w γ hγ h]) κ'⁻¹
  calc ∫ h in R.fdY t (k + 1), thetaKO (R.ωY t k) (g * κ) h (R.toRealDat.ptY t k φ) * y.1 w h ∂(R.νY t (k + 1))
      = ∫ h in R.fdY t (k + 1), c * χ1 κ' * Ψ (h * κ'⁻¹) ∂(R.νY t (k + 1)) := by
        congr 1
        funext h
        have e := hlev w (h * κ'⁻¹)
        rw [inv_mul_cancel_right] at e
        simp only [hΨ, hθ1 h, e]
        ring
    _ = c * χ1 κ' * ∫ h in R.fdY t (k + 1), Ψ h ∂(R.νY t (k + 1)) := by
        rw [integral_const_mul, hRI.2]

end GlobalTheory.Mem.R3.DTheta
