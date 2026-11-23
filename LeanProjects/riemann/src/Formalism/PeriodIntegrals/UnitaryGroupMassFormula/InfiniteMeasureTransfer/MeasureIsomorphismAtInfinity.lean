import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.ContinuousEvI
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.MeasInfXferOf

noncomputable section

open NumberField Matrix Formalism.L2.SG.AdBridge
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)

namespace Formalism.L2.SG.Pf.MeasInfW

variable (I : AutInst)

abbrev hmI (g : HI I) : Matrix (Fin I.n) (Fin I.n) (TI I) :=
  ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J g : GL (Fin I.n) (TI I)) :
    Matrix (Fin I.n) (Fin I.n) (TI I))

def matI : HI I →* GL (Fin I.n) (TI I) :=
  (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J).subtype

theorem matI_apply (g : HI I) : ((matI I g : GL (Fin I.n) (TI I)) : Matrix _ _ _) = hmI I g := rfl

theorem thI_mem (g : HI I) (v : InfinitePlace I.F) :
    Formalism.REAL.inUJ (I.ε v) ((I.P v)⁻¹ * (hmI I g).map (thI I v) * I.P v) := by
  have hg : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig) (hmI I g) *
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.J * hmI I g =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.J := by
    have hm : ∀ h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J,
        (h : GL (Fin I.n) (TI I)) ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J :=
      fun h => h.2
    exact hm g
  have h1 : ((hmI I g).map (thI I v))ᴴ * I.J.map (I.φ v) * (hmI I g).map (thI I v) =
      I.J.map (I.φ v) := by
    have h2 := congrArg (fun M => M.map (thI I v)) hg
    simp only [Matrix.map_mul] at h2
    have e1 : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig)
        (hmI I g)).map (thI I v) = ((hmI I g).map (thI I v))ᴴ := by
      ext i j
      simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
        thI_sigR, starRingEnd_apply]
    have e2 : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.J).map (thI I v) =
        I.J.map (I.φ v) := by
      ext i j
      simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply, thI_inclR]
    rw [e1, e2] at h2
    exact h2
  have hd : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
  have hPP : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hPPh : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hPP, Matrix.conjTranspose_one]
  show ((I.P v)⁻¹ * (hmI I g).map (thI I v) * I.P v)ᴴ * Formalism.REAL.Jm (I.ε v) *
      ((I.P v)⁻¹ * (hmI I g).map (thI I v) * I.P v) = Formalism.REAL.Jm (I.ε v)
  rw [← I.P_spec v]
  simp only [Matrix.conjTranspose_mul]
  calc _ = (I.P v)ᴴ * (((hmI I g).map (thI I v))ᴴ * ((((I.P v)⁻¹)ᴴ * (I.P v)ᴴ) *
          I.J.map (I.φ v) * ((I.P v * (I.P v)⁻¹) * (hmI I g).map (thI I v)))) * I.P v := by
        simp only [Matrix.mul_assoc]
    _ = (I.P v)ᴴ * (((hmI I g).map (thI I v))ᴴ * I.J.map (I.φ v) * (hmI I g).map (thI I v)) *
          I.P v := by
        rw [hPPh, hPP]
        simp only [Matrix.one_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1]

def betaV (v : InfinitePlace I.F) : HI I →* Formalism.REAL.UJ (I.ε v) :=
  ((MulAut.conj (Formalism.L2.SG.Pf.Pu I v)⁻¹).toMonoidHom.comp ((Formalism.UG.bc (thI I v)).comp (matI I))).codRestrict
    (Formalism.REAL.UJ (I.ε v)) (fun g => by
      show Formalism.REAL.inUJ (I.ε v) _
      convert thI_mem I g v using 1
      simp [Formalism.L2.SG.Pf.Pu, Formalism.UG.bc, matI_apply, Matrix.coe_units_inv])

theorem betaV_val (v : InfinitePlace I.F) (g : HI I) :
    uMat (betaV I v g) = (I.P v)⁻¹ * (hmI I g).map (thI I v) * I.P v := by
  simp [betaV, uMat, Formalism.L2.SG.Pf.Pu, Formalism.UG.bc, matI_apply, Matrix.coe_units_inv]

def betaI : HI I →* I.Ginf := MonoidHom.pi (betaV I)

theorem continuous_betaV (v : InfinitePlace I.F) : Continuous (betaV I v) := by
  have hval : Continuous (fun g : HI I => hmI I g) :=
    Units.continuous_val.comp continuous_subtype_val
  have hinv : Continuous (fun g : HI I => hmI I g⁻¹) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  have key : ∀ f : HI I → Matrix (Fin I.n) (Fin I.n) (TI I), Continuous f →
      Continuous (fun g => (I.P v)⁻¹ * (f g).map (thI I v) * I.P v) := fun f hf =>
    (continuous_const.matrix_mul (hf.matrix_map (continuous_thI I v))).matrix_mul continuous_const
  apply continuous_induced_rng.2
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · convert key _ hval using 1
    funext g
    exact betaV_val I v g
  · convert key _ hinv using 1
    funext g
    simp only [Function.comp_apply]
    rw [← betaV_val, map_inv]
    rfl

theorem continuous_betaI : Continuous (betaI I) := continuous_pi fun v => continuous_betaV I v

section Bridge

variable (hb : Formalism.L2.SG.AdBridge.AdBridgeIso I)

theorem continuous_toInfL : Continuous (Formalism.L2.SG.Pf.MeasInf.toInfL I hb) := by
  have h1 : Continuous (fun s : I.Ginf => toHA I hb (s, 1)) :=
    (toHA I hb).continuous.comp (continuous_id.prodMk continuous_const)
  have hv : Continuous (fun x : HAd I => (hmat I x).map (kap I)) :=
    (Units.continuous_val.comp continuous_subtype_val).matrix_map (continuous_kap I)
  have hi : Continuous (fun x : HAd I =>
      (((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J x)⁻¹ :
        GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)).map (kap I)) :=
    (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map (continuous_kap I)
  apply continuous_induced_rng.2
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hv.comp h1
  · exact hi.comp h1

def toInfH : I.Ginf →* HI I :=
  (Formalism.L2.SG.Measures.haMap I.cm.sig I.J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA I.F)).comp
    ((toHA I hb).toMulEquiv.toMonoidHom.comp (MonoidHom.inl I.Ginf I.Gf))

theorem hmI_toInfL (s : I.Ginf) (i j : Fin I.n) :
    hmI I (Formalism.L2.SG.Pf.MeasInf.toInfL I hb s) i j = kap I (hmat I (toHA I hb (s, 1)) i j) := rfl

theorem betaI_toInfL (s : I.Ginf) : betaI I (Formalism.L2.SG.Pf.MeasInf.toInfL I hb s) = s := by
  funext v
  apply Subtype.ext
  apply Units.ext
  change uMat (betaV I v (Formalism.L2.SG.Pf.MeasInf.toInfL I hb s)) = uMat (s v)
  rw [betaV_val, show uMat (s v) = _ from (hb.choose_spec (s, 1)).1 v]
  simp only [Formalism.L2.SG.AdBridge.ofHAInf]
  congr 2
  ext i j
  simp only [Matrix.map_apply]
  rw [hmI_toInfL, thI_kap]
  rfl

private lemma eq_of_conj_eq_of_isUnit {n : ℕ} (A B P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (h : P⁻¹ * A * P = P⁻¹ * B * P) : A = B := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have h1 := congrArg (fun M => P * M * P⁻¹) h
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one] at h1
  simpa only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul] using h1

theorem betaI_inj (g g' : HI I) (h : betaI I g = betaI I g') : g = g' := by
  have hv : ∀ v, (hmI I g).map (thI I v) = (hmI I g').map (thI I v) := by
    intro v
    have h1 := congrArg uMat (congrFun h v)
    have e1 : uMat (betaI I g v) = (I.P v)⁻¹ * (hmI I g).map (thI I v) * I.P v := betaV_val I v g
    have e2 : uMat (betaI I g' v) = (I.P v)⁻¹ * (hmI I g').map (thI I v) * I.P v :=
      betaV_val I v g'
    rw [e1, e2] at h1
    exact eq_of_conj_eq_of_isUnit _ _ _ (I.P_unit v) h1
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply thI_ext I
  intro v
  have h3 := congrFun (congrFun (hv v) i) j
  simp only [Matrix.map_apply] at h3
  exact h3

theorem toInfL_betaI (g : HI I) : Formalism.L2.SG.Pf.MeasInf.toInfL I hb (betaI I g) = g := betaI_inj I _ g (betaI_toInfL I hb (betaI I g))

def toInfE : I.Ginf ≃ₜ* HI I where
  toFun := Formalism.L2.SG.Pf.MeasInf.toInfL I hb
  invFun := betaI I
  left_inv := betaI_toInfL I hb
  right_inv := toInfL_betaI I hb
  map_mul' := (toInfH I hb).map_mul
  continuous_toFun := continuous_toInfL I hb
  continuous_invFun := continuous_betaI I

end Bridge

theorem measure_isomorphism_at_infinity : IsoStep := fun I hb => ⟨toInfE I hb, fun _ => rfl⟩

end Formalism.L2.SG.Pf.MeasInfW
