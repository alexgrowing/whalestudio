import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic

noncomputable section

namespace Formalism.L2.SG.AdBridge

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)

variable (I : AutInst)

abbrev HAd : Type := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J

abbrev hmat (h : HAd I) : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :=
  ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h :
    GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) _)

def evV (v : InfinitePlace I.F) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding v).comp
    ((Pi.evalRingHom (fun w : InfinitePlace I.F => w.Completion) v).comp
      (RingHom.fst (InfiniteAdeleRing I.F) (FiniteAdeleRing (𝓞 I.F) I.F)))

theorem evV_algebraMap (v : InfinitePlace I.F) (a : I.F) :
    evV I v (algebraMap I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) a) = v.embedding a := by
  first
    | (exact InfinitePlace.Completion.extensionEmbedding_coe v ((WithAbs.equiv v.1).symm a))
    | (have h := InfinitePlace.Completion.extensionEmbedding_coe v ((WithAbs.equiv v.1).symm a); simp only [Equiv.apply_symm_apply] at h; exact h)
    | (simp [evV]; done)

def thetaV (v : InfinitePlace I.F) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E →+* ℂ :=
  letI : Algebra I.F ℂ := v.embedding.toAlgebra
  (Algebra.TensorProduct.lift
    ({ evV I v with commutes' := fun a => evV_algebraMap I v a } :
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F →ₐ[I.F] ℂ)
    ({ I.φ v with commutes' := I.φ_over v } : I.E →ₐ[I.F] ℂ)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem thetaV_tmul (v : InfinitePlace I.F) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (x : I.E) :
    thetaV I v (a ⊗ₜ[I.F] x) = evV I v a * I.φ v x := by
  first
    | (simp [thetaV]; done)
    | (exact Algebra.TensorProduct.lift_tmul _ _ _ a x)
    | rfl

def tauF : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E →+* I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F :=
  (Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeRight : Formalism.MainNotions.S.Af I.F →ₐ[I.F] I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F).comp
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA I.F))
    (Algebra.TensorProduct.includeLeft : I.E →ₐ[I.F] I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem tauF_tmul (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (x : I.E) :
    tauF I (a ⊗ₜ[I.F] x) = x ⊗ₜ[I.F] a.2 := by
  first
    | (simp [tauF, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA, Algebra.TensorProduct.tmul_mul_tmul]; done)
    | (show (1 : I.E) ⊗ₜ[I.F] a.2 * x ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F) = _
       rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one])

def ofHAInf (h : HAd I) (v : InfinitePlace I.F) : Matrix (Fin I.n) (Fin I.n) ℂ :=
  (I.P v)⁻¹ * (hmat I h).map (thetaV I v) * I.P v

def ofHAFin (h : HAd I) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :=
  (hmat I h).map (tauF I)

def IsBridge (e : I.GA ≃ₜ* HAd I) : Prop :=
  ∀ x : I.GA, (∀ v, uMat (x.1 v) = ofHAInf I (e x) v) ∧ I.fmat x.2 = ofHAFin I (e x)

def AdBridgeIso : Prop := ∃ e : I.GA ≃ₜ* HAd I, IsBridge I e

def ratHA : Set (HAd I) :=
  {h | Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h ∈
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFin (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J}

def KinfV (v : InfinitePlace I.F) : Set (Formalism.REAL.UJ (I.ε v)) :=
  {k | ∀ a b, I.ε v a ≠ I.ε v b → uMat k a b = 0}

def KGA : Set I.GA := {x | (∀ v, x.1 v ∈ KinfV I v) ∧ x.2 ∈ I.Kset}

def majV (v : InfinitePlace I.F) : Matrix (Fin I.n) (Fin I.n) ℂ := ((I.P v)⁻¹)ᴴ * (I.P v)⁻¹

def KinfHA : Set (HAd I) :=
  {h | ∀ v, ((hmat I h).map (thetaV I v))ᴴ * majV I v * (hmat I h).map (thetaV I v) = majV I v}

def prF : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E →+* Formalism.MainNotions.S.Af I.F ⊗[I.F] I.E :=
  (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA I.F) (AlgHom.id I.F I.E)).toRingHom

def KfHA : Set (HAd I) :=
  {h | ∀ v : HeightOneSpectrum (𝓞 I.F),
    Formalism.L2.SG.Sub.compV v (Formalism.UG.bc (prF I)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h)) ∈
      Formalism.L2.SG.Sub.Kloc v (I.L : Set (Fin I.n → I.E))}

def KHA : Set (HAd I) := KinfHA I ∩ KfHA I

def AdBridgeGF : Prop := ∀ e : I.GA ≃ₜ* HAd I, IsBridge I e → e '' I.GFset = ratHA I

def AdBridgeK : Prop := ∀ e : I.GA ≃ₜ* HAd I, IsBridge I e → e '' KGA I = KHA I

def AdelicIsomorphism : Prop := AdBridgeIso I ∧ AdBridgeGF I ∧ AdBridgeK I

def toHA (hb : AdBridgeIso I) : I.GA ≃ₜ* HAd I := hb.choose

theorem toHA_isBridge (hb : AdBridgeIso I) : IsBridge I (toHA I hb) := hb.choose_spec

theorem thetaV_inclR (v : InfinitePlace I.F) (x : I.E) :
    thetaV I v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) x) = I.φ v x := by
  have h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) x =
      (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) ⊗ₜ[I.F] x := rfl
  rw [h, thetaV_tmul, map_one, one_mul]

theorem tauF_inclR (x : I.E) :
    tauF I (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) x) =
      Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x := by
  have h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) x =
      (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) ⊗ₜ[I.F] x := rfl
  rw [h, tauF_tmul]
  rfl

theorem thetaV_sigR (v : InfinitePlace I.F) (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    thetaV I v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig x) =
      starRingEnd ℂ (thetaV I v x) := by
  have hv : v.IsReal := by
    first
    | exact I.cm.totReal.isReal v
    | (haveI := I.cm.totReal; exact NumberField.IsTotallyReal.isReal v)
  have hc : Continuous (InfinitePlace.Completion.extensionEmbedding v) := by
    first
    | exact (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous
    | fun_prop
  have hK : ∀ y : I.F, starRingEnd ℂ (v.embedding y) = v.embedding y := by
    intro y
    first
    | exact RingHom.congr_fun
        (NumberField.ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hv)) y
    | simpa using RingHom.congr_fun
        (NumberField.ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hv)) y
  have key : ∀ c : v.Completion, starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding v c) =
      InfinitePlace.Completion.extensionEmbedding v c := by
    intro c
    first
    | (refine InfinitePlace.Completion.induction_on c (isClosed_eq (Complex.continuous_conj.comp hc) hc) ?_; intro y; first | (rw [InfinitePlace.Completion.extensionEmbedding_coe]; exact hK _) | (simp only [InfinitePlace.Completion.extensionEmbedding_coe]; exact hK _) | (simp [InfinitePlace.Completion.extensionEmbedding_coe, hK]; done) | (simp [hK]; done))
    | (refine (InfinitePlace.Completion.denseRange_coe (v := v)).induction_on c (isClosed_eq (Complex.continuous_conj.comp hc) hc) ?_; intro y; first | (rw [InfinitePlace.Completion.extensionEmbedding_coe]; exact hK _) | (simp only [InfinitePlace.Completion.extensionEmbedding_coe]; exact hK _) | (simp [InfinitePlace.Completion.extensionEmbedding_coe, hK]; done) | (simp [hK]; done))
    | (refine (InfinitePlace.Completion.denseRange_coe v).induction_on c (isClosed_eq (Complex.continuous_conj.comp hc) hc) ?_; intro y; first | (rw [InfinitePlace.Completion.extensionEmbedding_coe]; exact hK _) | (simp only [InfinitePlace.Completion.extensionEmbedding_coe]; exact hK _) | (simp [InfinitePlace.Completion.extensionEmbedding_coe, hK]; done) | (simp [hK]; done))
    | (obtain ⟨c'⟩ := c; refine UniformSpace.Completion.induction_on c' (isClosed_eq (Complex.continuous_conj.comp (hc.comp (by fun_prop))) (hc.comp (by fun_prop))) ?_; intro y; first | (rw [InfinitePlace.Completion.extensionEmbedding_coe]; exact hK _) | (simp only [InfinitePlace.Completion.extensionEmbedding_coe]; exact hK _) | (simp [InfinitePlace.Completion.extensionEmbedding_coe, hK]; done) | (simp [hK]; done))
  have hreal : ∀ a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F, starRingEnd ℂ (evV I v a) = evV I v a :=
    fun a => key (a.1 v)
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    have hs : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig (a ⊗ₜ[I.F] y) =
        a ⊗ₜ[I.F] I.cm.sig y := rfl
    rw [hs, thetaV_tmul, thetaV_tmul, map_mul, hreal]
    congr 1
    exact I.cm.cmUnram.2.1 (I.φ v) y
  | add a b ha hb => simp only [map_add, ha, hb]

theorem ofHAInf_rat (h : HAd I) (γ : GL (Fin I.n) I.E)
    (hγ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h =
      Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) γ) (v : InfinitePlace I.F) :
    ofHAInf I h v = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
  have hh : hmat I h = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) := by
    first
      | (unfold hmat; rw [hγ]; rfl)
      | (simp only [hmat, hγ]; rfl)
      | (simp only [hmat, hγ]; done)
      | (rw [show hmat I h = ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h :
          GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)) :
          Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)) from rfl, hγ]; rfl)
  have key : (hmat I h).map (thetaV I v) = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) := by
    rw [hh]
    ext i j
    simp only [Matrix.map_apply]
    exact thetaV_inclR I v _
  unfold ofHAInf
  rw [key]

theorem ofHAFin_rat (h : HAd I) (γ : GL (Fin I.n) I.E)
    (hγ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h =
      Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) γ) :
    ofHAFin I h = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := by
  have hh : hmat I h = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) := by
    first
      | (unfold hmat; rw [hγ]; rfl)
      | (simp only [hmat, hγ]; rfl)
      | (simp only [hmat, hγ]; done)
      | (rw [show hmat I h = ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h :
          GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)) :
          Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)) from rfl, hγ]; rfl)
  unfold ofHAFin
  rw [hh]
  ext i j
  simp only [Matrix.map_apply]
  exact tauF_inclR I _

theorem ofHAInf_mem (h : HAd I) (v : InfinitePlace I.F) : Formalism.REAL.inUJ (I.ε v) (ofHAInf I h v) := by
  have hM : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) (hmat I h) *
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J * hmat I h =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J := h.2
  have h1 : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig)
      (hmat I h)).map (thetaV I v) = ((hmat I h).map (thetaV I v))ᴴ := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
    rw [thetaV_sigR, starRingEnd_apply]
  have h2 : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J).map (thetaV I v) =
      I.J.map (I.φ v) := by
    ext i j
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply]
    exact thetaV_inclR I v _
  have hA : ((hmat I h).map (thetaV I v))ᴴ * I.J.map (I.φ v) * (hmat I h).map (thetaV I v) =
      I.J.map (I.φ v) := by
    have h3 := congrArg (fun X => X.map (thetaV I v)) hM
    simp only [Matrix.map_mul] at h3
    rw [h1, h2] at h3
    exact h3
  have hPu : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
  have hPP : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hPu
  have hPPh : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hPP, Matrix.conjTranspose_one]
  unfold Formalism.REAL.inUJ ofHAInf
  rw [← I.P_spec v]
  calc _ = (I.P v)ᴴ * (((hmat I h).map (thetaV I v))ᴴ * (((I.P v)⁻¹)ᴴ * (I.P v)ᴴ) *
        I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) * (hmat I h).map (thetaV I v)) * I.P v := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (I.P v)ᴴ * (((hmat I h).map (thetaV I v))ᴴ * I.J.map (I.φ v) *
        (hmat I h).map (thetaV I v)) * I.P v := by
        rw [hPPh, hPP]
        simp only [Matrix.mul_one]
    _ = _ := by rw [hA]

private theorem tauF_sigR_comm (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    tauF I (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig x) =
      Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F) (tauF I x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    have hs : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig (a ⊗ₜ[I.F] y) =
        a ⊗ₜ[I.F] I.cm.sig y := rfl
    rw [hs, tauF_tmul, tauF_tmul]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem ofHAFin_mem (h : HAd I) :
    Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (ofHAFin I h) *
      I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * ofHAFin I h =
      I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := by
  have hM : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) (hmat I h) *
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J * hmat I h =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J := h.2
  have h1 : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig)
      (hmat I h)).map (tauF I) =
      Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (ofHAFin I h) := by
    ext i j
    simp only [Formalism.UG.cT, ofHAFin, Matrix.map_apply, Matrix.transpose_apply]
    exact tauF_sigR_comm I _
  have h2 : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J).map (tauF I) =
      I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := by
    ext i j
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply]
    exact tauF_inclR I _
  have h3 := congrArg (fun X => X.map (tauF I)) hM
  simp only [Matrix.map_mul] at h3
  rw [h1, h2] at h3
  exact h3

end Formalism.L2.SG.AdBridge
