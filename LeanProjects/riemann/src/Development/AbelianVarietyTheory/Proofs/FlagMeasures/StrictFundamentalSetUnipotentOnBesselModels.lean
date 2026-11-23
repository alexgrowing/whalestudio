import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TypeAsm.CovTrans

open Formalism.L2.SG.LocWSOf

section Gen

variable {n m : ℕ} {ε : Fin n → Bool}

theorem conj_cancel (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ) (h : Q * Qi = 1)
    (A : Matrix (Fin n) (Fin n) ℂ) : Q * (Qi * A * Q) * Qi = A := by
  calc Q * (Qi * A * Q) * Qi = (Q * Qi) * A * (Q * Qi) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [h, Matrix.one_mul, Matrix.mul_one]

theorem inUJ_conj (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ) (H : Matrix (Fin m) (Fin m) ℂ)
    (hQ : Q * Qi = 1) (hH : Qᴴ * Formalism.REAL.Jm ε * Q = H) (x : Matrix (Fin m) (Fin m) ℂ) (hx : xᴴ * H * x = H) :
    Formalism.REAL.inUJ ε (Q * x * Qi) := by
  unfold Formalism.REAL.inUJ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc Qiᴴ * (xᴴ * Qᴴ) * Formalism.REAL.Jm ε * (Q * x * Qi) = Qiᴴ * (xᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * x) * Qi := by
        simp only [Matrix.mul_assoc]
    _ = Qiᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * Qi := by rw [hH, hx, ← hH]
    _ = (Q * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * Qi) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hQ]; simp

theorem inv_mul_of_inUJ (M : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.REAL.inUJ ε M) :
    Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε * M = 1 := by
  calc Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε * (Mᴴ * Formalism.REAL.Jm ε * M) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h]; exact Formalism.REAL.Jm_mul_self ε

def mkUJ (M : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.REAL.inUJ ε M) : Formalism.REAL.UJ ε :=
  ⟨⟨M, Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε, mul_eq_one_comm.1 (inv_mul_of_inUJ M h), inv_mul_of_inUJ M h⟩, h⟩

def mkUJ' (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.UJ ε :=
  if h : Formalism.REAL.inUJ ε M then mkUJ M h else 1

theorem mkUJ'_val (M : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.REAL.inUJ ε M) :
    Formalism.MainNotions.S.uMat (mkUJ' ε M) = M := by
  rw [mkUJ', dif_pos h]; rfl

theorem mkUJ'_coe (γ : Formalism.REAL.UJ ε) :
    mkUJ' ε (((γ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) = γ := by
  apply Subtype.ext; apply Units.ext
  exact mkUJ'_val _ γ.2

end Gen

section Tr

variable {D : D7} {X : HidaSetting D} (C : Choice X 1)

theorem trI_of (x : X.B.I.Ginf) (τ : D.what₂.Tau) :
    Matrix.of (trI C x τ) = C.Qi τ * Formalism.MainNotions.S.uMat (x (vOf X τ)) * C.Q τ :=
  rfl

theorem vOf_pl (v : InfinitePlace X.B.I.F) : vOf X (X.pl v) = v := X.pl.symm_apply_apply v

theorem trI_mul (a b : X.B.I.Ginf) : trI C (a * b) = GlobalTheory.DegVol.mulP (trI C a) (trI C b) := by
  funext τ
  apply Matrix.of.injective
  show Matrix.of (trI C (a * b) τ) = Matrix.of (trI C a τ) * Matrix.of (trI C b τ)
  rw [trI_of, trI_of, trI_of]
  rw [show Formalism.MainNotions.S.uMat ((a * b) (vOf X τ)) = Formalism.MainNotions.S.uMat (a (vOf X τ)) * Formalism.MainNotions.S.uMat (b (vOf X τ)) from rfl]
  generalize Formalism.MainNotions.S.uMat (a (vOf X τ)) = A
  generalize Formalism.MainNotions.S.uMat (b (vOf X τ)) = B
  have h := (C.isT τ).2.1
  calc C.Qi τ * (A * B) * C.Q τ = C.Qi τ * A * (C.Q τ * C.Qi τ) * B * C.Q τ := by
        rw [h]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = C.Qi τ * A * C.Q τ * (C.Qi τ * B * C.Q τ) := by simp only [Matrix.mul_assoc]

theorem trI_inj : Function.Injective (trI C) := by
  intro a b h
  funext v
  have e := congrArg Matrix.of (congrFun h (X.pl v))
  rw [trI_of, trI_of] at e
  have e2 : C.Q (X.pl v) * (C.Qi (X.pl v) * Formalism.MainNotions.S.uMat (a (vOf X (X.pl v))) * C.Q (X.pl v)) * C.Qi (X.pl v) =
      C.Q (X.pl v) * (C.Qi (X.pl v) * Formalism.MainNotions.S.uMat (b (vOf X (X.pl v))) * C.Q (X.pl v)) * C.Qi (X.pl v) := by rw [e]
  rw [conj_cancel _ _ (C.isT _).2.1, conj_cancel _ _ (C.isT _).2.1, vOf_pl] at e2
  exact Subtype.ext (Units.ext e2)

end Tr

section Back

variable {D : D7} {X : HidaSetting D} (C : Choice X 1)

def back (x : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) : X.B.I.Ginf :=
  fun v => mkUJ' (X.B.I.ε v) (C.Q (X.pl v) * Matrix.of (x (X.pl v)) * C.Qi (X.pl v))

def Sg : Set (D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :=
  {x | ∀ τ, Formalism.REAL.inUJ (X.B.I.ε (vOf X τ)) (C.Q τ * Matrix.of (x τ) * C.Qi τ)}

theorem back_trI (a : X.B.I.Ginf) : back C (trI C a) = a := by
  funext v
  unfold back
  rw [trI_of, conj_cancel _ _ (C.isT _).2.1, vOf_pl]
  exact mkUJ'_coe _

theorem trI_back {x : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS} (hx : x ∈ Sg C) : trI C (back C x) = x := by
  funext τ
  apply Matrix.of.injective
  rw [trI_of]
  unfold back
  have h := hx τ
  simp only [vOf, Equiv.apply_symm_apply] at h ⊢
  rw [mkUJ'_val _ h]
  calc C.Qi τ * (C.Q τ * Matrix.of (x τ) * C.Qi τ) * C.Q τ = (C.Qi τ * C.Q τ) * Matrix.of (x τ) * (C.Qi τ * C.Q τ) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.of (x τ) := by rw [(C.isT τ).1, Matrix.one_mul, Matrix.mul_one]

theorem range_trI : Set.range (trI C) = Sg C := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩ τ
    rw [trI_of]
    rw [conj_cancel _ _ (C.isT _).2.1]
    exact (a (vOf X τ)).2
  · intro hx
    exact ⟨back C x, trI_back C hx⟩

theorem cont_uMat {n : ℕ} {ε : Fin n → Bool} : Continuous (fun γ : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat γ) :=
  Units.continuous_val.comp continuous_subtype_val

theorem measurable_trI : Measurable (trI C) := by
  refine measurable_pi_lambda _ (fun τ => ?_)
  have hc : Continuous (fun γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      (Matrix.of.symm (C.Qi τ * Formalism.MainNotions.S.uMat γ * C.Q τ) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    (continuous_const.matrix_mul cont_uMat).matrix_mul continuous_const
  exact hc.measurable.comp (measurable_pi_apply (vOf X τ))

theorem measurableSet_Sg : MeasurableSet (Sg C) := by
  have : Sg C = ⋂ τ, (fun x : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => x τ) ⁻¹'
      {y : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS | Formalism.REAL.inUJ (X.B.I.ε (vOf X τ)) (C.Q τ * Matrix.of y * C.Qi τ)} := by
    ext x; simp [Sg]
  rw [this]
  refine MeasurableSet.iInter (fun τ => measurable_pi_apply τ ?_)
  apply IsClosed.measurableSet
  unfold Formalism.REAL.inUJ
  have hm : Continuous (fun y : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => C.Q τ * Matrix.of y * C.Qi τ) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact isClosed_eq ((hm.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hm) continuous_const

theorem measurable_mkUJ' {n m : ℕ} (ε : Fin n → Bool) (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ) :
    Measurable (fun y : (Fin m → Fin m → ℂ) => mkUJ' ε (Q * Matrix.of y * Qi)) := by
  set S : Set (Fin m → Fin m → ℂ) := {y | Formalism.REAL.inUJ ε (Q * Matrix.of y * Qi)} with hS
  have hm : Continuous (fun y : (Fin m → Fin m → ℂ) => Q * Matrix.of y * Qi) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hSc : IsClosed S := by
    unfold Formalism.REAL.inUJ at hS
    rw [hS]
    exact isClosed_eq ((hm.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hm) continuous_const
  have hf : Continuous (fun y : S => mkUJ (ε := ε) (Q * Matrix.of (y : Fin m → Fin m → ℂ) * Qi) y.2) := by
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    refine ⟨hm.comp continuous_subtype_val, ?_⟩
    exact ((continuous_const.matrix_mul (hm.comp continuous_subtype_val).matrix_conjTranspose).matrix_mul
      continuous_const)
  have e : (fun y : (Fin m → Fin m → ℂ) => mkUJ' ε (Q * Matrix.of y * Qi)) =
      fun y => if hy : y ∈ S then mkUJ (ε := ε) (Q * Matrix.of y * Qi) hy else (fun _ : (Sᶜ : Set _) => (1 : Formalism.REAL.UJ ε)) ⟨y, hy⟩ := by
    funext y; rfl
  rw [e]
  exact Measurable.dite hf.measurable measurable_const hSc.measurableSet

theorem measurable_back : Measurable (back C) := by
  refine measurable_pi_lambda _ (fun v => ?_)
  exact (measurable_mkUJ' _ _ _).comp (measurable_pi_apply (X.pl v))

theorem measEmb_trI : MeasurableEmbedding (trI C) :=
  MeasurableEmbedding.of_measurable_inverse (measurable_trI C) (by rw [range_trI]; exact measurableSet_Sg C)
    (measurable_back C) (back_trI C)

end Back

theorem isFund_trI : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1),
    GlobalTheory.DegVol.IsFund (trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u)
      (GlobalTheory.DegVol.RP D.R.k D.R.rS (fun _ => 1)) (trI C '' Y.FN u) := by
  intro D X Y u C
  have hsub : ∀ a b, a ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u → b ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u →
      a * b⁻¹ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u := by
    intro a b ha hb
    rw [← Formalism.L2.SG.Pf.NOsub_coe X u Y.hK] at ha hb ⊢
    exact Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hb)
  obtain ⟨hFm, hcov, hstr⟩ := Y.FN_fund u
  refine ⟨(measEmb_trI C).measurableSet_image.2 hFm, fun x hx => ?_⟩
  have hxS : x ∈ Sg C := fun τ =>
    inUJ_conj _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _ (hx τ).1.1
  have hy : trI C (back C x) = x := trI_back C hxS
  obtain ⟨s, hs, hsF⟩ := hcov (back C x)
  refine ⟨trI C s, ⟨⟨s, hs, rfl⟩, ?_⟩, ?_⟩
  · rw [← hy, ← trI_mul]
    exact ⟨_, hsF, rfl⟩
  · rintro m ⟨⟨s', hs', rfl⟩, ⟨f, hf, hfe⟩⟩
    rw [← hy, ← trI_mul] at hfe
    have e : f = s' * back C x := trI_inj C hfe
    rw [e] at hf
    have h1 := hstr _ hsF (s' * s⁻¹) (hsub _ _ hs' hs) (by rwa [mul_assoc, inv_mul_cancel_left])
    rw [mul_inv_eq_one.1 h1]

end GlobalTheory.TypeAsm.CovTrans
