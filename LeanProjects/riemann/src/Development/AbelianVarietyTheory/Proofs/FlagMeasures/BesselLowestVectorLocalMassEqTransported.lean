import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureRightInvariant
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGroupMatGroupUnimodular
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PhiTranslate

variable {D : D7} {X : HidaSetting D}

theorem transp_mem (C : Choice X 1) (τ : D.what₂.Tau) {m : MatKR D.R.k D.R.rS}
    (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    Formalism.REAL.inUJ (X.B.I.ε (vOf X τ)) (C.Q τ * m * C.Qi τ) := by
  obtain ⟨-, h2, h3, -⟩ := C.isT τ
  have hm' : mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm
  unfold Formalism.REAL.inUJ
  calc (C.Q τ * m * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * m * C.Qi τ)
      = (C.Qi τ)ᴴ * (mᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * m) * C.Qi τ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ := by rw [h3, hm']
    _ = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by rw [h2]; simp

theorem exists_uj {n : ℕ} {ε : Fin n → Bool} {M : Matrix (Fin n) (Fin n) ℂ} (hM : Formalism.REAL.inUJ ε M) :
    ∃ γ : Formalism.REAL.UJ ε, uMat γ = M := by
  have hM' : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε := hM
  have hl : (Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε) * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM', Formalism.REAL.Jm_mul_self]
  have hr : M * (Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε) = 1 := mul_eq_one_comm.1 hl
  exact ⟨⟨⟨M, _, hr, hl⟩, hM⟩, rfl⟩

theorem phiOf_eq (C : Choice X 1) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau) {m : MatKR D.R.k D.R.rS}
    (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    phiOf hB u τ m = wT C u τ (m * C.y τ) := by
  have hmy : m * C.y τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hm (C.y_mem τ)
  have hex : ∃ γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), uMat γ = C.Q τ * (m * C.y τ) * C.Qi τ :=
    exists_uj (transp_mem C τ hmy)
  unfold wT
  rw [dif_pos hex, (hB u τ).choose_spec.2 hex.choose, hex.choose_spec]
  unfold phiOf v0Of sigB bOf
  have hmul := (X.ds (vOf X τ)).2.2.1.1.2 _ (transp_mem C τ hm) _ (transp_mem C τ (C.y_mem τ))
  have e : C.Q τ * m * C.Qi τ * (C.Q τ * C.y τ * C.Qi τ) = C.Q τ * (m * C.y τ) * C.Qi τ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (C.Qi τ) (C.Q τ), (C.isT τ).1, Matrix.one_mul]
  rw [← ContinuousLinearMap.comp_apply, ← hmul, e]
  rfl

theorem bessel_lowest_vector_local_mass_eq_transported : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB →
    ∀ (u : D.what₂.Word) (τ : D.what₂.Tau), l2SG (C.nuS u τ) (phiOf hB u τ) = l2SG (C.nuS u τ) (wT C u τ) := by
  intro D X C hB hG u τ
  obtain ⟨hLF, hGW⟩ := hG
  obtain ⟨hW, -⟩ := hGW u τ
  obtain ⟨hc, -, hz, -, hTz, -, hGm, hWm, -, -, -, -, hq, -⟩ := hW
  obtain ⟨-, -, hSm, hcont, heq, -⟩ := hLF u τ
  have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
    refine lt_of_lt_of_eq ?_ hTz.symm
    unfold Tr
    exact_mod_cast (D.mem u).A.T_prime.pos
  have hN0 : muNB D 1 ≠ 0 := by
    intro h0
    apply hSm.2.1
    show (((C.muW u τ).prod (muNB D 1)).map _ : Measure _) = 0
    rw [h0, Measure.prod_zero, Measure.map_zero]
  have hκ : kapN D 1 ≠ 0 := fun h => hN0 (by simp [muNB, haarLie, h])
  have hN : IsHaarOn (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) (muNB D 1) :=
    Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ hκ ENNReal.ofReal_ne_top
  obtain ⟨hGG, hGH⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular D.R.k D.R.rS
  obtain ⟨hGH1, hGH2⟩ := hGH _ hGm
  obtain ⟨hSG, hsub, hS1, hS2⟩ := GlobalTheory.muSof_isHaar _ _ _ _ _ hz hT hWm hN
  have hset : PI.QuotientSetting (BranchingSupport.GG D.R.k D.R.rS) (Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ))
      (muGB X (C.Q τ) (C.Qi τ) τ) (Formalism.FourierDecayAlt.ThreeDimData.muSof (C.muW u τ) (muNB D 1)) (C.nuS u τ) :=
    ⟨hGG, hSG, hsub, hGH1, hS1, hGH2, hS2, hq⟩
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hWm hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hGm.2.2.1 h0 h1 hq
  have hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ), ∀ x ∈ BranchingSupport.GG D.R.k D.R.rS,
      ‖wT C u τ (s * x)‖ = ‖wT C u τ x‖ := by
    rintro _ ⟨h', hh, m, hmN, rfl⟩ x hx
    rw [heq h' hh m hmN x hx, norm_smul,
      show ‖psiS D (zB X (C.Qi τ) u τ) m‖ = 1 from Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_norm _ _ _, one_mul]
    exact Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary hT hc h' hh _
  set A : Set (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) := {x | Matrix.of x ∈ BranchingSupport.GG D.R.k D.R.rS} with hA
  have hAm : MeasurableSet A := IsClosed.measurableSet (α := Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) hGG.1
  have hc' : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => ‖wT C u τ (Matrix.of x)‖₊) A := hcont.nnnorm
  have hm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => ‖wT C u τ (Matrix.of x)‖₊)
      (fun _ => 0)) :=
    hc'.measurable_piecewise continuousOn_const hAm
  have hval : ∀ x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS, Matrix.of x ∈ BranchingSupport.GG D.R.k D.R.rS →
      A.piecewise (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => ‖wT C u τ (Matrix.of x)‖₊) (fun _ => 0) x =
        ‖wT C u τ (Matrix.of x)‖₊ :=
    fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have key := GlobalTheory.QuotRightInv.quotInv _ _ _ _ _ _ hset _ (hm.coe_nnreal_ennreal.pow_const 2) (fun s hs x hx => by
    rw [hval x hx, hval (fun i j => (s * Matrix.of x) i j) (hGG.2.2.1 s (hsub hs) _ hx)]
    congr 2
    exact NNReal.eq (hinv s hs _ hx)) (C.y τ) (C.y_mem τ)
  unfold l2SG
  refine Eq.trans (lintegral_congr_ae (hae.mono fun x hx => ?_))
    (key.trans (lintegral_congr_ae (hae.mono fun x hx => ?_)))
  · simp only
    rw [hval (fun i j => (Matrix.of x * C.y τ) i j) (hGG.2.2.1 _ hx _ (C.y_mem τ)), phiOf_eq C hB u τ hx]
    rfl
  · simp only
    rw [hval x hx]

end GlobalTheory.PhiTranslate
