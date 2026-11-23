import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptRed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsCongruentMod

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

section G

variable (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

theorem av_cv (hθ : IsSplitEquiv X p θ) (s t : Idx D.R.rS D.R.k) :
    aV X u p θ s ⬝ᵥ cV X u p θ t =
      (θ (inclR (FpX X p) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J (vecAt (frameOf X u) s) (vecAt (frameOf X u) t)))).1 := by
  have h := MassDataIdxSteps.adq_pairR (X := X) (p := p) (θ := θ) (Q := 1) hθ (vecAt (frameOf X u) s) (vecAt (frameOf X u) t)
  unfold aV cV
  simpa only [MassDataIdxSteps.crd1, MassDataIdxSteps.crd2, inv_one, Units.val_one, Matrix.transpose_one, Matrix.one_mulVec] using h

def lF : Idx D.R.rS D.R.k → FpX X p
  | Sum.inr (Sum.inl (Sum.inr _)) =>
      (θ (inclR (FpX X p) (algebraMap X.B.I.F X.B.I.E (-(((D.mem u).A.T : ℕ) : X.B.I.F))))).1
  | _ => 1

theorem hac_frame (hθ : IsSplitEquiv X p θ) (s t : Idx D.R.rS D.R.k) (hs : ¬ IsW s) (ht : ¬ IsW t) :
    aV X u p θ s ⬝ᵥ cV X u p θ t = if t = dlH s then lF X u p θ s else 0 := by
  obtain ⟨hee, hff, hef, hez, hfz, hzz, -⟩ := MassDataIdxSteps.adq_std X u
  have hsw := MassDataMassesW.NRatW.hE_swap X
  rw [av_cv X u p θ hθ s t]
  rcases s with a | (i | ⟨⟩) | c
  · rcases t with b | (j | ⟨⟩) | d
    · simp only [vecAt, dlH]
      rw [hee]
      simp
    · exact absurd ⟨j, rfl⟩ ht
    · simp only [vecAt, dlH]
      rw [hez]
      simp
    · simp only [vecAt, dlH, lF]
      rw [hef]
      by_cases h : a = Fin.rev d
      · subst h
        simp
      · have h' : d ≠ Fin.rev a := fun e => h (by rw [e, Fin.rev_rev])
        simp [h, h']
  · exact absurd ⟨i, rfl⟩ hs
  · rcases t with b | (j | ⟨⟩) | d
    · simp only [vecAt, dlH]
      rw [hsw, hez, star_zero]
      simp
    · exact absurd ⟨j, rfl⟩ ht
    · simp only [vecAt, dlH, lF]
      simp only [hzz, ↓reduceIte]
    · simp only [vecAt, dlH]
      rw [hsw, hfz, star_zero]
      simp
  · rcases t with b | (j | ⟨⟩) | d
    · simp only [vecAt, dlH, lF]
      rw [hsw, hef]
      by_cases h : b = Fin.rev c
      · subst h
        simp
      · simp [h]
    · exact absurd ⟨j, rfl⟩ ht
    · simp only [vecAt, dlH]
      rw [hfz]
      simp
    · simp only [vecAt, dlH]
      rw [hff]
      simp

theorem lF_unit (hb : AdBridgeIso X.B.I) (hθ : IsSplitEquiv X p θ) (s : Idx D.R.rS D.R.k) (hs : ¬ IsW s) :
    lF X u p θ s ≠ 0 ∧ (lF X u p θ s)⁻¹ ∈ p.1.adicCompletionIntegers X.B.I.F := by
  rcases s with a | (i | ⟨⟩) | c
  · simp [lF]
  · exact absurd ⟨i, rfl⟩ hs
  · obtain ⟨Q, hQ⟩ := MassDataIdxSteps.exists_GL_latBasis_of_isSplitEquiv X p θ hθ
    have h := MassDataIdxSteps.adq_tau_inv X hb u p θ Q hθ hQ
    have htau : adqTau X u p θ Q = lF X u p θ (Sum.inr (Sum.inl (Sum.inr ()))) := by
      unfold adqTau
      rw [adq_pairR X p θ Q hθ]
      exact congrArg (fun x => (θ (inclR (FpX X p) x)).1) (MassDataIdxSteps.adq_std X u).2.2.2.2.2.1
    rw [htau] at h
    exact ⟨h.2, h.1⟩
  · simp [lF]

end G

end PIW.MassDataColumns
