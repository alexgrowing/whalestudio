import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricTestFunctionsAgreeRationalPointsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdditiveCharacterOneNe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierTransformCosetIndicatorEqFiniteColumnTranStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepTestFunctionEqColumnsTestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PenultimateStepPsiRationalRepEqColumnsDatumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocallyConstantSupportInvarianceOfDenseRationalStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

noncomputable section

namespace GlobalTheory.TwLast

theorem toLoc_of_mat {E k A B : Type} [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : E →+* k) {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (x : Matrix A B E) :
    x.map ι = toLoc ι e e' (Matrix.toLin' (Matrix.of fun i j => x (e.symm i) (e'.symm j))) := by
  ext i j
  simp [toLoc, Matrix.toLin'_apply, Matrix.mulVec_single]

theorem psi_isLocallyConstant {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (R : Ranks) (W : TwData k) (g : GL (XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1)) k) :
    IsLocallyConstant (fun p : Matrix (XIx (Fin R.k) (Fin R.t) (s + 1)) (XIx (Fin R.k) (Fin R.t) s) k × (XIx (Fin R.k) (Fin R.t) (s + 1) → k) =>
      (W.T s R).Psi g p.1 p.2) := by
  have hΦ : (W.T s R).Phi s 0 rfl ∈ SB _ := (Chain.ofTwist_regular _ _ _ _ _).1 s 0 rfl
  unfold Chain.Psi om
  refine (IsLocallyConstant.const _).mul (hΦ.1.comp_continuous ?_)
  refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
  refine continuous_pi fun r => continuous_pi fun c => ?_
  rcases r with r | r <;> rcases c with c | c
  · exact (continuous_apply c).comp ((continuous_apply r).comp continuous_fst)
  · exact (continuous_apply r).comp continuous_snd
  · exact r.elim0
  · exact r.elim0

theorem lastAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → LastAgree Ch sel mu cst σ₀ P ι s W ν L := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hc hA L G hL
  have hPhi := GlobalTheory.T.parahoric_test_functions_agree_rational_points X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA
  have hnm : P.1 ∉ Pr.vGs := hA.nmem
  have hint : ∀ a : X.E, ι a ∈ 𝒪[k] ↔ IntAt P.1 a := hA.compl.int
  have hϖ : (W.ϖ : k) = ι (qOf P.1 : X.E) := hA.compl.unif
  refine ⟨fun al g hg => ⟨fun x₀ y => ?_, fun e' e he' he x₀ y' =>
    GlobalTheory.T.penultimateStepPsi_rationalRep_eq_columnsDatum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hc hA hPhi _ g hg e' e he' he x₀ y'⟩, ?_⟩
  · have hrat := GlobalTheory.T.penultimateStepPsi_rationalRep_eq_columnsDatum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hc hA hPhi _ g hg
      (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R s) (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) (GlobalTheory.MatchCompare.isOrd_ordX R s) (GlobalTheory.MatchCompare.isOrd_ordX R (s + 1))
    refine GlobalTheory.T.locallyConstant_support_invariance_of_dense_rational k X.E ι hA.compl.dense _ _ ((W.T s R).Psi g) (psi_isLocallyConstant s R W g) (W.ϖ ^ cst.M) ?_ ?_ x₀ y
    · intro x y hne
      rw [toLoc_of_mat ι (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R s) x] at hne
      have hy : (fun a => ι (y a)) = fun a => ι ((fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)) ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)) := by
        simp
      rw [hy, hrat _ (fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i))] at hne
      have hs := hL.psiSupp al P _ _ (fun h => (right_ne_zero_of_mul hne) (by rw [h, map_zero]))
      rw [if_neg hnm] at hs
      rw [mem_box]
      intro a
      have h1 := hs ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)
      simp only [Equiv.symm_apply_apply] at h1
      have h' := (hint _).2 h1
      rw [map_mul, map_pow, ← hϖ] at h'
      have hϖ0 : ((W.ϖ : k) ^ cst.M) ≠ 0 := pow_ne_zero _ W.ϖ.ne_zero
      calc valuation k (ι (y a)) = valuation k (((W.ϖ : k) ^ cst.M)⁻¹ * ((W.ϖ : k) ^ cst.M * ι (y a))) := by
            rw [inv_mul_cancel_left₀ hϖ0]
        _ = valuation k (((W.ϖ : k) ^ cst.M)⁻¹) * valuation k ((W.ϖ : k) ^ cst.M * ι (y a)) := map_mul _ _ _
        _ ≤ valuation k (((W.ϖ : k) ^ cst.M)⁻¹) * 1 := by gcongr; exact (Valuation.mem_integer_iff _ _).1 h'
        _ = valuation k (((W.ϖ ^ cst.M)⁻¹ : kˣ) : k) := by simp
    · intro x y z hz
      rw [toLoc_of_mat ι (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R s) x]
      have hy : (fun a => ι (y a)) = fun a => ι ((fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)) ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)) := by
        simp
      have hyz : (fun a => ι (y a + z a)) = fun a => ι (((fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)) +
          (fun i => z ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i))) ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)) := by
        simp
      rw [hy, hyz, hrat, hrat _ (fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)), hL.psiInv al P _ _ _ ?_]
      rw [if_neg hnm]
      intro i
      apply (hint _).1
      rw [mem_box] at hz
      have h1 := hz ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)
      rw [map_mul, map_inv₀, map_pow, ← hϖ, Valuation.mem_integer_iff, map_mul, map_inv₀]
      have hv0 : valuation k ((W.ϖ : k) ^ cst.M) ≠ 0 := by simp
      calc (valuation k ((W.ϖ : k) ^ cst.M))⁻¹ * valuation k (ι (z ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)))
          ≤ (valuation k ((W.ϖ : k) ^ cst.M))⁻¹ * valuation k ((W.ϖ : k) ^ cst.M) :=
            by gcongr; simpa using h1
        _ = 1 := inv_mul_cancel₀ hv0
  · intro e' e he' he y y' hy'
    simp only [Chain.xiTop]
    rw [GlobalTheory.T.lastStepTestFunction_eq_columnsTestFunction X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hA hPhi e' e he' he y,
      GlobalTheory.T.fourierTransform_cosetIndicator_eq_finiteColumnTransform X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA (hL.depthQ P hnm) e' e he' he y y' hy', map_mul]

end GlobalTheory.TwLast
