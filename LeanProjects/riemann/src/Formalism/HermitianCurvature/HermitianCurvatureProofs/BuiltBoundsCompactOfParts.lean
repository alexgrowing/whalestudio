import Formalism.HermitianCurvature.ArchimedeanUniformConstantsCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopRatio
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCFinal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalNormNonneg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfLocal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopOfLocal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordMemBoundedLetterLists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralFormulaPassesToLimits
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBJoint
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StepFormCptAllOfStepFormAll

namespace Formalism.FourierDecayAlt.P.PBASM

open Formalism.FourierDecayAlt NumberField MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

def cutN {k r : ℕ} (n : ℕ) (g : B.Mat k r) : ℂ :=
  ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def cutSeq (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (n : ℕ) :
    ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :=
  fun v ε g => cutN n g • D.cutF (p v).T.base χ (f v) ε g

end defs

def WaveLocB : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∃ X : ℕ → Fin S.f → ℝ, JC.HidaCurvatureBarriers S X ∧
      ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.WaveLoc (PBL.setC S p F) v fun i => X i v

def LiftLocB : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∃ Λ : ℕ → ℕ → Fin S.f → ℝ, (∀ b s v, 0 ≤ Λ b s v) ∧
      (∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, Λ b s v ≤ S.base.szL b s v) ∧
      ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.LiftLoc (PBL.setC S p F) v fun b s => Λ b s v

def GermLocB : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∀ n v, KB.GermLoc (PBL.setC S p (cutSeq S p f χ n)) v

def PosB : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → C.ThmPPos (PBL.setC S p F)

def DecayUnif : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∀ v ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → ∀ h h', D.ptSize h = i - 1 →
      D.ptSize h' = i - 1 → ∃ C : ℝ, ∀ n, (∀ c : ℂ, c ≠ 0 →
        ‖(PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤
          C * ((1 + ‖c‖) ^ 3)⁻¹) ∧
        ∀ l : ℂ, ‖∫ c : ℂ, (PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)]) *
          KB.psiL S l c‖ ≤ C * ((1 + ‖l‖) ^ 3)⁻¹

def IntB : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∀ n, KB.IntAll (PBL.setC S p (cutSeq S p f χ n))

def ThresholdsPositive : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∀ b s v, 1 ≤ b → 1 ≤ s → 0 < J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s (S.pl v)

theorem psd_of_tendsto {α : Type} (Y : Finset α) (k : ℕ → α → α → ℂ) (k0 : α → α → ℂ)
    (hk : ∀ n, TB.PSDOn Y (k n)) (hl : ∀ x y, Tendsto (fun n => k n x y) atTop (𝓝 (k0 x y))) :
    TB.PSDOn Y k0 := by
  rw [PBA.psd_iff_qf]
  refine ⟨fun x _ y _ => ?_, fun c => ?_⟩
  · have h1 : Tendsto (fun n => k n y x) atTop (𝓝 (conj (k0 x y))) := by
      have := ((Complex.continuous_conj.tendsto _).comp (hl x y))
      refine this.congr fun n => ?_
      exact (((PBA.psd_iff_qf Y (k n)).1 (hk n)).1 x ‹_› y ‹_›).symm
    exact tendsto_nhds_unique (hl y x) h1
  · have hq : Tendsto (fun n => (PBA.qf Y (k n) c).re) atTop (𝓝 (PBA.qf Y k0 c).re) := by
      refine (Complex.continuous_re.tendsto _).comp ?_
      unfold PBA.qf
      refine tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun y _ => ?_
      exact ((tendsto_const_nhds.mul (hl x y)).mul tendsto_const_nhds)
    exact ge_of_tendsto' hq fun n => (((PBA.psd_iff_qf Y (k n)).1 (hk n)).2 c)

theorem core (hW : WaveLocB) (hL : LiftLocB) (hTL : PBL.TopLocB) (hDT : KB.DegTop) (hVT : Top.VecVTypes)
    (hTR : PBL.TopRatio) (hG : GermLocB) (hP : PosB) (hI : IntB) (hD : DecayUnif) (hTh : ThresholdsPositive) (Cb : ℝ) :
    ∃ Cc C₄ : ℝ, 1 ≤ C₄ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
      [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
      [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
      [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
      (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
      (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
      KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
        C.ThmPPos S ∧ KB.IntAll S ∧ (∃ Lw, JC.WaveByPlaces S Lw ∧ JC.HidaCurvatureBarriers S Lw) ∧
        (∃ Ll Ll', JC.LiftBelowTop S Ll ∧ JC.LiftTopDiag S Ll' ∧ JC.ThresholdsLift S Ll Ll') ∧
        JC.SumFormConcrete S C₄ := by
  obtain ⟨c1, h1⟩ := limit_of_module_forms Cb
  obtain ⟨C₄, hC₄, hSF⟩ := sum_form_of_local_statements
  obtain ⟨c2, h2⟩ := hW Cb
  obtain ⟨c3, h3⟩ := hL Cb
  obtain ⟨c4, h4⟩ := hG Cb
  obtain ⟨c5, h5⟩ := hP Cb
  obtain ⟨c6, h6⟩ := hI Cb
  obtain ⟨c7, h7⟩ := hD Cb
  obtain ⟨c8, h8⟩ := hTh Cb
  set Cc : ℝ := max (max (max c1 c2) (max c3 c4)) (max (max c5 c6) (max c7 (max c8 (28 * Real.exp 1)))) with hCc
  refine ⟨Cc, C₄, hC₄, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB
  have le1 : c1 ≤ Cc := by simp [hCc]
  have le2 : c2 ≤ Cc := by simp [hCc]
  have le3 : c3 ≤ Cc := by simp [hCc]
  have le4 : c4 ≤ Cc := by simp [hCc]
  have le5 : c5 ≤ Cc := by simp [hCc]
  have le6 : c6 ≤ Cc := by simp [hCc]
  have le7 : c7 ≤ Cc := by simp [hCc]
  have le8 : c8 ≤ Cc := by simp [hCc]
  have le9 : 28 * Real.exp 1 ≤ Cc := by simp [hCc]
  have hB' := hB
  obtain ⟨hg1, hg2, hU, hcut, -, -, -, -, -, -, hGo, -, -, -, hA, hv⟩ := hB'
  have hCI : KB.CutInside S := PBCut.cutInside_of_built hB

  have hFL : ∀ v ε, 0 < ε → (∀ n, KB.CptCoef (p v).T.base (cutSeq S p f χ n v ε)) ∧
      ∀ i w, KB.CutWord (D.parOf S v) (p v).l0 w → w.length ≤ S.Ntop → ∀ a b,
        Tendsto (fun n => (p v).RR (cutSeq S p f χ n v ε) i w a b) atTop
          (𝓝 ((p v).RR (D.cutF (p v).T.base χ (f v) ε) i w a b)) := by
    intro v ε hε
    obtain ⟨hl0, hInD, -, hCk, hCC⟩ := hv v
    refine h1 (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (f v) χ ε A₀ S.Ntop cutN (by rw [hl0]; exact hInD)
      hcut hε hCk hCC (le_trans ?_ hA) (fun n g => rfl)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right le1 (by positivity)) (by positivity)
  have hcpt : ∀ n v ε, 0 < ε → KB.CptCoef (p v).T.base (cutSeq S p f χ n v ε) := fun n v ε hε => (hFL v ε hε).1 n
  have hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ P Q,
      Tendsto (fun n => PBL.rrC S p (cutSeq S p f χ n) v ε i a P Q) atTop (𝓝 ((S.pd v).RR ε i a P Q)) := by
    intro v ε hε i a ha P Q
    obtain ⟨hl0, -, hpd, -, -⟩ := hv v
    obtain ⟨w, rfl⟩ := ha
    have hcw : KB.CutWord (D.parOf S v) (p v).l0 (w.1 v) := by rw [hl0]; exact PBD.cutWord_of_adm S hGo hCI w v
    have hlen : (w.1 v).length ≤ S.Ntop := le_trans (PBB.len_le_cnt S w v) w.2.2
    have ht := ((hFL v ε hε).2 i (w.1 v) hcw hlen (D.toStd S.G.r (S.g : ℝ) 1 P) (D.toStd S.G.r (S.g : ℝ) 1 Q)).const_mul
      (((1 / (D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) P * D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) Q *
        D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i) : ℝ) : ℂ))
    have hval : (S.pd v).RR ε i (w.1 v) P Q = (((1 / (D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) P *
        D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) Q *
        D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i) : ℝ) : ℂ)) *
        (p v).RR (D.cutF (p v).T.base χ (f v) ε) i (w.1 v) (D.toStd S.G.r (S.g : ℝ) 1 P)
          (D.toStd S.G.r (S.g : ℝ) 1 Q) := by
      rw [hpd]
      simp only [D.componentFamilySetting_ofSetting, KB.Pl.RR, hl0, one_pow]
    rw [hval]
    exact ht

  set RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ := fun n => PBL.rrC S p (cutSeq S p f χ n)
    with hRR
  have hIn : ∀ n, KB.IntAll (KB.withRR S (RR n)) := h6 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place le6 hB)
  have hPn : ∀ n, C.ThmPPos (KB.withRR S (RR n)) := fun n =>
    h5 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place le5 hB) _ (hcpt n)
  obtain ⟨hIS, hWL⟩ := integral_formula_passes_to_limits E Wp Wq S RR hg1 hg2 hU hconv hIn
    (h7 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place le7 hB))
  obtain ⟨hLC1, hLC2, hLC3⟩ := PBA.limit_closed E Wp Wq S RR hconv
  obtain ⟨X0, hXt0, hXl0⟩ := h2 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place le2 hB)

  set X : ℕ → Fin S.f → ℝ := fun i v => if 1 ≤ i ∧ i ≤ S.G.r + 1 then X0 i v else 0 with hXdef
  have hX0 : ∀ i v, 0 ≤ X i v := by
    intro i v
    by_cases hi : 1 ≤ i ∧ i ≤ S.G.r + 1
    · simp only [hXdef, if_pos hi]; exact (hXt0 i hi.1 hi.2 v).1
    · simp only [hXdef, if_neg hi, le_refl]
  have hXt : JC.HidaCurvatureBarriers S X := by
    intro i hi1 hi2 v
    simp only [hXdef, if_pos (And.intro hi1 hi2)]
    exact hXt0 i hi1 hi2 v
  have hXl : ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.WaveLoc (PBL.setC S p F) v fun i => X i v := by
    intro F hF v i hi1 hi2
    have hXi : X i v = X0 i v := by rw [hXdef]; exact if_pos ⟨hi1, hi2⟩
    simp only [hXi]
    exact hXl0 F hF v i hi1 hi2
  obtain ⟨Λ, hΛ0, hΛs, hΛl⟩ := h3 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place le3 hB)
  obtain ⟨hTt, hTl⟩ := hTL hDT hVT hTR Cb Cc E Wp Wq S p f χ A₀ le9 hB
  have hGL := h4 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place le4 hB)
  have hthr := h8 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place le8 hB)
  have hWn : ∀ n, JC.WaveByPlaces (KB.withRR S (RR n)) X := fun n =>
    plane_wave_bound_of_local_bounds E Wp Wq (KB.withRR S (RR n)) X hg1 hg2 hU hGo (hIn n) hX0 (hXl _ (hcpt n))
  have hLn : ∀ n, JC.LiftBelowTop (KB.withRR S (RR n)) Λ := fun n =>
    PBA.liftOfLoc_statement E Wp Wq (KB.withRR S (RR n)) Λ (hPn n) hGo hΛ0 (hΛl _ (hcpt n))
  have hTn : ∀ n, JC.LiftTopDiag (KB.withRR S (RR n)) (fun b _ v => PBL.lamTop S b v) := fun n =>
    PBA.top_of_local E Wp Wq (KB.withRR S (RR n)) _ (hPn n) hGo (hTl _ (hcpt n))
  have hSn : ∀ n, JC.SumFormConcrete (KB.withRR S (RR n)) C₄ := fun n =>
    hSF E Wp Wq (KB.withRR S (RR n)) X Λ hg1 hg2 hU (hPn n) hGo (hIn n) (hXl _ (hcpt n)) hXt (hΛl _ (hcpt n))
      (fun b s hb hs hbs v => ⟨hΛ0 b s v, hΛs b s hb hs hbs v⟩) hthr (hGL n)

  have hpos : C.ThmPPos S := by
    intro v ε hε i hi w Y
    refine psd_of_tendsto Y (fun n => (KB.withRR S (RR n)).gramLoc v ε i (w.1 v)) _ (fun n => hPn n v ε hε i hi w Y)
      fun x y => ?_
    exact (hconv v ε hε i (w.1 v) ⟨w, rfl⟩ x y).const_mul _
  exact ⟨hpos, hIS, ⟨X, hWL X hWn, hXt⟩, ⟨Λ, fun b _ v => PBL.lamTop S b v, hLC1 Λ hLn, hLC2 _ hTn,
    fun b s hb hs hbs v => ⟨hΛ0 b s v, hΛs b s hb hs hbs v⟩, hTt⟩, hLC3 C₄ hPn hGo hSn⟩

def BuiltBounds2CptOfParts : Prop :=
  (P5.ThmPActualCpt → WaveLocB) → (P5.ThmPActualCpt → LiftLocB) → PBL.TopLocB →
  (P5.ThmPActualCpt → KB.DegTop) → (P5.ThmPActualCpt → Top.VecVTypes) → (P5.ThmPActualCpt → PBL.TopRatio) →
  (P5.ThmPActualCpt → GermLocB) → (P5.ThmPActualCpt → PosB) → (P5.ThmPActualCpt → IntB) →
  (P5.ThmPActualCpt → DecayUnif) → (P5.ThmPActualCpt → ThresholdsPositive) → KB.BuiltBounds2Cpt

def BuiltBounds2OfParts : Prop :=
  (P5.ThmPActual → WaveLocB) → (P5.ThmPActual → LiftLocB) → PBL.TopLocB →
  (P5.ThmPActual → KB.DegTop) → (P5.ThmPActual → Top.VecVTypes) → (P5.ThmPActual → PBL.TopRatio) →
  (P5.ThmPActual → GermLocB) → (P5.ThmPActual → PosB) → (P5.ThmPActual → IntB) →
  (P5.ThmPActual → DecayUnif) → (P5.ThmPActual → ThresholdsPositive) → KB.BuiltBounds2

theorem builtBounds2CptOfParts : BuiltBounds2CptOfParts := by
  intro hW hL hTL hDT hVT hTR hG hP hI hD hTh hA Cb
  exact core (hW hA) (hL hA) hTL (hDT hA) (hVT hA) (hTR hA) (hG hA) (hP hA) (hI hA) (hD hA) (hTh hA) Cb

end

end Formalism.FourierDecayAlt.P.PBASM

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
