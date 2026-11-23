import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RealInputsBuiltClosedForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalisationScaledIdealMemIff

open Finset NumberField MeasureTheory Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.PBJoint

open Formalism.FourierDecayAlt.P

noncomputable section

theorem toBuiltPlace {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {Wp Wq : NumberField.InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    {Cb Cc A₀ : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    (h : KB.IsLeadingFormPlace Cb Cc S p f χ A₀) :
    JCT.IsBuiltPlace Cc S (KB.plT S p) f χ (KB.plν S p) (KB.plm S p) (KB.plTop S p) A₀ := by
  obtain ⟨⟨hg1, hg2, hU, hcut, -, -, -, hl1, hl2, -, hGr, -, hLC, hCA, hA, hv⟩, hE, hIn⟩ := h
  exact ⟨hg1, hg2, hU, ⟨hcut, fun v => ⟨(hv v).2.2.1, (p v).hT, (p v).hF, (p v).hP, (hv v).2.2.2.2, hE v⟩⟩,
    hl1, hl2, hGr, hLC, hCA, fun v => (hv v).2.2.2.1, by omega, hA, hIn⟩

theorem built_setting_to_model_place {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {Wp Wq : NumberField.InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    {Cb Cc c A₀ : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    (hc : c ≤ Cc) (h : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : KB.IsLeadingFormSetting Cb c S p f χ A₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, fun v => le_trans ?_ (h13 v), le_trans hc h14,
    le_trans ?_ h15, h16⟩
  · exact mul_le_mul_of_nonneg_right hc (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)

theorem prod_dlB {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (hU : S6.Unram E) (hg : 0 < S.g) (i : ℕ) :
    ∏ _v : Fin S.f, KB.dlB S i 1 =
      ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) := by
  rw [unipotent_dual_lattice_covolume E hU S.g _ 1 hg, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hf : S.f = S6.deg E := by
    rw [← (Formalism.FourierDecayAlt.P.S6x2.degreeFacts E).2.1, Fintype.card_congr S.pl.symm, Fintype.card_fin]
  rw [hf]
  unfold KB.dlB D.deG
  push_cast
  conv_rhs => rw [zpow_mul, zpow_natCast, pow_mul, ← mul_pow, ← mul_pow]
  rw [div_div_eq_mul_div]
  congr 1
  ring

theorem real_inputs_closed_model_place_two_of : KB.RealInputsClosedAdmissibleSettings := by
  intro hPA hRMF hPD hFS hMA hMu hLEM hLA hSL hMP hTP hBB Cb
  obtain ⟨C₆, hC₆, hLE⟩ := lemma_E_of_model lemma_E_of_residue level_zero_holds good_of_admissible hLEM
  obtain ⟨c1, hLA⟩ := hLA
  obtain ⟨c2, hSL⟩ := hSL
  obtain ⟨c7, hMP⟩ := hMP
  obtain ⟨c3, C₄, hC₄, hBB⟩ := hBB hPA Cb
  refine ⟨C₆, max c1 (max c2 (max c3 c7)), C₄, hC₆, hC₄, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ c H _ _ Vt hBPT hSB hc hcut hVt
  obtain ⟨-, -, -, -, hOk, hWd, hWd', -⟩ := hBPT.1
  have hBP := toBuiltPlace hBPT
  have m1 := jct_isBuiltPlace_mono (by simp) hBP (c := c1)
  have m2 := jct_isBuiltPlace_mono (by simp) hBP (c := c2)
  have m7 := jct_isBuiltPlace_mono (by simp) hBP (c := c7)
  have hB2 : KB.IsLeadingFormSetting Cb c3 S p f χ A₀ := built_setting_to_model_place (by simp) hBPT.1
  obtain ⟨-, hIA, ⟨Lw, hW, hTW⟩, ⟨Ll, Ll', hLB, hLT, hTL⟩, hSF⟩ := hBB E Wp Wq S p f χ A₀ hB2
  have htop : ∀ v, D.TopPSD (KB.plT S p v) (f v) χ (D.AdmAt S v) (KB.plTop S p v) := fun v =>
    hTP (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (S.l + 1) (p v).T (p v).ν' (p v).m₀ (p v).Θ (p v).TP (f v) χ
      (D.AdmAt S v)
  obtain ⟨hg1, hg2, hU, hB, hl1, hl2, hGr, -, -, hsm, -, -, -⟩ := hBP
  choose L j lam Cm σ hmod using
    hMP E Wp Wq S (KB.plT S p) f χ (KB.plν S p) (KB.plm S p) (KB.plTop S p) A₀ m7 hOk hWd hWd' c hc
  have hIn : JCT.BuiltInputs C₄ C₆ S (KB.plT S p) f χ (KB.plν S p) (KB.plm S p) (KB.plTop S p) L j lam c Cm σ
      Lw Ll Ll' Vt :=
    ⟨hl1, hl2, hLA E Wp Wq S _ f χ _ _ _ A₀ m1, hSL E Wp Wq S _ f χ _ _ _ A₀ m2 hSB, htop, hGr, hW, hTW, hLB, hLT,
      hTL, hSF, hsm, hcut, hmod, hVt⟩
  refine ⟨L, j, lam, Cm, σ, hmod, ?_⟩
  intro Kr hK0 Th e
  have hg : 0 < S.g := Nat.mul_pos hg1 hg2
  have hIBl : ∃ dl : ℕ → Fin S.f → ℝ,
      (∀ i, 1 ≤ i → i ≤ S.G.r + 1 →
        ∏ v, dl i v = ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1)) ∧
      ∀ v, JC.ThmPIntPlace S v fun i => dl i v :=
    ⟨fun i _ => KB.dlB S i 1, fun i _ _ => prod_dlB S hU hg i, hIA⟩
  obtain ⟨hPos, hGr', hInt, hP1, hP23, hT, hPG⟩ :=
    jct_parts_loc hPA hRMF hPD hFS hMA hMu C₄ C₆ E Wp Wq S (KB.plT S p) f χ (KB.plν S p) (KB.plm S p)
      (KB.plTop S p) A₀ L j lam c Cm σ Lw Ll Ll' H Vt hg1 hg2 hU hB hIBl hIn
  have hE : C.LemmaE S (JCT.jvModel S j Cm) :=
    hLE E Wp Wq S (KB.plT S p) f χ (KB.plν S p) (KB.plm S p) (KB.plTop S p) A₀ L j lam c Cm σ hB
      (fun v ε hε => cutoff_smooth _ _ _ _ (KB.plT S p v).base χ (f v) ε hB.1 (hsm v) hε) hcut hmod
  exact real_inputs_concrete_holds E Wp Wq S (JCT.jvModel S j Cm) H Vt C₄ hg1 hg2 hPos hGr' hInt hP1 hP23 hT hE
    hPG Kr hK0 Th e

end

end Formalism.FourierDecayAlt.P.PBJoint

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem jct_modelPlaceBuilt2_of (h : JCT.ModelPlaceBuilt) : JCT.ModelPlaceBuilt2 := by
  obtain ⟨Cc, hM⟩ := h
  exact ⟨Cc, fun E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB _ _ _ c hc v =>
    hM E Wp Wq S T f χ ν' m₀ top A₀ hB c hc v⟩

theorem real_inputs_closed_model_place_two : KB.RealInputsClosedAdmissibleSettings :=
  PBJoint.real_inputs_closed_model_place_two_of

theorem real_inputs_closed_model_place : KB.RealInputsClosedLeadingForm := by
  intro hPA hRMF hPD hFS hMA hMu hLEM hLA hSL hMP hTP hBB
  exact real_inputs_closed_model_place_two hPA hRMF hPD hFS hMA hMu hLEM hLA hSL (jct_modelPlaceBuilt2_of hMP) hTP hBB

end Formalism.FourierDecayAlt.P
