import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HalfRatioLeSegmentBaseOfStd
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.IsTestGTranslate
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.DerivSmulConstAll
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.CoefficientIntegralPointwise
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HsInnerSmulSmul
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StCut4

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem sep_minors (I : Type) (ka al ga : I → I → ℂ)
    (h : ∀ A B E F, ka A B * star (ka E F) = al A F * ga B E) :
    ∀ A B A' B', ka A B * ka A' B' = ka A B' * ka A' B := by
  intro A B A' B'
  by_cases h0 : ∀ E F, ka E F = 0
  · simp [h0]
  push Not at h0
  obtain ⟨E, F, hEF⟩ := h0
  have hc : star (ka E F) ≠ 0 := by simpa using hEF
  have key : ∀ A B, ka A B = al A F * ga B E / star (ka E F) := fun A B => by
    rw [eq_div_iff hc, h]
  rw [key A B, key A' B', key A B', key A' B]
  ring

theorem one_mem_N : (1 : Mat k r) ∈ Nset k r :=
  ⟨gv_one, fun a i _ => by simp [Matrix.one_apply], fun i j _ _ _ => by simp [Matrix.one_apply]⟩

theorem gi_of (hIn : UnitaryGroupStructuralFacts) (hXi : XiExists) (hSm : StSmooth) (h1p : StCut1p) (h2 : StCut2) (hBI : StBetaInf)
    (hSB : StSymBeta) (h4c : StInvCC) (h0 : StSchurG) (h1 : StPairs) (h1' : StBeConv)
    (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (hX : SqIntG D X) (ha : aM k r ≤ X.a)
    {d : ℝ} (hd : IsFdegG D X d) {c : ℝ} (hc : 0 < c)
    (hcB : ∀ F F' : Mat k r → (Wp →L[ℂ] Wp), InCC (X.a - AG k r - 1) 5 F → InCC (X.a - AG k r - 1) 5 F' →
      beta D F F' = (c : ℂ) * betaInf D F F')
    (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hγ : IsZFrame k r D.z γ) (C : X.Hs ≃ₗᵢ⋆[ℂ] X.Hs)
    (hC1 : ∀ g ∈ GV k r, ∀ x y : X.Hs, ⟪y, X.σ (th k r γ g) x⟫_ℂ = ⟪C x, X.σ g (C y)⟫_ℂ)
    (hCm : ∀ u ∈ Vfl X, C u ∈ VflA X (X.a - AG k r - 1))
    {a₁ a₂ b₁ b₂ : X.Hs} (ha₁ : a₁ ∈ DDinf D X) (ha₂ : a₂ ∈ DDinf D X) (hb₁ : b₁ ∈ DDinf D X)
    (hb₂ : b₂ ∈ DDinf D X) :
    (ContinuousLinearMap.adjoint (beOp D X b₁ b₂)).comp (beOp D X a₁ a₂) =
      (ContinuousLinearMap.adjoint (beOp D X (C a₁) b₂)).comp (beOp D X (C b₁) a₂) := by
  have hA := half_ratio_le_segment_base_of_std D.k_pos ha
  have ha0 : 0 ≤ X.a := le_trans (by unfold aM nR; positivity) ha
  have hV : ∀ u ∈ DDinf D X, u ∈ Vfl X := by
    rintro u ⟨φ, hφ, rfl⟩; exact dd_mem D X ha0 hφ
  have i11 := incc_dd hSm D X hD hX ha ha₁ hb₁
  have i22 := incc_dd hSm D X hD hX ha ha₂ hb₂
  have hI := beInt_integrable_of D X hD hX ha h0 h1 h1'
  apply hs_ext
  intro X₀
  have v1 := beta_val h1p h2 hBI hXi D X hD hd hA hcB (mc X a₁ b₁) a₁ b₁ a₂ b₂ X₀ (fun g _ => rfl) i11 i22
    (hI a₁ (hV _ ha₁) a₂ (hV _ ha₂)) (hI b₁ (hV _ hb₁) b₂ (hV _ hb₂))
  have v2 := beta_val h1p h2 hBI hXi D X hD hd hA hcB (mc X a₁ b₁ ∘ th k r γ) (C b₁) (C a₁) a₂ b₂ X₀
    (fun g hg => hC1 g hg a₁ b₁) ((h4c k r Wp D X hD hX γ hγ).2 _ 5 _ i11) i22
    (beInt_int_mixed D X hD hX ha h0 h1 h1' (hCm _ (hV _ hb₁)) (hV _ ha₂))
    (beInt_int_mixed D X hD hX ha h0 h1 h1' (hCm _ (hV _ ha₁)) (hV _ hb₂))
  have sym := hSB k r Wp D X hD hX γ hγ _ hA (jcont_of hIn D hA) (mc X a₁ b₁) (fun g => mc X a₂ b₂ g • X₀)
    i11 (h1p k r Wp _ 5 _ X₀ i22)
  rw [v1, v2] at sym
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.1.ne'
  exact ((div_left_inj' hd').1 (mul_left_cancel₀ hc' sym)).symm

theorem pq_of (h0cut : StCut0) (hInv : StInvGroup) (hD1 : StBeEquiv)
    (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (hX : SqIntG D X)
    (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hγ : IsZFrame k r D.z γ) (C : X.Hs ≃ₗᵢ⋆[ℂ] X.Hs)
    (hC2 : ∀ h ∈ GV k r, ∀ v : X.Hs, C (X.σ h v) = X.σ (th k r γ h)⁻¹ (C v))
    (hI : ∀ a₁ ∈ DDinf D X, ∀ a₂ ∈ DDinf D X, Integrable (beInt D X a₁ a₂) (D.μW.prod D.μN))
    (hIC : ∀ a₁ ∈ DDinf D X, ∀ b₂ ∈ DDinf D X, Integrable (beInt D X (C a₁) b₂) (D.μW.prod D.μN))
    (gi : ∀ a₁ ∈ DDinf D X, ∀ a₂ ∈ DDinf D X, ∀ b₁ ∈ DDinf D X, ∀ b₂ ∈ DDinf D X,
      (ContinuousLinearMap.adjoint (beOp D X b₁ b₂)).comp (beOp D X a₁ a₂) =
        (ContinuousLinearMap.adjoint (beOp D X (C a₁) b₂)).comp (beOp D X (C b₁) a₂))
    {a₁ a₂ b₁ b₂ : X.Hs} (ha₁ : a₁ ∈ DDinf D X) (ha₂ : a₂ ∈ DDinf D X) (hb₁ : b₁ ∈ DDinf D X)
    (hb₂ : b₂ ∈ DDinf D X) {h : Mat k r} (hh : h ∈ UWset k r D.z) :
    (ContinuousLinearMap.adjoint (beOp D X b₁ b₂)).comp ((D.π h).comp (beOp D X a₁ a₂)) =
      (ContinuousLinearMap.adjoint (beOp D X (C a₁) b₂)).comp
        ((D.π (th k r γ h)).comp (beOp D X (C b₁) a₂)) := by
  have hUg : gbar k r γ h ∈ UWset k r D.z := (hInv k r Wp D X hD hX γ hγ).2.2.1 h hh
  have hthU : th k r γ h ∈ UWset k r D.z := uw_inv_mem hUg
  have hthi : (th k r γ h)⁻¹ ∈ UWset k r D.z := uw_inv_mem hthU
  have e1 : beOp D X (X.σ h a₁) a₂ = (D.π h).comp (beOp D X a₁ a₂) := by
    have := (hD1 k r Wp D X hD hX a₁ a₂ (hI a₁ ha₁ a₂ ha₂) h hh 1 one_mem_N).1
    rwa [one_mul, psiD_one, one_smul] at this
  have e4 : beOp D X (X.σ (th k r γ h)⁻¹ (C a₁)) b₂ =
      (D.π (th k r γ h)⁻¹).comp (beOp D X (C a₁) b₂) := by
    have := (hD1 k r Wp D X hD hX (C a₁) b₂ (hIC a₁ ha₁ b₂ hb₂) _ hthi 1 one_mem_N).1
    rwa [one_mul, psiD_one, one_smul] at this
  have hσa : X.σ h a₁ ∈ DDinf D X := h0cut k r Wp D X h (uw_gv hh) a₁ ha₁
  rw [← e1, gi _ hσa _ ha₂ _ hb₁ _ hb₂, hC2 h (uw_gv hh) a₁, e4, ContinuousLinearMap.adjoint_comp,
    pi_adj D hthi, gv_inv_inv (uw_gv hthU), ContinuousLinearMap.comp_assoc]

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem minors_DD (hIn : UnitaryGroupStructuralFacts) (hXi : XiExists) (hSm : StSmooth) (h0cut : StCut0) (h1p : StCut1p)
    (h2 : StCut2) (h3 : StCut3) (h4cut : StCut4) (hBI : StBetaInf) (hSB : StSymBeta) (h4c : StInvCC)
    (hInv : StInvGroup) (hD1 : StBeEquiv) (h0 : StSchurG) (h1 : StPairs) (h1' : StBeConv) (hW : StSchurW)
    (hF : StFrame) (h9g : StDichoG) (h9w : StDichoW) (h10 : StMixed)
    (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (hX : SqIntG D X) (ha : aM k r ≤ X.a) :
    ∀ u₁ ∈ DDinf D X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
  have hA := half_ratio_le_segment_base_of_std D.k_pos ha
  have ha0 : 0 ≤ X.a := le_trans (by unfold aM nR; positivity) ha
  have hV : ∀ u ∈ DDinf D X, u ∈ Vfl X := by
    rintro u ⟨φ, hφ, rfl⟩; exact dd_mem D X ha0 hφ
  obtain ⟨d, hd⟩ := h0 k r Wp D X hD hX
  obtain ⟨c, hc, hcB⟩ := lemB_of hIn hXi D hA
  obtain ⟨γ, hγ⟩ := hF k r D.z D.k_pos D.z_mem D.T_pos
  have hI := beInt_integrable_of D X hD hX ha h0 h1 h1'
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.1.ne'
  have hzero : (∀ a₁ ∈ DDinf D X, ∀ a₂ ∈ DDinf D X, ∀ η x : Wp, ⟪η, beOp D X a₁ a₂ x⟫_ℂ = 0) →
      ∀ u₁ ∈ DDinf D X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp,
        Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro hz u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    simp only [Mn, hz u₁ hu₁ u₂ hu₂, hz u₁ hu₁ u₄ hu₄, zero_mul, sub_zero]
  rcases h9g k r Wp D X hD hX γ hγ with hZ | ⟨C, hC1, hC2⟩
  · apply hzero
    intro a₁ ha₁ a₂ ha₂ η x
    have i11 := incc_dd hSm D X hD hX ha ha₁ ha₁
    have i22 := incc_dd hSm D X hD hX ha ha₂ ha₂
    have hAA : (ContinuousLinearMap.adjoint (beOp D X a₁ a₂)).comp (beOp D X a₁ a₂) = 0 := by
      apply hs_ext
      intro X₀
      have v1 := beta_val h1p h2 hBI hXi D X hD hd hA hcB (mc X a₁ a₁) a₁ a₁ a₂ a₂ X₀ (fun g _ => rfl)
        i11 i22 (hI _ (hV _ ha₁) _ (hV _ ha₂)) (hI _ (hV _ ha₁) _ (hV _ ha₂))
      have sym := hSB k r Wp D X hD hX γ hγ _ hA (jcont_of hIn D hA) (mc X a₁ a₁)
        (fun g => mc X a₂ a₂ g • X₀) i11 (h1p k r Wp _ 5 _ X₀ i22)
      rw [beta_zero h3 hInv h1p hBI hXi D X hD hX hA hcB γ hγ hZ a₁ a₁ a₂ a₂ X₀
        ((h4c k r Wp D X hD hX γ hγ).2 _ 5 _ i11) i22, v1] at sym
      have h5 : hsInner ((ContinuousLinearMap.adjoint (beOp D X a₁ a₂)).comp (beOp D X a₁ a₂)) X₀ = 0 := by
        rcases mul_eq_zero.1 sym.symm with h | h
        · exact absurd h hc'
        · exact (div_eq_zero_iff.1 h).resolve_right hd'
      rw [h5]
      unfold hsInner
      rw [show hsVec (0 : Wp →L[ℂ] Wp) = 0 by ext i; simp [hsVec], inner_zero_right]
    have hAx : beOp D X a₁ a₂ x = 0 := by
      have h5 : ⟪beOp D X a₁ a₂ x, beOp D X a₁ a₂ x⟫_ℂ = 0 := by
        rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply, hAA]
        simp
      exact inner_self_eq_zero.1 h5
    rw [hAx, inner_zero_right]
  · have hCm : ∀ u ∈ Vfl X, C u ∈ VflA X (X.a - AG k r - 1) := h10 k r Wp D X hD hX γ hγ ha C hC1
    have gi : ∀ a₁ ∈ DDinf D X, ∀ a₂ ∈ DDinf D X, ∀ b₁ ∈ DDinf D X, ∀ b₂ ∈ DDinf D X,
        (ContinuousLinearMap.adjoint (beOp D X b₁ b₂)).comp (beOp D X a₁ a₂) =
          (ContinuousLinearMap.adjoint (beOp D X (C a₁) b₂)).comp (beOp D X (C b₁) a₂) :=
      fun a₁ ha₁ a₂ ha₂ b₁ hb₁ b₂ hb₂ => gi_of hIn hXi hSm h1p h2 hBI hSB h4c h0 h1 h1' D X hD hX ha hd hc hcB
        γ hγ C hC1 hCm ha₁ ha₂ hb₁ hb₂
    have hIC : ∀ a₁ ∈ DDinf D X, ∀ b₂ ∈ DDinf D X, Integrable (beInt D X (C a₁) b₂) (D.μW.prod D.μN) :=
      fun a₁ ha₁ b₂ hb₂ => beInt_int_mixed D X hD hX ha h0 h1 h1' (hCm _ (hV _ ha₁)) (hV _ hb₂)
    have hPQ := fun {a₁ a₂ b₁ b₂ : X.Hs} (ha₁ : a₁ ∈ DDinf D X) (ha₂ : a₂ ∈ DDinf D X)
        (hb₁ : b₁ ∈ DDinf D X) (hb₂ : b₂ ∈ DDinf D X) =>
      h4cut hW k r Wp D hD γ (beOp D X b₁ b₂) (beOp D X a₁ a₂) (beOp D X (C a₁) b₂) (beOp D X (C b₁) a₂)
        (fun h hh => pq_of h0cut hInv hD1 D X hD hX γ hγ C hC2
          (fun a₁ ha₁ a₂ ha₂ => hI _ (hV _ ha₁) _ (hV _ ha₂)) hIC gi ha₁ ha₂ hb₁ hb₂ hh)
    rcases h9w k r Wp D X hD hX γ hγ with hZW | ⟨C₀, hC₀1, -⟩
    · apply hzero
      intro a₁ ha₁ a₂ ha₂ η x
      have h4 := (hPQ ha₁ ha₂ ha₁ ha₂).1 hZW x x η η
      rw [← inner_conj_symm (beOp D X a₁ a₂ x) η, Complex.mul_conj] at h4
      have h6 : Complex.normSq ⟪η, beOp D X a₁ a₂ x⟫_ℂ = 0 := by exact_mod_cast h4
      exact Complex.normSq_eq_zero.1 h6
    · intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
      have hsep := sep_minors ({u : X.Hs // u ∈ DDinf D X} × Wp)
        (fun A B => ⟪A.2, beOp D X A.1.1 B.1.1 B.2⟫_ℂ)
        (fun A F => ⟪A.2, C₀ (beOp D X (C A.1.1) F.1.1 F.2)⟫_ℂ)
        (fun B E => ⟪C₀ (beOp D X (C E.1.1) B.1.1 B.2), E.2⟫_ℂ)
        (fun A B E F => by
          have h4 := (hPQ A.1.2 B.1.2 E.1.2 F.1.2).2 C₀ hC₀1 B.2 F.2 E.2 A.2
          rw [← h4, ← starRingEnd_apply, inner_conj_symm])
        (⟨u₁, hu₁⟩, e₁) (⟨u₂, hu₂⟩, e₂) (⟨u₃, hu₃⟩, e₃) (⟨u₄, hu₄⟩, e₄)
      exact sub_eq_zero.2 hsep

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

theorem AG_ge {k r : ℕ} (hk : 1 ≤ k) : AB k r ≤ AG k r + 1 := by
  have e : nR k r = 2 * (r : ℝ) + k + 1 := by unfold nR; push_cast; ring
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold AB AG
  rw [e]
  nlinarith

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH
