import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec

open MeasureTheory Filter Topology
open scoped Matrix ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Mul

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rAdj_realMul (μ : Measure (Mt k r)) (W : Module.End ℂ (RadSp k r z z' π π')) (m : Mx k r → ℝ)
    (hW : ∀ (Φ : RadSp k r z z' π π'), ∀ x ∈ DomR k r z z',
      (W Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = ((m x.2 : ℝ) : ℂ) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2) :
    RAdj μ (mkP W W) := by
  have hval : ∀ (Φ : RadSp k r z z' π π') (x : (Fin r → ℂ) × Mx k r),
      (W Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = ((m x.2 : ℝ) : ℂ) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 := by
    intro Φ x
    by_cases hx : x ∈ DomR k r z z'
    · exact hW Φ x hx
    · rw [Formalism.FourierDecayAlt.P5.radSp_zero_off (W Φ) hx, Formalism.FourierDecayAlt.P5.radSp_zero_off Φ hx, smul_zero]
  have htest : ∀ Ψ : RadSp k r z z' π π', RTest Ψ → RTest (W Ψ) := by
    rintro Ψ ⟨K, hK, hKD, h0⟩
    exact ⟨K, hK, hKD, fun x hx => by rw [hval, h0 x hx, smul_zero]⟩
  have hip : ∀ Φ Ψ : RadSp k r z z' π π', radIp μ (W Φ) Ψ = radIp μ Φ (W Ψ) := by
    intro Φ Ψ
    unfold radIp
    congr 1; funext c; congr 1; funext x
    have e1 := hval Φ (c, Matrix.of x)
    have e2 := hval Ψ (c, Matrix.of x)
    simp only at e1 e2
    rw [e1, e2, hsVec_smul_rd, hsVec_smul_rd, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  exact ⟨htest, htest, fun Φ Ψ _ => hip Φ Ψ, fun Φ Ψ _ => hip Φ Ψ⟩

end Mul

theorem spectral_function_adjoint : RDSFnAdj := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ _
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hGGi, -⟩ := hD.2.2.1
  rw [hGGi]
  refine rAdj_realMul μ (X.fn 5) (fun g => (GGl P.k P.r z z' g)⁻¹) fun Φ x hx => ?_
  rw [X.fn_apply 5 Φ x hx]
  simp [fnVal]

section MulC

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rAdj_mulPair (μ : Measure (Mt k r)) (W W' : Module.End ℂ (RadSp k r z z' π π')) (m : (Fin r → ℂ) → ℂ)
    (hW : ∀ (Φ : RadSp k r z z' π π') c g, (W Φ : Fn k r (Wq →L[ℂ] Wp)) c g = m c • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g)
    (hW' : ∀ (Φ : RadSp k r z z' π π') c g,
      (W' Φ : Fn k r (Wq →L[ℂ] Wp)) c g = conj (m c) • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) :
    RAdj μ (mkP W W') ∧ RAdj μ (mkP W' W) := by
  have ht : ∀ (V : Module.End ℂ (RadSp k r z z' π π')) (m' : (Fin r → ℂ) → ℂ),
      (∀ (Φ : RadSp k r z z' π π') c g, (V Φ : Fn k r (Wq →L[ℂ] Wp)) c g = m' c • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) →
      ∀ Ψ, RTest Ψ → RTest (V Ψ) := by
    rintro V m' hV Ψ ⟨K, hK, hKD, h0⟩
    exact ⟨K, hK, hKD, fun x hx => by rw [hV, h0 x hx, smul_zero]⟩
  have h1 : ∀ Φ Ψ : RadSp k r z z' π π', radIp μ (W Φ) Ψ = radIp μ Φ (W' Ψ) := by
    intro Φ Ψ
    unfold radIp
    congr 1; funext c; congr 1; funext x
    rw [hW, hW', hsVec_smul_rd, hsVec_smul_rd, inner_smul_left, inner_smul_right]
  have h2 : ∀ Φ Ψ : RadSp k r z z' π π', radIp μ (W' Φ) Ψ = radIp μ Φ (W Ψ) := by
    intro Φ Ψ
    unfold radIp
    congr 1; funext c; congr 1; funext x
    rw [hW, hW', hsVec_smul_rd, hsVec_smul_rd, inner_smul_left, inner_smul_right, Complex.conj_conj]
  exact ⟨⟨ht W m hW, ht W' _ hW', fun Φ Ψ _ => h1 Φ Ψ, fun Φ Ψ _ => h2 Φ Ψ⟩,
    ⟨ht W' _ hW', ht W m hW, fun Φ Ψ _ => h2 Φ Ψ, fun Φ Ψ _ => h1 Φ Ψ⟩⟩

end MulC

def RDSPAdj : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∀ l, RAdj μ (L.p l) ∧ RAdj μ (L.pb l)

theorem rDSCoordAdj_of_p (hp : RDSPAdj) : RDSCoordAdj := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' hr l
  obtain ⟨-, -, hc, hci, hcb, hcbi, -⟩ := hD.2.2.1
  obtain ⟨hpl, hpbl⟩ := hp Wp Wq P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' hr l
  have e : ∀ (i : Fin 6) (Φ : RadSp P.k P.r z z' π π') c g,
      (X.op l i Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = Formalism.QuantumDeterminants.opL l i (fun c' => (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c' g) c :=
    fun i Φ c g => by rw [X.op_apply]; rfl
  have C1 := rAdj_mulPair μ (X.op l 1) (X.op l 4) (fun c => c l) (fun Φ c g => by rw [e]; rfl)
    (fun Φ c g => by rw [e]; rfl)
  have C2 := rAdj_mulPair μ (X.op l 2) (X.op l 5) (fun c => (c l)⁻¹) (fun Φ c g => by rw [e]; rfl)
    (fun Φ c g => by rw [e]; simp [Formalism.QuantumDeterminants.opL, Formalism.QuantumDeterminants.cbiOp, map_inv₀])
  refine ⟨hpl, hpbl, ?_, ?_, ?_, ?_⟩
  · rw [hc]; exact C1.1
  · rw [hci]; exact C2.1
  · rw [hcb]; exact C1.2
  · rw [hcbi]; exact C2.2

section IpLin

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem continuous_hsVec' : Continuous (fun A : Wq →L[ℂ] Wp => B.hsVec A) := by
  unfold B.hsVec
  first
  | fun_prop
  | continuity

theorem hsVec_add'_RDSCA (A A' : Wq →L[ℂ] Wp) : B.hsVec (A + A') = B.hsVec A + B.hsVec A' := by
  unfold B.hsVec
  ext i
  simp

theorem dxc_compact {C : Set (Fin r → ℂ)} (hC : IsCompact C) (hCO : C ⊆ OmX r) : dxc r C < ⊤ := by
  have hcont : ContinuousOn (fun c : Fin r → ℂ => ∏ l, (‖c l‖ ^ 2)⁻¹) C := by
    refine continuousOn_finset_prod _ fun l _ => ?_
    refine ContinuousOn.inv₀ ((continuous_norm.comp (continuous_apply l)).pow 2).continuousOn fun c hc => ?_
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hCO hc l))
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcont
  unfold dxc
  rw [withDensity_apply' _ C]
  calc ∫⁻ c in C, ENNReal.ofReal (∏ l, (‖c l‖ ^ 2)⁻¹) ≤ ∫⁻ _ in C, ENNReal.ofReal M :=
        setLIntegral_mono' hC.measurableSet fun c hc => ENNReal.ofReal_le_ofReal
          ((Real.le_norm_self _).trans (hM c hc))
    _ = ENNReal.ofReal M * volume C := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top

end IpLin

end Formalism.FourierDecayAlt.P.CutSE
