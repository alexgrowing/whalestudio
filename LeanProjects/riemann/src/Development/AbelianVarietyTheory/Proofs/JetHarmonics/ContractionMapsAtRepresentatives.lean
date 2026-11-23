import Mathlib
import Formalism.HermitianCurvature.StatementD
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormSubRight
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPolyDegStar

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

namespace GlobalTheory.WigSh

open Matrix in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] in
private lemma exists_omg_eq_smul_of_isDFrame (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ)
    (m₀ g : _root_.Formalism.FourierDecayAlt.B.Mat k r) (hg : g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r) (hd : _root_.Formalism.FourierDecayAlt.D.IsDFrame D ν' m₀ g) :
    ∃ a : ℝ, 0 < a ∧ _root_.GlobalTheory.WigSh.omg k r D.z D.z' g =
      ((a : ℂ) * (starRingEnd ℂ) (_root_.Formalism.QuantumDeterminants.Zhat k r D.z D.z' g).det) • ν' := by
  have hu : g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) := hg
  have hinv : g⁻¹ = _root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r :=
    Matrix.inv_eq_right_inv (_root_.GlobalTheory.WigSh.OmgNorm.mul_adj hu)
  have hω : _root_.GlobalTheory.WigSh.omg k r D.z D.z' g = _root_.Formalism.FourierDecayAlt.D.prW k r D.z' (g⁻¹ *ᵥ _root_.Formalism.FourierDecayAlt.D.cofL D g) := by
    rw [hinv]; rfl
  unfold _root_.Formalism.FourierDecayAlt.D.IsDFrame at hd
  obtain ⟨-, ⟨a, ha, hEq⟩, -⟩ := hd
  exact ⟨a, ha, hω.trans hEq⟩

open Matrix in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] in
private lemma herm_smul_self_re_eq (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (a : ℝ) (d : ℂ) (ν : Fin (2 * r + k + 1) → ℂ) :
    (_root_.Formalism.QuantumDeterminants.herm H (((a : ℂ) * (starRingEnd ℂ) d) • ν) (((a : ℂ) * (starRingEnd ℂ) d) • ν)).re =
      a ^ 2 * (Complex.normSq d * (_root_.Formalism.QuantumDeterminants.herm H ν ν).re) := by
  rw [_root_.GlobalTheory.WigSh.OmgNorm.form_smul_left, _root_.GlobalTheory.WigSh.OmgNorm.form_smul_right, ← mul_assoc, Complex.star_def,
    Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_conj]
  ring

open Matrix in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] in
private lemma cofactor_eq_of_frames_lemma (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ)
    (m₀ g₁ g₂ : _root_.Formalism.FourierDecayAlt.B.Mat k r) (h₁ : g₁ ∈ _root_.Formalism.FourierDecayAlt.B.GV k r) (h₂ : g₂ ∈ _root_.Formalism.FourierDecayAlt.B.GV k r)
    (d₁ : _root_.Formalism.FourierDecayAlt.D.IsDFrame D ν' m₀ g₁) (d₂ : _root_.Formalism.FourierDecayAlt.D.IsDFrame D ν' m₀ g₂)
    (hZ : _root_.Formalism.QuantumDeterminants.Zhat k r D.z D.z' g₁ = _root_.Formalism.QuantumDeterminants.Zhat k r D.z D.z' g₂)
    (hG : _root_.Formalism.QuantumDeterminants.Gf k r D.z D.z' g₁ = _root_.Formalism.QuantumDeterminants.Gf k r D.z D.z' g₂)
    (hpos : 0 < _root_.Formalism.QuantumDeterminants.Gf k r D.z D.z' g₁) :
    _root_.GlobalTheory.WigSh.omg k r D.z D.z' g₁ = _root_.GlobalTheory.WigSh.omg k r D.z D.z' g₂ := by
  obtain ⟨a₁, ha₁, e₁⟩ := exists_omg_eq_smul_of_isDFrame D ν' m₀ g₁ h₁ d₁
  obtain ⟨a₂, ha₂, e₂⟩ := exists_omg_eq_smul_of_isDFrame D ν' m₀ g₂ h₂ d₂
  have n₁ := (_root_.GlobalTheory.WigSh.OmgNorm.omg_norm k r D.z D.z' g₁ D.z_mem D.T_pos D.z'_mem
    D.T'_pos h₁).2.2
  have n₂ := (_root_.GlobalTheory.WigSh.OmgNorm.omg_norm k r D.z D.z' g₂ D.z_mem D.T_pos D.z'_mem
    D.T'_pos h₂).2.2
  rw [e₁, herm_smul_self_re_eq] at n₁
  rw [e₂, herm_smul_self_re_eq, ← hZ, ← hG] at n₂
  set X := Complex.normSq (_root_.Formalism.QuantumDeterminants.Zhat k r D.z D.z' g₁).det * (_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) ν' ν').re
  have hT := D.T'_pos
  have hX : X ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at n₁
    have : 0 < _root_.Formalism.QuantumDeterminants.Gf k r D.z D.z' g₁ / _root_.Formalism.QuantumDeterminants.Tz k r D.z' := div_pos hpos hT
    linarith
  have hsq : a₁ ^ 2 = a₂ ^ 2 := mul_right_cancel₀ hX (n₁.trans n₂.symm)
  have ha : a₁ = a₂ := by nlinarith [sq_nonneg (a₁ - a₂), sq_nonneg (a₁ + a₂)]
  rw [e₁, e₂, ha, hZ]

open Matrix in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] in
private lemma omg_sgs_eq_inv_mulVec (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (p : _root_.Formalism.FourierDecayAlt.B.SS k r) (hp : D.inSS p)
    (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) (hg : g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r) :
    _root_.GlobalTheory.WigSh.omg k r D.z D.z' (_root_.Formalism.FourierDecayAlt.B.sgs p g) =
      (Matrix.of p.2.1)⁻¹ *ᵥ _root_.GlobalTheory.WigSh.omg k r D.z D.z' g := by
  unfold _root_.Formalism.FourierDecayAlt.B.RealPlaceData.inSS at hp
  obtain ⟨h1, n1, h2, n2⟩ := hp
  have hn1 : (Matrix.of p.1.2)⁻¹ ∈ _root_.Formalism.QuantumDeterminants.Nset k r := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv n1
  have u1 : (Matrix.of p.1.2)⁻¹ * g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (_root_.Formalism.FourierDecayAlt.P.B6.Nset_sub k r hn1) hg
  have u2 : (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) :=
    _root_.Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul u1 (_root_.Formalism.FourierDecayAlt.P.B6.Nset_sub k r n2)
  have e : (Matrix.of p.1.2 * Matrix.of p.1.1)⁻¹ * g * (Matrix.of p.2.2 * Matrix.of p.2.1) =
      (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1 := by
    rw [Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
  rw [_root_.Formalism.FourierDecayAlt.P.B5.sgs_eq, e, _root_.GlobalTheory.WigSh.omg_equivariant k r D.z D.z' _ _ _ D.z_mem D.T_pos
    D.z'_mem D.T'_pos u2 h1 h2, _root_.GlobalTheory.WigSh.omg_mul_N k r D.z D.z' _ _
    D.z_mem D.z'_mem u1 n2, _root_.GlobalTheory.WigSh.OmLeftN.omg_mul_left k r D.z D.z' _ _ D.z_mem hn1]

open Matrix in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] in
private lemma integrand_comp_lemma_5 {Wq' : Type} [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq']
    (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (D' : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq') (hz : D'.z = D.z) (hz' : D'.z' = D.z')
    (hπ : ∀ h ∈ _root_.Formalism.QuantumDeterminants.UWset k r D.z, D'.π h = D.π h) {n : ℕ}
    (A' : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq))
    (hA : _root_.GlobalTheory.WigSh.WigMap k r D.z' D'.π' D.π' n A') (g₀ : _root_.Formalism.FourierDecayAlt.B.Mat k r)
    (hg₀ : g₀ ∈ _root_.Formalism.FourierDecayAlt.B.GV k r) (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (p : _root_.Formalism.FourierDecayAlt.B.SS k r) (hp : D.inSS p) :
    _root_.Formalism.FourierDecayAlt.D.orbIntegrand D' g₀ (fun g => (F g).comp (A' (_root_.GlobalTheory.WigSh.omg k r D.z D.z' g))) p =
      (_root_.Formalism.FourierDecayAlt.D.orbIntegrand D g₀ F p).comp (A' (_root_.GlobalTheory.WigSh.omg k r D.z D.z' g₀)) := by
  have hp' := hp
  unfold _root_.Formalism.FourierDecayAlt.B.RealPlaceData.inSS at hp'
  obtain ⟨h1, -, h2, -⟩ := hp'
  unfold _root_.GlobalTheory.WigSh.WigMap at hA
  have hint := hA.2.1 _ (_root_.GlobalTheory.WigSh.OmgEquiv.inv_mem h2) (_root_.GlobalTheory.WigSh.omg k r D.z D.z' g₀)
  have hRF : _root_.Formalism.FourierDecayAlt.B.xiTau D' (1, 1) p = _root_.Formalism.FourierDecayAlt.B.xiTau D (1, 1) p := by unfold _root_.Formalism.FourierDecayAlt.B.xiTau; rw [hz, hz']
  unfold _root_.Formalism.FourierDecayAlt.D.orbIntegrand _root_.Formalism.FourierDecayAlt.B.rho
  beta_reduce
  rw [hRF, hπ _ h1, omg_sgs_eq_inv_mulVec D p hp g₀ hg₀, ContinuousLinearMap.smul_comp]
  congr 1
  simp only [ContinuousLinearMap.comp_assoc, hint]

open Matrix in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] in
private lemma orbital_comp_lemma_2 {Wq' : Type} [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq']
    [CompleteSpace Wp] (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (D' : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq') (hz : D'.z = D.z) (hz' : D'.z' = D.z')
    (hπ : ∀ h ∈ _root_.Formalism.QuantumDeterminants.UWset k r D.z, D'.π h = D.π h) (hμ : D'.μSS = D.μSS) {n : ℕ}
    (A' : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq))
    (hA : _root_.GlobalTheory.WigSh.WigMap k r D.z' D'.π' D.π' n A') (g₀ : _root_.Formalism.FourierDecayAlt.B.Mat k r)
    (hg₀ : g₀ ∈ _root_.Formalism.FourierDecayAlt.B.GV k r) (μ : MeasureTheory.Measure (_root_.Formalism.QuantumDeterminants.Mt k r))
    (hμH : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.FourierDecayAlt.C6.Rset g₀) μ) (hrel : _root_.Formalism.FourierDecayAlt.C6.IsRelevant D g₀) (hrel' : _root_.Formalism.FourierDecayAlt.C6.IsRelevant D' g₀)
    (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (θ : _root_.Formalism.FourierDecayAlt.B.SS k r → ℝ) (hθ : _root_.Formalism.FourierDecayAlt.D.IsNormCut D g₀ μ θ)
    (hint : MeasureTheory.Integrable (fun p => θ p • _root_.Formalism.FourierDecayAlt.D.orbIntegrand D g₀ F p) D.μSS) :
    _root_.Formalism.FourierDecayAlt.D.orbJ D' g₀ μ (fun g => (F g).comp (A' (_root_.GlobalTheory.WigSh.omg k r D.z D.z' g))) =
      (_root_.Formalism.FourierDecayAlt.D.orbJ D g₀ μ F).comp (A' (_root_.GlobalTheory.WigSh.omg k r D.z D.z' g₀)) := by
  have indep := _root_.Formalism.FourierDecayAlt.P.orbital_integral_indep_choice
  unfold _root_.Formalism.FourierDecayAlt.D.OrbJIndep at indep
  set L := A' (_root_.GlobalTheory.WigSh.omg k r D.z D.z' g₀) with hL
  set F' := fun g => (F g).comp (A' (_root_.GlobalTheory.WigSh.omg k r D.z D.z' g)) with hF'
  let CL : (Wq →L[ℂ] Wp) →L[ℂ] (Wq' →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq' Wq Wp).flip L
  have hCL : ∀ X, CL X = X.comp L := fun X => rfl
  have hθ' : _root_.Formalism.FourierDecayAlt.D.IsNormCut D' g₀ μ θ := by
    unfold _root_.Formalism.FourierDecayAlt.D.IsNormCut _root_.Formalism.FourierDecayAlt.B.RealPlaceData.inSS at hθ ⊢; rw [hz, hz']; exact hθ
  have hae : ∀ᵐ p ∂D.μSS, θ p • _root_.Formalism.FourierDecayAlt.D.orbIntegrand D' g₀ F' p = CL (θ p • _root_.Formalism.FourierDecayAlt.D.orbIntegrand D g₀ F p) := by
    filter_upwards [_root_.Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
    rw [ContinuousLinearMap.map_smul_of_tower, hCL, integrand_comp_lemma_5 D D' hz hz' hπ A' hA g₀ hg₀ F p hp]
  have hint' : MeasureTheory.Integrable (fun p => θ p • _root_.Formalism.FourierDecayAlt.D.orbIntegrand D' g₀ F' p) D'.μSS := by
    rw [hμ]; exact (CL.integrable_comp hint).congr (hae.mono fun p hp => hp.symm)
  have hval : ∫ p, θ p • _root_.Formalism.FourierDecayAlt.D.orbIntegrand D' g₀ F' p ∂D'.μSS =
      (∫ p, θ p • _root_.Formalism.FourierDecayAlt.D.orbIntegrand D g₀ F p ∂D.μSS).comp L := by
    rw [hμ, ← hCL, ← ContinuousLinearMap.integral_comp_comm CL hint]
    exact MeasureTheory.integral_congr_ae hae
  unfold _root_.Formalism.FourierDecayAlt.D.orbJ
  split_ifs with h₁ h₂ h₂
  · calc _ = ∫ p, θ p • _root_.Formalism.FourierDecayAlt.D.orbIntegrand D' g₀ F' p ∂D'.μSS :=
          indep k r Wp Wq' D' g₀ μ hrel' hμH F' _ θ h₁.choose_spec.1 hθ' h₁.choose_spec.2 hint'
      _ = (∫ p, θ p • _root_.Formalism.FourierDecayAlt.D.orbIntegrand D g₀ F p ∂D.μSS).comp L := hval
      _ = _ := congrArg (fun X => X.comp L)
          (indep k r Wp Wq D g₀ μ hrel hμH F _ θ h₂.choose_spec.1 hθ h₂.choose_spec.2 hint).symm
  · exact (h₂ ⟨θ, hθ, hint⟩).elim
  · exact (h₁ ⟨θ, hθ', hint'⟩).elim
  · exact (h₁ ⟨θ, hθ', hint'⟩).elim

open Matrix in

theorem _root_.GlobalTheory.WigSh.contraction_maps_at_representatives :
    ∃ c₃ : ℝ, ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ
        Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ
        Wq] (Wqp : Type) [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ
        Wqp] (Wqm : Type) [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ
        Wqm] (k r : ℕ) (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (Dp
        : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wqp) (Dm
        : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wqm) (ν' : (Fin (2 * r + k + 1) →
        ℂ)) (m₀ : _root_.Formalism.FourierDecayAlt.Q.Mx k r) (n₀ : ℕ) (b : ℝ) (Ap' : (Fin (2 * r + k
        + 1) → ℂ) → (Wqp →L[ℂ] Wq)) (Am' : (Fin (2 * r + k + 1) → ℂ) → (Wqm →L[ℂ]
        Wq)), Dp.z = D.z → Dp.z' = D.z' → (∀ h ∈ _root_.Formalism.QuantumDeterminants.UWset k r D.z, Dp.π h = D.π h) → Dp.μSS = D.μSS → Dm.z = D.z → Dm.z' = D.z' → (∀ h ∈ _root_.Formalism.QuantumDeterminants.UWset k r D.z, Dm.π h = D.π h) → Dm.μSS = D.μSS → _root_.Formalism.FourierDecayAlt.D.IsBaseFrame D ν' m₀ → _root_.GlobalTheory.WigSh.WigMap k r D.z' Dp.π' D.π' n₀ Ap' → _root_.GlobalTheory.WigSh.WigMap k r D.z' Dm.π' D.π' n₀ Am' → (∀ ω, _root_.Formalism.QuantumDeterminants.inWb k r ω → _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk
        k r) ω D.z' = 0 → ∀ v : Wq, (_root_.Formalism.QuantumDeterminants.herm
        (_root_.Formalism.QuantumDeterminants.Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 *
        n₀) * (‖ContinuousLinearMap.adjoint (Ap' ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am' ω) v‖
        ^ 2)) → ∃ (Ap : _root_.Formalism.FourierDecayAlt.Q.Mx k r → (Wqp →L[ℂ] Wq)) (Am
        : _root_.Formalism.FourierDecayAlt.Q.Mx k r → (Wqm →L[ℂ] Wq)) (ApPt
        : _root_.Formalism.FourierDecayAlt.C.LPt → (Wqp →L[ℂ] Wq)) (AmPt
        : _root_.Formalism.FourierDecayAlt.C.LPt → (Wqm →L[ℂ] Wq)), (∃ (t : ℕ) (c
        : Fin t → _root_.Formalism.FourierDecayAlt.Q.Mx k r → ℂ) (L : Fin t → (Wqp →L[ℂ]
        Wq)), (∀ i, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg (n₀ * (r + 1)) (c
        i)) ∧ ∀ g, Ap g = ∑ i, c i g • L i) ∧ (∃ (t : ℕ) (c
        : Fin t → _root_.Formalism.FourierDecayAlt.Q.Mx k r → ℂ) (L : Fin t → (Wqm →L[ℂ]
        Wq)), (∀ i, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg (n₀ * (r + 1)) (c
        i)) ∧ ∀ g, Am g = ∑ i, c i g • L i) ∧ (∀ γ, _root_.Formalism.FourierDecayAlt.D.IsLocPt γ (r
        + 1) → 0 < _root_.Formalism.FourierDecayAlt.D.ptG (_root_.Formalism.QuantumDeterminants.Tz k
        r D.z * _root_.Formalism.QuantumDeterminants.Tz k r
        D.z') r γ → ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, _root_.Formalism.QuantumDeterminants.Zhat k r D.z D.z' g = _root_.Formalism.FourierDecayAlt.D.ptMatN γ (r
        +
        1) → _root_.Formalism.FourierDecayAlt.D.IsDFrame D ν' m₀ g → ApPt γ = Ap g ∧ AmPt γ = Am g) ∧ (∀ g, Ap g = Ap' (_root_.GlobalTheory.WigSh.omg
        k r D.z D.z' g) ∧ Am g = Am' (_root_.GlobalTheory.WigSh.omg k r D.z D.z' g)) ∧ (∀ (A₀
        : ℝ) (f : _root_.Formalism.FourierDecayAlt.Q.Mx k r → (Wq →L[ℂ] Wp)), c₃ * ((r : ℝ) +
        1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) +
        1) ≤ A₀ → _root_.Formalism.FourierDecayAlt.B.InCC A₀ 1 f → (∀ γ, _root_.Formalism.FourierDecayAlt.D.IsLocPt γ (r
        + 1) → 0 < _root_.Formalism.FourierDecayAlt.D.ptG (_root_.Formalism.QuantumDeterminants.Tz k
        r D.z * _root_.Formalism.QuantumDeterminants.Tz k r
        D.z') r γ → _root_.Formalism.FourierDecayAlt.D.vecV Dp ν' m₀ (fun g => (f g).comp (Ap
        g)) γ = (_root_.Formalism.FourierDecayAlt.D.vecV D ν' m₀ f γ).comp (ApPt
        γ)) ∧ (∀ γ, _root_.Formalism.FourierDecayAlt.D.IsLocPt γ (r +
        1) → 0 < _root_.Formalism.FourierDecayAlt.D.ptG (_root_.Formalism.QuantumDeterminants.Tz k r
        D.z * _root_.Formalism.QuantumDeterminants.Tz k r
        D.z') r γ → _root_.Formalism.FourierDecayAlt.D.vecV Dm ν' m₀ (fun g => (f g).comp (Am
        g)) γ = (_root_.Formalism.FourierDecayAlt.D.vecV D ν' m₀ f γ).comp (AmPt
        γ))) ∧ (∀ γ, _root_.Formalism.FourierDecayAlt.D.IsLocPt γ (r +
        1) → 0 < _root_.Formalism.FourierDecayAlt.D.ptG (_root_.Formalism.QuantumDeterminants.Tz k r
        D.z * _root_.Formalism.QuantumDeterminants.Tz k r D.z') r γ → ∀ v : Wq, ‖v‖ ^ 2 ≤ (3 *
        b) ^ (2 * n₀) * (_root_.Formalism.QuantumDeterminants.Tz k r D.z' /
        _root_.Formalism.FourierDecayAlt.D.ptG (_root_.Formalism.QuantumDeterminants.Tz k r D.z *
        _root_.Formalism.QuantumDeterminants.Tz k r D.z') r γ) ^ n₀ * (‖ContinuousLinearMap.adjoint
        (ApPt γ) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (AmPt γ) v‖ ^
        2)) ∧ (∀ γ, _root_.Formalism.FourierDecayAlt.D.IsLocPt γ (r +
        1) → 0 < _root_.Formalism.FourierDecayAlt.D.ptG (_root_.Formalism.QuantumDeterminants.Tz k r
        D.z * _root_.Formalism.QuantumDeterminants.Tz k r
        D.z') r γ → ‖ApPt γ‖ ^ 2 ≤ (_root_.Formalism.FourierDecayAlt.D.ptG
        (_root_.Formalism.QuantumDeterminants.Tz k r D.z * _root_.Formalism.QuantumDeterminants.Tz k
        r D.z') r γ / _root_.Formalism.QuantumDeterminants.Tz k r
        D.z') ^ n₀) ∧ (∀ γ, _root_.Formalism.FourierDecayAlt.D.IsLocPt γ (r +
        1) → 0 < _root_.Formalism.FourierDecayAlt.D.ptG (_root_.Formalism.QuantumDeterminants.Tz k r
        D.z * _root_.Formalism.QuantumDeterminants.Tz k r
        D.z') r γ → ‖AmPt γ‖ ^ 2 ≤ (_root_.Formalism.FourierDecayAlt.D.ptG
        (_root_.Formalism.QuantumDeterminants.Tz k r D.z * _root_.Formalism.QuantumDeterminants.Tz k
        r D.z') r γ / _root_.Formalism.QuantumDeterminants.Tz k r D.z') ^ n₀) := by
  have hconv := _root_.Formalism.FourierDecayAlt.P.Dx3.d_orbJConv
  unfold _root_.Formalism.FourierDecayAlt.D.OrbJConv at hconv
  obtain ⟨c₃, hc₃⟩ := hconv
  have hspec := _root_.Formalism.FourierDecayAlt.P.ptG_spec
  unfold _root_.Formalism.FourierDecayAlt.D.PtGSpec at hspec
  replace hspec := And.intro hspec trivial
  have hexist := _root_.Formalism.FourierDecayAlt.P.exists_isotropic_frame
  unfold _root_.Formalism.FourierDecayAlt.D.DFrameExists at hexist
  refine ⟨c₃, ?_⟩
  intro Wp _ _ _ Wq _ _ _ Wqp _ _ _ Wqm _ _ _ k r D Dp Dm ν' m₀ n₀ b Ap' Am' hpz hpz' hpπ hpμ
    hmz hmz' hmπ hmμ hbase hAp hAm hlow
  classical
  let Rep : _root_.Formalism.FourierDecayAlt.C.LPt → _root_.Formalism.FourierDecayAlt.B.Mat k r → Prop := fun γ g =>
    g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r ∧ _root_.Formalism.QuantumDeterminants.Zhat k r D.z D.z' g = _root_.Formalism.FourierDecayAlt.D.ptMatN γ (r + 1) ∧ _root_.Formalism.FourierDecayAlt.D.IsDFrame D ν' m₀ g
  let rep : _root_.Formalism.FourierDecayAlt.C.LPt → _root_.Formalism.FourierDecayAlt.B.Mat k r := fun γ => if h : ∃ g, Rep γ g then h.choose else 1
  have rep_spec : ∀ γ, _root_.Formalism.FourierDecayAlt.D.IsLocPt γ (r + 1) →
      0 < _root_.Formalism.FourierDecayAlt.D.ptG (_root_.Formalism.QuantumDeterminants.Tz k r D.z * _root_.Formalism.QuantumDeterminants.Tz k r D.z') r γ → Rep γ (rep γ) := by
    intro γ hγ hpos
    have hex : ∃ g, Rep γ g := by
      obtain ⟨g, hg, hZ, hd⟩ := hexist k r Wp Wq D ν' m₀ γ hbase hγ hpos
      exact ⟨g, hg, hZ, hd⟩
    simp only [rep, dif_pos hex]
    exact hex.choose_spec
  have rep_eq : ∀ γ, _root_.Formalism.FourierDecayAlt.D.IsLocPt γ (r + 1) →
      0 < _root_.Formalism.FourierDecayAlt.D.ptG (_root_.Formalism.QuantumDeterminants.Tz k r D.z * _root_.Formalism.QuantumDeterminants.Tz k r D.z') r γ → ∀ g, Rep γ g →
        _root_.GlobalTheory.WigSh.omg k r D.z D.z' (rep γ) = _root_.GlobalTheory.WigSh.omg k r D.z D.z' g := by
    intro γ hγ hpos g ⟨hg, hZ, hd⟩
    obtain ⟨h₀, hZ₀, hd₀⟩ := rep_spec γ hγ hpos
    have e₀ := hspec.1 k r D.z D.z' γ (rep γ) hγ hZ₀
    have e₁ := hspec.1 k r D.z D.z' γ g hγ hZ
    exact cofactor_eq_of_frames_lemma D ν' m₀ _ _ h₀ hg hd₀ hd (hZ₀.trans hZ.symm) (e₀.symm.trans e₁)
      (e₀ ▸ hpos)
  have hApC := hAp
  unfold _root_.GlobalTheory.WigSh.WigMap at hApC
  have hAmC := hAm
  unfold _root_.GlobalTheory.WigSh.WigMap at hAmC
  refine ⟨fun g => Ap' (_root_.GlobalTheory.WigSh.omg k r D.z D.z' g),
    fun g => Am' (_root_.GlobalTheory.WigSh.omg k r D.z D.z' g),
    fun γ => Ap' (_root_.GlobalTheory.WigSh.omg k r D.z D.z' (rep γ)),
    fun γ => Am' (_root_.GlobalTheory.WigSh.omg k r D.z D.z' (rep γ)), ?_, ?_, ?_,
    fun g => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨t, c, L, hc, hL⟩ := (_root_.GlobalTheory.WigSh.wigMap_omg Wq Wqp k r D.z D.z' D.π'
      Dp.π' n₀ Ap' D.z_mem D.T_pos D.z'_mem D.T'_pos hAp).1
    exact ⟨t, c, L, hc, hL⟩
  · obtain ⟨t, c, L, hc, hL⟩ := (_root_.GlobalTheory.WigSh.wigMap_omg Wq Wqm k r D.z D.z' D.π'
      Dm.π' n₀ Am' D.z_mem D.T_pos D.z'_mem D.T'_pos hAm).1
    exact ⟨t, c, L, hc, hL⟩
  · intro γ hγ hpos g hg hZ hd
    have e := rep_eq γ hγ hpos g ⟨hg, hZ, hd⟩
    exact ⟨congrArg Ap' e, congrArg Am' e⟩
  · intro A₀ f hA₀ hf
    have haar := _root_.Formalism.FourierDecayAlt.P.radial_measure_is_haar
    unfold _root_.Formalism.FourierDecayAlt.D.MuRHaar at haar
    have hrelv := _root_.Formalism.FourierDecayAlt.P.relevant_points_holds
    unfold _root_.Formalism.FourierDecayAlt.D.PtRelevant at hrelv
    have hvi := _root_.Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep
    unfold _root_.Formalism.FourierDecayAlt.D.VecVIndep at hvi
    have side : ∀ {Wq' : Type} [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq']
        (D' : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq') (A' : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)),
        D'.z = D.z → D'.z' = D.z' → (∀ h ∈ _root_.Formalism.QuantumDeterminants.UWset k r D.z, D'.π h = D.π h) →
        D'.μSS = D.μSS → _root_.GlobalTheory.WigSh.WigMap k r D.z' D'.π' D.π' n₀ A' →
        ∀ γ, _root_.Formalism.FourierDecayAlt.D.IsLocPt γ (r + 1) → 0 < _root_.Formalism.FourierDecayAlt.D.ptG (_root_.Formalism.QuantumDeterminants.Tz k r D.z * _root_.Formalism.QuantumDeterminants.Tz k r D.z') r γ →
          _root_.Formalism.FourierDecayAlt.D.vecV D' ν' m₀ (fun g => (f g).comp (A' (_root_.GlobalTheory.WigSh.omg k r D.z D.z' g))) γ =
            (_root_.Formalism.FourierDecayAlt.D.vecV D ν' m₀ f γ).comp (A' (_root_.GlobalTheory.WigSh.omg k r D.z D.z' (rep γ))) := by
      intro Wq' _ _ D' A' hz hz' hπ hμ hA γ hγ hpos
      obtain ⟨h₀, hZ₀, hd₀⟩ := rep_spec γ hγ hpos
      have hbase' : _root_.Formalism.FourierDecayAlt.D.IsBaseFrame D' ν' m₀ := by
        unfold _root_.Formalism.FourierDecayAlt.D.IsBaseFrame at hbase ⊢; rw [hz, hz']; exact hbase
      have hd' : _root_.Formalism.FourierDecayAlt.D.IsDFrame D' ν' m₀ (rep γ) := by
        unfold _root_.Formalism.FourierDecayAlt.D.IsDFrame _root_.Formalism.FourierDecayAlt.D.cofR _root_.Formalism.FourierDecayAlt.D.cofL at hd₀ ⊢; rw [hz, hz']; exact hd₀
      have hpos' : 0 < _root_.Formalism.FourierDecayAlt.D.ptG (_root_.Formalism.QuantumDeterminants.Tz k r D'.z * _root_.Formalism.QuantumDeterminants.Tz k r D'.z') r γ := by
        rw [hz, hz']; exact hpos
      have hZ' : _root_.Formalism.QuantumDeterminants.Zhat k r D'.z D'.z' (rep γ) = _root_.Formalism.FourierDecayAlt.D.ptMatN γ (r + 1) := by
        rw [hz, hz']; exact hZ₀
      have hN : ∀ w, _root_.Formalism.FourierDecayAlt.D.muR D' (rep γ) w = _root_.Formalism.FourierDecayAlt.D.muR D (rep γ) w := by
        intro w; unfold _root_.Formalism.FourierDecayAlt.D.muR _root_.Formalism.FourierDecayAlt.D.rhoOfU; rw [hz]
      have hγ' := hγ
      unfold _root_.Formalism.FourierDecayAlt.D.IsLocPt at hγ'
      obtain ⟨hm, hne⟩ := _root_.Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' γ (r + 1) hγ'.2 hγ'.1
      have hGf := hspec.1 k r D.z D.z' γ (rep γ) hγ hZ₀
      have hrel := hrelv k r Wp Wq D γ (rep γ) hγ h₀ hZ₀
      have hrel' := hrelv k r Wp Wq' D' γ (rep γ) hγ h₀ hZ'
      have hH := haar k r Wp Wq D (rep γ) _ _ h₀ hne (hZ₀.trans hm)
      obtain ⟨θ, hθ, hθi⟩ := hc₃ k r Wp Wq D (rep γ) _ _ A₀ f h₀ hrel hne (hZ₀.trans hm)
        (by rw [← hGf]; exact hpos) hA₀ hf
      rw [hvi k r Wp Wq D ν' m₀ f γ hγ (rep γ) hbase hpos h₀ hZ₀ hd₀,
        hvi k r Wp Wq' D' ν' m₀ _ γ hγ (rep γ) hbase' hpos' h₀ hZ' hd', hN]
      exact orbital_comp_lemma_2 D D' hz hz' hπ hμ A' hA (rep γ) h₀ _ hH hrel hrel' f θ hθ hθi
    exact ⟨side Dp Ap' hpz hpz' hpπ hpμ hAp, side Dm Am' hmz hmz' hmπ hmμ hAm⟩
  · intro γ hγ hpos v
    obtain ⟨h₀, hZ₀, -⟩ := rep_spec γ hγ hpos
    have hG := hspec.1 k r D.z D.z' γ (rep γ) hγ hZ₀
    have hmem := _root_.GlobalTheory.WigSh.OmgNorm.omg_norm k r D.z D.z' (rep γ) D.z_mem D.T_pos
      D.z'_mem D.T'_pos h₀
    have hv := hlow _ hmem.1 hmem.2.1 v
    rw [hmem.2.2] at hv
    rw [hG] at hpos ⊢
    have hX : 0 < _root_.Formalism.QuantumDeterminants.Gf k r D.z D.z' (rep γ) / _root_.Formalism.QuantumDeterminants.Tz k r D.z' := div_pos hpos D.T'_pos
    have hXn := pow_pos hX n₀
    calc ‖v‖ ^ 2 = ((_root_.Formalism.QuantumDeterminants.Gf k r D.z D.z' (rep γ) / _root_.Formalism.QuantumDeterminants.Tz k r D.z') ^ n₀)⁻¹ *
          ((_root_.Formalism.QuantumDeterminants.Gf k r D.z D.z' (rep γ) / _root_.Formalism.QuantumDeterminants.Tz k r D.z') ^ n₀ * ‖v‖ ^ 2) := by
          rw [← mul_assoc, inv_mul_cancel₀ hXn.ne', one_mul]
      _ ≤ ((_root_.Formalism.QuantumDeterminants.Gf k r D.z D.z' (rep γ) / _root_.Formalism.QuantumDeterminants.Tz k r D.z') ^ n₀)⁻¹ *
          ((3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint
            (Ap' (_root_.GlobalTheory.WigSh.omg k r D.z D.z' (rep γ))) v‖ ^ 2 +
            ‖ContinuousLinearMap.adjoint
              (Am' (_root_.GlobalTheory.WigSh.omg k r D.z D.z' (rep γ))) v‖ ^ 2)) := by gcongr
      _ = _ := by rw [← inv_pow, inv_div]; ring
  · intro γ hγ hpos
    obtain ⟨h₀, hZ₀, -⟩ := rep_spec γ hγ hpos
    have hG := hspec.1 k r D.z D.z' γ (rep γ) hγ hZ₀
    have hmem := _root_.GlobalTheory.WigSh.OmgNorm.omg_norm k r D.z D.z' (rep γ) D.z_mem D.T_pos
      D.z'_mem D.T'_pos h₀
    have h := hApC.2.2.2 _ hmem.1 hmem.2.1
    rw [hmem.2.2] at h
    rw [hG]
    exact h
  · intro γ hγ hpos
    obtain ⟨h₀, hZ₀, -⟩ := rep_spec γ hγ hpos
    have hG := hspec.1 k r D.z D.z' γ (rep γ) hγ hZ₀
    have hmem := _root_.GlobalTheory.WigSh.OmgNorm.omg_norm k r D.z D.z' (rep γ) D.z_mem D.T_pos
      D.z'_mem D.T'_pos h₀
    have h := hAmC.2.2.2 _ hmem.1 hmem.2.1
    rw [hmem.2.2] at h
    rw [hG]
    exact h

end GlobalTheory.WigSh
