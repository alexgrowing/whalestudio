import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Commutant
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

namespace CasimirBoundOperators

section Comm

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem comm_casimir (E : Fin n → Fin n → Module.End ℂ M) (f : Module.End ℂ M)
    (hf : ∀ a b x, f (E a b x) = E a b (f x)) (x : M) : f (casimir E x) = casimir E (f x) := by
  simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum, hf]

theorem comm_casimirK (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (f : Module.End ℂ M)
    (hf : ∀ a b x, f (E a b x) = E a b (f x)) (x : M) : f (casimirK ε E x) = casimirK ε E (f x) := by
  simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply, map_sum, hf]

end Comm

section Ops

variable {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

def uOp (Ω : Module.End ℂ M) (κ : ℝ) : Module.End ℂ M := (κ : ℂ) • LinearMap.id - Ω

def bOp (Ω : Module.End ℂ M) (κ R : ℝ) : Module.End ℂ M :=
  LinearMap.id + (((R ^ 2)⁻¹ : ℝ) : ℂ) • (uOp Ω κ * uOp Ω κ)

theorem uOp_apply (Ω : Module.End ℂ M) (κ : ℝ) (x : M) : uOp Ω κ x = (κ : ℂ) • x - Ω x := by
  simp [uOp]

theorem bOp_apply (Ω : Module.End ℂ M) (κ R : ℝ) (x : M) :
    bOp Ω κ R x = x + (((R ^ 2)⁻¹ : ℝ) : ℂ) • uOp Ω κ (uOp Ω κ x) := by
  simp [bOp]

theorem bOp_apply_real (Ω : Module.End ℂ M) (κ R : ℝ) (x : M) :
    bOp Ω κ R x = x + ((R ^ 2)⁻¹ : ℝ) • uOp Ω κ (uOp Ω κ x) := by
  rw [bOp_apply, Complex.coe_smul]

theorem re_inner_real_smul (r : ℝ) (v w : M) : (⟪(r : ℂ) • v, w⟫_ℂ).re = r * (⟪v, w⟫_ℂ).re := by
  rw [inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul]

theorem re_inner_self (x : M) : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) x)

theorem re_inner_le (x y : M) : (⟪x, y⟫_ℂ).re ≤ ‖x‖ * ‖y‖ := by
  simpa using (re_inner_le_norm (𝕜 := ℂ) x y)

theorem re_inner_comm (x y : M) : (⟪x, y⟫_ℂ).re = (⟪y, x⟫_ℂ).re := by
  rw [← inner_conj_symm, Complex.conj_re]

variable {Ω : Module.End ℂ M}

theorem uOp_symm (hΩ : ∀ x y, ⟪Ω x, y⟫_ℂ = ⟪x, Ω y⟫_ℂ) (κ : ℝ) : (uOp Ω κ).IsSymmetric := by
  intro x y
  simp only [uOp_apply, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hΩ, Complex.conj_ofReal]

theorem re_uOp (κ : ℝ) (x : M) : (⟪uOp Ω κ x, x⟫_ℂ).re = κ * ‖x‖ ^ 2 - (⟪Ω x, x⟫_ℂ).re := by
  rw [uOp_apply, inner_sub_left, Complex.sub_re, re_inner_real_smul, re_inner_self]

theorem bOp_symm (hΩ : ∀ x y, ⟪Ω x, y⟫_ℂ = ⟪x, Ω y⟫_ℂ) (κ R : ℝ) : (bOp Ω κ R).IsSymmetric := by
  intro x y
  have hu := uOp_symm hΩ κ
  simp only [bOp_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [hu (uOp Ω κ x) y, hu x (uOp Ω κ y)]

theorem bOp_re (hΩ : ∀ x y, ⟪Ω x, y⟫_ℂ = ⟪x, Ω y⟫_ℂ) (κ R : ℝ) (x : M) :
    (⟪bOp Ω κ R x, x⟫_ℂ).re = ‖x‖ ^ 2 + (R ^ 2)⁻¹ * ‖uOp Ω κ x‖ ^ 2 := by
  rw [bOp_apply, inner_add_left, Complex.add_re, re_inner_real_smul, uOp_symm hΩ κ (uOp Ω κ x) x, re_inner_self,
    re_inner_self]

theorem norm_le_bOp (hΩ : ∀ x y, ⟪Ω x, y⟫_ℂ = ⟪x, Ω y⟫_ℂ) (κ R : ℝ) (x : M) : ‖x‖ ≤ ‖bOp Ω κ R x‖ := by
  have h1 := bOp_re hΩ κ R x
  have h2 := re_inner_le (bOp Ω κ R x) x
  have h3 : 0 ≤ (R ^ 2)⁻¹ * ‖uOp Ω κ x‖ ^ 2 := by positivity
  have h4 := norm_nonneg x
  have h5 := norm_nonneg (bOp Ω κ R x)
  nlinarith

theorem comm_uOp {f : Module.End ℂ M} (hf : ∀ x, f (Ω x) = Ω (f x)) (κ : ℝ) (x : M) :
    f (uOp Ω κ x) = uOp Ω κ (f x) := by
  rw [uOp_apply, uOp_apply, map_sub, map_smul, hf]

theorem comm_bOp {f : Module.End ℂ M} (hf : ∀ x, f (Ω x) = Ω (f x)) (κ R : ℝ) (x : M) :
    f (bOp Ω κ R x) = bOp Ω κ R (f x) := by
  rw [bOp_apply, bOp_apply, map_add, map_smul, comm_uOp hf, comm_uOp hf]

end Ops

section Group

variable {n : ℕ} {ε : Fin n → Bool}

theorem left_inv {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : (Jm ε * gᴴ * Jm ε) * g = 1 := by
  have h : gᴴ * Jm ε * g = Jm ε := hg
  calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, Jm_mul_Jm]

theorem det_unit {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : IsUnit g.det :=
  Matrix.isUnit_det_of_left_inverse (left_inv hg)

theorem inv_eq {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : g⁻¹ = Jm ε * gᴴ * Jm ε :=
  Matrix.inv_eq_left_inv (left_inv hg)

theorem inv_mem' {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : g⁻¹ ∈ UJset ε := by
  have hr : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (det_unit hg)
  rw [inv_eq hg] at hr ⊢
  have h2 : g * Jm ε * gᴴ = Jm ε := by
    calc g * Jm ε * gᴴ = g * (Jm ε * gᴴ * Jm ε) * Jm ε := by
          simp only [Matrix.mul_assoc, Jm_mul_Jm, Matrix.mul_one]
      _ = Jm ε := by rw [hr, Matrix.one_mul]
  show (Jm ε * gᴴ * Jm ε)ᴴ * Jm ε * (Jm ε * gᴴ * Jm ε) = Jm ε
  have hc : (Jm ε * gᴴ * Jm ε)ᴴ = Jm ε * g * Jm ε := by
    simp only [Matrix.conjTranspose_mul, Jm_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hc]
  calc Jm ε * g * Jm ε * Jm ε * (Jm ε * gᴴ * Jm ε) = Jm ε * (g * Jm ε * gᴴ) * Jm ε := by
        simp only [Matrix.mul_assoc, Jm_mul_Jm_mul]
    _ = Jm ε := by rw [h2, Matrix.mul_assoc, Jm_mul_Jm, Matrix.mul_one]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem adj_eq (hρ : IsURepOn (UJset ε) ρ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ContinuousLinearMap.adjoint (ρ g) = ρ g⁻¹ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  have hgi := inv_mem' hg
  have h1 : ρ g (ρ g⁻¹ x) = x := by
    have h := hρ.1.2 g hg g⁻¹ hgi
    rw [Matrix.mul_nonsing_inv g (det_unit hg), hρ.1.1] at h
    have h' := congrArg (fun F : H →L[ℂ] H => F x) h
    simpa using h'.symm
  calc ⟪ρ g⁻¹ x, y⟫_ℂ = ⟪ρ g (ρ g⁻¹ x), ρ g y⟫_ℂ := (inner_map_map_of_isURep hρ hg _ _).symm
    _ = ⟪x, ρ g y⟫_ℂ := by rw [h1]

end Group

end CasimirBoundOperators

open CasimirBoundOperators in
set_option maxHeartbeats 1000000 in
theorem casimir_bound_of_inputs : SqId → Markov → PosNeg → Inv → Commutant → AdEq → CasAd → Cut := by
  intro hSq hMk hPN hInv hCom hAd hCA n ε H _ _ _ ρ hρ hDense ν κ S y hS hy hq
  have hD := isDerivedOn_smE hρ
  have hE : IsGlRep (smE ε ρ) := hD.glRep
  have hU : IsInfUnitary ε (smE ε ρ) := isInfUnitary_of_isDerivedOn hρ hD
  have hSq' := hSq n ε (smD ε ρ) (smE ε ρ) hE hU
  have hR : 0 < 2 * S := by linarith
  have hΩs : ∀ x y : smD ε ρ, ⟪casimir (smE ε ρ) x, y⟫_ℂ = ⟪x, casimir (smE ε ρ) y⟫_ℂ := fun x y => (hSq' x).2.2 y
  have hΩE : ∀ a b x, casimir (smE ε ρ) (smE ε ρ a b x) = smE ε ρ a b (casimir (smE ε ρ) x) := fun a b x => by
    have h := congrArg (fun F : Module.End ℂ (smD ε ρ) => F x) (casimir_comm hE a b)
    simpa only [Module.End.mul_apply] using h
  have hΩK : ∀ x, casimir (smE ε ρ) (casimirK ε (smE ε ρ) x) = casimirK ε (smE ε ρ) (casimir (smE ε ρ) x) :=
    comm_casimirK ε (smE ε ρ) _ hΩE
  have hBs := bOp_symm hΩs κ (2 * S)
  have hBn := norm_le_bOp hΩs κ (2 * S)
  have hadj : ∀ i : {g : Matrix (Fin n) (Fin n) ℂ // g ∈ UJset ε}, ∃ j : {g : Matrix (Fin n) (Fin n) ℂ // g ∈ UJset ε},
      ContinuousLinearMap.adjoint (ρ i.1) = ρ j.1 := fun i => ⟨⟨i.1⁻¹, inv_mem' i.2⟩, adj_eq hρ i.2⟩
  have hUp : ∀ i : {g : Matrix (Fin n) (Fin n) ℂ // g ∈ UJset ε}, ∀ x : smD ε ρ, ∃ y : smD ε ρ,
      (y : H) = ρ i.1 x ∧ (bOp (casimir (smE ε ρ)) κ (2 * S) y : H) = ρ i.1 (bOp (casimir (smE ε ρ)) κ (2 * S) x) := by
    intro i x
    obtain ⟨T', hT'1, hT'2⟩ := hAd n ε H ρ hρ i.1 i.2
    have hcas := hCA n (smD ε ρ) (smE ε ρ) i.1 (det_unit i.2)
    have key : ∀ x, T' (casimir (smE ε ρ) x) = casimir (smE ε ρ) (T' x) := fun x => by
      calc T' (casimir (smE ε ρ) x) = ∑ a, ∑ b, T' (actM (smE ε ρ) (Matrix.single a b 1)
              (actM (smE ε ρ) (Matrix.single b a 1) x)) := by
            simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum, actM_single']
        _ = ∑ a, ∑ b, actM (smE ε ρ) (i.1 * Matrix.single a b 1 * i.1⁻¹)
              (actM (smE ε ρ) (i.1 * Matrix.single b a 1 * i.1⁻¹) (T' x)) := by
            simp only [hT'2]
        _ = casimir (smE ε ρ) (T' x) := by
            rw [← hcas]; simp only [LinearMap.sum_apply, Module.End.mul_apply]
    refine ⟨T' x, hT'1 x, ?_⟩
    rw [← comm_bOp key, hT'1]
  have hCm : ∀ T : H →L[ℂ] H, (∀ i : {g : Matrix (Fin n) (Fin n) ℂ // g ∈ UJset ε}, Commute T (ρ i.1)) →
      ∀ x : smD ε ρ, ∃ y : smD ε ρ, (y : H) = T x ∧
        (bOp (casimir (smE ε ρ)) κ (2 * S) y : H) = T (bOp (casimir (smE ε ρ)) κ (2 * S) x) := by
    intro T hT x
    obtain ⟨T', hT'1, hT'2⟩ := hCom n ε H ρ hρ T fun g hg => hT ⟨g, hg⟩
    refine ⟨T' x, hT'1 x, ?_⟩
    rw [← comm_bOp (comm_casimir _ T' hT'2), hT'1]
  obtain ⟨T, hTsa, hTc, hTB⟩ := hInv H (smD ε ρ) (bOp (casimir (smE ε ρ)) κ (2 * S))
    {g : Matrix (Fin n) (Fin n) ℂ // g ∈ UJset ε} (fun i => ρ i.1) hDense hBs hBn hadj hUp hCm
  obtain ⟨T1, hT11, hT12⟩ := hCom n ε H ρ hρ T fun g hg => hTc ⟨g, hg⟩
  set a : H →L[ℂ] H := T - (((2⁻¹ : ℝ)) : ℂ) • (1 : H →L[ℂ] H) with ha_def
  have ha_apply : ∀ x, a x = T x - (((2⁻¹ : ℝ)) : ℂ) • x := fun x => by simp [ha_def]
  have ha : IsSelfAdjoint a := by
    refine hTsa.sub ?_
    show star ((((2⁻¹ : ℝ)) : ℂ) • (1 : H →L[ℂ] H)) = (((2⁻¹ : ℝ)) : ℂ) • (1 : H →L[ℂ] H)
    rw [star_smul, star_one, Complex.star_def, Complex.conj_ofReal]
  have haC : ∀ g ∈ UJset ε, Commute a (ρ g) := fun g hg =>
    (hTc ⟨g, hg⟩).sub_left ((Commute.one_left _).smul_left _)
  obtain ⟨p, m, hapm, hmp, hp0, hm0, hcomm⟩ := hPN H a ha
  have hapm' : ∀ x, a x = p x - m x := fun x => by rw [hapm]; rfl
  obtain ⟨p1, hp11, hp12⟩ := hCom n ε H ρ hρ p fun g hg => (hcomm _ (haC g hg)).1
  obtain ⟨m1, hm11, hm12⟩ := hCom n ε H ρ hρ m fun g hg => (hcomm _ (haC g hg)).2
  refine ⟨LinearMap.ker m1, fun a b v hv => ?_, ?_, ?_⟩
  · rw [LinearMap.mem_ker] at hv ⊢
    rw [hm12, hv, map_zero]
  ·
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hmw1 : m1 (bOp (casimir (smE ε ρ)) κ (2 * S) x) = 0 := by
      rw [comm_bOp (comm_casimir _ m1 hm12), hx, map_zero]
    have hmw : m ((bOp (casimir (smE ε ρ)) κ (2 * S) x : smD ε ρ) : H) = 0 := by
      rw [← hm11, hmw1]; rfl
    have hTw := hTB x
    have h1 : 0 ≤ (⟪a ((bOp (casimir (smE ε ρ)) κ (2 * S) x : smD ε ρ) : H),
        ((bOp (casimir (smE ε ρ)) κ (2 * S) x : smD ε ρ) : H)⟫_ℂ).re := by
      rw [hapm', hmw, sub_zero]; exact hp0 _
    rw [ha_apply, hTw, inner_sub_left, Complex.sub_re, re_inner_real_smul, re_inner_self] at h1
    have h3 := re_inner_le (x : H) ((bOp (casimir (smE ε ρ)) κ (2 * S) x : smD ε ρ) : H)
    have h4 := bOp_re hΩs κ (2 * S) x
    have h5 : (⟪(x : H), ((bOp (casimir (smE ε ρ)) κ (2 * S) x : smD ε ρ) : H)⟫_ℂ).re =
        (⟪bOp (casimir (smE ε ρ)) κ (2 * S) x, x⟫_ℂ).re := re_inner_comm _ _
    have h6 := re_uOp (Ω := casimir (smE ε ρ)) κ x
    have h7 := re_inner_le (uOp (casimir (smE ε ρ)) κ x) x
    set X := ‖x‖ with hX
    set W := ‖((bOp (casimir (smE ε ρ)) κ (2 * S) x : smD ε ρ) : H)‖ with hW
    set V := ‖uOp (casimir (smE ε ρ)) κ x‖ with hV
    have hX0 : 0 ≤ X := norm_nonneg _
    have hW0 : 0 ≤ W := norm_nonneg _
    have hV0 : 0 ≤ V := norm_nonneg _
    have hxX : ‖(x : H)‖ = X := rfl
    rw [hxX] at h3
    have hWX : W ≤ 2 * X := by nlinarith
    have hq2 : (2 * S) ^ 2 * ((2 * S) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    have hV2 : V ^ 2 ≤ (2 * S) ^ 2 * X ^ 2 := by
      have h8 : ((2 * S) ^ 2)⁻¹ * V ^ 2 ≤ X ^ 2 := by nlinarith
      have h9 := mul_le_mul_of_nonneg_left h8 (sq_nonneg (2 * S))
      rw [← mul_assoc, hq2, one_mul] at h9
      exact h9
    have hVX : V ≤ 2 * S * X := by
      by_contra hc
      push Not at hc
      have h0 : 0 ≤ 2 * S * X := by positivity
      have := mul_lt_mul'' hc hc h0 h0
      nlinarith
    have : (⟪uOp (casimir (smE ε ρ)) κ x, x⟫_ℂ).re ≤ 2 * S * X ^ 2 := by nlinarith
    nlinarith
  ·
    have hx0 : bOp (casimir (smE ε ρ)) κ (2 * S) (T1 y) = y := by
      apply Subtype.ext
      rw [← comm_bOp (comm_casimir _ T1 hT12), hT11, hTB]
    set Z : Submodule ℂ (smD ε ρ) := LinearMap.ker (casimirK ε (smE ε ρ) - (κ : ℂ) • LinearMap.id) with hZ
    have memZ : ∀ z, z ∈ Z ↔ casimirK ε (smE ε ρ) z = (κ : ℂ) • z := fun z => by
      rw [hZ, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    have hyc := hy.cas
    have hx0Z : T1 y ∈ Z := by
      rw [memZ, ← comm_casimirK ε _ T1 hT12, hyc, map_smul]
    have hZu : ∀ z ∈ Z, uOp (casimir (smE ε ρ)) κ z ∈ Z := fun z hz => by
      rw [memZ] at hz ⊢
      try simp only [uOp_apply]
      rw [map_sub, map_smul, hz, ← hΩK z, hz, map_smul, smul_sub]
    have hZpos : ∀ z ∈ Z, 0 ≤ (⟪uOp (casimir (smE ε ρ)) κ z, z⟫_ℂ).re := fun z hz => by
      rw [memZ] at hz
      rw [re_uOp]
      have h1 := (hSq' z).2.1
      rw [hz, re_inner_real_smul, re_inner_self] at h1
      have h2 : 0 ≤ ∑ a, ∑ b ∈ univ.filter (fun b => ε b ≠ ε a), ‖smE ε ρ a b z‖ ^ 2 :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      linarith
    have hM := hMk (smD ε ρ) (uOp (casimir (smE ε ρ)) κ) Z (2 * S) (uOp_symm hΩs κ) hR hZu hZpos (T1 y) hx0Z
    rw [← bOp_apply_real, hx0, re_uOp] at hM
    rw [inner_sub_left, Complex.sub_re, re_inner_self] at hM
    have hT1y : (⟪T1 y, y⟫_ℂ).re = (⟪T (y : H), (y : H)⟫_ℂ).re := by
      show (⟪((T1 y : smD ε ρ) : H), (y : H)⟫_ℂ).re = _
      rw [hT11]
    rw [hT1y] at hM
    have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy.ne
    have hy2 : 0 < ‖y‖ ^ 2 := by positivity
    have hbig : 3 / 4 * ‖y‖ ^ 2 ≤ (⟪T (y : H), (y : H)⟫_ℂ).re := by
      have h1 : (κ * ‖y‖ ^ 2 - (⟪casimir (smE ε ρ) y, y⟫_ℂ).re) / (2 * (2 * S)) ≤ S * ‖y‖ ^ 2 / (2 * (2 * S)) :=
        div_le_div_of_nonneg_right hq (by positivity)
      have h2 : S * ‖y‖ ^ 2 / (2 * (2 * S)) = ‖y‖ ^ 2 / 4 := by field_simp; ring
      linarith
    have hpy : p (y : H) ≠ 0 := by
      intro hpy
      have h1 := hm0 (y : H)
      have h2 : (⟪a (y : H), (y : H)⟫_ℂ).re = -(⟪m (y : H), (y : H)⟫_ℂ).re := by
        rw [hapm', hpy, zero_sub, inner_neg_left, Complex.neg_re]
      rw [ha_apply, inner_sub_left, Complex.sub_re, re_inner_real_smul, re_inner_self] at h2
      have hyH : ‖(y : H)‖ = ‖y‖ := rfl
      rw [hyH] at h2
      linarith
    have hfin := hy.fin
    obtain ⟨F, hFd, hFk, hyF⟩ := hfin
    have := hFd
    have hm : p1 y ∈ LinearMap.ker m1 := by
      rw [LinearMap.mem_ker, ← Submodule.coe_eq_zero, hm11, hp11]
      rw [← ContinuousLinearMap.mul_apply, hmp, ContinuousLinearMap.zero_apply]
    have hne : p1 y ≠ 0 := fun h => hpy (by rw [← hp11, Submodule.coe_eq_zero]; exact h)
    have hst : IsKStableSub ε (smE ε ρ) (F.map p1) := by
      intro a b hab v hv
      obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.1 hv
      rw [← hwv, ← hp12]
      exact Submodule.mem_map_of_mem (f := p1) (hFk a b hab w hw)
    have hwt : IsWt (smE ε ρ) ν (p1 y) := fun a => by
      rw [← hp12, hy.wt a, map_smul]
    have hcas' : casimirK ε (smE ε ρ) (p1 y) = (κ : ℂ) • p1 y := by
      rw [← comm_casimirK ε (smE ε ρ) p1 hp12, hyc, map_smul]
    have hfd : FiniteDimensional ℂ (F.map p1) := inferInstance
    exact ⟨p1 y, hm, ⟨hne, ⟨F.map p1, hfd, hst, Submodule.mem_map_of_mem hyF⟩, hwt, hcas'⟩⟩

end PositivityTheory.RgHe3
