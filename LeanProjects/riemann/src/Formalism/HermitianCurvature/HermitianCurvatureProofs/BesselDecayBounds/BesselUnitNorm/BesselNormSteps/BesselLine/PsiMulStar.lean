import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.OpNormLeOneOfIso

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.Cv

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

theorem psi_mul_star (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mx k r) :
    psi k r z c g * star (psi k r z c g) = 1 := by
  unfold psi
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero
  simp <;> ring

theorem beF_tEq (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (σ : Mx k r → (H →L[ℂ] H)) (hG : GrpF k r z) (hσ : SigU σ) (hπ : PiU z π) (hψ : PsiF k r z c)
    (h m : Mx k r) (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) (w v : H) (p : Mt k r × Mt k r)
    (hp : Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) :
    beF z c π σ (σ (h * m) w) v p =
      (psi k r z c m • π h).comp (beF z c π σ w v (tEq h m p)) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hG
  obtain ⟨hs1, hsm, hsn⟩ := hσ
  obtain ⟨hp1, hpm, hpn⟩ := hπ
  obtain ⟨ψ1, ψ2, ψ3, ψ4⟩ := hψ
  obtain ⟨hP1, hP2⟩ := hp
  have hhU : h ∈ UH (Hpk k r) := hh.1
  have hmU : m ∈ UH (Hpk k r) := hm.1
  have hP1U : Matrix.of p.1 ∈ UH (Hpk k r) := hP1.1
  have hP2U : Matrix.of p.2 ∈ UH (Hpk k r) := hP2.1
  have hinv : h * h⁻¹ = 1 := (g2 h hhU).1
  have e1 : Matrix.of (tEq h m p).1 = Matrix.of p.1 * h := rfl
  have e2 : Matrix.of (tEq h m p).2 = h⁻¹ * Matrix.of p.2 * h * m := rfl
  have hQ : Matrix.of p.1 * h * (h⁻¹ * Matrix.of p.2 * h * m) =
      Matrix.of p.1 * Matrix.of p.2 * (h * m) := by
    calc _ = Matrix.of p.1 * (h * h⁻¹) * Matrix.of p.2 * (h * m) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hinv, Matrix.mul_one]
  have hσw : σ (Matrix.of p.1 * Matrix.of p.2) (σ (h * m) w) =
      σ (Matrix.of p.1 * Matrix.of p.2 * (h * m)) w := by
    rw [hsm _ (g1 _ hP1U _ hP2U) _ (g1 _ hhU _ hmU)]
    rfl
  have hn : h⁻¹ * Matrix.of p.2 * h ∈ Nset k r := g5 h hh _ hP2
  have hψQ : psi k r z c (h⁻¹ * Matrix.of p.2 * h * m) = psi k r z c (Matrix.of p.2) * psi k r z c m := by
    rw [ψ1 _ hn _ hm, ψ2 h hh _ hP2]
  have hπQ : (π h).comp (π (Matrix.of p.1 * h)⁻¹) = π (Matrix.of p.1)⁻¹ := by
    have hu : h⁻¹ * (Matrix.of p.1)⁻¹ ∈ UWset k r z := g7 _ (g3 h hh) _ (g3 _ hP1)
    rw [Matrix.mul_inv_rev, ← hpm h hh _ hu, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hms := psi_mul_star z c m
  unfold beF
  rw [e1, e2, hQ, hσw, hψQ, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, hπQ, smul_smul]
  congr 1
  rw [star_mul]
  first
  | linear_combination (-(⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * (h * m)) w⟫_ℂ *
      star (psi k r z c (Matrix.of p.2)))) * hms
  | linear_combination (⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * (h * m)) w⟫_ℂ *
      star (psi k r z c (Matrix.of p.2))) * hms

theorem conv_equiv (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H))
    (hG : GrpF k r z) (hσ : SigU σ) (hπ : PiU z π) (hψ : PsiF k r z c) (hM : MeasF z π μW μN)
    (hD : DecayAt μW μN σ) :
    ∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v : H,
      IsKFinHpk (k := k) (r := r) σ v →
      be z c π μW μN σ (σ (h * m) w) v = (psi k r z c m • π h).comp (be z c π μW μN σ w v) := by
  intro h hh m hm w hw v hv
  have hint := conv_int z c π μW μN σ hG hπ hM hD w hw v hv
  obtain ⟨hae, htEq, -, -⟩ := hM
  have hmp := htEq h hh m hm
  have hchg : ∫ p, beF z c π σ w v (tEq h m p) ∂(μW.prod μN) = ∫ p, beF z c π σ w v p ∂(μW.prod μN) := by
    have e := integral_map (μ := μW.prod μN) (f := beF z c π σ w v) hmp.measurable.aemeasurable
      (by rw [hmp.map_eq]; exact hint.aestronglyMeasurable)
    rw [hmp.map_eq] at e
    exact e.symm
  have hint2 : Integrable (fun p => beF z c π σ w v (tEq h m p)) (μW.prod μN) :=
    (hmp.integrable_comp hint.aestronglyMeasurable).mpr hint
  have hL := ContinuousLinearMap.integral_comp_comm
    (ContinuousLinearMap.compL ℂ Wp Wp Wp (psi k r z c m • π h)) hint2
  simp only [ContinuousLinearMap.compL_apply] at hL
  unfold be
  rw [← hchg, ← hL]
  apply integral_congr_ae
  filter_upwards [hae] with p hp
  exact beF_tEq z c π σ hG hσ hπ hψ h m hh hm w v p hp

def adjR (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] :
    (Wp →L[ℂ] Wp) →ₗᵢ[ℝ] (Wp →L[ℂ] Wp) where
  toFun T := ContinuousLinearMap.adjoint T
  map_add' S T := map_add _ S T
  map_smul' a T := by
    show ContinuousLinearMap.adjoint (a • T) = a • ContinuousLinearMap.adjoint T
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) a T,
      RCLike.real_smul_eq_coe_smul (K := ℂ) a (ContinuousLinearMap.adjoint T),
      LinearIsometryEquiv.map_smulₛₗ]
    simp
  norm_map' T := ContinuousLinearMap.adjoint.norm_map T

theorem beF_tInv (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (σ : Mx k r → (H →L[ℂ] H)) (hG : GrpF k r z) (hσ : SigU σ) (hπ : PiU z π) (hψ : PsiF k r z c)
    (w v : H) (p : Mt k r × Mt k r)
    (hp : Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) :
    beF z c π σ v w (tInv p) = ContinuousLinearMap.adjoint (beF z c π σ w v p) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hG
  obtain ⟨hs1, hsm, hsn⟩ := hσ
  obtain ⟨hp1, hpm, hpn⟩ := hπ
  obtain ⟨ψ1, ψ2, ψ3, ψ4⟩ := hψ
  obtain ⟨hP1, hP2⟩ := hp
  have hP1U : Matrix.of p.1 ∈ UH (Hpk k r) := hP1.1
  have hP2U : Matrix.of p.2 ∈ UH (Hpk k r) := hP2.1
  have hAU : Matrix.of p.1 * Matrix.of p.2 ∈ UH (Hpk k r) := g1 _ hP1U _ hP2U
  have e1 : Matrix.of (tInv p).1 = (Matrix.of p.1)⁻¹ := rfl
  have e2 : Matrix.of (tInv p).2 = Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹ := rfl
  have hQ : (Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹) =
      (Matrix.of p.1 * Matrix.of p.2)⁻¹ := by
    rw [Matrix.mul_inv_rev]
    calc _ = ((Matrix.of p.1)⁻¹ * Matrix.of p.1) * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [(g2 _ hP1U).2.1, Matrix.one_mul]
  have hψQ : psi k r z c (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹) =
      star (psi k r z c (Matrix.of p.2)) := by
    rw [ψ3 _ hP1 _ (g4 _ hP2), ψ4 _ hP2]
  have hσadj : ⟪w, σ (Matrix.of p.1 * Matrix.of p.2)⁻¹ v⟫_ℂ = ⟪σ (Matrix.of p.1 * Matrix.of p.2) w, v⟫_ℂ := by
    set A := Matrix.of p.1 * Matrix.of p.2 with hAdef
    have hAi := g2 A hAU
    let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ A : H →ₗ[ℂ] H), norm_map' := hsn A hAU }
    have hv : σ A (σ A⁻¹ v) = v := by
      rw [← ContinuousLinearMap.comp_apply, ← hsm A hAU _ hAi.2.2, hAi.1, hs1, ContinuousLinearMap.one_apply]
    calc ⟪w, σ A⁻¹ v⟫_ℂ = ⟪L w, L (σ A⁻¹ v)⟫_ℂ := (L.inner_map_map _ _).symm
      _ = ⟪σ A w, σ A (σ A⁻¹ v)⟫_ℂ := rfl
      _ = ⟪σ A w, v⟫_ℂ := by rw [hv]
  have hπadj : ContinuousLinearMap.adjoint (π (Matrix.of p.1)⁻¹) = π ((Matrix.of p.1)⁻¹)⁻¹ := by
    set A := (Matrix.of p.1)⁻¹ with hAdef
    have hA : A ∈ UWset k r z := g3 _ hP1
    have hAi : A⁻¹ ∈ UWset k r z := g3 _ hA
    have h1 : A * A⁻¹ = 1 := (g2 A hA.1).1
    let L : Wp →ₗᵢ[ℂ] Wp := { toLinearMap := (π A : Wp →ₗ[ℂ] Wp), norm_map' := hpn A hA }
    have hx : ∀ x : Wp, π A (π A⁻¹ x) = x := by
      intro x
      rw [← ContinuousLinearMap.comp_apply, ← hpm A hA _ hAi, h1, hp1, ContinuousLinearMap.one_apply]
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    calc ⟪π A⁻¹ x, y⟫_ℂ = ⟪L (π A⁻¹ x), L y⟫_ℂ := (L.inner_map_map _ _).symm
      _ = ⟪π A (π A⁻¹ x), π A y⟫_ℂ := rfl
      _ = ⟪x, π A y⟫_ℂ := by rw [hx]
  unfold beF
  rw [e1, e2, hQ, hψQ, star_star, hσadj, LinearIsometryEquiv.map_smulₛₗ, hπadj]
  congr 1
  simp only [map_mul, inner_conj_symm, Complex.star_def, Complex.conj_conj]

theorem conv_herm (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H))
    (hG : GrpF k r z) (hσ : SigU σ) (hπ : PiU z π) (hψ : PsiF k r z c) (hM : MeasF z π μW μN)
    (hD : DecayAt μW μN σ) :
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v ∈ smoothVecs (k := k) (r := r) σ,
      IsKFinHpk (k := k) (r := r) σ w → IsKFinHpk (k := k) (r := r) σ v →
      ContinuousLinearMap.adjoint (be z c π μW μN σ w v) = be z c π μW μN σ v w := by
  intro w hw v hv hwK hvK
  have hint := conv_int z c π μW μN σ hG hπ hM hD v hv w hwK
  obtain ⟨hae, -, hinvmp, -⟩ := hM
  have hchg : ∫ p, beF z c π σ v w (tInv p) ∂(μW.prod μN) = ∫ p, beF z c π σ v w p ∂(μW.prod μN) := by
    have e := integral_map (μ := μW.prod μN) (f := beF z c π σ v w) hinvmp.measurable.aemeasurable
      (by rw [hinvmp.map_eq]; exact hint.aestronglyMeasurable)
    rw [hinvmp.map_eq] at e
    exact e.symm
  have h1 : ContinuousLinearMap.adjoint (∫ p, beF z c π σ w v p ∂(μW.prod μN)) =
      ∫ p, ContinuousLinearMap.adjoint (beF z c π σ w v p) ∂(μW.prod μN) :=
    ((adjR Wp).integral_comp_comm _).symm
  unfold be
  rw [h1, ← hchg]
  apply integral_congr_ae
  filter_upwards [hae] with p hp
  exact (beF_tInv z c π σ hG hσ hπ hψ w v p hp).symm

theorem convAt_of (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H))
    (hG : GrpF k r z) (hσ : SigU σ) (hπ : PiU z π) (hψ : PsiF k r z c) (hM : MeasF z π μW μN)
    (hD : DecayAt μW μN σ) : ConvAt z c π μW μN σ := by
  exact ⟨conv_int z c π μW μN σ hG hπ hM hD, conv_cont z c π μW μN σ hG hπ hM hD,
    conv_equiv z c π μW μN σ hG hσ hπ hψ hM hD, conv_herm z c π μW μN σ hG hσ hπ hψ hM hD⟩

end PI.WBL.Cv
