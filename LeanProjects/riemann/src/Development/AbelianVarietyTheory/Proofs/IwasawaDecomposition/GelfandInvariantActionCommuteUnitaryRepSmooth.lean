import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivedActionSmoothVectorRealLinearStatement

open Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmVec Matrix

noncomputable section
namespace GlobalTheory.SmVecGelfComm

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def RealLin (G : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H) : Prop :=
  (∀ X ∈ lieG G, ∀ Y ∈ lieG G, dRep π (X + Y) w = dRep π X w + dRep π Y w) ∧
    ∀ (a : ℝ), ∀ X ∈ lieG G, dRep π (a • X) w = (a : ℂ) • dRep π X w

theorem lie_smul (a : ℝ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) : a • X ∈ lieG G := by
  have h : Xᴴ * G + G * X = 0 := hX
  show _ + _ = 0
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, star_trivial, ← smul_add, h, smul_zero]

theorem conjG_add (Z W : Matrix (Fin n) (Fin n) ℂ) : conjG G (Z + W) = conjG G Z + conjG G W := by
  simp only [conjG, conjTranspose_add, Matrix.mul_add, Matrix.add_mul, neg_add]

theorem conjG_smul (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) : conjG G (c • Z) = star c • conjG G Z := by
  simp only [conjG, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem dRepC_add_left (hG : IsUnit G) (hh : Gᴴ = G) {w : H} (hl : RealLin G π w) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    dRepC G π (Z + W) w = dRepC G π Z w + dRepC G π W w := by
  have e1 : (1 / 2 : ℂ) • (Z + W + conjG G (Z + W)) =
      (1 / 2 : ℂ) • (Z + conjG G Z) + (1 / 2 : ℂ) • (W + conjG G W) := by rw [conjG_add]; module
  have e2 : (1 / (2 * Complex.I)) • (Z + W - conjG G (Z + W)) =
      (1 / (2 * Complex.I)) • (Z - conjG G Z) + (1 / (2 * Complex.I)) • (W - conjG G W) := by
    rw [conjG_add]; module
  unfold dRepC
  rw [e1, e2, hl.1 _ (parts_mem hG hh Z).1 _ (parts_mem hG hh W).1,
    hl.1 _ (parts_mem hG hh Z).2 _ (parts_mem hG hh W).2]
  module

theorem dRepC_smul_left (hG : IsUnit G) (hh : Gᴴ = G) {w : H} (hl : RealLin G π w) (c : ℂ)
    (Z : Matrix (Fin n) (Fin n) ℂ) : dRepC G π (c • Z) w = c • dRepC G π Z w := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℝ, c = a + b * Complex.I := ⟨c.re, c.im, (Complex.re_add_im c).symm⟩
  have hs : star ((a : ℂ) + b * Complex.I) = a - b * Complex.I := by simp [sub_eq_add_neg]
  have hi : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
    field_simp
    simp
  have hI := Complex.I_mul_I
  obtain ⟨h1, h2⟩ := parts_mem hG hh Z
  have e1 : (1 / 2 : ℂ) • (((a : ℂ) + b * Complex.I) • Z + conjG G (((a : ℂ) + b * Complex.I) • Z)) =
      a • (1 / 2 : ℂ) • (Z + conjG G Z) + (-b) • (1 / (2 * Complex.I)) • (Z - conjG G Z) := by
    rw [conjG_smul, hs, hi, ← Complex.coe_smul, ← Complex.coe_smul]
    push_cast
    module
  have e2 : (1 / (2 * Complex.I)) • (((a : ℂ) + b * Complex.I) • Z - conjG G (((a : ℂ) + b * Complex.I) • Z)) =
      b • (1 / 2 : ℂ) • (Z + conjG G Z) + a • (1 / (2 * Complex.I)) • (Z - conjG G Z) := by
    rw [conjG_smul, hs, hi, ← Complex.coe_smul, ← Complex.coe_smul]
    match_scalars
    · linear_combination (-(b : ℂ) / 2) * hI
    · linear_combination (-(b : ℂ) / 2) * hI
  unfold dRepC
  rw [e1, e2, hl.1 _ (lie_smul _ h1) _ (lie_smul _ h2), hl.1 _ (lie_smul _ h1) _ (lie_smul _ h2),
    hl.2 _ _ h1, hl.2 _ _ h1, hl.2 _ _ h2, hl.2 _ _ h2]
  push_cast
  match_scalars
  · ring
  · linear_combination (-(b : ℂ)) * hI

def dLin (hG : IsUnit G) (hh : Gᴴ = G) {w : H} (hl : RealLin G π w) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] H where
  toFun Z := dRepC G π Z w
  map_add' := dRepC_add_left hG hh hl
  map_smul' := dRepC_smul_left hG hh hl

theorem dRepC_eq_sum (hG : IsUnit G) (hh : Gᴴ = G) {w : H} (hl : RealLin G π w) (Z : Matrix (Fin n) (Fin n) ℂ) :
    dRepC G π Z w = ∑ c, ∑ d, Z c d • dRepC G π (Matrix.single c d 1) w := by
  have e : Z = ∑ c, ∑ d, Z c d • Matrix.single c d (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    simp
  show dLin hG hh hl Z = _
  conv_lhs => rw [e]
  simp only [map_sum, map_smul]
  rfl

theorem conjG_conj (hG : IsUnit G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    (Z : Matrix (Fin n) (Fin n) ℂ) : conjG G (g⁻¹ * Z * g) = g⁻¹ * conjG G Z * g := by
  have h : gᴴ * G * g = G := hg
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 (isUnit_of_mem_UH hG hg)
  have hD := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have h1 : G * g⁻¹ = gᴴ * G := by
    conv_lhs => rw [← h]
    rw [Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]
  have h2 : (g⁻¹)ᴴ * G = G * g := by
    conv_lhs => rw [← h]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hd]; simp
  have h3 : G⁻¹ * gᴴ = g⁻¹ * G⁻¹ := by
    calc G⁻¹ * gᴴ = G⁻¹ * (gᴴ * G) * G⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hD, Matrix.mul_one]
      _ = _ := by rw [← h1, ← Matrix.mul_assoc, nonsing_inv_mul _ hD, Matrix.one_mul]
  calc conjG G (g⁻¹ * Z * g) = -((G⁻¹ * gᴴ) * Zᴴ * ((g⁻¹)ᴴ * G)) := by
        simp only [conjG, conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h3, h2]; simp only [conjG, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]

theorem dRepC_rep (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {w : H} (hw : w ∈ smSub G π)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) (Z : Matrix (Fin n) (Fin n) ℂ) :
    dRepC G π Z (π g w) = π g (dRepC G π (g⁻¹ * Z * g) w) := by
  unfold dRepC
  rw [dRep_rep hG hπ hw hg (parts_mem hG hh Z).1, dRep_rep hG hπ hw hg (parts_mem hG hh Z).2, conjG_conj hG hg,
    map_add, map_smul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]

def dEnd (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Module.End ℂ (smSub G π) where
  toFun w := ⟨dRepC G π Z w, dRepC_mem hG hh hπ Z w.2⟩
  map_add' v w := Subtype.ext <| by
    show dRepC G π Z (v + w) = dRepC G π Z v + dRepC G π Z w
    unfold dRepC
    rw [dRep_add v.2 w.2 (parts_mem hG hh Z).1, dRep_add v.2 w.2 (parts_mem hG hh Z).2]
    module
  map_smul' c w := Subtype.ext <| by
    show dRepC G π Z (c • w) = c • dRepC G π Z w
    unfold dRepC
    rw [dRep_smul c w.2 (parts_mem hG hh Z).1, dRep_smul c w.2 (parts_mem hG hh Z).2]
    module

def gEnd (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) : Module.End ℂ (smSub G π) :=
  (π g : H →ₗ[ℂ] H).restrict fun _ hw => rep_mem hG hπ hw hg

theorem gEnd_coe (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) (w : smSub G π) : ((gEnd hG hπ hg w : smSub G π) : H) = π g w := rfl

theorem foldr_dEnd (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (w : smSub G π) :
    (((l.map (dEnd hG hh hπ)).prod w : smSub G π) : H) = (l.map (dRepC G π)).foldr (fun f acc => f acc) (w : H) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.map_cons, List.foldr_cons, ← ih]
    rfl

theorem gelfH_eq (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) (k : ℕ) (w : smSub G π) :
    gelfH G π k w =
      ((∑ c, (Matrix.of (fun a b => dEnd hG hh hπ (Matrix.single a b 1)) ^ (k + 1)) c c) w : smSub G π) := by
  rw [← GlobalTheory.SmoothForms.gelfA_eq_sum_pow, GlobalTheory.SmoothForms.gelfA, LinearMap.sum_apply, Submodule.coe_sum, gelfH]
  refine Finset.sum_congr rfl fun idx _ => ?_
  have := foldr_dEnd hG hh hπ (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) w
  rw [List.map_ofFn, List.map_ofFn] at this
  exact this.symm

theorem gelfH_rep_of (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π)
    (hl : ∀ w ∈ smSub G π, RealLin G π w) (k : ℕ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    {w : H} (hw : w ∈ smSub G π) : gelfH G π k (π g w) = π g (gelfH G π k w) := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 (isUnit_of_mem_UH hG hg)
  have hQP : gᵀ * (g⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, nonsing_inv_mul _ hd, Matrix.transpose_one]
  have h := GlobalTheory.Dec.GelfAd.trace_pow_comm (fun a b => dEnd hG hh hπ (Matrix.single a b 1)) (gEnd hG hπ hg) _ _ hQP
    (fun a b => by
      refine LinearMap.ext fun v => Subtype.ext ?_
      rw [Module.End.mul_apply, Module.End.mul_apply]
      refine (dRepC_rep hG hh hπ v.2 hg _).trans ?_
      rw [gEnd_coe]
      congr 1
      rw [dRepC_eq_sum hG hh (hl v v.2)]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      congr 1
      simp [Matrix.mul_apply, Matrix.single, ite_and]) (k + 1)
  have h2 := congrArg (fun T : Module.End ℂ (smSub G π) => ((T ⟨w, hw⟩ : smSub G π) : H)) h
  simp only [Module.End.mul_apply] at h2
  rw [← gelfH_eq] at h2
  refine h2.trans ?_
  rw [gEnd_coe, ← gelfH_eq]

theorem gelfH_rep : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P →
    Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (k : ℕ), ∀ g ∈ Formalism.QuantumDeterminants.UH G,
    ∀ w ∈ smSub G (trRep σ P),
    gelfH G (trRep σ P) k ((trRep σ P) g w) = (trRep σ P) g (gelfH G (trRep σ P) k w) :=
  fun n ε H _ _ _ σ P G hP h hσ k _ hg _ hw =>
    gelfH_rep_of (gram_unit hP h) (gram_herm h) (isURepOn_trRep hP h hσ) (GlobalTheory.T.derived_action_smooth_vector_real_linear n ε H σ P G hP h hσ) k hg hw

end GlobalTheory.SmVecGelfComm
