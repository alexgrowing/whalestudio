import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MatrixKroneckerPowerTensorActionAlgebra

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.SiegelBound

variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : Type}

def Bdd (F : T → Matrix ι ι ℂ) : Prop := ∃ C : ℝ, ∀ t i j, ‖F t i j‖ ≤ C

omit [DecidableEq ι] in
theorem Bdd.cont {F : T → Matrix ι ι ℂ} (hF : Bdd F) {f : Matrix ι ι ℂ → ℝ} (hf : Continuous f) :
    ∃ C : ℝ, ∀ t, f (F t) ≤ C := by
  obtain ⟨C, hC⟩ := hF
  have hK : IsCompact (Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : ι => Metric.closedBall (0 : ℂ) C) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨B, hB⟩ := hK.bddAbove_image (f := f) hf.continuousOn
  refine ⟨B, fun t => hB ⟨F t, fun i _ j _ => ?_, rfl⟩⟩
  simpa using hC t i j

omit [DecidableEq ι] in
theorem Bdd.comp {F : T → Matrix ι ι ℂ} (hF : Bdd F) {f : Matrix ι ι ℂ → Matrix ι ι ℂ} (hf : Continuous f) :
    Bdd fun t => f (F t) := by
  obtain ⟨C, hC⟩ := hF.cont (f := fun y => ∑ i, ∑ j, ‖f y i j‖) (by fun_prop)
  refine ⟨C, fun t i j => le_trans ?_ (hC t)⟩
  calc ‖f (F t) i j‖ ≤ ∑ j, ‖f (F t) i j‖ :=
        Finset.single_le_sum (f := fun j => ‖f (F t) i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun i => ∑ j, ‖f (F t) i j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

omit [DecidableEq ι] in
theorem Bdd.mul {F G : T → Matrix ι ι ℂ} (hF : Bdd F) (hG : Bdd G) : Bdd fun t => F t * G t := by
  obtain ⟨C, hC⟩ := hF
  obtain ⟨D, hD⟩ := hG
  refine ⟨∑ _k : ι, C * D, fun t i j => ?_⟩
  beta_reduce
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (hC t i k) (hD t k j) (norm_nonneg _) ((norm_nonneg _).trans (hC t i k))

theorem Bdd.adj {F : T → Matrix ι ι ℂ} (hF : Bdd F) : Bdd fun t => (F t).adjugate :=
  hF.comp (f := fun y => y.adjugate) (continuous_id.matrix_adjugate)

omit [DecidableEq ι] in
theorem Bdd.ct {F : T → Matrix ι ι ℂ} (hF : Bdd F) : Bdd fun t => (F t)ᴴ :=
  hF.comp (f := fun y => yᴴ) (continuous_id.matrix_conjTranspose)

theorem bdd_unitary {F : T → Matrix ι ι ℂ} (hF : ∀ t, (F t)ᴴ * F t = 1) : Bdd F :=
  ⟨1, fun t i j => entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 (hF t)) i j⟩

theorem Bdd.nsq_act {m : ℕ} (d : Fin m → ℕ) (v : TIdx ι d → ℂ) {F : T → Matrix ι ι ℂ} (hF : Bdd F) :
    ∃ C : ℝ, ∀ t, nsq (act d v (F t)) ≤ C := by
  refine hF.cont (f := fun y => nsq (act d v y)) ?_
  simp only [nsq, act, tpow, vecMul, dotProduct, of_apply]
  fun_prop

theorem sq_le_nsq {κ : Type} [Fintype κ] (v : κ → ℂ) (k : κ) : ‖v k‖ ^ 2 ≤ nsq v :=
  Finset.single_le_sum (f := fun k => ‖v k‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)

theorem core {m : ℕ} (d : Fin m → ℕ) (v : TIdx ι d → ℂ)
    (h1 : ∀ C : ℝ, ∃ C' : ℝ, ∀ y : Matrix ι ι ℂ, y.det = 1 → nsq (act d v y) ≤ C →
      ∃ h : Matrix ι ι ℂ, h.det = 1 ∧ act d v h = v ∧ ∀ i j, ‖(h * y) i j‖ ≤ C')
    (h2 : ∀ g : Matrix ι ι ℂ, g.det = 1 → act d v g = v → act d v gᴴ = v)
    (c : ℝ) (hc : 0 < c) (K N D : T → Matrix ι ι ℂ) (e : T → ι → ℂ)
    (hK : ∀ t, (K t)ᴴ * K t = 1) (hKd : ∀ t, (K t).det = 1) (hNd : ∀ t, (N t).det = 1)
    (hDd : ∀ t, (D t).det = 1) (hDh : ∀ t, (D t)ᴴ = D t) (hDe : ∀ t, D t * diagonal (e t) = 1)
    (hN : Bdd N) (hN1 : Bdd fun t => D t * N t * diagonal (e t))
    (hN2 : Bdd fun t => D t * (D t * N t * diagonal (e t)) * diagonal (e t))
    (hw : ∀ t j, act d v (K t * D t * N t) j = 0 ∨ c ≤ ‖act d v (K t * D t * N t) j‖) :
    ∃ C' : ℝ, ∀ t, nsq (act d v (K t * D t * N t)) ≤ C' := by
  have amul : ∀ (u : TIdx ι d → ℂ) (y z : Matrix ι ι ℂ), act d u (y * z) = act d (act d u y) z :=
    fun u => ((GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d u).2.1
  have adiag : ∀ (u : TIdx ι d → ℂ) (a : ι → ℂ) (k : TIdx ι d),
      act d u (diagonal a) k = u k * ∏ j, a (k.2 j) := fun u => ((GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d u).2.2.1
  have aone : act d v 1 = v := ((GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d v).1
  have heD : ∀ t, diagonal (e t) * D t = 1 := fun t => mul_eq_one_comm.1 (hDe t)
  have hKK : ∀ t, K t * (K t)ᴴ = 1 := fun t => mul_eq_one_comm.1 (hK t)
  have hed : ∀ t, (diagonal (e t)).det = 1 := fun t => by
    have := congrArg Matrix.det (hDe t)
    rwa [det_mul, hDd, one_mul, det_one] at this
  obtain ⟨C₁, hC₁⟩ := ((bdd_unitary hK).mul hN1).nsq_act d v
  have hz : ∀ t, nsq (act d v (K t * D t * N t * diagonal (e t) * diagonal (e t))) ≤
      ∑ _j : TIdx ι d, (C₁ / c) ^ 2 := by
    intro t
    refine Finset.sum_le_sum fun j _ => ?_
    have h3 := (sq_le_nsq _ j).trans (hC₁ t)
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, amul, adiag] at h3
    rw [amul, adiag, amul, adiag]
    rcases hw t j with h0 | h0
    · rw [h0]; simp; positivity
    · rw [norm_mul] at h3
      rw [norm_mul, norm_mul]
      set W := ‖act d v (K t * D t * N t) j‖
      set X := ‖∏ l, e t (j.2 l)‖
      have hX : 0 ≤ X := norm_nonneg _
      have hW : 0 ≤ W := norm_nonneg _
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      rw [le_div_iff₀ hc]
      calc W * X * X * c ≤ W * X * X * W := by gcongr
        _ = (W * X) ^ 2 := by ring
        _ ≤ C₁ := h3
  obtain ⟨C₂, hC₂⟩ := h1 (∑ _j : TIdx ι d, (C₁ / c) ^ 2)
  have hex := fun t => hC₂ _ (by simp only [det_mul, hKd, hDd, hNd, hed, mul_one]) (hz t)
  choose h hd hv hb using hex
  have hb' : Bdd fun t => h t * (K t * D t * N t * diagonal (e t) * diagonal (e t)) := ⟨C₂, hb⟩
  have hω := hb'.mul hN2.adj
  have eω : ∀ t, h t * (K t * D t * N t * diagonal (e t) * diagonal (e t)) *
      (D t * (D t * N t * diagonal (e t)) * diagonal (e t)).adjugate = h t * K t * diagonal (e t) := by
    intro t
    have e1 : K t * D t * N t * diagonal (e t) * diagonal (e t) =
        K t * diagonal (e t) * (D t * (D t * N t * diagonal (e t)) * diagonal (e t)) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (diagonal (e t)) (D t), heD, Matrix.one_mul]
    rw [e1, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (adjugate _), mul_adjugate]
    simp only [det_mul, hDd, hNd, hed, mul_one, one_smul, Matrix.mul_assoc]
  simp only [eω] at hω
  have hh : ∀ t, h t * (h t).adjugate = 1 := fun t => by rw [mul_adjugate, hd, one_smul]
  have eadj : ∀ t, (h t * K t * diagonal (e t)).adjugate = D t * (K t)ᴴ * (h t).adjugate := by
    intro t
    have l : (h t * K t * diagonal (e t)).adjugate * (h t * K t * diagonal (e t)) = 1 := by
      rw [adjugate_mul]; simp only [det_mul, hd, hKd, hed, mul_one, one_smul]
    have r : (h t * K t * diagonal (e t)) * (D t * (K t)ᴴ * (h t).adjugate) = 1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (diagonal (e t)) (D t), heD, Matrix.one_mul, ← Matrix.mul_assoc (K t), hKK,
        Matrix.one_mul, hh]
    exact left_inv_eq_right_inv l r
  obtain ⟨C₃, hC₃⟩ := (hω.adj.ct.mul hN).nsq_act d v
  refine ⟨C₃, fun t => ?_⟩
  have hfix : act d v ((h t).adjugate)ᴴ = v := by
    refine h2 _ (by rw [det_adjugate, hd, one_pow]) ?_
    conv_lhs => rw [← hv t]
    rw [← amul, hh, aone]
  have := hC₃ t
  rw [eadj, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hDh, Matrix.mul_assoc,
    amul, hfix] at this
  exact this

theorem borel_harishChandra : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [LinearOrder ι] (m : ℕ) (d : Fin m → ℕ) (v : TIdx ι d → ℂ), (∀ C : ℝ, ∃ C' : ℝ, ∀ y : Matrix ι ι ℂ, y.det = 1 → nsq (act d v y) ≤ C → ∃ h : Matrix ι ι ℂ, h.det = 1 ∧ act d v h = v ∧ ∀ i j, ‖(h * y) i j‖ ≤ C') → (∀ g : Matrix ι ι ℂ, g.det = 1 → act d v g = v → act d v gᴴ = v) → ∀ C c : ℝ, 0 < c → ∃ C' : ℝ, ∀ (k : Matrix ι ι ℝ) (a : ι → ℝ) (n : Matrix ι ι ℝ), IsSiegel C k a n → (∀ j, act d v ((k * diagonal a * n).map (fun r : ℝ => (r : ℂ))) j = 0 ∨ c ≤ ‖act d v ((k * diagonal a * n).map (fun r : ℝ => (r : ℂ))) j‖) → nsq (act d v ((k * diagonal a * n).map (fun r : ℝ => (r : ℂ)))) ≤ C' := by
  intro ι _ _ _ m d v h1 h2 C c hc
  let φ : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix
  have hφ : ∀ y : Matrix ι ι ℝ, y.map (fun r : ℝ => (r : ℂ)) = φ y := fun _ => rfl
  have hφa : ∀ (y : Matrix ι ι ℝ) i j, φ y i j = (y i j : ℂ) := fun _ _ _ => rfl
  have hφd : ∀ y : Matrix ι ι ℝ, y.det = 1 → (φ y).det = 1 := fun y hy => by
    rw [← RingHom.map_det, hy, map_one]
  have hφh : ∀ y : Matrix ι ι ℝ, (φ y)ᴴ = φ yᵀ := fun y => by
    ext i j; simp [hφa]
  have hφdiag : ∀ a : ι → ℝ, φ (diagonal a) = diagonal fun i => (a i : ℂ) := fun a => by
    ext i j; by_cases hij : i = j <;> simp [hφa, diagonal_apply, hij]
  simp only [hφ, map_mul]
  let S := {p : Matrix ι ι ℝ × (ι → ℝ) × Matrix ι ι ℝ // IsSiegel C p.1 p.2.1 p.2.2 ∧
    ∀ j, act d v (φ p.1 * φ (diagonal p.2.1) * φ p.2.2) j = 0 ∨
      c ≤ ‖act d v (φ p.1 * φ (diagonal p.2.1) * φ p.2.2) j‖}
  have ratio : ∀ t : S, ∀ i j, t.1.2.2 i j = 0 ∨ t.1.2.1 i * (t.1.2.1 j)⁻¹ ≤ max 1 C := by
    intro t i j
    have hs := t.2.1
    rcases lt_trichotomy i j with h | h | h
    · right
      rw [← div_eq_mul_inv, div_le_iff₀ (hs.pos j)]
      exact (hs.le i j h).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hs.pos j).le)
    · right; subst h; rw [mul_inv_cancel₀ (hs.pos i).ne']; exact le_max_left _ _
    · left; exact hs.lower i j h
  have nrm : ∀ t : S, ∀ i, ‖(t.1.2.1 i : ℂ)‖ = t.1.2.1 i := fun t i => by
    rw [Complex.norm_real, Real.norm_of_nonneg (t.2.1.pos i).le]
  obtain ⟨C', hC'⟩ := core (T := S) d v h1 h2 c hc (fun t => φ t.1.1) (fun t => φ t.1.2.2)
    (fun t => φ (diagonal t.1.2.1)) (fun t i => ((t.1.2.1 i : ℂ))⁻¹)
    (fun t => by rw [hφh, ← map_mul, t.2.1.orth, map_one])
    (fun t => hφd _ t.2.1.det_k)
    (fun t => hφd _ (by
      rw [det_of_upperTriangular (fun i j h => t.2.1.lower i j h)]
      simp [t.2.1.diag]))
    (fun t => hφd _ (by rw [det_diagonal, t.2.1.prod_eq]))
    (fun t => by rw [hφh, diagonal_transpose])
    (fun t => by
      rw [hφdiag, diagonal_mul_diagonal, ← diagonal_one]
      congr 1; funext i
      exact mul_inv_cancel₀ (by exact_mod_cast (t.2.1.pos i).ne'))
    ⟨C, fun t i j => by beta_reduce; rw [hφa, Complex.norm_real]; exact t.2.1.bdd i j⟩
    ⟨max 1 C * max 1 C, fun t i j => by
      simp only [hφdiag, mul_diagonal, diagonal_mul, hφa, norm_mul, norm_inv, nrm]
      rcases ratio t i j with h | h
      · rw [h]; simp
      · have hp := (t.2.1.pos i).le
        have hq := (t.2.1.pos j).le
        have hn : ‖(t.1.2.2 i j : ℂ)‖ ≤ max 1 C := by
          rw [Complex.norm_real]; exact (t.2.1.bdd i j).trans (le_max_right _ _)
        calc _ = (t.1.2.1 i * (t.1.2.1 j)⁻¹) * ‖(t.1.2.2 i j : ℂ)‖ := by ring
          _ ≤ _ := by gcongr⟩
    ⟨max 1 C * max 1 C * max 1 C, fun t i j => by
      simp only [hφdiag, mul_diagonal, diagonal_mul, hφa, norm_mul, norm_inv, nrm]
      rcases ratio t i j with h | h
      · rw [h]; simp
      · have hp := (t.2.1.pos i).le
        have hq := (t.2.1.pos j).le
        have hn : ‖(t.1.2.2 i j : ℂ)‖ ≤ max 1 C := by
          rw [Complex.norm_real]; exact (t.2.1.bdd i j).trans (le_max_right _ _)
        calc _ = (t.1.2.1 i * (t.1.2.1 j)⁻¹) * (t.1.2.1 i * (t.1.2.1 j)⁻¹) * ‖(t.1.2.2 i j : ℂ)‖ := by ring
          _ ≤ _ := by gcongr⟩
    (fun t => t.2.2)
  exact ⟨C', fun k a n hs hw => hC' ⟨(k, a, n), hs, hw⟩⟩

end GlobalTheory.ClassFin.SiegelBound
