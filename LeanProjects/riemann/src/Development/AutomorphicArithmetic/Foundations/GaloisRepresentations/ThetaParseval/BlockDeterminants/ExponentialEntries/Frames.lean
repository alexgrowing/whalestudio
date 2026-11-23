import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.RightSub

open scoped TensorProduct Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.RealLift UpperTheory.TP.RP

namespace UpperTheory.TP.RP.HermitianFrame

private noncomputable def io (n : ℕ) : Matrix (Fin n) (Ix n 0) ℂ :=
  Matrix.of fun i j => Sum.elim (fun k => if i = k then (1 : ℂ) else 0) (fun _ => 0) j

private theorem incM_map' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n m : Type}
    (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) : (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

private theorem jm_eq_one (n : ℕ) : Jm n 0 = 1 := by
  ext a b
  rcases a with a | a
  · rcases b with b | b
    · simp [Jm, Formalism.UG.Jpq, Matrix.one_apply]
    · exact b.elim0
  · exact a.elim0

private theorem mul_io {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m) : (g * io m) a (Sum.inl b) = g a b := by
  simp [Matrix.mul_apply, io]

private theorem io_mul {m : ℕ} {κ : Type} (Z : Matrix (Ix m 0) κ ℂ) (a : Fin m) (b : κ) : (io m * Z) a b = Z (Sum.inl a) b := by
  simp [Matrix.mul_apply, io, Fintype.sum_sum_type]

private theorem io_map_star (m : ℕ) : (io m).map star = io m := by
  ext i j
  rcases j with j | j
  · by_cases h : i = j <;> simp [io, h]
  · exact j.elim0

private theorem io_mul_tr (m : ℕ) : io m * (io m)ᵀ = 1 := by
  ext a b
  rw [io_mul]
  by_cases h : a = b <;> simp [io, h, Matrix.one_apply, eq_comm]

private theorem tr_mul_io (m : ℕ) : (io m)ᵀ * io m = 1 := by
  ext a b
  rcases a with a | a
  · rcases b with b | b
    · by_cases h : a = b
      · subst h; simp [Matrix.mul_apply, io]
      · simp [Matrix.mul_apply, io, h, Ne.symm h]
    · exact b.elim0
  · exact a.elim0

private theorem frame_io {m : ℕ} (z c : ℂ) (hc : c ≠ 0) (h : z * (c * star c) = 1) :
    IsFrame (P := m) (Q := 0) (z • (1 : Matrix (Fin m) (Fin m) ℂ)) (c • io m) := by
  refine ⟨?_, c⁻¹ • (io m)ᵀ, ?_⟩
  · have : (c • io m).map star = star c • io m := by
      ext i j
      have e := congrFun (congrFun (io_map_star m) i) j
      simp only [Matrix.map_apply] at e
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, star_mul', e]
    rw [this, jm_eq_one, Matrix.transpose_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, tr_mul_io, smul_smul]
    have e : star c * (z * c) = 1 := by rw [← h]; ring
    rw [e, one_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, io_mul_tr, smul_smul, mul_inv_cancel₀ hc, one_smul]

private theorem cartan_pos {m : ℕ} (r : ℝ) (hr : 0 < r) (θ : Matrix (Fin m) (Fin m) ℂ)
    (h : IsCartan ((r : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) θ) : θ = 1 := by
  obtain ⟨h2, -, hp⟩ := h
  have key : ∀ u : Fin m → ℂ, θ *ᵥ u = u := by
    intro u
    by_contra hne
    set v : Fin m → ℂ := u - θ *ᵥ u with hv
    have hv0 : v ≠ 0 := fun e => hne (sub_eq_zero.mp e).symm
    have hθ : θ *ᵥ v = -v := by
      rw [hv, Matrix.mulVec_sub, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, neg_sub]
    have := hp v hv0
    rw [hθ] at this
    have e : ((-v) ⬝ᵥ ((r : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ star v).re = -(r * ∑ i, Complex.normSq (v i)) := by
      simp [dotProduct, Matrix.smul_mulVec, Complex.mul_conj, Finset.mul_sum, Complex.normSq_apply]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e] at this
    have : 0 ≤ r * ∑ i, Complex.normSq (v i) := mul_nonneg hr.le (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)
    linarith
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

private theorem sig_pos {m : ℕ} (hm : 0 < m) (z : ℂ) (h : HasSig (z • (1 : Matrix (Fin m) (Fin m) ℂ)) m 0) :
    ∃ r : ℝ, 0 < r ∧ z = r := by
  obtain ⟨-, A, hA⟩ := h
  let a : Fin m := ⟨0, hm⟩
  have e := congrFun (congrFun hA (Sum.inl a)) (Sum.inl a)
  set s : ℝ := ∑ k, Complex.normSq (A k (Sum.inl a)) with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have e2 : z * (s : ℂ) = 1 := by
    have : (Aᵀ * (z • (1 : Matrix (Fin m) (Fin m) ℂ)) * A.map star) (Sum.inl a) (Sum.inl a) = z * (s : ℂ) := by
      simp [Matrix.mul_apply, hs, Finset.mul_sum, Complex.mul_conj, Matrix.smul_mul, mul_assoc]
    rw [← this, e]
    simp
  have hsne : (s : ℂ) ≠ 0 := fun h0 => by rw [h0] at e2; simp at e2
  have hsr : s ≠ 0 := fun h0 => hsne (by simp [h0])
  refine ⟨s⁻¹, inv_pos.mpr (lt_of_le_of_ne hs0 hsr.symm), ?_⟩
  push_cast
  exact eq_inv_of_mul_eq_one_left e2

private theorem key (m : ℕ) (z : ℂ) (h : HasSig (z • (1 : Matrix (Fin m) (Fin m) ℂ)) m 0) :
    ∃ c : ℂ, c ≠ 0 ∧ IsFrame (P := m) (Q := 0) (z • (1 : Matrix (Fin m) (Fin m) ℂ)) (c • io m) ∧
      ∀ θ : Matrix (Fin m) (Fin m) ℂ, IsCartan (z • (1 : Matrix (Fin m) (Fin m) ℂ)) θ → θ = 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨1, one_ne_zero, ⟨Subsingleton.elim _ _, 0, Subsingleton.elim _ _⟩, fun _ _ => Subsingleton.elim _ _⟩
  · obtain ⟨r, hr, rfl⟩ := sig_pos hm z h
    have hq : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    refine ⟨(((Real.sqrt r)⁻¹ : ℝ) : ℂ), by exact_mod_cast (inv_pos.mpr hq).ne', frame_io _ _ (by exact_mod_cast (inv_pos.mpr hq).ne') ?_,
      fun θ hθ => cartan_pos r hr θ hθ⟩
    have e : r * ((Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹) = 1 := by
      have := Real.mul_self_sqrt hr.le
      field_simp
      nlinarith
    have : (r : ℂ) * ((((Real.sqrt r)⁻¹ : ℝ) : ℂ) * star (((Real.sqrt r)⁻¹ : ℝ) : ℂ)) = ((r * ((Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹) : ℝ) : ℂ) := by
      simp
    rw [this, e]
    simp

end UpperTheory.TP.RP.HermitianFrame

open UpperTheory.TP.RP.HermitianFrame in
theorem UpperTheory.TP.RP.frames :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n)
      (W : Spc (maximalRealSubfield E) E d) (δ : E), X.IsHerm (UpperTheory.TP.cj E) B n 0 → W.IsSkew (UpperTheory.TP.cj E) B d 0 → X.J = 1 → W.J = δ • (1 : Matrix (Fin d) (Fin d) E) →
      ∃ (A : InfinitePlace (maximalRealSubfield E) → Matrix (Fin n) (Ix n 0) ℂ) (C : InfinitePlace (maximalRealSubfield E) → Matrix (Fin d) (Ix d 0) ℂ),
        Framed B.emb (incM (maximalRealSubfield E) X.J) (incM (maximalRealSubfield E) W.J) 1 Complex.I A C ∧ (∀ w, X.θ w * A w = A w * Jm n 0) ∧ (∀ w, W.θ w * C w = C w * Jm d 0) ∧
        (∀ w (g : Matrix (Fin n) (Fin n) ℂ) (Y : Mat n 0), g * A w = A w * NormedSpace.exp Y → ∀ a b, g a b = NormedSpace.exp Y (Sum.inl a) (Sum.inl b)) ∧
        ∀ w (g : Matrix (Fin d) (Fin d) ℂ) (Y : Mat d 0), g * C w = C w * NormedSpace.exp Y → ∀ a b, g a b = NormedSpace.exp Y (Sum.inl a) (Sum.inl b) := by
  intro E _ _ _ B n d X W δ hX hW hXJ hWJ
  have hM : ∀ w, X.J.map (B.emb w).1 = (1 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := fun w => by
    rw [hXJ, one_smul]
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hN : ∀ w, Complex.I • W.J.map (B.emb w).1 =
      (Complex.I * (B.emb w).1 δ) • (1 : Matrix (Fin d) (Fin d) ℂ) := fun w => by
    rw [hWJ]
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hθX : ∀ w, X.θ w = 1 := fun w => by
    have := hX.cartan w
    rw [hM w] at this
    exact cartan_pos 1 one_pos _ (by simpa using this)
  have hsig : ∀ w, HasSig ((Complex.I * (B.emb w).1 δ) • (1 : Matrix (Fin d) (Fin d) ℂ)) d 0 := fun w => by
    rw [← hN w]; exact hW.sig w
  choose c hc0 hcF hcθ using fun w => key d _ (hsig w)
  have hθW : ∀ w, W.θ w = 1 := fun w => hcθ w _ (by rw [← hN w]; exact hW.cartan w)
  refine ⟨fun _ => io n, fun w => c w • io d, ⟨one_mul _, fun w => ?_, fun w => ?_⟩, fun w => ?_, fun w => ?_, fun w g Y h a b => ?_, fun w g Y h a b => ?_⟩
  · rw [incM_map', one_smul, hM w]
    have := frame_io (m := n) 1 1 one_ne_zero (by simp)
    simpa using this
  · rw [incM_map', hN w]
    exact hcF w
  · simp only [hθX w, jm_eq_one, Matrix.one_mul, Matrix.mul_one]
  · simp only [hθW w, jm_eq_one, Matrix.one_mul, Matrix.mul_one]
  · have := congrFun (congrFun h a) (Sum.inl b)
    rwa [mul_io, io_mul] at this
  · have e := congrFun (congrFun h a) (Sum.inl b)
    rw [Matrix.mul_smul, Matrix.smul_mul] at e
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    rw [mul_io, io_mul] at e
    exact mul_left_cancel₀ (hc0 w) e
