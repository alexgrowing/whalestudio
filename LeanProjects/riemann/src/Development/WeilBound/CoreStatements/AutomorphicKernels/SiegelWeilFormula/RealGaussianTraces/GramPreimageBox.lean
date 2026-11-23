import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.TraceReOfHerm

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tr4 {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℂ) : (B * (C * D * A)).trace = (A * B * C * D).trace := by
  rw [show A * B * C * D = A * (B * C * D) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm A]
  simp only [Matrix.mul_assoc]

theorem gl_mul_inv {n : ℕ} (g : GL (Fin n) ℂ) : g.1 * (g⁻¹).1 = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem gl_inv_mul {n : ℕ} (g : GL (Fin n) ℂ) : (g⁻¹).1 * g.1 = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem gl_conj_cancel {n : ℕ} (g : GL (Fin n) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) :
    (g.1)ᴴ * ((((g⁻¹).1)ᴴ * Q * (g⁻¹).1)) * g.1 = Q := by
  have h1 : (g.1)ᴴ * ((g⁻¹).1)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, gl_inv_mul, Matrix.conjTranspose_one]
  simp only [← Matrix.mul_assoc]
  rw [h1, Matrix.one_mul, Matrix.mul_assoc, gl_inv_mul, Matrix.mul_one]

theorem re_sum_cast {n : ℕ} (x y : WR.E n) :
    ((((∑ a, ∑ b, ((x a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ)) : ℂ).re : ℝ) : ℂ) =
      ∑ a, ∑ b, ((x a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ) := by
  have : (∑ a, ∑ b, ((x a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ)) = ((∑ a, ∑ b, x a b * y a b : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.ofReal_re]

theorem gram_mem (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (ε : ι → Fin M → Bool) (fr : ι → GL (Fin M) ℂ) (hfr : IsFrames J θ ε fr) (g : ι → GL (Fin n) ℂ)
    (Y : Fin n → Fin M → Ainf F ⊗[F] E) : gramR (Ainf F) σ J Y ∈ HermR (Ainf F) σ n := by
  intro a b
  apply hP.bij.injective
  funext i
  show θ i (sigR _ σ (gramR (Ainf F) σ J Y b a)) = θ i (gramR (Ainf F) σ J Y a b)
  rw [hP.conj]
  have h := map_gramR_crd σ ψ θ l hP J ε fr hfr g Y i
  have hh : ((gramR (Ainf F) σ J Y).map (θ i)).IsHermitian := by
    rw [h]; exact Matrix.isHermitian_conjTranspose_mul_mul _ (gramX_isHerm _ _)
  have := congrFun (congrFun hh a) b
  simpa [Matrix.conjTranspose_apply] using this

theorem phi_mul_psi (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (ε : ι → Fin M → Bool) (fr : ι → GL (Fin M) ℂ) (hfr : IsFrames J θ ε fr) (g : ι → GL (Fin n) ℂ) (P : ι → PX M n)
    (b : HermR (Ainf F) σ n) (Y : Fin n → Fin M → Ainf F ⊗[F] E) :
    phiInf θ l fr g P Y * psiInf F ψ (trPair (Ainf F) (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (gramR (Ainf F) σ J Y)) =
      ∏ i, (evX (P i) (crdAll θ fr g Y i) * gs (2 * Real.pi * |l i|) (crdAll θ fr g Y i) *
        Complex.exp (Complex.I * ((2 * Real.pi * l i : ℝ) : ℂ) *
          (herm (ybAll σ θ g b i) * gramX (ε i) (crdAll θ fr g Y i)).trace)) := by
  rw [psi_trPair_gen σ hCM ψ θ l hP, Finset.mul_sum, Complex.exp_sum]
  unfold phiInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have htr : ((((b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (gramR (Ainf F) σ J Y).map (θ i)).trace.re : ℝ) : ℂ) =
      (herm (ybAll σ θ g b i) * gramX (ε i) (crdAll θ fr g Y i)).trace := by
    rw [map_gramR_crd σ ψ θ l hP J ε fr hfr g Y i, tr4, ← herm_ybAll σ ψ θ l hP g b i]
    exact trace_re_of_herm (WR.I.herm_isHermitian _) (gramX_isHerm _ _)
  rw [htr]
  congr 2
  push_cast
  ring

theorem psi_neg_trPair (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (g : ι → GL (Fin n) ℂ)
    (T b : HermR (Ainf F) σ n) :
    psiInf F ψ (-trPair (Ainf F) (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))) =
      ∏ i, WR.chr (2 * Real.pi * l i) (ygAll σ θ g T i) (ybAll σ θ g b i) := by
  rw [psi_neg_trPair_gen σ hCM ψ θ l hP, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : (herm (ygAll σ θ g T i) * herm (ybAll σ θ g b i)).trace =
      ((T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i)).trace := by
    rw [herm_ygAll σ ψ θ l hP g T i, herm_ybAll σ ψ θ l hP g b i]
    have h1 : (((g i)⁻¹).1)ᴴ * ((g i).1)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, gl_mul_inv, Matrix.conjTranspose_one]
    calc (((g i).1)ᴴ * (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (g i).1 *
          (((g i)⁻¹).1 * (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (((g i)⁻¹).1)ᴴ)).trace
        = (((g i).1)ᴴ * ((T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) *
            (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (((g i)⁻¹).1)ᴴ)).trace := by
          congr 1
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (g i).1, gl_mul_inv, Matrix.one_mul]
      _ = ((T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) *
            (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * ((((g i)⁻¹).1)ᴴ * ((g i).1)ᴴ)).trace := by
          rw [Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]
  rw [← e, trace_herm_mul, re_sum_cast, WR.chr]
  congr 1
  push_cast
  ring

theorem nuInf_eq (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (g : ι → GL (Fin n) ℂ)
    (b : HermR (Ainf F) σ n) :
    nuInf θ g (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = ∏ i, WR.dP (ybAll σ θ g b i) := by
  unfold nuInf
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [WR.dP, herm_ybAll σ ψ θ l hP g b i]

theorem gram_preimage_box (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (ε : ι → Fin M → Bool) (fr : ι → GL (Fin M) ℂ) (hfr : IsFrames J θ ε fr)
    (g : ι → GL (Fin n) ℂ) (K : ι → Set (WR.E n)) :
    gramR (Ainf F) σ J ⁻¹' (Subtype.val '' (ygAll σ θ g ⁻¹' Set.univ.pi K)) =
      crdAll θ fr g ⁻¹' Set.univ.pi (fun i => gramX (ε i) ⁻¹' (herm '' K i)) := by
  ext Y
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_univ_pi]
  constructor
  · rintro ⟨s, hs, hsY⟩ i
    refine ⟨ygAll σ θ g s i, hs i, ?_⟩
    rw [herm_ygAll σ ψ θ l hP g s i, hsY, map_gramR_crd σ ψ θ l hP J ε fr hfr g Y i, gl_conj_cancel]
  · intro h
    refine ⟨⟨gramR (Ainf F) σ J Y, gram_mem σ ψ θ l hP J ε fr hfr g Y⟩, fun i => ?_, rfl⟩
    obtain ⟨k, hk, hkQ⟩ := h i
    have : ygAll σ θ g ⟨gramR (Ainf F) σ J Y, gram_mem σ ψ θ l hP J ε fr hfr g Y⟩ i = k := by
      rw [← hinv_herm k, hkQ]
      show hinv _ = _
      congr 1
      show ((g i).1)ᴴ * (gramR (Ainf F) σ J Y).map (θ i) * (g i).1 = _
      rw [map_gramR_crd σ ψ θ l hP J ε fr hfr g Y i, gl_conj_cancel]
    rw [this]
    exact hk

theorem psi_pairHerm (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (g : ι → GL (Fin n) ℂ)
    (S T : HermR (Ainf F) σ n) :
    psiInf F ψ (pairHerm (Ainf F) σ n S T) = Complex.exp (2 * Real.pi * Complex.I *
      ∑ i, (l i : ℂ) * ∑ a, ∑ b, ((ybAll σ θ g S i a b : ℝ) : ℂ) * ((ygAll σ θ g T i a b : ℝ) : ℂ)) := by
  have e0 : pairHerm (Ainf F) σ n S T =
      trPair (Ainf F) (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) := rfl
  rw [e0, psi_trPair_gen σ hCM ψ θ l hP]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have e : (herm (ybAll σ θ g S i) * herm (ygAll σ θ g T i)).trace =
      ((S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i)).trace := by
    rw [herm_ygAll σ ψ θ l hP g T i, herm_ybAll σ ψ θ l hP g S i]
    have h1 : (((g i)⁻¹).1)ᴴ * ((g i).1)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, gl_mul_inv, Matrix.conjTranspose_one]
    calc (((g i)⁻¹).1 * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (((g i)⁻¹).1)ᴴ *
          (((g i).1)ᴴ * (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (g i).1)).trace
        = (((g i)⁻¹).1 * ((S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) *
            (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (g i).1)).trace := by
          congr 1
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (((g i)⁻¹).1)ᴴ, h1, Matrix.one_mul]
      _ = ((S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) *
            (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * ((g i).1 * ((g i)⁻¹).1)).trace := by
          rw [Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [gl_mul_inv, Matrix.mul_one]
  rw [← e, trace_herm_mul, re_sum_cast]

theorem pairHerm_comm (σ : E →ₐ[F] E) {n : ℕ} (S T : HermR (Ainf F) σ n) :
    pairHerm (Ainf F) σ n S T = pairHerm (Ainf F) σ n T S := by
  simp only [pairHerm]
  congr 2
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem det_herm_ygAll (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (g : ι → GL (Fin n) ℂ)
    (S : HermR (Ainf F) σ n) (hS : IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det) (i : ι) :
    (herm (ygAll σ θ g S i)).det ≠ 0 := by
  rw [herm_ygAll σ ψ θ l hP g S i, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  have h1 : ((S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i)).det ≠ 0 := by
    rw [show ((S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i)).det =
      θ i (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det from (RingHom.map_det _ _).symm]
    exact (hS.map (θ i)).ne_zero
  have h2 : ((g i).1).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp (g i).isUnit).ne_zero
  exact mul_ne_zero (mul_ne_zero (star_ne_zero.mpr h2) h1) h2

end PositivityTheory.SiegelWeilFormula.GReal
