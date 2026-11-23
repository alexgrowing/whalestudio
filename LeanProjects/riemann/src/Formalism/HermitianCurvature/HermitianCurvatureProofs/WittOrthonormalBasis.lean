import Formalism.HermitianCurvature.HermitianCurvatureProofs.FlagGramRestriction

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P

namespace WittOrthonormalBasis

open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector FlagGramRestriction

variable {k r : ℕ}

lemma mul_col {m κ μ : Type*} [Fintype κ] (M : Matrix m κ ℂ) (N : Matrix κ μ ℂ) (i : m) (j : μ) :
    (M * N) i j = (M *ᵥ fun a => N a j) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

lemma left_inv_square {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ] (W : Matrix (Fin n) κ ℂ)
    (L : Matrix κ (Fin n) ℂ) (hcard : Fintype.card κ = n) (h : L * W = 1) : W * L = 1 := by
  exact (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivFinOfCardEq hcard)).mp h

lemma onb {z z' : Fin (2 * r + k + 1) → ℂ} (hstd : C2.Std k r z z') {γ : B.Mat k r} (hpos : C2.PosPt k r z z' γ) :
    ∃ Bm : Matrix (Fin (2 * r + k + 1)) (Fin (k - 1) ⊕ Fin 0) ℂ,
      (gnB k r z z' γ)ᴴ * Hpk k r * Bm = 0 ∧ Bmᴴ * Hpk k r * Bm = 1 := by
  classical
  letI : PartialOrder ℂ := Complex.partialOrder
  obtain ⟨-, -, hposU, hfin⟩ := gram_independent_signature' k r z z' γ hstd hpos
  have hH : (Hpk k r)ᴴ = Hpk k r := Formalism.QuantumDeterminants.GBasic.Hpk_herm k r
  let b := Module.finBasisOfFinrankEq ℂ (C2.Uperp k r z z' γ) hfin
  let M : Matrix (Fin (2 * r + k + 1)) (Fin (k - 1)) ℂ :=
    Matrix.of fun i j => (b j : Fin (2 * r + k + 1) → ℂ) i
  have hMv : ∀ x : Fin (k - 1) → ℂ,
      M *ᵥ x = ((∑ j, x j • b j : C2.Uperp k r z z' γ) : Fin (2 * r + k + 1) → ℂ) := by
    intro x
    ext i
    simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hMmem : ∀ x, M *ᵥ x ∈ C2.Uperp k r z z' γ := fun x => by
    rw [hMv]
    exact Submodule.coe_mem _
  have hMne : ∀ x, x ≠ 0 → M *ᵥ x ≠ 0 := by
    intro x hx h
    rw [hMv] at h
    have h' : (∑ j, x j • b j) = 0 := Submodule.coe_eq_zero.mp h
    exact hx (funext (Fintype.linearIndependent_iff.mp b.linearIndependent x h'))
  have key : ∀ x : Fin (k - 1) → ℂ,
      star x ⬝ᵥ ((Mᴴ * Hpk k r * M) *ᵥ x) = herm (Hpk k r) (M *ᵥ x) (M *ᵥ x) := by
    intro x
    rw [herm, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hHerm : (Mᴴ * Hpk k r * M).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH,
      Matrix.mul_assoc]
  have hPD : (Mᴴ * Hpk k r * M).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hHerm (fun x hx => ?_)
    have hre := hposU _ (hMmem x) (hMne x hx)
    have him := hHerm.im_star_dotProduct_mulVec_self x
    rw [key] at him ⊢
    exact Complex.lt_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩

  have hspec := hHerm.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  obtain ⟨Uu, hUu⟩ : ∃ U : Matrix (Fin (k - 1)) (Fin (k - 1)) ℂ, U = (hHerm.eigenvectorUnitary : _) := ⟨_, rfl⟩
  have hUU : Uuᴴ * Uu = 1 := by
    rw [hUu, ← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self _
  rw [← hUu, Matrix.star_eq_conjTranspose] at hspec
  let s : Fin (k - 1) → ℂ := fun i => (((Real.sqrt (hHerm.eigenvalues i))⁻¹ : ℝ) : ℂ)
  have hX : (Uu * Matrix.diagonal s)ᴴ * (Mᴴ * Hpk k r * M) * (Uu * Matrix.diagonal s) = 1 := by
    rw [hspec]
    calc (Uu * Matrix.diagonal s)ᴴ * (Uu * Matrix.diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) * Uuᴴ) *
          (Uu * Matrix.diagonal s)
        = (Matrix.diagonal s)ᴴ * (Uuᴴ * Uu) * Matrix.diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) *
            (Uuᴴ * Uu) * Matrix.diagonal s := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by
        rw [hUU, Matrix.mul_one, Matrix.mul_one, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
          Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        have hl : 0 < hHerm.eigenvalues i := hPD.eigenvalues_pos i
        have hsq := Real.mul_self_sqrt hl.le
        have hne : Real.sqrt (hHerm.eigenvalues i) ≠ 0 := (Real.sqrt_pos.mpr hl).ne'
        have hreal : (Real.sqrt (hHerm.eigenvalues i))⁻¹ * hHerm.eigenvalues i *
            (Real.sqrt (hHerm.eigenvalues i))⁻¹ = 1 := by
          rw [mul_right_comm, ← mul_inv, hsq, inv_mul_cancel₀ hl.ne']
        simp only [s, Pi.star_apply, Function.comp_apply, Complex.star_def, Complex.conj_ofReal]
        show (((Real.sqrt (hHerm.eigenvalues i))⁻¹ : ℝ) : ℂ) * ((hHerm.eigenvalues i : ℝ) : ℂ) *
          (((Real.sqrt (hHerm.eigenvalues i))⁻¹ : ℝ) : ℂ) = 1
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hreal, Complex.ofReal_one]
  let Bm0 := M * (Uu * Matrix.diagonal s)
  have hVM : (gnB k r z z' γ)ᴴ * Hpk k r * M = 0 := by
    ext i j
    rw [mul_col]
    have hcol : (fun a => M a j) = ((b j : C2.Uperp k r z z' γ) : Fin (2 * r + k + 1) → ℂ) := by
      funext a
      rfl
    rw [hcol, (mem_Uperp z z' γ _).mp (b j).2]
    rfl
  have h0 : (gnB k r z z' γ)ᴴ * Hpk k r * Bm0 = 0 := by
    simp only [Bm0, ← Matrix.mul_assoc, hVM, Matrix.zero_mul]
  have h1 : Bm0ᴴ * Hpk k r * Bm0 = 1 := by
    rw [← hX]
    simp only [Bm0, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  let e := Equiv.sumEmpty (Fin (k - 1)) (Fin 0)
  refine ⟨Bm0.submatrix id e, ?_, ?_⟩
  · ext i j
    have := congrFun (congrFun h0 i) (e j)
    simpa [Matrix.mul_apply] using this
  · ext i j
    have := congrFun (congrFun h1 (e i)) (e j)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id] at this ⊢
    rw [this]
    simp only [Matrix.one_apply, e.injective.eq_iff]

lemma witt_nd {z z' : Fin (2 * r + k + 1) → ℂ} (hstd : C2.Std k r z z') {g₁ g₂ : B.Mat k r}
    (hp1 : C2.PosPt k r z z' g₁) (hp2 : C2.PosPt k r z z' g₂)
    (hΓ : (gnB k r z z' g₁)ᴴ * Hpk k r * gnB k r z z' g₁ = (gnB k r z z' g₂)ᴴ * Hpk k r * gnB k r z z' g₂) :
    ∃ s0 ∈ B.GV k r, s0 * gnB k r z z' g₁ = gnB k r z z' g₂ := by
  classical
  obtain ⟨Bm1, h01, h11⟩ := onb hstd hp1
  obtain ⟨Bm2, h02, h12⟩ := onb hstd hp2
  have hdet : IsUnit ((gnB k r z z' g₁)ᴴ * Hpk k r * gnB k r z z' g₁).det := gram_det z z' g₁ hstd hp1
  have hH : (Hpk k r)ᴴ = Hpk k r := Formalism.QuantumDeterminants.GBasic.Hpk_herm k r
  have hk := hstd.1
  generalize gnB k r z z' g₁ = V1 at *
  generalize gnB k r z z' g₂ = V2 at *
  have hBV : ∀ (V : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ)
      (Bm : Matrix (Fin (2 * r + k + 1)) (Fin (k - 1) ⊕ Fin 0) ℂ),
      Vᴴ * Hpk k r * Bm = 0 → Bmᴴ * Hpk k r * V = 0 := by
    intro V Bm h
    have := congrArg Matrix.conjTranspose h
    simpa [Matrix.conjTranspose_mul, hH, Matrix.mul_assoc] using this
  have hB1V := hBV V1 Bm1 h01
  have hB2V := hBV V2 Bm2 h02
  have hGW : ∀ (V : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ)
      (Bm : Matrix (Fin (2 * r + k + 1)) (Fin (k - 1) ⊕ Fin 0) ℂ),
      (Matrix.fromCols V Bm)ᴴ * Hpk k r * Matrix.fromCols V Bm =
        Matrix.fromBlocks (Vᴴ * Hpk k r * V) (Vᴴ * Hpk k r * Bm) (Bmᴴ * Hpk k r * V) (Bmᴴ * Hpk k r * Bm) := by
    intro V Bm
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
  obtain ⟨W1, hW1⟩ : ∃ W, W = Matrix.fromCols V1 Bm1 := ⟨_, rfl⟩
  obtain ⟨W2, hW2⟩ : ∃ W, W = Matrix.fromCols V2 Bm2 := ⟨_, rfl⟩
  obtain ⟨L1, hL1⟩ : ∃ L, L = Matrix.fromRows ((V1ᴴ * Hpk k r * V1)⁻¹ * V1ᴴ * Hpk k r) (Bm1ᴴ * Hpk k r) :=
    ⟨_, rfl⟩
  have hLW : L1 * W1 = 1 := by
    rw [hL1, hW1, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, hB1V, h11⟩
    · have e1 := Matrix.nonsing_inv_mul _ hdet
      simpa only [Matrix.mul_assoc] using e1
    · have e1 := congrArg (fun X => (V1ᴴ * Hpk k r * V1)⁻¹ * X) h01
      simpa only [Matrix.mul_assoc, Matrix.mul_zero] using e1
  have hcard : Fintype.card ((Fin (r + 1) ⊕ Fin (r + 1)) ⊕ (Fin (k - 1) ⊕ Fin 0)) = 2 * r + k + 1 := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hWL : W1 * L1 = 1 := left_inv_square W1 L1 hcard hLW
  have hWW : W2ᴴ * Hpk k r * W2 = W1ᴴ * Hpk k r * W1 := by
    rw [hW1, hW2, hGW, hGW, h01, h02, hB1V, hB2V, h11, h12, hΓ]
  refine ⟨W2 * L1, ?_, ?_⟩
  · show (W2 * L1)ᴴ * Hpk k r * (W2 * L1) = Hpk k r
    calc (W2 * L1)ᴴ * Hpk k r * (W2 * L1) = L1ᴴ * (W2ᴴ * Hpk k r * W2) * L1 := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = L1ᴴ * (W1ᴴ * Hpk k r * W1) * L1 := by rw [hWW]
      _ = (W1 * L1)ᴴ * Hpk k r * (W1 * L1) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [hWL]; simp
  · have h : (W2 * L1) * W1 = W2 := by rw [Matrix.mul_assoc, hLW, Matrix.mul_one]
    generalize W2 * L1 = s0 at h
    rw [hW1, hW2] at h
    ext i j
    have := congrFun (congrFun h i) (Sum.inl j)
    simpa [Matrix.mul_apply] using this

end WittOrthonormalBasis

open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector FlagGramRestriction WittOrthonormalBasis

theorem fibre_orbit_description : C2.FibreOrbit := by
  intro k r z z' hstd g₁ hg₁ g₂ hg₂ hG hZ
  have hH2 : Hpk k r * Hpk k r = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r

  have hunit : ∀ g ∈ B.GV k r, IsUnit g.det := by
    intro g hg
    have hg' : g ᴴ * Hpk k r * g = Hpk k r := hg
    have : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
      calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hg', hH2]
    exact Matrix.isUnit_det_of_left_inverse this
  have hinv : ∀ g ∈ B.GV k r, g⁻¹ ∈ B.GV k r := by
    intro g hg
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
    show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
    calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
      _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [Matrix.mul_nonsing_inv _ (hunit g hg)]; simp
  have hmul : ∀ g ∈ B.GV k r, ∀ h ∈ B.GV k r, g * h ∈ B.GV k r := by
    intro g hg h hh
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
    have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
    show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    calc (g * h)ᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [hg', hh']
  have hGf : Gf k r z z' g₂ = Gf k r z z' g₁ := by simp only [Gf, Dmin, hZ]
  have hp1 : C2.PosPt k r z z' g₁ := ⟨hg₁, hG⟩
  have hp2 : C2.PosPt k r z z' g₂ := ⟨hg₂, by rw [hGf]; exact hG⟩
  have hgram : gramM k r z z' g₁ = gramM k r z z' g₂ := by
    rw [gram_block_form k r z z' hstd.2.1 hstd.2.2 g₁ hg₁, gram_block_form k r z z' hstd.2.1 hstd.2.2 g₂ hg₂,
      hZ]
  rw [gn_gramM_eq, gn_gramM_eq] at hgram
  obtain ⟨s0, hs0, hs0V⟩ := witt_nd hstd hp1 hp2 hgram
  have hcol : ∀ j, s0 *ᵥ gramVec k r z z' g₁ j = gramVec k r z z' g₂ j := by
    intro j
    rw [← col_mul s0 z z' g₁ j, hs0V]
    rfl
  have hfa : ∀ a, s0 *ᵥ fvec k r z a = fvec k r z a := fun a => hcol (Sum.inl a)
  have hfb : ∀ b, s0 *ᵥ (g₁ *ᵥ fvec k r z' b) = g₂ *ᵥ fvec k r z' b := fun b => hcol (Sum.inr b)
  have hu0 := hunit s0 hs0
  have hu1 := hunit g₁ hg₁
  have hu2 := hunit g₂ hg₂
  refine ⟨s0⁻¹, ?_, g₁⁻¹ * s0⁻¹ * g₂, ?_, ?_⟩
  · rw [← fixed_frame_property k r z hstd.2.1]
    refine ⟨hinv s0 hs0, fun a => ?_⟩
    calc s0⁻¹ *ᵥ fvec k r z a = s0⁻¹ *ᵥ (s0 *ᵥ fvec k r z a) := by rw [hfa]
      _ = fvec k r z a := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu0, Matrix.one_mulVec]
  · rw [← fixed_frame_property k r z' hstd.2.2]
    refine ⟨hmul _ (hmul _ (hinv g₁ hg₁) _ (hinv s0 hs0)) _ hg₂, fun b => ?_⟩
    calc (g₁⁻¹ * s0⁻¹ * g₂) *ᵥ fvec k r z' b = g₁⁻¹ *ᵥ (s0⁻¹ *ᵥ (g₂ *ᵥ fvec k r z' b)) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = g₁⁻¹ *ᵥ (s0⁻¹ *ᵥ (s0 *ᵥ (g₁ *ᵥ fvec k r z' b))) := by rw [hfb]
      _ = fvec k r z' b := by
          have e0 : s0⁻¹ *ᵥ (s0 *ᵥ (g₁ *ᵥ fvec k r z' b)) = g₁ *ᵥ fvec k r z' b := by
            rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu0, Matrix.one_mulVec]
          rw [e0, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu1, Matrix.one_mulVec]
  · rw [Matrix.nonsing_inv_nonsing_inv _ hu0]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc s0 g₁ g₁⁻¹, Matrix.mul_nonsing_inv _ hu1, Matrix.mul_one, Matrix.mul_nonsing_inv _ hu0,
      Matrix.one_mul]

end Formalism.FourierDecayAlt.P
