import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CayleyTransformUnitarySkewInvolutive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCm

noncomputable section

namespace PositivityTheory.SA

open Matrix Filter Topology

theorem units_fd (k R : Type) [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k] [T1Space k] [CommRing R]
    [Algebra k R] [Module.Finite k R] [TopologicalSpace R] [IsModuleTopology k R] (x : R) (hx : IsUnit x) :
    (∀ᶠ y in 𝓝 x, IsUnit y) ∧ ContinuousAt Ring.inverse x := by
  let b := Module.finBasis k R
  have := IsModuleTopology.toContinuousAdd k R
  have cL : Continuous (Algebra.leftMulMatrix b) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  let f : R → R := fun y => b.equivFun.symm ((Algebra.leftMulMatrix b y)⁻¹ *ᵥ b.repr 1)
  have hf : ∀ y, (Algebra.leftMulMatrix b y).det ≠ 0 → y * f y = 1 := fun y hy => by
    apply b.equivFun.injective
    have := Algebra.leftMulMatrix_mulVec_repr b y (f y)
    rw [show ⇑(b.repr (f y)) = (Algebra.leftMulMatrix b y)⁻¹ *ᵥ b.repr 1 from b.equivFun.apply_symm_apply _, mulVec_mulVec,
      mul_nonsing_inv _ hy.isUnit, one_mulVec] at this
    exact this.symm
  have h0 : (Algebra.leftMulMatrix b x).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 (hx.map _)).ne_zero
  have ev : ∀ᶠ y in 𝓝 x, (Algebra.leftMulMatrix b y).det ≠ 0 := cL.matrix_det.continuousAt.eventually_ne h0
  refine ⟨ev.mono fun y hy => IsUnit.of_mul_eq_one _ (hf y hy), ContinuousAt.congr (f := f) ?_ (ev.mono fun y hy => ?_)⟩
  · have c1 : Continuous b.equivFun.symm := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
    have c2 : ContinuousAt (fun y => (Algebra.leftMulMatrix b y)⁻¹) x :=
      ContinuousAt.comp (f := Algebra.leftMulMatrix b)
        (continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ h0)) cL.continuousAt
    exact c1.continuousAt.comp ((continuous_id.matrix_mulVec continuous_const).continuousAt.comp c2)
  · exact (Ring.eq_mul_inverse_iff_mul_eq _ _ _ (IsUnit.of_mul_eq_one _ (hf y hy))).2
      ((mul_comm _ _).trans (hf y hy)) |>.trans (one_mul _)

theorem map_inv' {K R n : Type} [Field K] [CommRing R] [Fintype n] [DecidableEq n] (ι : K →+* R) {A : Matrix n n K}
    (h : A.det ≠ 0) : (A⁻¹).map ι = (A.map ι)⁻¹ :=
  (inv_eq_right_inv (by rw [← Matrix.map_mul, mul_nonsing_inv _ h.isUnit, Matrix.map_one _ (map_zero ι) (map_one ι)])).symm

theorem map_smul₀ {K R m n : Type} [CommRing K] [CommRing R] (ι : K →+* R) (a : K) (A : Matrix m n K) :
    (a • A).map ι = ι a • A.map ι := Matrix.ext fun _ _ => map_mul ι _ _

theorem dense_unitary {K R : Type} [Field K] [CharZero K] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsArtinianRing R] [Nontrivial R] (ι : K →+* R) (hd : DenseRange ι) (c : K →+* K) (σ : R →+* R)
    (hσι : ∀ x, σ (ι x) = ι (c x)) (hc : ∀ x, c (c x) = x) (hne : ∃ z, c z ≠ z) (hσ : ∀ x, σ (σ x) = x)
    (cσ : Continuous σ) (hu : ∀ x : R, IsUnit x → (∀ᶠ y in 𝓝 x, IsUnit y) ∧ ContinuousAt Ring.inverse x) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) (hG : (G.map c)ᵀ = G) (hdet : G.det ≠ 0) (g : Matrix (Fin n) (Fin n) R)
    (hg : gᵀ * G.map ι * g.map σ = G.map ι) :
    g ∈ closure {M | ∃ γ : Matrix (Fin n) (Fin n) K, γᵀ * G * γ.map c = G ∧ M = γ.map ι} := by
  have hmm : ∀ A : Matrix (Fin n) (Fin n) K, (A.map ι).map σ = (A.map c).map ι := fun A => Matrix.ext fun _ _ => hσι _
  have hdet' : IsUnit (G.map ι).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hdet.isUnit.map ι
  have h2 : IsUnit (2 : R) := by simpa [map_ofNat] using (two_ne_zero (α := K)).isUnit.map ι
  obtain ⟨c1, c2, -, -⟩ := GlobalTheory.CayleyInv.cayley_transform R σ n (G.map ι) hσ
    (by rw [hmm, ← transpose_map, hG]) hdet' h2
  obtain ⟨-, -, d3, d4⟩ := GlobalTheory.CayleyInv.cayley_transform K c n G hc hG hdet.isUnit (two_ne_zero (α := K)).isUnit
  obtain ⟨lam, ⟨hlam, -⟩, hl⟩ := GlobalTheory.NormSum.RepAt.exists_unit_det ι g _ (GlobalTheory.NormSum.RepAt.normOne_infinite c hc hne)
  have hl0 : lam ≠ 0 := left_ne_zero_of_mul_eq_one hlam
  have hl1 : ι lam * σ (ι lam) = 1 := by rw [hσι, ← map_mul, hlam, map_one]
  obtain ⟨hS, hS1⟩ := c1 (ι lam • g) (by
    rw [map_smul₀, transpose_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, hl1, one_smul, hg]) hl
  have hS2 := c2 _ hl
  set S := (1 - ι lam • g) * (1 + ι lam • g)⁻¹
  let P : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R :=
    fun A => ι 2⁻¹ • (A - (G.map ι * A.map σ * (G.map ι)⁻¹)ᵀ)
  have cP : Continuous P := (continuous_id.sub (((continuous_const.matrix_mul (continuous_id.matrix_map cσ)).matrix_mul
    continuous_const).matrix_transpose)).const_smul (ι 2⁻¹)
  have PS : P S = S := by
    have e : G.map ι * S.map σ * (G.map ι)⁻¹ = -Sᵀ := by
      rw [eq_neg_of_add_eq_zero_right hS, Matrix.neg_mul, Matrix.mul_assoc, mul_nonsing_inv _ hdet', Matrix.mul_one]
    simp only [P]
    rw [e, transpose_neg, transpose_transpose, sub_neg_eq_add, ← two_smul R S, smul_smul, ← map_ofNat ι 2, ← map_mul,
      inv_mul_cancel₀ two_ne_zero, map_one, one_smul]
  have c3 : Continuous fun A => 1 + P A := continuous_const.add cP
  have hS1' : IsUnit (1 + P S).det := by rwa [PS]
  have hf : Tendsto (fun A => ι lam⁻¹ • ((1 - P A) * (1 + P A)⁻¹)) (𝓝 S) (𝓝 g) := by
    have : ContinuousAt (fun A => ι lam⁻¹ • ((1 - P A) * (1 + P A)⁻¹)) S :=
      ((continuous_const.sub cP).continuousAt.mul (ContinuousAt.comp (f := fun A => 1 + P A)
        (continuousAt_matrix_inv _ (hu _ hS1').2) c3.continuousAt)).const_smul (ι lam⁻¹)
    have e : ι lam⁻¹ • ((1 - P S) * (1 + P S)⁻¹) = g := by
      rw [PS, hS2, smul_smul, ← map_mul, inv_mul_cancel₀ hl0, map_one, one_smul]
    exact e ▸ this.tendsto
  have hD : DenseRange fun A : Matrix (Fin n) (Fin n) K => A.map ι := DenseRange.piMap fun _ => DenseRange.piMap fun _ => hd
  refine mem_closure_of_frequently_of_tendsto (((mem_closure_iff_frequently.1 (hD S)).and_eventually
    (c3.matrix_det.continuousAt.eventually (hu _ hS1').1)).mono ?_) hf
  rintro _ ⟨⟨A, rfl⟩, hA⟩
  let T : Matrix (Fin n) (Fin n) K := (2⁻¹ : K) • (A - (G * A.map c * G⁻¹)ᵀ)
  have hT : T.map ι = P (A.map ι) := by
    simp only [T, P]
    rw [map_smul₀, Matrix.map_sub _ (map_sub ι), transpose_map, Matrix.map_mul, Matrix.map_mul, map_inv' ι hdet, hmm]
  have h1 : (1 + T).map ι = 1 + P (A.map ι) := by
    rw [Matrix.map_add _ (map_add ι), Matrix.map_one _ (map_zero ι) (map_one ι), hT]
  have h0 : (1 + T).det ≠ 0 := fun z => by
    rw [← h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det, z, map_zero] at hA
    exact not_isUnit_zero hA
  have hsk : Tᵀ * G + G * T.map c = 0 := by
    simp only [T]
    rw [map_smul₀, map_inv₀, map_ofNat, transpose_smul, smul_mul_assoc, mul_smul_comm, ← smul_add, d4, smul_zero]
  refine ⟨lam⁻¹ • ((1 - T) * (1 + T)⁻¹), ?_, ?_⟩
  · rw [map_smul₀, transpose_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, d3 T hsk h0.isUnit,
      map_inv₀, ← mul_inv, hlam, inv_one, one_smul]
  · rw [map_smul₀, Matrix.map_mul, map_inv' ι h0, h1, Matrix.map_sub _ (map_sub ι),
      Matrix.map_one _ (map_zero ι) (map_one ι), hT]

end PositivityTheory.SA

end
