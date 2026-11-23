import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeLeProdLayersUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTraceOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualFlagOfSaturatedIsotropicFlagStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianFlagPieceHeightsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianFlagAtComplexEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexFlagAtEmbeddingFrameFinrankAndLowersStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalEqLoweringStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinrankMatricesLoweringFiltrationByEqSuccAddStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBlockFrameOfComplexFlagStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSkewOrthonormalBasisAdaptedFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealComplexSpanOrthonormalSkewFamilyStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryLayerCoordsToBlocksStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumePiLatticeUnitaryCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HomLatticeCovolumeEmbeddingFamilyStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBiorthogonalFrameOfSaturatedFlagStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BiorthogonalBlockFramesTriangularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalBlockFrameLocalSplitStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HeightFlagPieceTriangularFrameStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSkewIntegerNormCoprimePrimeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjStableLatticeRealImagCovolumeLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ZlatticeCovolumeEqOfCoprimeScalarsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryLeadingTermOfSkewLayerStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdjointMemAndExistsIntegralPointStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralPointsAlgebraSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddingsMatchInfinitePlacesAutInstanceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentDimEqSumPairsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLayerHeightQuotientsEqSqStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

noncomputable section

namespace GlobalTheory.RadCov

def realMul (ι κ : Type) (c : ℂ) : (ι → κ → ℝ) →ₗ[ℤ] (ι → κ → ℂ) where
  toFun y := fun v i => c * (y v i : ℂ)
  map_add' x y := by funext v i; simp [mul_add]
  map_smul' k x := by funext v i; simp [mul_left_comm]

theorem real_domain (E : Type) [Field E] [NumberField E] [StarRing E] (hE : Formalism.HermitianLatticesTheory.IsCMUnram E)
    (ι κ : Type) [Fintype ι] [Fintype κ] (φ : ι → E →+* ℂ)
    (hφ : Function.Bijective (fun v => InfinitePlace.mk (φ v))) (L : Submodule ℤ (ι → κ → ℂ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (hO : ∀ x : 𝓞 E, ∀ z ∈ L, (fun v i => φ v (x : E) * z v i) ∈ L)
    (hc : ∀ z ∈ L, (fun v i => starRingEnd ℂ (z v i)) ∈ L) :
    ∃ D : Set (ι → κ → ℝ), MeasurableSet D ∧
      (∀ x, ∃ y : ι → κ → ℝ, (fun v i => (y v i : ℂ)) ∈ L ∧ y + x ∈ D) ∧
      volume D ≤ ENNReal.ofReal
        (Real.sqrt (2 ^ (Fintype.card ι * Fintype.card κ) * ZLattice.covolume L volume)) := by
  classical
  have hA : ∀ y, y ∈ L.comap (realMul ι κ 1) ↔ (fun v i => (y v i : ℂ)) ∈ L := fun y => by
    simp [realMul]
  have hB : ∀ y, y ∈ L.comap (realMul ι κ Complex.I) ↔ (fun v i => Complex.I * (y v i : ℂ)) ∈ L :=
    fun y => Iff.rfl
  generalize L.comap (realMul ι κ 1) = A at hA
  generalize L.comap (realMul ι κ Complex.I) = B at hB
  obtain ⟨⟨dA, lA⟩, ⟨dB, lB⟩, hle⟩ := GlobalTheory.T.conjStable_lattice_real_imag_covolume_le ι κ L hc A B hA hB
  have heq : ZLattice.covolume A volume = ZLattice.covolume B volume := by
    refine GlobalTheory.T.zlattice_covolume_eq_of_coprime_scalars ι κ A B fun p hp => ?_
    obtain ⟨δ, N, h1, h2, h3⟩ := GlobalTheory.T.exists_skew_integer_norm_coprime_prime E hE ι φ hφ p hp
    have hδ : ∀ v, φ v (δ : E) = Complex.I * ((φ v (δ : E)).im : ℂ) := by
      intro v
      have h := hE.2.1 (φ v) (δ : E)
      rw [h1, map_neg] at h
      have h4 := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.conj_re] at h4
      apply Complex.ext <;> simp
      linarith
    refine ⟨fun v => (φ v (δ : E)).im, N, h2, ?_, fun y hy => ?_, fun y hy => ?_⟩
    · rw [← h3]
      refine Finset.prod_congr rfl fun v _ => ?_
      conv_rhs => rw [hδ v]
      simp
    · rw [hB]
      have := hO δ _ ((hA y).1 hy)
      convert this using 3 with v i
      conv_rhs => rw [hδ v]
      push_cast
      ring
    · rw [hA]
      have := neg_mem (hO δ _ ((hB y).1 hy))
      convert this using 1
      funext v i
      simp only [Pi.neg_apply]
      conv_rhs => rw [hδ v]
      push_cast
      linear_combination (((φ v (δ : E)).im : ℂ) * (y v i : ℂ)) * Complex.I_mul_I
  let b := Module.Free.chooseBasis ℤ A
  refine ⟨ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ A), ZSpan.fundamentalDomain_measurableSet _,
    fun x => ⟨-(ZSpan.floor (b.ofZLatticeBasis ℝ A) x : ι → κ → ℝ), ?_, ?_⟩, ?_⟩
  · rw [← hA]
    refine neg_mem ?_
    exact (b.ofZLatticeBasis_span ℝ).le (ZSpan.floor (b.ofZLatticeBasis ℝ A) x).2
  · rw [neg_add_eq_sub]
    exact ZSpan.fract_mem_fundamentalDomain _ x
  · have h1 := ZLattice.covolume_eq_measure_fundamentalDomain A volume
      (ZLattice.isAddFundamentalDomain b volume)
    have h2 := (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ A)).measure_lt_top (μ := volume)
    rw [← ENNReal.ofReal_toReal h2.ne]
    refine ENNReal.ofReal_le_ofReal (Real.le_sqrt_of_sq_le ?_)
    rw [← measureReal_def, ← h1, sq]
    nth_rewrite 2 [heq]
    exact hle

theorem layer_covolume (E : Type) [Field E] [NumberField E] [StarRing E] (hE : IsTotallyComplex E)
    (ι : Type) [Fintype ι] (n m d : ℕ) (φ : ι → E →+* ℂ) (P : ι → Matrix (Fin n) (Fin n) ℂ)
    (X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ) (hX : PlaceMatch φ P X) (hP : ∀ v, IsUnit (P v))
    (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ) (T : ∀ b, Matrix (Fin n) (Fin (r b)) E)
    (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E))
    (hT : Biorth r m T T') (hΛ : ∀ b, Submodule.IsLattice E (Λ b))
    (hF : ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0))
    (U : ι → ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (hU : ∀ v, Biorth r m (U v) (fun b => (U v b)ᴴ))
    (hW : ∀ v k y, y ∈ locFlag (φ v) (P v) F k ↔ ∀ b, k ≤ b → (U v b)ᴴ *ᵥ y = 0)
    (B : ι → Fin d → Matrix (Fin n) (Fin n) ℂ) (deg : Fin d → ℕ)
    (hB : ∀ v i k, (B v i * (B v k)ᴴ).trace = if i = k then 1 else 0)
    (hs : ∀ v c, lowers (locFlag (φ v) (P v) F) c = Submodule.span ℂ (B v '' {i | c ≤ deg i})) (c : ℕ)
    (L : Submodule ℤ (ι → {i : Fin d // deg i = c} → ℂ))
    (hL : ∀ z, z ∈ L ↔ ∃ Y ∈ lowers F c, ∀ v i,
      z v i = ((P v)⁻¹ * Y.map (φ v) * P v * (B v i.1)ᴴ).trace) :
    ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L volume =
      ∏ b ∈ Finset.range m, Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (r b * r (b + c + 1))) *
        (pieceHt X F b ^ r (b + c + 1) / pieceHt X F (b + c + 1) ^ r b) := by
  classical
  obtain ⟨hloc, hrat⟩ := GlobalTheory.T.rational_block_frame_local_split E n m F r T T' Λ hT hΛ hF
  obtain ⟨hr1, hr2⟩ := hrat c
  choose Φ hΦ1 hΦ2 using fun v => GlobalTheory.T.exists_unitary_layerCoords_to_blocks n m d _ r (U v) (B v) deg (hU v) (hW v) (hB v) (hs v) c
  set G : ι → ∀ b, Matrix (Fin (r b)) (Fin (r b)) ℂ :=
    fun v b => (U v b)ᴴ * ((P v)⁻¹ * (T b).map (φ v)) with hG
  have hblk := fun v => GlobalTheory.T.biorthogonal_block_frames_triangular n m _ r _ (U v) _ _ (hloc (φ v) (P v) (hP v)).1 (hU v)
    (hloc (φ v) (P v) (hP v)).2 (hW v)
  have hinv : ∀ v b, (G v b)⁻¹ = (T' b).map (φ v) * P v * U v b :=
    fun v b => Matrix.inv_eq_right_inv ((hblk v).1 b)
  have hdet : ∀ v b, (G v b).det ≠ 0 := fun v b =>
    (Matrix.isUnit_det_of_right_inverse ((hblk v).1 b)).ne_zero
  have hkey : ∀ Y ∈ lowers F c, ∀ v (b : Fin m),
      Matrix.of (Φ v (fun i => ((P v)⁻¹ * Y.map (φ v) * P v * (B v i.1)ᴴ).trace) b) =
        G v b * (T' b * Y * T (b + c + 1)).map (φ v) * (G v (b + c + 1))⁻¹ := by
    intro Y hY v b
    have h1 := (GlobalTheory.T.complexFlagAtEmbeddingFrame_finrank_and_lowers E n (φ v) (P v) F (hP v)).2 c Y hY
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (hP v)
    rw [hΦ2 v _ h1, (hblk v).2 c _ h1, hinv, Matrix.map_mul, Matrix.map_mul]
    congr 2
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  let M : ∀ b : Fin m, Submodule ℤ (ι → Fin (r b) → Fin (r (b + c + 1)) → ℂ) := fun b =>
    { carrier := {z | ∃ Z : Matrix (Fin (r b)) (Fin (r (b + c + 1))) E, (∀ y ∈ Λ (b + c + 1), Z *ᵥ y ∈ Λ b) ∧
        ∀ v, Matrix.of (z v) = G v b * Z.map (φ v) * (G v (b + c + 1))⁻¹}
      zero_mem' := ⟨0, fun y _ => by simp, fun v => by
        rw [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]; rfl⟩
      add_mem' := by
        rintro z z' ⟨Z, h1, h2⟩ ⟨Z', h1', h2'⟩
        refine ⟨Z + Z', fun y hy => ?_, fun v => ?_⟩
        · rw [Matrix.add_mulVec]; exact add_mem (h1 y hy) (h1' y hy)
        · rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, ← h2, ← h2']; rfl
      smul_mem' := by
        rintro k z ⟨Z, h1, h2⟩
        refine ⟨k • Z, fun y hy => ?_, fun v => ?_⟩
        · rw [Matrix.smul_mulVec]; exact zsmul_mem (h1 y hy) k
        · have : (k • Z).map (φ v) = k • Z.map (φ v) := by ext p q; simp
          rw [this, Matrix.mul_smul, Matrix.smul_mul, ← h2]; rfl }
  have hM := fun b : Fin m => GlobalTheory.T.homLatticeCovolume_embedding_family E hE ι φ hX.1 _ _ (Λ b) (Λ (b + c + 1)) (hΛ _) (hΛ _)
    (fun v => G v b) (fun v => G v (b + c + 1)) (fun v => hdet v _) (fun v => hdet v _) (M b)
    (fun z => Iff.rfl)
  obtain ⟨dL, lL, hcov⟩ := GlobalTheory.T.covolume_pi_lattice_unitary_coordinates ι {i : Fin d // deg i = c} (Fin m) (fun b => r b)
    (fun b => r (b + c + 1)) Φ hΦ1 M (fun b => (hM b).imp fun _ h => h.1) L (fun z => by
      rw [hL]
      constructor
      · rintro ⟨Y, hY, hz⟩ b
        refine ⟨_, hr1 Y hY b, fun v => ?_⟩
        rw [← hkey Y hY v b, ← funext (hz v)]
      · intro h
        choose Z hZ1 hZ2 using h
        obtain ⟨Y, hY, hYZ⟩ := hr2 Z hZ1
        refine ⟨Y, hY, fun v i => ?_⟩
        have e : z v = fun i => ((P v)⁻¹ * Y.map (φ v) * P v * (B v i.1)ᴴ).trace := by
          refine (Φ v).injective (funext fun b => Matrix.of.injective ?_)
          rw [hkey Y hY v b, hYZ b, ← hZ2 b v]
        exact congrFun e i)
  refine ⟨dL, lL, ?_⟩
  rw [hcov, Finset.prod_range]
  refine Finset.prod_congr rfl fun b _ => ?_
  obtain ⟨_, -, h⟩ := hM b
  have hv : 0 < Formalism.HermitianLatticesTheory.vInv E := by
    have : 0 < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero E)
    unfold Formalism.HermitianLatticesTheory.vInv
    positivity
  have hp := GlobalTheory.T.height_flag_piece_triangular_frame E hE ι n m φ P X hX hP F r T T' Λ hT hΛ hF U hU hW
  rw [h, hp, hp, div_mul_cancel_left₀ (pow_pos hv _).ne', mul_pow, ← pow_mul, inv_pow, mul_assoc,
    mul_assoc, div_eq_mul_inv]

theorem exists_deg (m : ℕ) (k : ℕ → ℕ) (hk : ∀ c, m ≤ c → k c = 0) (d : ℕ)
    (hd : d = ∑ c ∈ Finset.range m, k c) :
    ∃ deg : Fin d → ℕ, ∀ c, Fintype.card {i : Fin d // deg i = c} = k c := by
  classical
  have e : Fin d ≃ (Σ c : Fin m, Fin (k c)) := Fintype.equivOfCardEq (by
    simp [hd, Finset.sum_range])
  refine ⟨fun i => (e i).1, fun c => ?_⟩
  rw [Fintype.card_congr (e.subtypeEquiv (q := fun x => (x.1 : ℕ) = c) fun _ => Iff.rfl),
    Fintype.card_subtype, Finset.card_filter, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  have h1 : ∀ x : Fin m, (∑ _y : Fin (k x), if (x : ℕ) = c then 1 else 0) = if (x : ℕ) = c then k x else 0 := by
    intro x
    split_ifs <;> simp
  refine (Finset.sum_congr rfl fun x _ => h1 x).trans ?_
  rw [← Finset.sum_range (fun x => if x = c then k x else 0), Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (hk c (by simpa using h)).symm

theorem covol_mono_left {G : Type} [Mul G] [MeasurableSpace G] {Γ Γ' : Set G} (h : Γ' ⊆ Γ) (μ : Measure G)
    (A : Set G) : covol Γ μ A ≤ covol Γ' μ A := by
  unfold covol
  refine le_iInf fun D => le_iInf fun hD => le_iInf fun hc => ?_
  exact iInf_le_of_le D (iInf_le_of_le hD (iInf_le_of_le
    (fun x hx => (hc x hx).imp fun γ hγ => ⟨h hγ.1, hγ.2⟩) le_rfl))

theorem adj_frame {E : Type} [Field E] [StarRing E] {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0)
    {φ : E →+* ℂ} (hφ : ∀ x, φ (star x) = starRingEnd ℂ (φ x)) {P : Matrix (Fin n) (Fin n) ℂ}
    (hP : IsUnit P) {ε : Fin n → Bool} (h : Pᴴ * J.map φ * P = Formalism.REAL.Jm ε)
    (Y : Matrix (Fin n) (Fin n) E) :
    P⁻¹ * (J⁻¹ * Yᴴ * J).map φ * P =
      Formalism.REAL.Jm ε * (P⁻¹ * Y.map φ * P)ᴴ * Formalism.REAL.Jm ε := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have hu' : IsUnit (Pᴴ).det := by rw [Matrix.det_conjTranspose]; exact hu.star
  have h1 : J.map φ * (J⁻¹).map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hJ.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (Yᴴ).map φ = (Y.map φ)ᴴ := by ext i k; simp [hφ]
  have h3 : Formalism.REAL.Jm ε * (P⁻¹ * (J⁻¹ * Yᴴ * J).map φ * P) = (P⁻¹ * Y.map φ * P)ᴴ * Formalism.REAL.Jm ε := by
    rw [← h, Matrix.map_mul, Matrix.map_mul, h2, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_nonsing_inv]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu,
      Matrix.nonsing_inv_mul_cancel_left _ _ hu']
    rw [← Matrix.mul_assoc (J.map φ), h1, Matrix.one_mul]
  rw [Matrix.mul_assoc (Formalism.REAL.Jm ε), ← h3, ← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.one_mul]

theorem radicalCovolume : RadicalCovolume := by
  classical
  intro I xf a j hj S hS ν _ hν
  obtain ⟨F, r, hF, hFm, hFS, hr, hrj, hra, hr0⟩ := GlobalTheory.T.exists_selfDual_flag_of_saturated_isotropic_flag I xf a j S hS
  obtain ⟨hτ, hha, hh1⟩ := GlobalTheory.T.selfDualHermitianFlag_piece_heights I xf a j hj S hS F hF hFm hFS
  obtain ⟨-, hfg, hsp, -, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I (1, xf)
  obtain ⟨htc, hf1, hf2, -, -⟩ := GlobalTheory.Count.FrameMajorant.frames_give_majorants I (1, xf)
  obtain ⟨hadjL, helt⟩ := GlobalTheory.T.adjoint_mem_and_exists_integral_point I xf
  have hX := GlobalTheory.T.embeddingsMatchInfinitePlaces_autInstance I xf
  have hJ : I.Jᴴ = I.J := I.J_herm
  have hφ := fun v => I.cm.cmUnram.2.1 (I.φ v)
  set m := 2 * a + 1 with hm
  rw [← hFm] at hfg hsp hadjL helt
  set W : InfinitePlace I.F → ℕ → Submodule ℂ (Fin I.n → ℂ) := fun v => locFlag (I.φ v) (I.P v) F with hWdef
  have hW : ∀ v, IsDualFlag (Formalism.REAL.Jm (I.ε v)) (W v) m ∧ W v m = ⊤ := fun v => GlobalTheory.T.selfDual_hermitianFlag_at_complex_embedding I.E I.n m I.J (I.φ v) (I.P v) (I.ε v) F (hφ v) (I.P_unit v) (I.P_spec v) hF hsp
  have hWr := fun v => GlobalTheory.T.complexFlagAtEmbeddingFrame_finrank_and_lowers I.E I.n (I.φ v) (I.P v) F (I.P_unit v)
  have hN : ∀ v, flagN (I.ε v) (flagAt I S v) = {g | uMat g - 1 ∈ lowers (W v) 0} := fun v =>
    GlobalTheory.T.isotropicFlagUnipotentRadical_eq_lowering I.n a (I.ε v) (W v) _ (hW v).1 (hW v).2 fun i => by
      simp only [hWdef, locFlag, flagAt, hFS]
  choose U hU hUW using fun v => GlobalTheory.T.exists_orthonormal_block_frame_of_complex_flag I.n m (W v) r (hW v).1.1 (hW v).1.2.1
    (fun b hb => ((hW v).1.2.2.1 b hb).trans (hW v).2) (fun b => by
      rw [hWdef, (hWr v).1, (hWr v).1, hr])
  obtain ⟨deg, hdeg⟩ := exists_deg m (fun c => ∑ b ∈ Finset.range m, r b * r (b + c + 1))
    (fun c hc => Finset.sum_eq_zero fun b _ => by rw [hr0 (b + c + 1) (by omega), mul_zero])
    (dimN I.n j) (GlobalTheory.T.isotropicFlagUnipotentDim_eq_sum_pairs I.n a j r hrj hra hr0)
  have hbot : ∀ v, lowers (W v) m = ⊥ := fun v =>
    lowers_eq_bot (hW v).1.2.1 (hW v).1.2.2.1 (by rw [(hW v).2]; simp)
  have hadj : ∀ v c, ∀ X ∈ lowers (W v) c,
      Formalism.REAL.Jm (I.ε v) * Xᴴ * Formalism.REAL.Jm (I.ε v) ∈ lowers (W v) c := fun v c X hX =>
    lowers_adj (Formalism.REAL.Jm_conjTranspose _) (hW v).1 hX
      (by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.one_mul])
      (fun y _ => by rw [(hW v).2]; trivial)
  choose B hB hBG hBs using fun v => GlobalTheory.T.exists_skew_orthonormal_basis_adapted_filtration I.n (dimN I.n j) m (I.ε v) (lowers (W v)) deg
    (lowers_succ_le (hW v).1.1) (hbot v) (hadj v) (fun c => by
      rw [hdeg, GlobalTheory.T.finrank_matricesLoweringFiltrationBy_eq_succ_add I.n m (W v) r (U v) (hU v) (hUW v) c])
  have hreal := fun v s => GlobalTheory.T.real_complex_span_orthonormal_skew_family I.n _ (I.ε v) (B v) s (hB v) (hBG v)
  have hle : ∀ b, F b ≤ F m := fun b => by
    rcases le_total b m with h | h
    · exact hF.1 h
    · exact (hF.2.2.1 b h).le
  obtain ⟨T, T', Λ, hT, hΛ, hFT⟩ := GlobalTheory.T.exists_biorthogonal_frame_of_saturated_flag I.E I.n m F r hF.1 hF.2.1 hF.2.2.1 ⟨hfg, hsp⟩
    (fun b y hy hyb => by
      by_cases hb : m ≤ b
      · rwa [hF.2.2.1 b hb]
      have e : b = m - (m - b) := by omega
      rw [e, hF.2.2.2 _ (by omega)]
      refine ⟨hy, fun x hx => ?_⟩
      clear hy
      induction hyb using Submodule.span_induction with
      | mem z hz => exact ((hF.2.2.2 (m - b) (by omega) z).1 (e ▸ hz)).2 x hx
      | zero => simp
      | add z z' _ _ h1 h2 => rw [Matrix.mulVec_add, dotProduct_add, h1, h2, add_zero]
      | smul c z _ h1 => rw [Matrix.mulVec_smul, dotProduct_smul, h1, smul_zero]) hr
  have hkeep : ∀ c, ∀ Y ∈ lowers F c, ∀ y ∈ F m, Y *ᵥ y ∈ F m := fun c Y hY y hy =>
    hY m y (by rwa [hF.2.2.1 _ (by omega)])
  have hadjF : ∀ c, ∀ Y ∈ lowers F c, I.J⁻¹ * Yᴴ * I.J ∈ lowers F c := fun c Y hY =>
    lowers_adj hJ hF hY
      (by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ I.J_det.isUnit])
      (hadjL Y (hkeep c Y hY))
  obtain ⟨Γ, hΓ⟩ := GlobalTheory.T.exists_integral_points_algebra_subgroup I xf (fun v => lowers (W v) 0)
    (fun v X hX Y hY => lowers_succ_le (hW v).1.1 0 (lowers_mul_zero hX hY).1) (fun v => hadj v 0)
  have hΓ' : ∀ g, g ∈ Γ ↔ g ∈ latGroup I xf ∧ ∀ v, uMat (g v) - 1 ∈ lowers (W v) 0 := fun g => by
    rw [← SetLike.mem_coe, hΓ]; rfl
  obtain ⟨w, hw⟩ := GlobalTheory.TraceOnto.exists_trace_one I.E I.cm.cmUnram

  have hlayer : ∀ c : ℕ, ∃ D : Set (InfinitePlace I.F → {i : Fin (dimN I.n j) // deg i = c} → ℝ),
      MeasurableSet D ∧ (∀ x : InfinitePlace I.F → {i : Fin (dimN I.n j) // deg i = c} → ℝ,
        ∃ γ ∈ Γ, (∀ v, uMat (γ v) - 1 ∈ (lowers (W v) c).restrictScalars ℝ) ∧
        (fun v (i : {i : Fin (dimN I.n j) // deg i = c}) =>
          (((uMat (γ v) - 1) * (B v i.1)ᴴ).trace).re + x v i) ∈ D) ∧
      volume D ≤ ENNReal.ofReal (Real.sqrt (2 ^ (I.f * ∑ b ∈ Finset.range m, r b * r (b + c + 1)) *
        ∏ b ∈ Finset.range m, Formalism.HermitianLatticesTheory.vInv I.E ^ (I.f * (r b * r (b + c + 1))) *
          (pieceHt (frm I (1, xf)) F b ^ r (b + c + 1) / pieceHt (frm I (1, xf)) F (b + c + 1) ^ r b))) := by
    intro c
    let crd : Matrix (Fin I.n) (Fin I.n) I.E →+
        (InfinitePlace I.F → {i : Fin (dimN I.n j) // deg i = c} → ℂ) :=
      { toFun := fun Y v i => ((I.P v)⁻¹ * Y.map (I.φ v) * I.P v * (B v i.1)ᴴ).trace
        map_zero' := by funext v i; simp
        map_add' := fun Y Y' => by
          funext v i
          simp [Matrix.map_add, Matrix.mul_add, Matrix.add_mul] }
    have c0 : ∀ Y v i, crd Y v i = ((I.P v)⁻¹ * Y.map (I.φ v) * I.P v * (B v i.1)ᴴ).trace :=
      fun _ _ _ => rfl
    have c1 : ∀ (x : 𝓞 I.E) Y v i, crd (x • Y) v i = I.φ v (x : I.E) * crd Y v i := by
      intro x Y v i
      have : (x • Y).map (I.φ v) = I.φ v (x : I.E) • Y.map (I.φ v) := by
        ext p q; simp [Algebra.smul_def]
      rw [c0, c0, this, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    have c2 : ∀ Y v i, crd (I.J⁻¹ * Yᴴ * I.J) v i = -starRingEnd ℂ (crd Y v i) := by
      intro Y v i
      rw [c0, c0, adj_frame I.J_det (hφ v) (I.P_unit v) (I.P_spec v), (hreal v ∅).2.2]
    have c3 : ∀ Y ∈ lowers F (c + 1), crd Y = 0 := by
      intro Y hY
      funext v i
      refine (hreal v {i | c + 1 ≤ deg i}).2.1 _ ?_ _ (by simp [i.2])
      rw [← hBs]
      exact (hWr v).2 _ Y hY
    let L : Submodule ℤ (InfinitePlace I.F → {i : Fin (dimN I.n j) // deg i = c} → ℂ) :=
      ((lowers F c).toAddSubgroup.map crd).toIntSubmodule
    have hL : ∀ z, z ∈ L ↔ ∃ Y ∈ lowers F c, crd Y = z := fun z => Iff.rfl
    obtain ⟨dL, lL, hcov⟩ := layer_covolume I.E htc _ I.n m _ I.φ I.P _ hX I.P_unit F r T T' Λ hT hΛ hFT
      U hU hUW B deg hB hBs c L (fun z => by
        rw [hL]
        refine exists_congr fun Y => and_congr_right fun _ => ?_
        exact ⟨fun h v i => by rw [← h]; rfl, fun h => funext fun v => funext fun i => (h v i).symm⟩)
    obtain ⟨D, hD1, hD2, hD3⟩ := real_domain I.E I.cm.cmUnram _ _ I.φ hX.1 L
      (fun x z hz => by
        obtain ⟨Y, hY, rfl⟩ := (hL z).1 hz
        exact (hL _).2 ⟨x • Y, Submodule.smul_mem _ _ hY, funext fun v => funext fun i => c1 x Y v i⟩)
      (fun z hz => by
        obtain ⟨Y, hY, rfl⟩ := (hL z).1 hz
        refine (hL _).2 ⟨_, neg_mem (hadjF c Y hY), funext fun v => funext fun i => ?_⟩
        rw [map_neg, Pi.neg_apply, Pi.neg_apply, c2, neg_neg])
    refine ⟨D, hD1, fun x => ?_, ?_⟩
    · obtain ⟨y, hy, hyD⟩ := hD2 x
      obtain ⟨Y, hY, hYy⟩ := (hL _).1 hy
      have hY' : w • Y ∈ lowers F c := Submodule.smul_mem _ _ hY
      have hX' := sub_mem hY' (hadjF c _ hY')
      obtain ⟨Z, hZ, hU'⟩ := GlobalTheory.T.exists_unitary_leading_term_of_skew_layer (𝓞 I.E) I.E I.n m I.J (lowers F) w hJ I.J_det hw
        (lowers_succ_le hF.1) (lowers_eq_bot hF.2.1 hF.2.2.1 hsp)
        (fun c X hX Y hY => lowers_mul_zero hX hY) hadjF c _ hX' (by
          have hu := I.J_det.isUnit
          rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_nonsing_inv, hJ, Matrix.conjTranspose_conjTranspose, Matrix.mul_sub,
            Matrix.sub_mul, neg_sub]
          simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu,
            Matrix.nonsing_inv_mul _ hu, Matrix.mul_one])
      have hcX : crd (w • Y - I.J⁻¹ * (w • Y)ᴴ * I.J) = fun v i => (y v i : ℂ) := by
        funext v i
        have h1 := congrArg (I.φ v) hw
        rw [map_add, hφ, map_one] at h1
        rw [map_sub, Pi.sub_apply, Pi.sub_apply, c2, c1, hYy, map_mul, Complex.conj_ofReal]
        linear_combination (y v i : ℂ) * h1
      generalize w • Y - I.J⁻¹ * (w • Y)ᴴ * I.J = X at hX' hU' hcX
      have hXZ : X + Z ∈ lowers F c := add_mem hX' (lowers_succ_le hF.1 c hZ)
      obtain ⟨g, hg, hgm⟩ := helt _ hU' (fun y hy => by
        rw [add_assoc, Matrix.add_mulVec, Matrix.one_mulVec]
        exact add_mem hy (hkeep c _ hXZ y hy))
      have hg1 : ∀ v, uMat (g v) - 1 = (I.P v)⁻¹ * (X + Z).map (I.φ v) * I.P v := by
        intro v
        rw [hgm, add_assoc, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _),
          Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
          Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)), add_sub_cancel_left]
      have hg2 : ∀ v, uMat (g v) - 1 ∈ lowers (W v) c := fun v => by
        rw [hg1]; exact (hWr v).2 _ _ hXZ
      refine ⟨g, (hΓ' g).2 ⟨hg, fun v => lowers_anti (hW v).1.1 (Nat.zero_le c) (hg2 v)⟩, hg2, ?_⟩
      convert hyD using 1
      funext v i
      rw [hg1, ← c0, map_add, c3 Z hZ, add_zero, hcX]
      simp
    · rw [hcov, hf2, hdeg, show Formalism.HermitianLatticesTheory.fDeg I.E = I.f from hf1] at hD3
      exact hD3
  choose D hD1 hD2 hD3 using hlayer
  have hnil := GlobalTheory.T.covolume_le_prod_layers_unipotent _ I.n (dimN I.n j) m I.ε (fun v c => (lowers (W v) c).restrictScalars ℝ) B deg
    (fun v c => lowers_succ_le (hW v).1.1 c) (fun v => by rw [hbot]; rfl)
    (fun v c X hX Y hY => lowers_mul_zero hX hY) hadj
    (fun v i k => by rw [hB]; split_ifs <;> simp)
    (fun v c X => by
      rw [← (hreal v _).1, ← hBs]; rfl) ν (fun v => by have := hν v; rwa [hN] at this) Γ D
    (fun γ hγ => ((hΓ' γ).1 hγ).2) hD1 hD2
  simp only [hN]
  refine le_trans (le_trans (covol_mono_left (fun g hg => ?_) _ _) hnil) ?_
  · obtain ⟨⟨γ, h1, h2, h3⟩, h4⟩ := (hΓ' g).1 hg
    exact ⟨γ, h1, h2, h3, h4⟩
  refine (Finset.prod_le_prod' fun c _ => hD3 c).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_prod_of_nonneg fun c _ => Real.sqrt_nonneg _]
  congr 1
  have hv : 0 < Formalism.HermitianLatticesTheory.vInv I.E := by
    have : 0 < |(discr I.E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero I.E)
    unfold Formalism.HermitianLatticesTheory.vInv
    positivity
  have hpos : ∀ b, 0 < pieceHt (frm I (1, xf)) F b := fun b => by
    have h := fun b => (Formalism.HN.plLat _ _ _ (bas I) (frm I (1, xf))
      (GlobalTheory.PointEquivariance.frm_det I (1, xf)) (F b) (Submodule.FG.of_le hfg (hle b))).2.2
    exact div_pos (h _) (h _)
  have hlp : 0 ≤ layerProd I.n I.f j
      (fun i => Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc)) id := by
    have := fun i => (hτ i).1
    unfold layerProd
    refine mul_nonneg (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun k _ => ?_)
      (Finset.prod_nonneg fun i _ => ?_)
    · have h1 := this i; have h2 := this k
      simp only [id]
      positivity
    · have := this i
      simp only [id]
      positivity
  rw [← Real.sqrt_prod _ (fun c _ => by
    have := hpos
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun b _ =>
      mul_nonneg (by positivity) (div_pos (pow_pos (hpos _) _) (pow_pos (hpos _) _)).le))]
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum]
  rw [← GlobalTheory.T.isotropicFlagUnipotentDim_eq_sum_pairs I.n a j r hrj hra hr0, GlobalTheory.T.prod_layer_height_quotients_eq_sq I.n I.f a j r _ _ hrj hra hr0 hτ hha hh1, ← mul_assoc,
    ← mul_pow, Real.sqrt_mul (by positivity), Real.sqrt_sq hlp, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  congr 2
  push_cast
  ring

end GlobalTheory.RadCov
