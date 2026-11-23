import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalGoodPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalGoodPlaceEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalUnramifiedVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalSphericalValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalLocalUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalDeterminedByUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinearRightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterAlmostUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalCharactersLinearBar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorSymplecticFormAtSplitFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

open GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PairingVecMulVec

theorem mul_vecMulVec_mul_transpose {K : Type} [CommRing K] {m n : ℕ} (A : Matrix (Fin m) (Fin m) K)
    (B : Matrix (Fin n) (Fin n) K) (p : Fin m → K) (w : Fin n → K) :
    A * Matrix.vecMulVec p w * Bᵀ = Matrix.vecMulVec (A *ᵥ p) (B *ᵥ w) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

theorem pairM_vecMulVec {K : Type} [CommRing K] {m n : ℕ} (Y : Matrix (Fin m) (Fin n) K) (a : Fin m → K)
    (b : Fin n → K) : GlobalTheory.FlipMatch.pairM Y (Matrix.vecMulVec a b) = a ⬝ᵥ (Y *ᵥ b) := by
  simp only [GlobalTheory.FlipMatch.pairM, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_vecMulVec {v : Pl F} {n d : ℕ} (x : Fin n → E) (z : Fin d → AE F E) (hz : At (evFin F v) z) :
    At (evFin F v) (Matrix.vecMulVec (incV F x) z) := by
  intro r hr
  have h := hz r hr
  ext i j
  have hj : r • z j = 0 := by simpa using congrFun h j
  rw [Matrix.smul_apply, Matrix.vecMulVec_apply, ← mul_smul_comm, hj, mul_zero, Matrix.zero_apply]

theorem map_vecMulVec {v : Pl F} {n d : ℕ} (τ : E →ₐ[F] Fv F v) (x : Fin n → E) (z : Fin d → AE F E) :
    (Matrix.vecMulVec (incV F x) z).map (piW τ) = Matrix.vecMulVec (fun i => τ (x i)) (fun j => piW τ (z j)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, incV, GlobalTheory.FlipMatch.SplitSymp.piW_incl]

end GlobalTheory.PairingVecMulVec

namespace GlobalTheory.PairingVecMulVec

set_option maxHeartbeats 1600000 in

theorem goodPlace_model : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₂ : ℕ) (H : Plane E a d₂), (d₂ + 2 = a ∧ form σ G.V.J H.x H.x = 0 ∧ form σ G.V.J H.y H.y = 0 ∧ form σ G.V.J H.x H.y = 1 ∧
          (∀ u, form σ G.V.J (H.ι *ᵥ u) H.x = 0 ∧ form σ G.V.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∃ (ν₀ β₀ : (Fv F B.v₁)ˣ →* ℂˣ) (ι : ((Fin a × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁) → ℂ))
      (ℓ : Fin a → Fv F B.v₁) (ψv : AddChar (Fv F B.v₁) ℂ),
      GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧ GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ ∧
      (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν₀ (unifAt B.v₁) : ℂ)) ^ m ≠ (r : ℂ)) ∧ ℓ ≠ 0 ∧ Continuous ψv ∧ ψv ≠ 1 ∧
      Set.BijOn ι (SB (Fin a × Fin (a + a') → Fv F B.v₁) : Set _) (SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁)) : Set _) ∧
      (∀ g' : GL (Fin a) (Fv F B.v₁), ∃ g ∈ UAt σ G.V (evFin F B.v₁), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), Acts (evFin F B.v₁) (om (g, 1)) φ φ₁ ∧ ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ g' 1 (ι φ)) ∧
      (∀ h' : GL (Fin (a + a')) (Fv F B.v₁), ∃ y ∈ UAt σ G.W (evFin F B.v₁), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), Acts (evFin F B.v₁) (om (1, y)) φ φ₁ ∧ ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h' (ι φ)) ∧
      (∀ z : Fin (a + a') → Fv F B.v₁, ∃ u ∈ {u : Matrix (Fin a) (Fin (a + a')) (AE F E) | ∃ z, u = Matrix.vecMulVec (incV F H.x) z},
        At (evFin F B.v₁) u ∧ ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁),
          Acts (evFin F B.v₁) (G.M.co.rho B.ψ u) φ φ₁ ∧ ι φ₁ = fun Y => ψv (ℓ ⬝ᵥ (Y *ᵥ z)) * ι φ Y) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hTr d₂ H hH
  obtain ⟨-, -, -, hxy, -, -⟩ := hH
  have hP := hK.base
  have hv : X.Good B.v₁ := hTr.chars.good
  obtain ⟨t, ι, hι⟩ := GlobalTheory.T.exists_linear_functional_good_place hP F E σ B a a' G X om om' hTr B.v₁ hv
  obtain ⟨ν₀, hV⟩ := GlobalTheory.T.linear_weil_functional_spherical_value hP F E σ B a a' G X om om' hTr B.v₁ hv t ι hι
    (GlobalTheory.T.linear_weil_functional_good_place_equivariant hP F E σ B a a' G X om om' hTr B.v₁ hv t ι hι)
  obtain ⟨t', ht'⟩ := GlobalTheory.T.linear_weil_functional_local_uniqueness hP F E σ B a a' G X om om' hTr B.v₁ hv t ι hι ν₀ hV
  obtain ⟨β₀, hW⟩ := GlobalTheory.T.linear_weil_functional_translation_equivariant hP F E σ B a a' G X om om' hTr B.v₁ hv t ι hι
    (GlobalTheory.T.linear_weil_functional_unramified_vector hP F E σ B a a' G X om om' hTr B.v₁ hv t ι hι)
  obtain ⟨hβs, hβu⟩ := GlobalTheory.T.linear_weil_functional_determined_by_unramified hP F E σ B a a' G X om om' hTr B.v₁ hv t ι hι β₀ hW
  obtain ⟨hs, hu⟩ := GlobalTheory.T.local_character_smooth_unitary hP F E σ B a a' G X om om' hTr B.v₁ hv t'
  have hνs : GlobalTheory.SmGL.IsSmoothChar ν₀ := by
    rcases ht' with h | h
    · rw [h]; exact hs
    · rw [h]; exact GlobalTheory.WeilLinA.isSmoothChar_inv _ hs
  have hνu : GlobalTheory.SmGL.IsUnitaryChar ν₀ := by
    rcases ht' with h | h
    · rw [h]; exact hu
    · rw [h]; exact GlobalTheory.WeilLinA.isUnitaryChar_inv _ hu
  have hloc := (GlobalTheory.T.theta_action_exists hP) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1 B.v₁

  have hnr : ∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν₀ (unifAt B.v₁) : ℂ)) ^ m ≠ (r : ℂ) := by
    intro m hm r h
    have hr : |r| = 1 := by
      have := congrArg norm h
      rw [norm_pow, hνu, one_pow, Complex.norm_real, Real.norm_eq_abs] at this
      exact this.symm
    have key : (ν₀ (unifAt B.v₁)) ^ (2 * m) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, pow_mul', h]
      rw [← Complex.ofReal_pow, ← sq_abs, hr, one_pow, Complex.ofReal_one]
    have hk : ((2 * m : ℕ) : ℤ) ≠ 0 := by omega
    rcases ht' with h' | h'
    · apply GlobalTheory.T.character_at_uniformizer_not_root_of_unity F E σ B a a' G X om om' hTr B.v₁ hv t' _ hk
      rw [zpow_natCast, ← h', key]
    · apply GlobalTheory.T.character_at_uniformizer_not_root_of_unity F E σ B a a' G X om om' hTr B.v₁ hv t' _ (neg_ne_zero.mpr hk)
      rw [zpow_neg, zpow_natCast, ← inv_pow, ← MonoidHom.inv_apply, ← h', key]

  have hcont : Continuous (GlobalTheory.VacAny.psiV B.ψ B.v₁) := GlobalTheory.VacAny.continuous_psiV hTr.base.std.1 B.v₁
  have hne : GlobalTheory.VacAny.psiV B.ψ B.v₁ ≠ 1 := by
    obtain ⟨x, hx⟩ := (GlobalTheory.T.standard_character_almost_unramified F B.ψ hTr.base.std).2 B.v₁
    intro h
    apply hx
    rw [← GlobalTheory.VacAny.psiV_eq_psiLoc, h, AddChar.one_apply]

  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have ht : Function.Injective t := t.toRingHom.injective
  have hVd : G.V.J.det ≠ 0 := GlobalTheory.LagrCoord.det_ne_zero_of_map G.V.J (B.emb w₀).1
    (GlobalTheory.LagrCoord.det_ne_zero_of_hasSig (hTr.geo.hV.sig w₀))
  have hWd : G.W.J.det ≠ 0 := GlobalTheory.LagrCoord.det_ne_zero_of_map G.W.J (B.emb w₀).1
    (GlobalTheory.LagrCoord.det_ne_zero_of_hasSig_smul (hTr.geo.hW.sig w₀))
  have hVt : (G.V.J.map t).det ≠ 0 := by
    intro h0; apply hVd; apply ht
    rw [map_zero, ← h0]; exact RingHom.map_det t.toRingHom G.V.J
  have hWt : IsUnit (G.W.J.map t).det := by
    rw [isUnit_iff_ne_zero]
    intro h0; apply hWd; apply ht
    rw [map_zero, ← h0]; exact RingHom.map_det t.toRingHom G.W.J

  set p : Fin a → Fv F B.v₁ := fun i => t (σ (H.x i)) with hp
  set ℓ : Fin a → Fv F B.v₁ := -(G.V.J.map t *ᵥ p) with hℓ
  have hℓ0 : ℓ ≠ 0 := by
    intro h0
    have h1 : G.V.J.map t *ᵥ p = 0 := by rw [hℓ] at h0; exact neg_eq_zero.mp h0
    have hp0 : p = 0 := by
      by_contra hpn
      exact hVt (Matrix.exists_mulVec_eq_zero_iff.mp ⟨p, hpn, h1⟩)
    have hx0 : H.x = 0 := by
      funext i
      have := congrFun hp0 i
      simp only [hp, Pi.zero_apply] at this
      exact (map_eq_zero_iff σ σ.toRingHom.injective).mp ((map_eq_zero_iff t ht).mp this)
    rw [hx0] at hxy
    simp [form] at hxy
  refine ⟨ν₀, β₀, ι, ℓ, GlobalTheory.VacAny.psiV B.ψ B.v₁, hνs, hνu, hβs, hβu, hnr, hℓ0, hcont, hne, hι.bij, ?_, ?_, ?_⟩
  · intro g'
    obtain ⟨g, hg, hgt⟩ := GlobalTheory.T.local_unitary_group_surjects_general_linear hP F E σ B a a' G X om om' hTr B.v₁ hv t g'
    refine ⟨g, hg, fun φ hφ => ?_⟩
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc.1 g hg 1 (GlobalTheory.WeilLinA.one_mem_UAt σ G.W _) φ hφ
    obtain ⟨g'', hg'', hgeq⟩ := hV g hg
    have : g'' = g' := Units.ext (hg''.symm.trans hgt)
    subst this
    exact ⟨φ₁, hφ₁, hA, by rw [hgeq φ hφ φ₁ hφ₁ hA, GlobalTheory.WeilLinA.omA_h_one ν₀ β₀]⟩
  · intro h'
    obtain ⟨h, hh, hht⟩ := GlobalTheory.T.local_unitary_group_surjects_general_linear_right hP F E σ B a a' G X om om' hTr B.v₁ hv t h'
    refine ⟨h, hh, fun φ hφ => ?_⟩
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc.1 1 (GlobalTheory.WeilLinA.one_mem_UAt σ G.V _) h hh φ hφ
    obtain ⟨h'', hh'', hheq⟩ := hW h hh
    have : h'' = h' := Units.ext (hh''.symm.trans hht)
    subst this
    exact ⟨φ₁, hφ₁, hA, by rw [hheq φ hφ φ₁ hφ₁ hA, GlobalTheory.WeilLinA.omA_g_one ν₀ β₀]⟩
  · intro z
    set w : Fin (a + a') → Fv F B.v₁ := (G.W.J.map t)⁻¹ *ᵥ z with hw
    have hKw : G.W.J.map t *ᵥ w = z := by
      rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hWt, Matrix.one_mulVec]
    obtain ⟨U, hUat, hU0, hU1⟩ := GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hTr.base.cm B.v₁ t (0 : Matrix (Fin 1) (Fin (a + a')) (Fv F B.v₁))
      (Matrix.of fun _ j => w j)
    set u : Matrix (Fin a) (Fin (a + a')) (AE F E) := Matrix.vecMulVec (incV F H.x) (U 0) with hu
    have hU0at : At (evFin F B.v₁) (U 0) := by
      intro r hr
      have := hUat r hr
      exact congrFun this 0
    have huat : At (evFin F B.v₁) u := at_vecMulVec H.x (U 0) hU0at
    have hut : u.map (piW t) = 0 := by
      rw [hu, map_vecMulVec]
      ext i j
      have := congrFun (congrFun hU0 0) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at this
      simp only [Matrix.vecMulVec_apply, this, mul_zero, Matrix.zero_apply]
    have huσ : u.map (piW (t.comp σ)) = Matrix.vecMulVec p w := by
      rw [hu, map_vecMulVec]
      ext i j
      have := congrFun (congrFun hU1 0) j
      simp only [Matrix.map_apply, Matrix.of_apply] at this
      simp only [Matrix.vecMulVec_apply, this, hp, AlgHom.comp_apply]
    refine ⟨u, ⟨U 0, rfl⟩, huat, fun φ hφ => ?_⟩
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc.2.1 u huat φ hφ
    refine ⟨φ₁, hφ₁, hA, funext fun Y => ?_⟩
    obtain ⟨x, hxat, hx0, hx1⟩ := GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hTr.base.cm B.v₁ t Y (0 : Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁))
    have hm := hι.mult u huat hut φ hφ φ₁ hφ₁ hA x hxat hx1
    have e : ((1 : GL (Fin a) (Fv F B.v₁))⁻¹).1 * x.map (piW t) * ((1 : GL (Fin (a + a')) (Fv F B.v₁))⁻¹).1ᵀ = Y := by
      simp [hx0]
    rw [e] at hm
    rw [hm, GlobalTheory.FlipMatch.SplitSymp.symp_at_split hTr.base.cm G.V G.W hTr.geo.hV.herm hTr.geo.hW.skew B.ψ t 1 1 x u
      hxat huat]
    have hcx : GlobalTheory.FlipMatch.coX t 1 1 x = Y := by simpa [GlobalTheory.FlipMatch.coX] using e
    have hcu : GlobalTheory.FlipMatch.coX t 1 1 u = 0 := by simp [GlobalTheory.FlipMatch.coX, hut]
    have hcyx : GlobalTheory.FlipMatch.coY σ G.V G.W t 1 1 x = 0 := by simp [GlobalTheory.FlipMatch.coY, hx1]
    have hcyu : GlobalTheory.FlipMatch.coY σ G.V G.W t 1 1 u =
        -Matrix.vecMulVec (G.V.J.map t *ᵥ p) (G.W.J.map t *ᵥ w) := by
      simp only [GlobalTheory.FlipMatch.coY, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, huσ,
        mul_vecMulVec_mul_transpose]
    have key : GlobalTheory.FlipMatch.pairM (GlobalTheory.FlipMatch.coX t 1 1 x) (GlobalTheory.FlipMatch.coY σ G.V G.W t 1 1 u) -
        GlobalTheory.FlipMatch.pairM (GlobalTheory.FlipMatch.coY σ G.V G.W t 1 1 x) (GlobalTheory.FlipMatch.coX t 1 1 u) = ℓ ⬝ᵥ (Y *ᵥ z) := by
      rw [hcx, hcu, hcyx, hcyu, hKw, hℓ, neg_dotProduct, ← pairM_vecMulVec]
      simp only [GlobalTheory.FlipMatch.pairM, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, Matrix.zero_apply, mul_zero,
        Finset.sum_const_zero, sub_zero]
    rw [key]
    rfl

end GlobalTheory.PairingVecMulVec
