import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviIsoPlaneUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightWittEmbeddingLeConstMul
open scoped TensorProduct NNReal Matrix ContDiff
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.DescB.GenGrowth

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem exp_block {n n₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) ℂ) (π : Matrix (Fin n₁) (Fin n) ℂ) (h : π * ι = 1)
    (Z : Matrix (Fin n₁) (Fin n₁) ℂ) :
    NormedSpace.exp (ι * Z * π) = (1 - ι * π) + ι * NormedSpace.exp Z * π := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  haveI : CompleteSpace (Matrix (Fin n₁) (Fin n₁) ℂ) := FiniteDimensional.complete ℝ _
  have h' : ∀ {k : ℕ} (X : Matrix (Fin n₁) (Fin k) ℂ), π * (ι * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  let f : Matrix (Fin n₁) (Fin n₁) ℂ × ℂ →+* Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun p => p.2 • (1 - ι * π) + ι * p.1 * π
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, h', Matrix.one_mul, Matrix.mul_one, sub_self, smul_zero,
          add_zero, zero_add, sub_zero, smul_smul, smul_sub]
        module
      map_zero' := by simp
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, add_smul, Matrix.mul_add, Matrix.add_mul]; abel }
  have hf : Continuous f :=
    (continuous_snd.smul continuous_const).add ((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const)
  have e := NormedSpace.map_exp f hf (Z, 0)
  have e1 : f (Z, 0) = ι * Z * π := by simp [f]
  rw [e1] at e
  refine e.symm.trans ?_
  show (NormedSpace.exp ((Z, 0) : Matrix (Fin n₁) (Fin n₁) ℂ × ℂ)).2 • (1 - ι * π) +
    ι * (NormedSpace.exp ((Z, 0) : Matrix (Fin n₁) (Fin n₁) ℂ × ℂ)).1 * π = _
  have a1 := NormedSpace.map_exp (RingHom.fst (Matrix (Fin n₁) (Fin n₁) ℂ) ℂ) continuous_fst (Z, 0)
  have a2 := NormedSpace.map_exp (RingHom.snd (Matrix (Fin n₁) (Fin n₁) ℂ) ℂ) continuous_snd (Z, 0)
  exact congrArg₂ (· + ·) ((congrArg (· • (1 - ι * π)) (a2.trans NormedSpace.exp_zero)).trans (one_smul _ _))
    (congrArg (ι * · * π) a1)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_proj (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {H : Plane E n n₁} {W : Spc F E n} {W₁ : Spc F E n₁}
    (h : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0) :
    ∃ π : Matrix (Fin n₁) (Fin n) E, π * H.ι = 1 ∧ H.ιᵀ * W.J = W₁.J * π.map σ ∧
      ∀ (h₁ : UA σ W₁.J) (m : UA σ W.J), IsLevi (W₁ := W₁) H 1 h₁ m → mat m = incM F (1 - H.ι * π) + incM F H.ι * mat h₁ * incM F π := by
  choose α β z hz using fun j : Fin n => GlobalTheory.UnipCocptForm.decomp σ W.J W₁.J H.x H.y H.ι hsk hσ h.1 h.2.1 h.2.2.1
    h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 hd (Pi.single j 1)
  let π : Matrix (Fin n₁) (Fin n) E := Matrix.of fun i j => z j i
  have e : (1 : Matrix (Fin n) (Fin n) E) = Matrix.vecMulVec H.x α + Matrix.vecMulVec H.y β + H.ι * π := by
    ext i j
    have := congrFun (hz j) i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Matrix.mulVec, dotProduct] at this
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, π, Matrix.of_apply, Matrix.one_apply, this]
    ring
  have hv : ∀ v a : Fin n → E, (∀ u, form σ W.J (H.ι *ᵥ u) v = 0) →
      H.ιᵀ * W.J * (Matrix.vecMulVec v a).map σ = 0 := fun v a hv => by
    ext i j
    have := hv (Pi.single i 1)
    rw [Matrix.mulVec_single_one] at this
    simp only [form, dotProduct, Matrix.mulVec, Matrix.col, Matrix.transpose_apply,
      Finset.mul_sum] at this
    rw [Finset.sum_comm] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, Matrix.transpose_apply,
      Matrix.zero_apply, ← mul_assoc, ← Finset.sum_mul]
    simp only [← mul_assoc, ← Finset.sum_mul] at this
    rw [this, zero_mul]
  have e2 : H.ιᵀ * W.J = W₁.J * π.map σ := by
    have e3 := congrArg (fun X : Matrix (Fin n) (Fin n) E => H.ιᵀ * W.J * X.map σ) e
    simp only [Matrix.map_add _ (map_add σ), Matrix.mul_add, hv _ _ fun u => (h.2.2.2.2.1 u).1,
      hv _ _ fun u => (h.2.2.2.2.1 u).2, zero_add, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.mul_one] at e3
    rw [e3, Matrix.map_mul, ← Matrix.mul_assoc, h.2.2.2.2.2]
  have e4 : π * H.ι = 1 := by
    have e5 : W₁.J * (π * H.ι).map σ = W₁.J * (1 : Matrix (Fin n₁) (Fin n₁) E).map σ := by
      rw [Matrix.map_mul, ← Matrix.mul_assoc, ← e2, h.2.2.2.2.2, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.mul_one]
    have hu : IsUnit W₁.J := (Matrix.isUnit_iff_isUnit_det _).2 (IsUnit.mk0 _ hd)
    exact Matrix.map_injective (Function.LeftInverse.injective hσ) (hu.mul_left_cancel e5)
  refine ⟨π, e4, e2, fun h₁ m hm => ?_⟩
  obtain ⟨ax, ay, aι⟩ := hm
  simp only [inv_one, Units.val_one, map_one, one_smul] at ax ay
  have hvv : ∀ v a : Fin n → E, incM F (Matrix.vecMulVec v a) = Matrix.vecMulVec (incV F v) (incV F a) := fun v a =>
    Matrix.ext fun i j => map_mul (inclR (F := F) (AF F)) _ _
  have e6 : 1 - H.ι * π = Matrix.vecMulVec H.x α + Matrix.vecMulVec H.y β := by rw [sub_eq_iff_eq_add]; exact e
  have e7 : (1 : Matrix (Fin n) (Fin n) (AE F E)) = Matrix.vecMulVec (incV F H.x) (incV F α) +
      Matrix.vecMulVec (incV F H.y) (incV F β) + incM F H.ι * incM F π := by
    have := congrArg (incM F) e
    rw [← hvv, ← hvv]
    simpa only [incM, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] using this
  have e8 : incM F (1 - H.ι * π) = Matrix.vecMulVec (incV F H.x) (incV F α) +
      Matrix.vecMulVec (incV F H.y) (incV F β) := by
    rw [e6, ← hvv, ← hvv]; exact Matrix.map_add _ (map_add _) _ _
  rw [e8, ← aι]
  conv_lhs => rw [← Matrix.mul_one (mat m), e7]
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, ax, ay, Matrix.mul_assoc]

theorem isRealLine_conj {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (a : GAd σ J) :
    IsRealLine σ J fun t => a⁻¹ * γ t * a := by
  obtain ⟨w, τ, Z, hZ, hγ⟩ := hγ
  have hu : ∀ x : GArch σ J w, (GlobalTheory.Orb.archMat σ J τ x)ᴴ * J.map τ.1 * GlobalTheory.Orb.archMat σ J τ x = J.map τ.1 :=
    fun x => (archEquiv J h τ x).2
  have h1 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have u1 := hu (projArch σ J w a)
  have u2 := hu (projArch σ J w a)⁻¹
  refine ⟨w, τ, GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * Z * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a), ?_,
    fun t => ?_⟩
  · generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
    generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
    generalize J.map τ.1 = Q at u1 u2 hZ ⊢
    have e1 : M'ᴴ * Q = Q * M := by
      conv_rhs => rw [← u2, Matrix.mul_assoc, h1, Matrix.mul_one]
    have e2 : Q * M' = Mᴴ * Q := by
      conv_lhs => rw [← u1, Matrix.mul_assoc, h2, Matrix.mul_one]
    calc (M' * Z * M)ᴴ * Q + Q * (M' * Z * M) = Mᴴ * Zᴴ * (M'ᴴ * Q) + (Q * M') * Z * M := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Mᴴ * (Zᴴ * Q + Q * Z) * M := by
          rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨y, e1, e2⟩ := hγ t
    refine ⟨(projArch σ J w a)⁻¹ * y * projArch σ J w a, ?_, ?_⟩
    · show a⁻¹ * γ t * a = _
      rw [e1]
      refine GAd_ext σ J (fun u => ?_) fun v => by simp
      by_cases e : u = w
      · subst e; simp
      · simp [projArch_embArch_ne σ J e]
    · rw [map_mul, map_mul, e2]
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
      have hM : IsUnit M := ⟨⟨M, M', h2, h1⟩, rfl⟩
      rw [← Matrix.inv_eq_left_inv h1, ← Matrix.exp_conj' _ _ hM, Matrix.mul_smul, Matrix.smul_mul]

theorem isRealLine_block (h : IsCMExt F E σ) {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E}
    {ι : Matrix (Fin n) (Fin n₁) E} {π : Matrix (Fin n₁) (Fin n) E} (h1 : π * ι = 1)
    (h2 : (ι.map σ)ᵀ * J = J₁ * π) (h3 : J * ι = (π.map σ)ᵀ * J₁) (M : GAd σ J₁ → GAd σ J)
    (hM : ∀ x, (matHom _ σ J (M x)).1 = adMat F (1 - ι * π) + adMat F ι * (matHom _ σ J₁ x).1 * adMat F π)
    {γ : ℝ → GAd σ J₁} (hγ : IsRealLine σ J₁ γ) : IsRealLine σ J fun t => M (γ t) := by
  obtain ⟨w, τ, Z, hZ, hγ⟩ := hγ
  have hone : adMat F (1 - ι * π) + adMat F ι * (1 : Matrix (Fin n₁) (Fin n₁) (AF F ⊗[F] E)) * adMat F π = 1 := by
    rw [Matrix.mul_one, adMat, adMat, adMat, ← Matrix.map_mul, ← Matrix.map_add _ (map_add _), sub_add_cancel,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have key : ∀ {R : Type} [CommRing R] (φ : AF F ⊗[F] E →+* R) (x : GAd σ J₁), (matHom _ σ J₁ x).1.map φ = 1 →
      (matHom _ σ J (M x)).1.map φ = 1 := fun φ x hx => by
    rw [hM, GlobalTheory.EmbHeight.map_aff, hx, ← Matrix.map_one φ (map_zero _) (map_one _), ← GlobalTheory.EmbHeight.map_aff, hone,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hs : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) E), ((X.map σ)ᵀ).map τ.1 = (X.map τ.1)ᴴ := fun X =>
    Matrix.ext fun i j => h.2.2.2 τ.1 (X j i)
  have g1 : π.map τ.1 * ι.map τ.1 = 1 := by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have g2 : (ι.map τ.1)ᴴ * J.map τ.1 = J₁.map τ.1 * π.map τ.1 := by rw [← hs, ← Matrix.map_mul, h2, Matrix.map_mul]
  have g3 : J.map τ.1 * ι.map τ.1 = (π.map τ.1)ᴴ * J₁.map τ.1 := by rw [← hs, ← Matrix.map_mul, h3, Matrix.map_mul]
  refine ⟨w, τ, ι.map τ.1 * Z * π.map τ.1, ?_, fun t => ?_⟩
  · calc _ = (π.map τ.1)ᴴ * Zᴴ * ((ι.map τ.1)ᴴ * J.map τ.1) + (J.map τ.1 * ι.map τ.1) * Z * π.map τ.1 := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (π.map τ.1)ᴴ * (Zᴴ * J₁.map τ.1 + J₁.map τ.1 * Z) * π.map τ.1 := by
          rw [g2, g3]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨y, e1, e2⟩ := hγ t
    refine ⟨projArch σ J w (M (γ t)), GAd_ext σ J (fun u => ?_) fun v => ?_, ?_⟩
    · by_cases e : u = w
      · subst e; simp
      · rw [projArch_embArch_ne σ J e]
        have : projArch σ J₁ u (γ t) = 1 := by rw [e1, projArch_embArch_ne σ J₁ e]
        exact Subtype.ext (Units.ext (key (compInf F E u) (γ t) (congrArg (fun z => z.1.1) this)))
    · have : proj σ J₁ v (γ t) = 1 := by rw [e1]; simp
      rw [show proj σ J v (embArch σ J w (projArch σ J w (M (γ t)))) = 1 by simp]
      exact Subtype.ext (Units.ext (key (compFin F E v) (γ t) (congrArg (fun z => z.1.1) this)))
    · let φ := (infEmb τ).comp (compInf F E w)
      have h0 : ∀ x : E, φ (inclR (F := F) (AF F) x) = τ.1 x := fun x => by
        change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
        simp
      have h4 : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) E), (adMat F X).map φ = X.map τ.1 := fun X =>
        Matrix.ext fun i j => h0 _
      have h5 : (matHom _ σ J₁ (γ t)).1.map φ = NormedSpace.exp (t • Z) := by
        rw [← e2, ← projArch_embArch_self σ J₁ w y, ← e1]; rfl
      show (matHom _ σ J (M (γ t))).1.map φ = _
      rw [hM, GlobalTheory.EmbHeight.map_aff, h4, h4, h4, h5, ← Matrix.smul_mul, ← Matrix.mul_smul, exp_block _ _ g1,
        Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul]

omit [NumberField E] in

theorem foldr_lineDer_hom {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E}
    (M : GAd σ J₁ →* GAd σ J) (a : GAd σ J) (f : GAd σ J → ℂ) (l : List (ℝ → GAd σ J₁)) :
    l.foldr lineDer (fun x => f (M x * a)) =
      fun x => (l.map fun γ t => a⁻¹ * M (γ t) * a).foldr lineDer f (M x * a) := by
  induction l with
  | nil => rfl
  | cons γ l ih =>
    rw [List.foldr_cons, ih, List.map_cons, List.foldr_cons]
    funext g
    simp only [lineDer]
    congr 1
    funext t
    simp [mul_assoc]

theorem one_mem_kInf {n : ℕ} (Y : Spc F E n) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    (1 : UA σ Y.J) ∈ KInf σ Y τ := by
  have h1 : mat (1 : UA σ Y.J) = 1 := rfl
  refine ⟨?_, fun w => ?_⟩
  · show At (evI F) (mat (1 : UA σ Y.J) - 1)
    rw [h1, sub_self]
    unfold At
    simp
  · rw [h1, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Commute.one_left _

theorem growth_block (h : IsCMExt F E σ) {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E}
    {ι : Matrix (Fin n) (Fin n₁) E} {π : Matrix (Fin n₁) (Fin n) E} (h1 : π * ι = 1)
    (h2 : (ι.map σ)ᵀ * J = J₁ * π) (h3 : J * ι = (π.map σ)ᵀ * J₁) (M : GAd σ J₁ →* GAd σ J)
    (hM : ∀ x, (matHom _ σ J (M x)).1 = adMat F (1 - ι * π) + adMat F ι * (matHom _ σ J₁ x).1 * adMat F π)
    (a : GAd σ J) {f : GAd σ J → ℂ} {N : ℕ} (hN : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∃ C : ℝ, ∀ g, ‖l.foldr lineDer f g‖ ≤ C * (height σ J g : ℝ) ^ N)
    (l : List (ℝ → GAd σ J₁)) (hl : ∀ γ ∈ l, IsRealLine σ J₁ γ) :
    ∃ C : ℝ, ∀ x, ‖l.foldr lineDer (fun x => f (M x * a)) x‖ ≤ C * (height σ J₁ x : ℝ) ^ N := by
  obtain ⟨K, hK⟩ := GlobalTheory.EmbHeight.exists_heightGL_aff_le F (adMat F (1 - ι * π)) (adMat F ι) (adMat F π)
  have hK' : ∀ x, height σ J (M x) ≤ K * height σ J₁ x := fun x =>
    hK _ _ (hM x) (by rw [← map_inv, ← map_inv, ← map_inv]; exact hM x⁻¹)
  obtain ⟨C, hC⟩ := hN (l.map fun γ t => a⁻¹ * M (γ t) * a) (by
    intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hγ'
    exact isRealLine_conj h (isRealLine_block h h1 h2 h3 M hM (hl γ hγ)) a)
  refine ⟨max C 0 * ((K : ℝ) * (height σ J a : ℝ)) ^ N, fun x => ?_⟩
  rw [foldr_lineDer_hom M a f l]
  have hh : (height σ J (M x * a) : ℝ) ≤ ((K : ℝ) * (height σ J a : ℝ)) * (height σ J₁ x : ℝ) := by
    have := (height_mul_le σ J (M x) a).trans (mul_le_mul' (hK' x) le_rfl)
    rw [mul_right_comm] at this
    exact_mod_cast this
  have h0 : (0 : ℝ) ≤ (height σ J (M x * a) : ℝ) := by positivity
  refine (hC _).trans ((mul_le_mul_of_nonneg_right (le_max_left C 0) (pow_nonneg h0 N)).trans ?_)
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hh N) (le_max_right _ _)

omit [NumberField F] [NumberField E] in

theorem gram_rel (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E}
    {ι : Matrix (Fin n) (Fin n₁) E} {π : Matrix (Fin n₁) (Fin n) E} (hsk : ∀ i j, σ (J j i) = -J i j)
    (hsk₁ : ∀ i j, σ (J₁ j i) = -J₁ i j) (p2 : ιᵀ * J = J₁ * π.map σ) (c : E) :
    (ι.map σ)ᵀ * (c • J.map σ) = (c • J₁.map σ) * π ∧ (c • J.map σ) * ι = (π.map σ)ᵀ * (c • J₁.map σ) := by
  have hmm : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) E), (X.map σ).map σ = X := fun X => Matrix.ext fun i j => hσ _
  constructor
  · have := congrArg (fun X : Matrix (Fin n₁) (Fin n) E => X.map σ) p2
    simp only [Matrix.map_mul, hmm] at this
    rw [Matrix.mul_smul, Matrix.smul_mul, ← this]; rfl
  · have := congrArg Matrix.transpose p2
    have t1 : J.map σ = -Jᵀ := Matrix.ext fun i j => hsk j i
    have t2 : J₁.map σ = -J₁ᵀ := Matrix.ext fun i j => hsk₁ j i
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at this
    rw [Matrix.mul_smul, Matrix.smul_mul, t1, t2, Matrix.neg_mul, Matrix.mul_neg, this]

theorem exists_hom_move (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E)
    {c : E} (hc : c ≠ 0) (M₀ : UA σ J₁ →* UA σ J) :
    ∃ M : GAd σ (c • J₁.map σ) →* GAd σ (c • J.map σ),
      (∀ x, (toGAd hσ J hc).symm (M x) = M₀ ((toGAd hσ J₁ hc).symm x)) ∧
      (∀ x, (matHom _ σ _ (M x)).1 = mat (M₀ ((toGAd hσ J₁ hc).symm x))) ∧
      ∀ x, (matHom _ σ _ x).1 = mat ((toGAd hσ J₁ hc).symm x) :=
  ⟨(toGAd hσ J hc).toMonoidHom.comp (M₀.comp (toGAd hσ J₁ hc).symm.toMonoidHom),
    fun _ => (toGAd hσ J hc).symm_apply_apply _, fun _ => rfl, fun _ => rfl⟩

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E), B.IsGood σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (P : Plane E n n₁), (∀ i j, σ (Y.J j i) = -Y.J i j) →
      IsIsoPlane σ B P Y Y₁ →
      ∀ (c : E) (hc : c ≠ 0), σ c = -c →
      ∀ fa : UA σ Y.J → ℂ, (∀ K : Subgroup (GAd σ (c • Y.J.map σ)), (∀ x ∈ K, (toGAd hσ Y.J hc).symm x ∈ KInf σ Y B.emb) →
        IsAutOn σ (c • Y.J.map σ) ((unip σ Y P).map (toGAd hσ Y.J hc).toMonoidHom) K (fun x => fa ((toGAd hσ Y.J hc).symm x))) →
      ∀ h ∈ finK σ Y B.emb, (∀ h₁ : UA σ Y₁.J, ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) P 1 h₁ m) →
      ∀ g : UA σ Y₁.J → ℂ, (∀ h₁ m, IsLevi (W₁ := Y₁) P 1 h₁ m → g h₁ = fa (m * h)) →
      ∃ N : ℕ, ∀ l : List (ℝ → GAd σ (c • Y₁.J.map σ)), (∀ γ ∈ l, IsRealLine σ (c • Y₁.J.map σ) γ) →
        ∃ C : ℝ, ∀ x, ‖l.foldr lineDer (fun x => g ((toGAd hσ Y₁.J hc).symm x)) x‖ ≤ C * (height σ (c • Y₁.J.map σ) x : ℝ) ^ N := by
  intro F E _ _ _ _ _ σ hσ B hB n n₁ Y Y₁ P hsk hP c hc _ fa hfa h _ _ g hg
  have hd : Y₁.J.det ≠ 0 := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    exact GlobalTheory.LeviUniqueCartan.det_ne_zero_of_isCartan _ _ _ (hP.2.2.2.2.2.2.2 w)
  have hH := GlobalTheory.ThK.GLTwo.IsIsoPlane.isHypPlane hP
  obtain ⟨M₀, -, hM₀, -⟩ := hH.exists_leviHom hσ hsk hd
  obtain ⟨π, p1, p2, p3⟩ := exists_proj hσ hH hsk hd
  obtain ⟨q2, q3⟩ := gram_rel hσ hsk (hH.skew hσ hsk) p2 c
  obtain ⟨N, hN⟩ := (hfa ⊥ fun x hx => by
    rw [Subgroup.mem_bot.1 hx, map_one]; exact one_mem_kInf Y B.emb).growth
  obtain ⟨M, m1, m2, m3⟩ := exists_hom_move hσ Y.J Y₁.J hc M₀
  refine ⟨N, fun l hl => ?_⟩
  have hgf : (fun x => g ((toGAd hσ Y₁.J hc).symm x)) = fun x => fa ((toGAd hσ Y.J hc).symm (M x * toGAd hσ Y.J hc h)) :=
    funext fun x => by rw [hg _ _ (hM₀ _), map_mul, m1, MulEquiv.symm_apply_apply]
  have hM : ∀ x, (matHom _ σ _ (M x)).1 =
      adMat F (1 - P.ι * π) + adMat F P.ι * (matHom _ σ _ x).1 * adMat F π := fun x => by
    rw [m2, m3, p3 _ _ (hM₀ _)]
    rfl
  rw [hgf]
  exact growth_block (f := fun x => fa ((toGAd hσ Y.J hc).symm x)) hB.cm p1 q2 q3 M hM (toGAd hσ Y.J hc h) hN l hl

end GlobalTheory.ThK.DescB.GenGrowth

end
