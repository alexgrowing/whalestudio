import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatBoundTuple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviEmbHC

open Matrix GlobalTheory.DoubledPlaneEmb

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem exp_sandwich {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    (A : Matrix m k ℂ) (B : Matrix k m ℂ) (hBA : B * A = 1) (X : Matrix k k ℂ) :
    NormedSpace.exp (A * X * B) = extM A B (NormedSpace.exp X) := by
  have hpow : ∀ j : ℕ, (A * X * B) ^ (j + 1) = A * X ^ (j + 1) * B := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ih, pow_succ X (j + 1)]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc B A, hBA, Matrix.one_mul]
  let L : Matrix k k ℂ →+ Matrix m m ℂ :=
    { toFun := fun Y => A * Y * B
      map_zero' := by simp
      map_add' := fun Y Z => by simp [Matrix.mul_add, Matrix.add_mul] }
  have hL : Continuous L := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h3 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X).map L hL
  have h4 : HasSum (fun n : ℕ => if n = 0 then (1 - A * B : Matrix m m ℂ) else 0) (1 - A * B) :=
    hasSum_ite_eq 0 _
  have h5 := h3.add h4
  have e : (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (A * X * B) ^ n) =
      fun n => (L ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • X ^ n) n + (if n = 0 then (1 - A * B) else 0) := by
    funext n
    cases n with
    | zero => simp [L]
    | succ j => simp [L, hpow, Matrix.mul_smul, Matrix.smul_mul]
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (A * X * B)
  rw [e] at h1
  refine (h1.unique h5).trans ?_
  simp only [extM, L, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  exact add_comm _ _

theorem extM_map {A B : Type} [CommRing A] [CommRing B] {m k : Type} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] (ρ : A →+* B) (ι : Matrix m k A) (Q : Matrix k m A) (g : Matrix k k A) :
    (extM ι Q g).map ρ = extM (ι.map ρ) (Q.map ρ) (g.map ρ) := by
  simp only [extM]
  rw [← RingHom.mapMatrix_apply, map_add, map_sub, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
    Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]

section Frame

variable {E : Type} [Field E] {n n₁ : ℕ}

theorem mid_injective : Function.Injective (mid (n₁ := n₁)) := fun a b h => by
  simpa [mid] using h

theorem mid_ne_x (k : Fin n₁) : mid k ≠ Fin.castAdd 1 (Fin.castAdd n₁ (0 : Fin 1)) := fun h => by
  have := congrArg (blk n₁) h
  rw [blk_mid, block_matrix_mulVec_basis] at this
  exact absurd this (by norm_num)

theorem mid_ne_y (k : Fin n₁) : mid k ≠ Fin.natAdd (1 + n₁) (0 : Fin 1) := fun h => by
  have := congrArg (blk n₁) h
  rw [blk_mid, blk_y] at this
  exact absurd this (by norm_num)

theorem col_cases (j : Fin (1 + n₁ + 1)) :
    j = Fin.castAdd 1 (Fin.castAdd n₁ (0 : Fin 1)) ∨ (∃ l, j = mid l) ∨ j = Fin.natAdd (1 + n₁) (0 : Fin 1) := by
  induction j using Fin.addCases with
  | left a =>
    induction a using Fin.addCases with
    | left b => left; rw [Subsingleton.elim b 0]
    | right b => right; left; exact ⟨b, rfl⟩
  | right a => right; right; rw [Subsingleton.elim a 0]

end Frame

section Gram

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E} {H : Plane E n n₁}
  {R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E}

omit [NumberField F] [NumberField E] in
theorem coef_frame (hRF : R * frame H = 1) :
    R.submatrix mid id * frame H = (1 : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) E).submatrix mid id := by
  rw [← hRF]; rfl

omit [NumberField F] [NumberField E] in
theorem coef_mul_ι (hRF : R * frame H = 1) : R.submatrix mid id * H.ι = 1 := by
  ext k l
  have := congrArg (fun M : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) E => M (mid k) (mid l)) hRF
  simp only [Matrix.mul_apply, frame_mid, Matrix.one_apply, mid_injective.eq_iff] at this
  simpa [Matrix.mul_apply, Matrix.one_apply] using this

omit [NumberField F] [NumberField E] in
theorem submatrix_mulVec_x_eq_zero_of_mul_frame (hRF : R * frame H = 1) : R.submatrix mid id *ᵥ H.x = 0 := by
  ext k
  have := congrArg (fun M : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) E =>
    M (mid k) (Fin.castAdd 1 (Fin.castAdd n₁ (0 : Fin 1)))) hRF
  simp only [Matrix.mul_apply, frame_alt, Matrix.one_apply, if_neg (mid_ne_x k)] at this
  simpa [Matrix.mulVec, dotProduct] using this

omit [NumberField F] [NumberField E] in
theorem coef_mulVec_y (hRF : R * frame H = 1) : R.submatrix mid id *ᵥ H.y = 0 := by
  ext k
  have := congrArg (fun M : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) E =>
    M (mid k) (Fin.natAdd (1 + n₁) (0 : Fin 1))) hRF
  simp only [Matrix.mul_apply, frame_y, Matrix.one_apply, if_neg (mid_ne_y k)] at this
  simpa [Matrix.mulVec, dotProduct] using this

omit [NumberField F] [NumberField E] in
theorem col_eq (k : Fin n₁) : (fun r => H.ι r k) = H.ι *ᵥ Pi.single k 1 := by
  funext r; simp [Matrix.mulVec, dotProduct, Pi.single_apply]

omit [NumberField F] [NumberField E] in
theorem one_sub_map (k : Fin n₁) (col : Fin (1 + n₁ + 1)) :
    ((1 : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) E).submatrix mid id).map σ k col =
      (1 : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) E) (mid k) col := by
  simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
  split_ifs <;> simp

omit [NumberField F] [NumberField E] in

theorem ιT_mul (hRF : R * frame H = 1) (hFR : frame H * R = 1)
    (horth : ∀ u, form σ J (H.ι *ᵥ u) H.x = 0 ∧ form σ J (H.ι *ᵥ u) H.y = 0)
    (hgram : H.ιᵀ * J * H.ι.map σ = J₁) : H.ιᵀ * J = J₁ * (R.submatrix mid id).map σ := by
  have hFRσ : (frame H).map σ * R.map σ = 1 := by
    rw [← Matrix.map_mul, hFR]; exact Matrix.map_one _ (map_zero _) (map_one _)
  suffices h : H.ιᵀ * J * (frame H).map σ = J₁ * (R.submatrix mid id).map σ * (frame H).map σ by
    calc H.ιᵀ * J = H.ιᵀ * J * ((frame H).map σ * R.map σ) := by rw [hFRσ, Matrix.mul_one]
      _ = J₁ * (R.submatrix mid id).map σ * ((frame H).map σ * R.map σ) := by
          rw [← Matrix.mul_assoc, h, Matrix.mul_assoc (J₁ * _)]
      _ = _ := by rw [hFRσ, Matrix.mul_one]
  rw [Matrix.mul_assoc J₁, ← Matrix.map_mul, coef_frame hRF]
  ext k col
  rw [GlobalTheory.LeviPlaneSection.gram_apply, Matrix.mul_apply]
  simp only [one_sub_map]
  rcases col_cases col with rfl | ⟨l, rfl⟩ | rfl
  · simp only [frame_alt, Matrix.one_apply, if_neg (mid_ne_x _), mul_zero, Finset.sum_const_zero]
    rw [col_eq, (horth _).1]
  · simp only [frame_mid, Matrix.one_apply, mid_injective.eq_iff, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← GlobalTheory.LeviPlaneSection.gram_apply, hgram]
  · simp only [frame_y, Matrix.one_apply, if_neg (mid_ne_y _), mul_zero, Finset.sum_const_zero]
    rw [col_eq, (horth _).2]

omit [NumberField F] [NumberField E] in

theorem coefT_mul (hσ : ∀ x, σ (σ x) = x) (hsk : ∀ i j, σ (J j i) = -J i j) (hRF : R * frame H = 1)
    (hFR : frame H * R = 1) (horth : ∀ u, form σ J (H.ι *ᵥ u) H.x = 0 ∧ form σ J (H.ι *ᵥ u) H.y = 0)
    (hgram : H.ιᵀ * J * H.ι.map σ = J₁) : (R.submatrix mid id)ᵀ * J₁ = J * H.ι.map σ := by
  have hRFt : Rᵀ * (frame H)ᵀ = 1 := by rw [← Matrix.transpose_mul, hFR, Matrix.transpose_one]
  suffices h : (frame H)ᵀ * ((R.submatrix mid id)ᵀ * J₁) = (frame H)ᵀ * (J * H.ι.map σ) by
    calc (R.submatrix mid id)ᵀ * J₁ = Rᵀ * (frame H)ᵀ * ((R.submatrix mid id)ᵀ * J₁) := by
          rw [hRFt, Matrix.one_mul]
      _ = Rᵀ * (frame H)ᵀ * (J * H.ι.map σ) := by rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc]
      _ = _ := by rw [hRFt, Matrix.one_mul]
  rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, coef_frame hRF, ← Matrix.mul_assoc]
  ext col l
  rw [GlobalTheory.LeviPlaneSection.gram_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id]
  rcases col_cases col with rfl | ⟨k, rfl⟩ | rfl
  · simp only [frame_alt, id_eq, Matrix.one_apply, if_neg (mid_ne_x _), zero_mul, Finset.sum_const_zero]
    rw [GlobalTheory.LeviPlaneSection.form_skew hσ hsk, col_eq, (horth _).1, map_zero, neg_zero]
  · simp only [frame_mid, id_eq, Matrix.one_apply, mid_injective.eq_iff, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← GlobalTheory.LeviPlaneSection.gram_apply, hgram]
  · simp only [frame_y, id_eq, Matrix.one_apply, if_neg (mid_ne_y _), zero_mul, Finset.sum_const_zero]
    rw [GlobalTheory.LeviPlaneSection.form_skew hσ hsk, col_eq, (horth _).2, map_zero, neg_zero]

end Gram

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH) in

theorem leviEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J → Y₁.J.det ≠ 0 →
    ∀ R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E, frame H * R = 1 → R * frame H = 1 →
    ∀ c : E, c ≠ 0 → IsHermND σ (c • Y.J.map σ) → IsHermND σ (c • Y₁.J.map σ) →
    ∃ ι : GAd σ (c • Y₁.J.map σ) →* GAd σ (c • Y.J.map σ),
      (∀ (g₁ : UA σ Y₁.J) (g' : GAd σ (c • Y₁.J.map σ)), g₁.1 = g'.1 →
        ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) H 1 g₁ m ∧ m.1 = (ι g').1) ∧
      ∀ (w : InfinitePlace F) (τ : EmbOver E w) (Z : Matrix (Fin n₁) (Fin n₁) ℂ) (γ : ℝ → GAd σ (c • Y₁.J.map σ)),
        IsLineOf σ (c • Y₁.J.map σ) τ Z γ →
        IsLineOf σ (c • Y.J.map σ) τ (H.ι.map τ.1 * Z * (R.submatrix mid id).map τ.1) fun t => ι (γ t) := by
  intro F E _ _ _ _ _ σ hcm n n₁ Y Y₁ H hsk hn hxx hyy hxy horth hgram hdet R hFR hRF c hc hJ hJ₁
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hcm
  have hQE := coef_mul_ι hRF
  have h3E := ιT_mul hRF hFR horth hgram
  have h2E := coefT_mul hσ hsk hRF hFR horth hgram
  have hcf : ∀ {a b : Type} (X : Matrix a b E), (incM F X).map (cA σ) = incM F (X.map σ) := fun X => by
    ext i j; exact GlobalTheory.LeviPlaneSection.cA_inclR' σ _
  have hQ : incM F (R.submatrix mid id) * incM F H.ι = 1 := by
    simp only [incM]; rw [← Matrix.map_mul, hQE]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : (incM F (R.submatrix mid id))ᵀ * incM F Y₁.J = incM F Y.J * (incM F H.ι).map (cA σ) := by
    rw [hcf]; simp only [incM]; rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h2E]
  have h3 : (incM F H.ι)ᵀ * incM F Y.J = incM F Y₁.J * (incM F (R.submatrix mid id)).map (cA σ) := by
    rw [hcf]; simp only [incM]; rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h3E]
  let ιU := GlobalTheory.DoubledPlaneEmb.extHom (cA σ) (incM F Y.J) (incM F Y₁.J) (incM F H.ι) (incM F (R.submatrix mid id))
    hQ h2 h3
  let ι : GAd σ (c • Y₁.J.map σ) →* GAd σ (c • Y.J.map σ) :=
    (SquareIntegrability.toGAd hσ Y.J hc).toMonoidHom.comp (ιU.comp (SquareIntegrability.toGAd hσ Y₁.J hc).symm.toMonoidHom)
  have hvec : ∀ v : Fin n → E, R.submatrix mid id *ᵥ v = 0 → incM F (R.submatrix mid id) *ᵥ incV F v = 0 := by
    intro v hv; ext i
    show ((R.submatrix mid id).map (inclR (F := F) (AF F)) *ᵥ (inclR (F := F) (AF F) ∘ v)) i = 0
    rw [← RingHom.map_mulVec, hv, Pi.zero_apply, map_zero]
  refine ⟨ι, fun g₁ g' hg => ?_, ?_⟩
  · have e : (SquareIntegrability.toGAd hσ Y₁.J hc).symm g' = g₁ := Subtype.ext hg.symm
    refine ⟨ιU g₁, ⟨?_, ?_, ?_⟩, ?_⟩
    · show extM (incM F H.ι) (incM F (R.submatrix mid id)) g₁.1.1 *ᵥ incV F H.x = _
      rw [extM_mulVec_of _ (hvec _ (submatrix_mulVec_x_eq_zero_of_mul_frame hRF)), Units.val_one, one_smul]
    · show extM (incM F H.ι) (incM F (R.submatrix mid id)) g₁.1.1 *ᵥ incV F H.y = _
      rw [extM_mulVec_of _ (hvec _ (coef_mulVec_y hRF)), inv_one, Units.val_one, map_one, one_smul]
    · exact extM_mul_self hQ _
    · show (ιU g₁).1 = (ιU ((SquareIntegrability.toGAd hσ Y₁.J hc).symm g')).1
      rw [e]
  · have hone : ∀ {R' : Type} [CommRing R'] [Algebra F R'] (φ : AF F →ₐ[F] R') (g : GAd σ (c • Y₁.J.map σ)),
        mapH σ (c • Y₁.J.map σ) φ g = 1 → mapH σ (c • Y.J.map σ) φ (ι g) = 1 := by
      intro R' _ _ φ g h1
      let ρ : AE F E →+* R' ⊗[F] E := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
      have e1 : (HA.mat R' σ (c • Y₁.J.map σ) (mapH σ (c • Y₁.J.map σ) φ g)).1 = 1 := by rw [h1]; rfl
      have e2 : (HA.mat R' σ (c • Y.J.map σ) (mapH σ (c • Y.J.map σ) φ (ι g))).1 =
          (extM (incM F H.ι) (incM F (R.submatrix mid id)) (HA.mat (AF F) σ (c • Y₁.J.map σ) g).1).map ρ := rfl
      have e3 : (HA.mat R' σ (c • Y₁.J.map σ) (mapH σ (c • Y₁.J.map σ) φ g)).1 =
          (HA.mat (AF F) σ (c • Y₁.J.map σ) g).1.map ρ := rfl
      refine GlobalTheory.AutFunCompare.HA_ext σ _ fun r s => ?_
      rw [e2, extM_map, ← e3, e1, extM_one]
      rfl
    intro w τ Z γ hγ t
    obtain ⟨y, hy, he⟩ := hγ t
    refine ⟨projArch σ _ w (ι (γ t)), ?_, ?_⟩
    · refine GAd_ext σ _ (fun u => ?_) (fun v => ?_)
      · by_cases hu : u = w
        · subst hu; rw [projArch_embArch_self]
        · rw [projArch_embArch_ne σ _ hu]
          exact hone (evInf F u) _ (by rw [hy]; exact projArch_embArch_ne σ _ hu y)
      · rw [proj_embArch]
        exact hone (evFin F v) _ (by rw [hy]; exact proj_embArch σ _ v w y)
    · let ρw : AE F E →+* w.Completion ⊗[F] E := (Algebra.TensorProduct.map (evInf F w) (AlgHom.id F E)).toRingHom
      have hρ : ∀ e : E, infEmb τ (ρw (inclR (F := F) (AF F) e)) = τ.1 e := by
        intro e; simp [ρw, inclR, infEmb_tmul]
      have hBA : (R.submatrix mid id).map τ.1 * H.ι.map τ.1 = 1 := by
        rw [← Matrix.map_mul, hQE]; exact Matrix.map_one _ (map_zero _) (map_one _)
      have key : GlobalTheory.Orb.archMat σ (c • Y.J.map σ) τ (projArch σ _ w (ι (γ t))) =
          extM (H.ι.map τ.1) ((R.submatrix mid id).map τ.1)
            (GlobalTheory.Orb.archMat σ (c • Y₁.J.map σ) τ (projArch σ _ w (γ t))) := by
        rw [GlobalTheory.Orb.archMat_apply, GlobalTheory.Orb.archMat_apply]
        change ((extM (incM F H.ι) (incM F (R.submatrix mid id)) (HA.mat (AF F) σ (c • Y₁.J.map σ) (γ t)).1).map ρw).map
            (infEmb τ) = extM _ _ (((HA.mat (AF F) σ (c • Y₁.J.map σ) (γ t)).1.map ρw).map (infEmb τ))
        rw [extM_map, extM_map]
        congr 1 <;> ext i j <;> exact hρ _
      rw [key, hy, projArch_embArch_self, he, ← Matrix.smul_mul, ← Matrix.mul_smul, exp_sandwich _ _ hBA]

end GlobalTheory.LeviEmbHC
