import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdaptedMajorant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitaryCommuting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqDiagonalOfUpperTriangularOfUnitary

set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal ComplexOrder

namespace GlobalTheory.CompanionTheory.SiegelArch

theorem isCompact_unitaryFn (n : ℕ) :
    IsCompact {U : Fin n → Fin n → ℂ | (Matrix.of U)ᴴ * Matrix.of U = 1} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have hc : Continuous fun U : Fin n → Fin n → ℂ => (Matrix.of U : Matrix (Fin n) (Fin n) ℂ) := continuous_id
    exact isClosed_eq (hc.matrix_conjTranspose.matrix_mul hc) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Fin n → Fin n → ℂ)) (r := 1)).subset fun U hU => ?_
    have hu : (Matrix.of U : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ :=
      Matrix.mem_unitaryGroup_iff'.2 hU
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    exact entry_norm_bound_of_unitary hu i j

open scoped MatrixOrder Matrix.Norms.L2Operator in
theorem exists_factor {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef) : ∃ B : Matrix (Fin n) (Fin n) ℂ, P = Bᴴ * B := by
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP.nonneg
  exact ⟨y, rfl⟩

theorem isCompact_stabFn {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) :
    IsCompact {M : Fin n → Fin n → ℂ | (Matrix.of M)ᴴ * P * Matrix.of M = P} := by
  have hdet : P.det ≠ 0 := hP.det_pos.ne'
  obtain ⟨B, rfl⟩ := exists_factor hP.posSemidef
  have hB : IsUnit B.det := isUnit_iff_ne_zero.2 fun h => hdet (by rw [Matrix.det_mul, h, mul_zero])
  have hc : Continuous fun U : Fin n → Fin n → ℂ => (Matrix.of U : Matrix (Fin n) (Fin n) ℂ) := continuous_id
  have hcl : IsClosed {M : Fin n → Fin n → ℂ | (Matrix.of M)ᴴ * (Bᴴ * B) * Matrix.of M = Bᴴ * B} :=
    isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc) continuous_const
  have hf : Continuous fun U : Fin n → Fin n → ℂ => ((B⁻¹ * Matrix.of U * B : Matrix (Fin n) (Fin n) ℂ) : Fin n → Fin n → ℂ) :=
    (continuous_const.matrix_mul hc).matrix_mul continuous_const
  refine ((isCompact_unitaryFn n).image hf).of_isClosed_subset hcl fun M hM => ?_
  have hM' : (Matrix.of M)ᴴ * (Bᴴ * B) * Matrix.of M = Bᴴ * B := hM
  refine ⟨(B * Matrix.of M * B⁻¹ : Matrix (Fin n) (Fin n) ℂ), ?_, ?_⟩
  · change (B * Matrix.of M * B⁻¹)ᴴ * (B * Matrix.of M * B⁻¹) = 1
    have h1 : (B * Matrix.of M * B⁻¹)ᴴ * (B * Matrix.of M * B⁻¹) =
        (B⁻¹)ᴴ * ((Matrix.of M)ᴴ * (Bᴴ * B) * Matrix.of M) * B⁻¹ := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    have h2 : (B⁻¹)ᴴ * (Bᴴ * B) * B⁻¹ = (B * B⁻¹)ᴴ * (B * B⁻¹) := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [h1, hM', h2, Matrix.mul_nonsing_inv _ hB]
    simp
  · change B⁻¹ * (B * Matrix.of M * B⁻¹) * B = Matrix.of M
    have : B⁻¹ * (B * Matrix.of M * B⁻¹) * B = (B⁻¹ * B) * Matrix.of M * (B⁻¹ * B) := by
      simp only [Matrix.mul_assoc]
    rw [this, Matrix.nonsing_inv_mul _ hB]
    simp

theorem stab_inv {n : ℕ} {A A' P : Matrix (Fin n) (Fin n) ℂ} (h : A * A' = 1) (hA : Aᴴ * P * A = P) :
    A'ᴴ * P * A' = P := by
  have h1 : (A * A')ᴴ * P * (A * A') = A'ᴴ * (Aᴴ * P * A) * A' := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [hA] at h1
  rw [← h1, h]
  simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} {w : InfinitePlace F}

theorem conjT_map (hcm : IsCMExt F E σ) (τ : E →+* ℂ) {a b : Type} (M : Matrix a b E) :
    (M.map τ)ᴴ = (cT (σ : E →+* E) M).map τ := by
  ext i j
  simp [cT, conjTranspose_apply, hcm.2.2.2 τ]

theorem cT_conj {a b : Type} (M : Matrix a b ℂ) : cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [cT, conjTranspose_apply]

theorem arch_unitary (hcm : IsCMExt F E σ) (τ : EmbOver E w) (y : GArch σ J w) :
    (archMat σ J τ y)ᴴ * J.map τ.1 * archMat σ J τ y = J.map τ.1 := by
  have h : cT (starRingEnd ℂ) (archEquiv J hcm τ y).1.1 * J.map τ.1 * (archEquiv J hcm τ y).1.1 = J.map τ.1 :=
    (archEquiv J hcm τ y).2
  rw [cT_conj] at h
  exact h

theorem det_map_ne (hdet : J.det ≠ 0) (τ : E →+* ℂ) : (J.map τ).det ≠ 0 := by
  have h : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [h]
  exact (map_ne_zero τ).2 hdet

theorem exists_lift (hcm : IsCMExt F E σ) (hdet : J.det ≠ 0) (τ : EmbOver E w) {m : Matrix (Fin n) (Fin n) ℂ}
    (hm : mᴴ * J.map τ.1 * m = J.map τ.1) : ∃ y : GArch σ J w, archMat σ J τ y = m := by
  have hJ := det_map_ne J hdet τ.1
  have hd : m.det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hm
    rw [Matrix.det_mul, h0, mul_zero] at h
    exact hJ h.symm
  let u : GL (Fin n) ℂ := Matrix.nonsingInvUnit m (isUnit_iff_ne_zero.2 hd)
  have hu : u ∈ Formalism.UG.UJ (starRingEnd ℂ) (J.map τ.1) := by
    change cT (starRingEnd ℂ) m * J.map τ.1 * m = J.map τ.1
    rw [cT_conj]
    exact hm
  refine ⟨(archEquiv J hcm τ).symm ⟨u, hu⟩, ?_⟩
  rw [GlobalTheory.Orb.archMat_eq_archEquiv J hcm, MulEquiv.apply_symm_apply]
  rfl

theorem archMat_injective (hcm : IsCMExt F E σ) (τ : EmbOver E w) : Function.Injective (archMat σ J τ) :=
  fun a b e => (GlobalTheory.Orb.isEmbedding_archMat J hcm τ).injective (congrArg (fun m i j => m i j) e)

variable (σ) in

def stabAt (τ : EmbOver E w) (P : Matrix (Fin n) (Fin n) ℂ) : Subgroup (GArch σ J w) where
  carrier := {y | (archMat σ J τ y)ᴴ * P * archMat σ J τ y = P}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have ha' : (archMat σ J τ a)ᴴ * P * archMat σ J τ a = P := ha
    have hb' : (archMat σ J τ b)ᴴ * P * archMat σ J τ b = P := hb
    change (archMat σ J τ (a * b))ᴴ * P * archMat σ J τ (a * b) = P
    have h : (archMat σ J τ (a * b))ᴴ * P * archMat σ J τ (a * b) =
        (archMat σ J τ b)ᴴ * ((archMat σ J τ a)ᴴ * P * archMat σ J τ a) * archMat σ J τ b := by
      simp only [map_mul, conjTranspose_mul, Matrix.mul_assoc]
    rw [h, ha', hb']
  inv_mem' := by
    intro a ha
    exact stab_inv (A := archMat σ J τ a) (by rw [← map_mul, mul_inv_cancel, map_one]) ha

theorem isCompact_stabAt (hcm : IsCMExt F E σ) (hdet : J.det ≠ 0) (τ : EmbOver E w)
    {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) : IsCompact (stabAt σ J τ P : Set (GArch σ J w)) := by
  have hemb := GlobalTheory.Orb.isEmbedding_archMat J hcm τ
  rw [hemb.isInducing.isCompact_iff]
  have hc : Continuous fun U : Fin n → Fin n → ℂ => (Matrix.of U : Matrix (Fin n) (Fin n) ℂ) := continuous_id
  have hcl : IsClosed {M : Fin n → Fin n → ℂ | (Matrix.of M)ᴴ * J.map τ.1 * Matrix.of M = J.map τ.1} :=
    isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc) continuous_const
  have himg : (fun y i j => archMat σ J τ y i j) '' (stabAt σ J τ P : Set (GArch σ J w)) =
      {M : Fin n → Fin n → ℂ | (Matrix.of M)ᴴ * P * Matrix.of M = P} ∩
        {M : Fin n → Fin n → ℂ | (Matrix.of M)ᴴ * J.map τ.1 * Matrix.of M = J.map τ.1} := by
    ext M
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, arch_unitary J hcm τ y⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨y, hy⟩ := exists_lift J hcm hdet τ (m := Matrix.of M) h2
      refine ⟨y, ?_, ?_⟩
      · change (archMat σ J τ y)ᴴ * P * archMat σ J τ y = P
        rw [hy]
        exact h1
      · funext i j
        exact congrFun (congrFun hy i) j
  refine himg ▸ (isCompact_stabFn hP).inter_right hcl

def evC (τ : EmbOver E w) : AF F ⊗[F] E →+* ℂ := (infEmb τ).comp (compInf F E w)

variable (F E) in

def finPart : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

theorem map_evW_fst (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) = compInf F E w z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

theorem tens_prod_ext {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] {z z' : (A × B) ⊗[F] E}
    (a : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z')
    (b : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z') : z = z' := by
  have hz : ∀ z : (A × B) ⊗[F] E, z = LinearMap.rTensor E (LinearMap.inl F A B)
        (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F A B)
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul x y => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [hz z, hz z', a, b]

theorem tens_ext (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {z z' : AF F ⊗[F] E}
    (h : ∀ w, evC (τ w) z = evC (τ w) z') (h' : finPart F E z = finPart F E z') : z = z' := by
  have h1 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z' :=
    GlobalTheory.AutFunCompare.infTens_ext fun w => by
      rw [map_evW_fst, map_evW_fst]
      exact (infEmb_bijective hcm (τ w)).1 (h w)
  exact tens_prod_ext (A := Ainf F) (B := Af F) h1 h'

theorem tensMat_ext (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {a b : Type}
    {A A' : Matrix a b (AF F ⊗[F] E)} (h : ∀ w, A.map (evC (τ w)) = A'.map (evC (τ w)))
    (h' : A.map (finPart F E) = A'.map (finPart F E)) : A = A' :=
  Matrix.ext fun i j => tens_ext hcm τ (fun w => congrFun (congrFun (h w) i) j) (congrFun (congrFun h' i) j)

theorem map_adMat {a b : Type} (τ : EmbOver E w) (M : Matrix a b E) : (adMat F M).map (evC τ) = M.map τ.1 := by
  ext i j
  change infEmb τ ((1 : w.Completion) ⊗ₜ[F] M i j) = _
  simp

theorem map_adMat_fin {a b : Type} (M : Matrix a b E) :
    (adMat F M).map (finPart F E) = M.map (inclR (F := F) (Af F)) := by
  ext i j
  change ((1 : Af F) ⊗ₜ[F] M i j) = _
  rfl

theorem map_matHom (τ : EmbOver E w) (g : GAd σ J) :
    (matHom _ σ J g).1.map (evC τ) = archMat σ J τ (projArch σ J w g) := rfl

theorem map_matHom_fin {g : GAd σ J} (hg : g ∈ infPts σ J) : (matHom _ σ J g).1.map (finPart F E) = 1 :=
  congrArg Units.val (MonoidHom.mem_ker.1 hg)

theorem frame_coeff (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {g : GAd σ J} (hg : g ∈ infPts σ J)
    {Q : Matrix (Fin r) (Fin n) E} {X : Matrix (Fin n) (Fin r) E} (hQ : Q * X = 1)
    (h : ∀ w, ∃ Bw : Matrix (Fin r) (Fin r) ℂ,
      archMat σ J (τ w) (projArch σ J w g) * X.map (τ w).1 = X.map (τ w).1 * Bw) :
    ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), (matHom _ σ J g).1 * adMat F X = adMat F X * B ∧
      B.map (finPart F E) = 1 ∧ ∀ w (Bw : Matrix (Fin r) (Fin r) ℂ),
        archMat σ J (τ w) (projArch σ J w g) * X.map (τ w).1 = X.map (τ w).1 * Bw → B.map (evC (τ w)) = Bw := by
  have hinf : ∀ w (Bw : Matrix (Fin r) (Fin r) ℂ),
      archMat σ J (τ w) (projArch σ J w g) * X.map (τ w).1 = X.map (τ w).1 * Bw →
      (adMat F Q * (matHom _ σ J g).1 * adMat F X).map (evC (τ w)) = Bw := by
    intro w Bw hB
    rw [Matrix.map_mul, Matrix.map_mul, map_adMat, map_adMat, map_matHom, Matrix.mul_assoc, hB, ← Matrix.mul_assoc,
      ← Matrix.map_mul, hQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  have hfin : (adMat F Q * (matHom _ σ J g).1 * adMat F X).map (finPart F E) = 1 := by
    rw [Matrix.map_mul, Matrix.map_mul, map_adMat_fin, map_adMat_fin, map_matHom_fin J hg, Matrix.mul_one,
      ← Matrix.map_mul, hQ, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨_, tensMat_ext hcm τ (fun w => ?_) ?_, hfin, hinf⟩
  · obtain ⟨Bw, hB⟩ := h w
    rw [Matrix.map_mul, Matrix.map_mul (L := adMat F X), hinf w Bw hB, map_adMat, map_matHom]
    exact hB
  · rw [Matrix.map_mul, Matrix.map_mul (L := adMat F X), hfin, map_matHom_fin J hg, Matrix.one_mul, Matrix.mul_one]

theorem mem_minPar_of (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {g : GAd σ J} (hg : g ∈ infPts σ J)
    {Q : Matrix (Fin r) (Fin n) E} {X : Matrix (Fin n) (Fin r) E} (hQ : Q * X = 1)
    (h : ∀ w, ∃ Bw : Matrix (Fin r) (Fin r) ℂ, Bw.BlockTriangular id ∧
      archMat σ J (τ w) (projArch σ J w g) * X.map (τ w).1 = X.map (τ w).1 * Bw) : g ∈ minPar σ J X := by
  choose Bw ht he using h
  obtain ⟨B, h1, h2, h3⟩ := frame_coeff J hcm τ hg hQ fun w => ⟨Bw w, he w⟩
  refine ⟨B, fun i j hij => ?_, h1⟩
  refine tens_ext hcm τ (fun w => ?_) ?_
  · have := congrFun (congrFun (h3 w (Bw w) (he w)) i) j
    rw [Matrix.map_apply] at this
    rw [this, ht w hij, map_zero]
  · have := congrFun (congrFun h2 i) j
    rw [Matrix.map_apply] at this
    have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    rw [this, map_zero, Matrix.one_apply_ne hne]

theorem exists_diag (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {g : GAd σ J} (hg : g ∈ infPts σ J)
    {Q : Matrix (Fin r) (Fin n) E} {X : Matrix (Fin n) (Fin r) E} (hQ : Q * X = 1)
    (h : ∀ w, ∃ d : Fin r → ℂ,
      archMat σ J (τ w) (projArch σ J w g) * X.map (τ w).1 = X.map (τ w).1 * diagonal d) :
    ∃ d : Fin r → AF F ⊗[F] E, (matHom _ σ J g).1 * adMat F X = adMat F X * diagonal d := by
  choose d he using h
  obtain ⟨B, h1, h2, h3⟩ := frame_coeff J hcm τ hg hQ fun w => ⟨_, he w⟩
  have hB : B = diagonal fun i => B i i := by
    ext i j
    by_cases e : i = j
    · subst e
      simp
    · rw [Matrix.diagonal_apply_ne _ e]
      refine tens_ext hcm τ (fun w => ?_) ?_
      · have := congrFun (congrFun (h3 w _ (he w)) i) j
        rw [Matrix.map_apply] at this
        rw [this, Matrix.diagonal_apply_ne _ e, map_zero]
      · have := congrFun (congrFun h2 i) j
        rw [Matrix.map_apply] at this
        rw [this, map_zero, Matrix.one_apply_ne e]
  exact ⟨fun i => B i i, by rw [← hB]; exact h1⟩

variable (σ) in

def kInf (τ : ∀ w : InfinitePlace F, EmbOver E w) (P : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) :
    Subgroup (GAd σ J) :=
  (Subgroup.pi Set.univ fun w => stabAt σ J (τ w) (P w)).map ((ofInf σ J).comp (embArchPi σ J))

theorem ofInf_mem_infPts (y : GInf σ J) : ofInf σ J y ∈ infPts σ J := mem_infPts.2 (by simp)

theorem kInf_le (τ : ∀ w : InfinitePlace F, EmbOver E w) (P : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) :
    kInf σ J τ P ≤ infPts σ J := by
  rintro _ ⟨x, -, rfl⟩
  exact ofInf_mem_infPts J _

theorem isCompact_kInf (hcm : IsCMExt F E σ) (hdet : J.det ≠ 0) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {P : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ} (hP : ∀ w, (P w).PosDef) :
    IsCompact (kInf σ J τ P : Set (GAd σ J)) := by
  rw [kInf, Subgroup.coe_map, Subgroup.coe_pi]
  exact (isCompact_univ_pi fun w => isCompact_stabAt J hcm hdet (τ w) (hP w)).image
    ((continuous_ofInf σ J).comp (continuous_embArchPi σ J))

theorem projArch_ofInf_embArchPi (x : ∀ w, GArch σ J w) (w : InfinitePlace F) :
    projArch σ J w (ofInf σ J (embArchPi σ J x)) = x w := by simp

theorem proj_ofInf_eq (y : GInf σ J) (v) : proj σ J v (ofInf σ J y) = 1 := by simp

theorem iwasawa (hcm : IsCMExt F E σ) (hdet : J.det ≠ 0) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {P : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ} {Q : Matrix (Fin r) (Fin n) E} {X : Matrix (Fin n) (Fin r) E}
    (hQ : Q * X = 1)
    (hiwa : ∀ w, ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * J.map (τ w).1 * g = J.map (τ w).1 →
      ∃ p k : Matrix (Fin n) (Fin n) ℂ, pᴴ * J.map (τ w).1 * p = J.map (τ w).1 ∧
        kᴴ * J.map (τ w).1 * k = J.map (τ w).1 ∧ kᴴ * P w * k = P w ∧ g = p * k ∧
        ∃ B : Matrix (Fin r) (Fin r) ℂ, B.BlockTriangular id ∧ p * X.map (τ w).1 = X.map (τ w).1 * B) :
    ∀ g ∈ infPts σ J, ∃ p ∈ minPar σ J X, p ∈ infPts σ J ∧ ∃ k ∈ kInf σ J τ P, g = p * k := by
  intro g hg
  choose p k hp hk hkP hgpk hB using fun w => hiwa w _ (arch_unitary J hcm (τ w) (projArch σ J w g))
  choose y hy using fun w => exists_lift J hcm hdet (τ w) (hp w)
  choose z hz using fun w => exists_lift J hcm hdet (τ w) (hk w)
  have hfin := mem_infPts_iff_forall.1 hg
  refine ⟨ofInf σ J (embArchPi σ J y), ?_, ofInf_mem_infPts J _, ofInf σ J (embArchPi σ J z), ?_, ?_⟩
  · refine mem_minPar_of J hcm τ (ofInf_mem_infPts J _) hQ fun w => ?_
    obtain ⟨B, ht, he⟩ := hB w
    refine ⟨B, ht, ?_⟩
    rw [projArch_ofInf_embArchPi, hy]
    exact he
  · refine ⟨z, fun w _ => ?_, rfl⟩
    change (archMat σ J (τ w) (z w))ᴴ * P w * archMat σ J (τ w) (z w) = P w
    rw [hz]
    exact hkP w
  · refine GAd_ext σ J (fun w => ?_) fun v => ?_
    · refine archMat_injective J hcm (τ w) ?_
      rw [map_mul, map_mul, projArch_ofInf_embArchPi, projArch_ofInf_embArchPi, hy, hz]
      exact hgpk w
    · rw [map_mul, proj_ofInf_eq, proj_ofInf_eq, mul_one]
      exact hfin v

theorem good (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {P : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ} {Q Q' : Matrix (Fin r) (Fin n) E}
    {X Y : Matrix (Fin n) (Fin r) E} (hQ : Q * X = 1) (hQ' : Q' * Y = 1)
    (hgood : ∀ w, ∀ p : Matrix (Fin n) (Fin n) ℂ, pᴴ * J.map (τ w).1 * p = J.map (τ w).1 → pᴴ * P w * p = P w →
      ∀ B : Matrix (Fin r) (Fin r) ℂ, B.BlockTriangular id → p * X.map (τ w).1 = X.map (τ w).1 * B →
      ∃ d : Fin r → ℂ, p * X.map (τ w).1 = X.map (τ w).1 * diagonal d ∧ p * Y.map (τ w).1 = Y.map (τ w).1 * diagonal d) :
    ∀ p ∈ minPar σ J X, p ∈ kInf σ J τ P → p ∈ leviMin σ J X Y := by
  intro p hp hpK
  have hinf := kInf_le J τ P hpK
  obtain ⟨x, hx, hxp⟩ := hpK
  have hproj : ∀ w, projArch σ J w p = x w := fun w => by
    rw [← hxp]
    exact projArch_ofInf_embArchPi J x w
  obtain ⟨B, hBt, hBe⟩ := hp
  have hw : ∀ w, ∃ d : Fin r → ℂ, archMat σ J (τ w) (projArch σ J w p) * X.map (τ w).1 = X.map (τ w).1 * diagonal d ∧
      archMat σ J (τ w) (projArch σ J w p) * Y.map (τ w).1 = Y.map (τ w).1 * diagonal d := by
    intro w
    refine hgood w _ (arch_unitary J hcm (τ w) _) ?_ (B.map (evC (τ w))) (fun i j hij => ?_) ?_
    · rw [hproj]
      exact hx w (Set.mem_univ w)
    · rw [Matrix.map_apply, hBt hij, map_zero]
    · have := congrArg (fun A => A.map (evC (τ w))) hBe
      simp only [Matrix.map_mul, map_adMat, map_matHom] at this
      exact this
  obtain ⟨d, hd⟩ := exists_diag J hcm τ hinf hQ fun w => (hw w).imp fun _ h => h.1
  obtain ⟨d', hd'⟩ := exists_diag J hcm τ hinf hQ' fun w => (hw w).imp fun _ h => h.2
  exact ⟨d, d', hd, hd'⟩

theorem exists_kInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ K : Subgroup (GAd σ J), K ≤ infPts σ J ∧ IsCompact (K : Set (GAd σ J)) ∧ (∀ g ∈ infPts σ J, ∃ p ∈ minPar σ J X, p ∈ infPts σ J ∧ ∃ k ∈ K, g = p * k) ∧ ∀ p ∈ minPar σ J X, p ∈ K → p ∈ leviMin σ J X Y := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y hW
  obtain ⟨τ⟩ : Nonempty (∀ w : InfinitePlace F, EmbOver E w) := ⟨fun _ => Classical.arbitrary _⟩
  have hcTJ : cT (σ : E →+* E) J = J := by
    ext i j
    exact hJ.1 i j
  have hher : ∀ w, (J.map (τ w).1).IsHermitian := fun w => by
    rw [Matrix.IsHermitian, conjT_map hcm, hcTJ]
  have hu : ∀ w, IsUnit (J.map (τ w).1).det := fun w => isUnit_iff_ne_zero.2 (det_map_ne J hJ.2 _)
  have hmap : ∀ (w : InfinitePlace F) {A B : Matrix (Fin n) (Fin r) E},
      (A.map (τ w).1)ᴴ * J.map (τ w).1 * B.map (τ w).1 = (cT (σ : E →+* E) A * J * B).map (τ w).1 := fun w {A B} => by
    rw [Matrix.map_mul, Matrix.map_mul, conjT_map hcm]
  have hxx : ∀ w, (X.map (τ w).1)ᴴ * J.map (τ w).1 * X.map (τ w).1 = 0 := fun w => by
    rw [hmap, hW.xx]; simp
  have hyy : ∀ w, (Y.map (τ w).1)ᴴ * J.map (τ w).1 * Y.map (τ w).1 = 0 := fun w => by
    rw [hmap, hW.yy]; simp
  have hxy : ∀ w, (X.map (τ w).1)ᴴ * J.map (τ w).1 * Y.map (τ w).1 = 1 := fun w => by
    rw [hmap, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]
  have hyx : ∀ w, (Y.map (τ w).1)ᴴ * J.map (τ w).1 * X.map (τ w).1 = 1 := fun w => by
    have h := congrArg conjTranspose (hxy w)
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, (hher w).eq, conjTranspose_one] at h
    rw [Matrix.mul_assoc]
    exact h
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hQ : cT (σ : E →+* E) Y * J * X = 1 := by
    have h : (cT (σ : E →+* E) Y * J * X).map (τ w₀).1 = (1 : Matrix (Fin r) (Fin r) E).map (τ w₀).1 := by
      rw [← hmap, hyx, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.map_injective (τ w₀).1.injective h
  choose P hPd hPJ hPX using fun w => GlobalTheory.CompanionTheory.WittMajorant.exists_adapted_majorant n r _ _ _ (hher w) (hu w) (hxx w) (hyy w) (hxy w)
  refine ⟨kInf σ J τ P, kInf_le J τ P, isCompact_kInf J hcm hJ.2 τ hPd, ?_, ?_⟩
  · exact iwasawa J hcm hJ.2 τ hQ fun w => GlobalTheory.CompanionTheory.WittIwasawa.iwasawa_witt_flag n r _ _ _ _ (hher w) (hu w) (hxx w) (hyy w) (hxy w) (hPd w) (hPJ w) (hPX w)
  · exact good J hcm τ hQ hW.xy fun w p h1 h2 B hB hpB =>
      GlobalTheory.CompanionTheory.RealPlace.flag_isometry_diagonal_on_frame n r _ _ p _ _ (hu w) (hxy w) (hPd w) (hPJ w) (hPX w) h1 h2 B hB hpB

end GlobalTheory.CompanionTheory.SiegelArch
