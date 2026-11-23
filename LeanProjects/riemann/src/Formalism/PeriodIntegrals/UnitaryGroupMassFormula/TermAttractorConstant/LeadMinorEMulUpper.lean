import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelativeEquivalence.DCRelEquivAllHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUpUniMulAlt

noncomputable section

open scoped Classical

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.DCRelEquiv PI.DCRelEquiv.UnitaryGroupMassFormula

section Mat

variable {K : Type*} [CommRing K]

theorem sub_mul_lower {N l : ℕ} (h : l ≤ N) (A Z : Matrix (Fin N) (Fin N) K)
    (hA : ∀ a c : Fin N, a < c → A a c = 0) :
    (A * Z).submatrix (Fin.castLE h) (Fin.castLE h) =
      A.submatrix (Fin.castLE h) (Fin.castLE h) * Z.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  let e : Fin l ↪ Fin N := ⟨Fin.castLE h, Fin.castLE_injective h⟩
  have hs : ∑ k : Fin l, A (Fin.castLE h i) (Fin.castLE h k) * Z (Fin.castLE h k) (Fin.castLE h j) =
      ∑ k ∈ Finset.univ.map e, A (Fin.castLE h i) k * Z k (Fin.castLE h j) := by
    rw [Finset.sum_map]; rfl
  rw [hs]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  have hkl : l ≤ k.val := by
    by_contra hc
    exact hk (Finset.mem_map.2 ⟨⟨k.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  rw [hA _ _ (by rw [Fin.lt_def]; simp; omega), zero_mul]

theorem sub_mul_upper {N l : ℕ} (h : l ≤ N) (Z B : Matrix (Fin N) (Fin N) K)
    (hB : ∀ c b : Fin N, b < c → B c b = 0) :
    (Z * B).submatrix (Fin.castLE h) (Fin.castLE h) =
      Z.submatrix (Fin.castLE h) (Fin.castLE h) * B.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  let e : Fin l ↪ Fin N := ⟨Fin.castLE h, Fin.castLE_injective h⟩
  have hs : ∑ k : Fin l, Z (Fin.castLE h i) (Fin.castLE h k) * B (Fin.castLE h k) (Fin.castLE h j) =
      ∑ k ∈ Finset.univ.map e, Z (Fin.castLE h i) k * B k (Fin.castLE h j) := by
    rw [Finset.sum_map]; rfl
  rw [hs]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  have hkl : l ≤ k.val := by
    by_contra hc
    exact hk (Finset.mem_map.2 ⟨⟨k.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  rw [hB _ _ (by rw [Fin.lt_def]; simp; omega), mul_zero]

theorem det_lower_one {N : ℕ} (A : Matrix (Fin N) (Fin N) K)
    (hA : ∀ a c : Fin N, a < c → A a c = 0) (hd : ∀ a, A a a = 1) : A.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular A (fun i j hij => hA i j (OrderDual.toDual_lt_toDual.1 hij))]
  simp [hd]

theorem det_upper_one {N : ℕ} (B : Matrix (Fin N) (Fin N) K)
    (hB : ∀ c b : Fin N, b < c → B c b = 0) (hd : ∀ a, B a a = 1) : B.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (M := B) (fun i j hij => hB i j hij)]
  simp [hd]

theorem isLoUni_mul {N : ℕ} {A L : Matrix (Fin N) (Fin N) K} (hA : IsLoUni A) (hL : IsLoUni L) :
    IsLoUni (A * L) := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge i k with hik | hki
    · rw [(hA i k).1 hik, zero_mul]
    · rw [(hL k j).1 (lt_of_le_of_lt hki hij), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hA i i).2 rfl, (hL i i).2 rfl, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hki | hik
      · rw [(hL k i).1 hki, mul_zero]
      · rw [(hA i k).1 hik, zero_mul]
    · simp

theorem isUpUni_mul {N : ℕ} {U B : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) (hB : IsUpUni B) :
    IsUpUni (U * B) := by
  first | exact GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul .. | (apply GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul <;> assumption) | (intros; apply GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul <;> assumption) | (apply @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul <;> assumption) | (intros; apply @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul <;> assumption) | (apply @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul <;> first | assumption | infer_instance) | exact @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul K ‹_› N U B hU hB | exact @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul K ‹_› N U B hU | exact @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul K ‹_› N U B | exact @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul K ‹_› N U | exact @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul K ‹_› N | exact @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul K ‹_› | exact @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul K

end Mat

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem leadMinorE_lower_mul {N : ℕ} (A Z : Matrix (Fin N) (Fin N) E) (hA : IsLoUni A) (l : ℕ) :
    leadMinorE (A * Z) l = leadMinorE Z l := by
  unfold leadMinorE
  split_ifs with h
  · rw [sub_mul_lower h A Z (fun a c hac => (hA a c).1 hac), Matrix.det_mul,
      det_lower_one (A.submatrix (Fin.castLE h) (Fin.castLE h)) (fun a c hac => (hA _ _).1 hac)
        (fun a => (hA _ _).2 rfl), one_mul]
  · rfl

theorem leadMinorE_mul_upper {N : ℕ} (Z B : Matrix (Fin N) (Fin N) E) (hB : IsUpUni B) (l : ℕ) :
    leadMinorE (Z * B) l = leadMinorE Z l := by
  unfold leadMinorE
  split_ifs with h
  · rw [sub_mul_upper h Z B (fun c b hbc => (hB c b).1 hbc), Matrix.det_mul,
      det_upper_one (B.submatrix (Fin.castLE h) (Fin.castLE h)) (fun c b hbc => (hB _ _).1 hbc)
        (fun a => (hB _ _).2 rfl), mul_one]
  · rfl

theorem exists_coeffs {N : ℕ} (f : Fin N → S.V) (a : Fin N) (v : S.V)
    (hv : v ∈ Submodule.span E (f '' {c | c < a})) :
    ∃ c : Fin N → E, (∀ d, ¬ d < a → c d = 0) ∧ ∑ d, c d • f d = v := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at hv
  obtain ⟨l, hl, rfl⟩ := hv
  refine ⟨l, fun d hd => ?_, ?_⟩
  · by_contra hne
    have : d ∈ (l.support : Set (Fin N)) := by simpa using hne
    exact hd ((Finsupp.mem_supported E l).1 hl this)
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp

theorem gram_first {N : ℕ} (f g w : Fin N → S.V)
    (h : ∀ a, g a - f a ∈ Submodule.span E (f '' {c | c < a})) :
    ∃ A : Matrix (Fin N) (Fin N) E, IsLoUni A ∧
      (Matrix.of fun a b => S.hT (g a) (w b)) = A * Matrix.of fun a b => S.hT (f a) (w b) := by
  choose c hc0 hcs using fun a => exists_coeffs f a _ (h a)
  refine ⟨Matrix.of fun a d => (if a = d then (1 : E) else 0) + star (c a d), ?_, ?_⟩
  · intro i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · simp [ne_of_lt hij, hc0 i j (lt_asymm hij)]
    · subst hij; simp [hc0 i i (lt_irrefl i)]
  · ext a b
    have hg : g a = f a + ∑ d, c a d • f d := by rw [hcs a]; abel
    have key : S.hT (g a) (w b) = S.hT (f a) (w b) + ∑ d, star (c a d) * S.hT (f d) (w b) := by
      rw [hg, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply]
      congr 1
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact key

theorem gram_second {N : ℕ} (f w w' : Fin N → S.V)
    (h : ∀ b, w' b - w b ∈ Submodule.span E (w '' {c | c < b})) :
    ∃ B : Matrix (Fin N) (Fin N) E, IsUpUni B ∧
      (Matrix.of fun a b => S.hT (f a) (w' b)) = (Matrix.of fun a b => S.hT (f a) (w b)) * B := by
  choose c hc0 hcs using fun b => exists_coeffs w b _ (h b)
  refine ⟨Matrix.of fun d b => (if d = b then (1 : E) else 0) + c b d, ?_, ?_⟩
  · intro i j
    refine ⟨fun hji => ?_, fun hij => ?_⟩
    · simp [ne_of_gt hji, hc0 j i (lt_asymm hji)]
    · subst hij; simp [hc0 i i (lt_irrefl i)]
  · ext a b
    have hw : w' b = w b + ∑ d, c b d • w d := by rw [hcs b]; abel
    have key : S.hT (f a) (w' b) = S.hT (f a) (w b) + ∑ d, S.hT (f a) (w d) * c b d := by
      rw [hw, map_add, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact key

variable {T T' : E}

theorem frame_castSucc (F : LFlag S r T) (i : Fin r) : frame F (Fin.castSucc i) = F.fl.e i := by
  simp [frame, Formalism.MainNotions.S.FlagG.fvec]

theorem frame_last (F : LFlag S r T) : frame F (Fin.last r) = F.fl.z := by
  simp [frame, Formalism.MainNotions.S.FlagG.fvec]

theorem z_mem_orth (F : LFlag S r T) : F.fl.z ∈ orth S (Xsp F) := by
  rw [mem_orth_iff]
  intro x hx
  dsimp only [Xsp, Formalism.MainNotions.S.FlagG.X] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact F.fl.z_orth i
  | zero => simp
  | add y y' _ _ h1 h2 => rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
  | smul c y _ h => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h, smul_zero]

theorem nlam_frame (Λ : Submodule (𝓞 E) S.V) {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F)
    (a : Fin (r + 1)) : n (frame F a) - frame F a ∈ Submodule.span E (frame F '' {c | c < a}) := by
  induction a using Fin.lastCases with
  | last =>
    have h := hn.2.2 _ (z_mem_orth F)
    rw [frame_last]
    refine (show Xsp F ≤ _ from ?_) h
    dsimp only [Xsp, Formalism.MainNotions.S.FlagG.X]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨Fin.castSucc j, Fin.castSucc_lt_last j, frame_castSucc F j⟩
  | cast i =>
    have h := hn.2.1 i.1 _ (e_mem_Xflag F i)
    rw [frame_castSucc]
    refine (show Xflag F i.1 ≤ _ from ?_) h
    dsimp only [Xflag, Formalism.MainNotions.S.FlagG.Xa]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨Fin.castSucc j, Fin.castSucc_lt_castSucc_iff.2 hj, frame_castSucc F j⟩

theorem zhat_eq (F : LFlag S r T) (F' : LFlag S r T') :
    ZhatL F F' = Matrix.of fun a b => S.hT (frame F a) (frame F' b) := by
  ext a b; rfl

theorem zhat_factor (Λ : Submodule (𝓞 E) S.V) {F : LFlag S r T} {F₁ F₂ : LFlag S r T'}
    (h : DCRel Λ F F₁ F₂) :
    ∃ A B : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsLoUni A ∧ IsUpUni B ∧
      ZhatL F F₂ = A * ZhatL F F₁ * B := by
  obtain ⟨n, hn, m, hm, hfr, -⟩ := h
  have hni := nlam_inv hn
  obtain ⟨A, hA, hAe⟩ := gram_first (frame F) (fun a => n⁻¹ (frame F a)) (fun b => m (frame F₁ b))
    (fun a => nlam_frame Λ hni a)
  obtain ⟨B, hB, hBe⟩ := gram_second (frame F) (frame F₁) (fun b => m (frame F₁ b))
    (fun b => nlam_frame Λ hm b)
  refine ⟨A, B, hA, hB, ?_⟩
  have h2 : ZhatL F F₂ = Matrix.of fun a b => S.hT (n⁻¹ (frame F a)) (m (frame F₁ b)) := by
    rw [zhat_eq]
    ext a b
    simp only [Matrix.of_apply]
    rw [hfr b, ← isom_app hn.1.1 (n⁻¹ (frame F a)) (m (frame F₁ b))]
    rw [show n (n⁻¹ (frame F a)) = frame F a from n.apply_symm_apply _]
  rw [h2, hAe, hBe, zhat_eq, Matrix.mul_assoc]

theorem dl_eq (Λ : Submodule (𝓞 E) S.V) {F : LFlag S r T} {F₁ F₂ : LFlag S r T'}
    (h : DCRel Λ F F₁ F₂) (l : ℕ) : Formalism.MainNotions.S.Dl F.fl F₂.fl l = Formalism.MainNotions.S.Dl F.fl F₁.fl l := by
  obtain ⟨A, B, hA, hB, he⟩ := zhat_factor Λ h
  have : Formalism.MainNotions.S.Zhat F.fl F₂.fl = A * Formalism.MainNotions.S.Zhat F.fl F₁.fl * B := he
  unfold Formalism.MainNotions.S.Dl
  rw [this, leadMinorE_mul_upper _ _ hB, leadMinorE_lower_mul _ _ hA]

theorem gFun_all (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (P : LFlag S r T' → Prop) :
    GFun Λ F P := by
  intro x y h
  have h' : DCRel Λ F x.1 y.1 := h
  show Formalism.MainNotions.S.Gflag F.fl x.1.fl = Formalism.MainNotions.S.Gflag F.fl y.1.fl
  unfold Formalism.MainNotions.S.Gflag
  rw [dl_eq Λ h', dl_eq Λ h']

theorem zhatOM_eq_mul {K : Type*} [CommRing K] (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ZhatOM Z = Z * Matrix.diagonal (fun b : Fin (r + 1) => ((-1 : K) ^ (r - b.val))) := by
  ext a b
  simp [ZhatOM, Matrix.mul_diagonal, mul_comm]

theorem sgn_sq {K : Type*} [CommRing K] (b : Fin (r + 1)) :
    ((-1 : K) ^ (r - b.val)) * ((-1 : K) ^ (r - b.val)) = 1 := by
  rw [← mul_pow]; simp

theorem isUpUni_conj_sgn {K : Type*} [CommRing K] {B : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hB : IsUpUni B) :
    IsUpUni (Matrix.diagonal (fun b : Fin (r + 1) => ((-1 : K) ^ (r - b.val))) * B *
      Matrix.diagonal (fun b : Fin (r + 1) => ((-1 : K) ^ (r - b.val)))) := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · simp [Matrix.mul_diagonal, Matrix.diagonal_mul, (hB i j).1 hji]
  · subst hij
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, (hB i i).2 rfl, mul_one]
    exact sgn_sq i

theorem cell_step {K : Type*} [CommRing K] {Z Z₂ A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hA : IsLoUni A) (hB : IsUpUni B) (he : Z₂ = A * Z * B) (w : Point K (r + 1))
    (hc : IsInCell (ZhatOM Z) w) : IsInCell (ZhatOM Z₂) w := by
  obtain ⟨L, U, hL, hU, hZ⟩ := hc
  set Ds := Matrix.diagonal (fun b : Fin (r + 1) => ((-1 : K) ^ (r - b.val))) with hDs
  have hDD : Ds * Ds = 1 := by
    rw [hDs, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext b
    exact sgn_sq b
  refine ⟨A * L, U * (Ds * B * Ds), isLoUni_mul hA hL, isUpUni_mul hU (isUpUni_conj_sgn hB), ?_⟩
  rw [zhatOM_eq_mul] at hZ ⊢
  rw [he]
  have e1 : A * Z * B * Ds = A * (Z * Ds) * (Ds * B * Ds) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ds Ds (B * Ds), hDD, Matrix.one_mul]
  rw [e1, hZ]
  simp only [Matrix.mul_assoc]

theorem cellFun_all (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (P : LFlag S r T' → Prop) :
    CellFun Λ F P := by
  intro x y h w
  have h' : DCRel Λ F x.1 y.1 := h
  have hs : DCRel Λ F y.1 x.1 := (dCRelEquivAll_holds E S r T T' Λ F).symm h'
  obtain ⟨A, B, hA, hB, he⟩ := zhat_factor Λ h'
  obtain ⟨A', B', hA', hB', he'⟩ := zhat_factor Λ hs
  exact ⟨cell_step hA hB he w, cell_step hA' hB' he' w⟩

theorem feqF_fwd (Λ : Submodule (𝓞 E) S.V) {F : LFlag S r T} {x y : LFlag S r T'} (h : DCRel Λ F x y)
    (hx : ∃ n ∈ NLam Λ F, ∀ a, n (frame F a) = frame x a) :
    ∃ n ∈ NLam Λ F, ∀ a, n (frame F a) = frame y a := by
  obtain ⟨n1, hn1, h1⟩ := hx
  obtain ⟨n, hn, m, hm, hfr, -⟩ := h
  have hTT : T' = T := by
    have e1 := isom_app hn1.1.1 (frame F (Fin.last r)) (frame F (Fin.last r))
    rw [h1, frame_last, frame_last, x.fl.z_norm, F.fl.z_norm] at e1
    exact neg_injective e1
  subst hTT
  have hc := (nLamConj_holds E S r T' Λ F x n1 hn1.1 (fun a => (h1 a).symm) m).1 hm
  refine ⟨n * m * n1, ?_, fun a => ?_⟩
  · have e : n * m * n1 = n * n1 * (n1⁻¹ * m * n1) := by group
    rw [e]
    exact nlam_mul (nlam_mul hn hn1) hc
  · rw [hfr a, ← h1 a]
    rfl

theorem feqFFun_all (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (P : LFlag S r T' → Prop) :
    FeqFFun Λ F P := by
  intro x y h
  have h' : DCRel Λ F x.1 y.1 := h
  have hs : DCRel Λ F y.1 x.1 := (dCRelEquivAll_holds E S r T T' Λ F).symm h'
  exact ⟨feqF_fwd Λ h', feqF_fwd Λ hs⟩

end Gen

end PI.TermAttrConst.UnitaryGroupMassFormula
