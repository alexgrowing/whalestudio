import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorsCommuteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorNormalStatement

noncomputable section

open Matrix
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.GelFlagPf

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem mem_iff_repr {ι E : Type*} [AddCommGroup E] [Module ℂ E] (b : Module.Basis ι ℂ E) (T : Set ι)
    (W : Submodule ℂ E) (hW : W = Submodule.span ℂ (b '' T)) (v : E) :
    v ∈ W ↔ ∀ a, a ∉ T → b.repr v a = 0 := by
  subst hW
  rw [Module.Basis.mem_span_image]
  constructor
  · intro h a ha
    by_contra hne
    exact ha (h (by simpa using hne))
  · intro h a ha
    by_contra hne
    exact (by simpa using ha : b.repr v a ≠ 0) (h a hne)

theorem exists_adapted (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hle : W₁ ≤ W₂) :
    ∃ (P : Mat n) (blk : Fin n → ℕ), IsUnit P ∧ (∀ a, blk a ≤ 2) ∧
      (∀ v, v ∈ W₁ ↔ ∀ a, 0 < blk a → (P⁻¹ *ᵥ v) a = 0) ∧
      (∀ v, v ∈ W₂ ↔ ∀ a, 1 < blk a → (P⁻¹ *ᵥ v) a = 0) := by
  classical
  obtain ⟨S₁, hS₁W, -, hWS₁, hi₁⟩ := exists_linearIndepOn_id_extension (K := ℂ) (s := ∅)
    (t := (W₁ : Set (Fin n → ℂ))) (linearIndepOn_empty _ _) (Set.empty_subset _)
  obtain ⟨S₂, hS₂W, h12, hWS₂, hi₂⟩ := exists_linearIndepOn_id_extension (t := (W₂ : Set (Fin n → ℂ))) hi₁
    (hS₁W.trans hle)
  obtain ⟨S₃, -, h23, hWS₃, hi₃⟩ := exists_linearIndepOn_id_extension (t := Set.univ) hi₂ (Set.subset_univ _)
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range (fun x : S₃ => (x : Fin n → ℂ))) := by
    intro v _
    have := hWS₃ (Set.mem_univ v)
    simpa using this
  let b₀ : Module.Basis S₃ ℂ (Fin n → ℂ) := Module.Basis.mk hi₃ hsp
  have hcard : Nat.card S₃ = n := by
    rw [← Module.finrank_eq_nat_card_basis b₀]; simp
  haveI : Finite S₃ := Module.Finite.finite_basis b₀
  let e : S₃ ≃ Fin n := Finite.equivFinOfCardEq hcard
  let b : Module.Basis (Fin n) ℂ (Fin n → ℂ) := b₀.reindex e
  have hb : ∀ a, b a = (e.symm a : Fin n → ℂ) := by
    intro a; simp [b, b₀]
  have himg : ∀ S : Set (Fin n → ℂ), S ⊆ S₃ → b '' {a | (e.symm a : Fin n → ℂ) ∈ S} = S := by
    intro S hS
    ext v
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [hb]; exact ha
    · intro hv
      exact ⟨e ⟨v, hS hv⟩, by simpa using hv, by simp [hb]⟩
  let blk : Fin n → ℕ := fun a =>
    if (e.symm a : Fin n → ℂ) ∈ S₁ then 0 else if (e.symm a : Fin n → ℂ) ∈ S₂ then 1 else 2
  let P : Mat n := (Pi.basisFun ℂ (Fin n)).toMatrix b
  let P' : Mat n := b.toMatrix (Pi.basisFun ℂ (Fin n))
  have hPP' : P * P' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hP'P : P' * P = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hinv : P⁻¹ = P' := Matrix.inv_eq_right_inv hPP'
  have hrepr : ∀ v, P⁻¹ *ᵥ v = b.repr v := by
    intro v
    rw [hinv]
    have h : b.toMatrix (Pi.basisFun ℂ (Fin n)) *ᵥ ((Pi.basisFun ℂ (Fin n)).repr v) = b.repr v :=
      Module.Basis.toMatrix_mulVec_repr _ _ v
    have e : ⇑((Pi.basisFun ℂ (Fin n)).repr v) = v := by ext i; simp
    rw [e] at h
    exact h
  have hW₁ : W₁ = Submodule.span ℂ (b '' {a | (e.symm a : Fin n → ℂ) ∈ S₁}) := by
    rw [himg S₁ (h12.trans h23)]
    exact le_antisymm hWS₁ (Submodule.span_le.2 hS₁W)
  have hW₂ : W₂ = Submodule.span ℂ (b '' {a | (e.symm a : Fin n → ℂ) ∈ S₂}) := by
    rw [himg S₂ h23]
    exact le_antisymm hWS₂ (Submodule.span_le.2 hS₂W)
  refine ⟨P, blk, ⟨⟨P, P', hPP', hP'P⟩, rfl⟩, ?_, ?_, ?_⟩
  · intro a
    simp only [blk]
    split_ifs <;> omega
  · intro v
    rw [mem_iff_repr b _ W₁ hW₁, hrepr]
    refine forall_congr' fun a => ?_
    have : 0 < blk a ↔ (e.symm a : Fin n → ℂ) ∉ S₁ := by
      simp only [blk]
      split_ifs <;> simp_all
    simp [this]
  · intro v
    rw [mem_iff_repr b _ W₂ hW₂, hrepr]
    refine forall_congr' fun a => ?_
    have : 1 < blk a ↔ (e.symm a : Fin n → ℂ) ∉ S₂ := by
      simp only [blk]
      split_ifs with h1 h2
      · simp [h12 h1]
      · simp [h2]
      · simp [h2]
    simp [this]

theorem map_eq {W : Submodule ℂ (Fin n → ℂ)} {blk : Fin n → ℕ} {k : ℕ} {P g : Mat n} (hP : IsUnit P) (hg : IsUnit g)
    (hW : ∀ v, v ∈ W ↔ ∀ a, k < blk a → (P⁻¹ *ᵥ v) a = 0) (hblk : ∀ a b, blk b < blk a → g a b = 0) :
    W.map (Matrix.mulVecLin (P * g * P⁻¹)) = W := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hQP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hM : IsUnit (P * g * P⁻¹) :=
    (hP.mul hg).mul ((Matrix.isUnit_nonsing_inv_iff).2 hP)
  have hinj : Function.Injective (Matrix.mulVecLin (P * g * P⁻¹)) := by
    intro v w h
    have hd : IsUnit (P * g * P⁻¹).det := (Matrix.isUnit_iff_isUnit_det _).1 hM
    have h' : (P * g * P⁻¹) *ᵥ v = (P * g * P⁻¹) *ᵥ w := by simpa only [Matrix.mulVecLin_apply] using h
    have := congrArg (fun z => (P * g * P⁻¹)⁻¹ *ᵥ z) h'
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec] at this
    exact this
  have hle : W.map (Matrix.mulVecLin (P * g * P⁻¹)) ≤ W := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hW]
    intro a ha
    have hv' := (hW v).1 hv
    have e1 : P⁻¹ *ᵥ (Matrix.mulVecLin (P * g * P⁻¹) v) = g *ᵥ (P⁻¹ *ᵥ v) := by
      have : P⁻¹ * (P * g * P⁻¹) = g * P⁻¹ := by
        rw [Matrix.mul_assoc P, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, this]
    rw [e1]
    change ∑ b, g a b * (P⁻¹ *ᵥ v) b = 0
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : blk b < blk a
    · rw [hblk a b hb, zero_mul]
    · have : k < blk b := by omega
      rw [hv' b this, mul_zero]
  exact Submodule.eq_of_le_of_finrank_eq hle
    (Submodule.equivMapOfInjective _ hinj W).finrank_eq.symm

theorem isUnit_unip {blk : Fin n → ℕ} (hb : ∀ a, blk a ≤ 2) {u : Mat n}
    (hu : ∀ a b, ¬ blk a < blk b → (u - 1) a b = 0) : IsUnit u := by
  have h3 : (u - 1) ^ 3 = 0 := by
    ext a d
    simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun e _ => ?_
    by_cases h1 : blk a < blk e
    · by_cases h2 : blk e < blk c
      · by_cases h3 : blk c < blk d
        · have := hb a; have := hb e; have := hb c; have := hb d; omega
        · simp [hu c d h3]
      · simp [hu e c h2]
    · simp [hu a e h1]
  have := IsNilpotent.isUnit_add_one (⟨3, h3⟩ : IsNilpotent (u - 1))
  simpa using this

theorem exists_nil {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} {blk : Fin n → ℕ} {P : Mat n} (hP : IsUnit P)
    (hb : ∀ a, blk a ≤ 2) (h1 : ∀ v, v ∈ W₁ ↔ ∀ a, 0 < blk a → (P⁻¹ *ᵥ v) a = 0)
    (h2 : ∀ v, v ∈ W₂ ↔ ∀ a, 1 < blk a → (P⁻¹ *ᵥ v) a = 0) {u : Mat n}
    (hu : ∀ a b, ¬ blk a < blk b → (u - 1) a b = 0) :
    ∃ U ∈ nilSet W₁ W₂, U.val = P * u * P⁻¹ := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hQP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPQ : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hM : IsUnit (P * u * P⁻¹) :=
    (hP.mul (isUnit_unip hb hu)).mul ((Matrix.isUnit_nonsing_inv_iff).2 hP)
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, ?_, hU⟩
  have hsub : U.val - 1 = P * (u - 1) * P⁻¹ := by
    rw [hU, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ]
  have hc : ∀ v, P⁻¹ *ᵥ ((U.val - 1) *ᵥ v) = (u - 1) *ᵥ (P⁻¹ *ᵥ v) := by
    intro v
    have : P⁻¹ * (P * (u - 1) * P⁻¹) = (u - 1) * P⁻¹ := by
      rw [Matrix.mul_assoc P, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
    simp only [hsub, Matrix.mulVec_mulVec, this]
  refine ⟨?_, ?_, ?_⟩
  · intro v
    rw [h2]
    intro a ha
    rw [hc]
    change ∑ c, (u - 1) a c * (P⁻¹ *ᵥ v) c = 0
    refine Finset.sum_eq_zero fun c _ => ?_
    have : ¬ blk a < blk c := by have := hb c; omega
    rw [hu a c this, zero_mul]
  · intro v hv
    rw [h1]
    intro a ha
    rw [hc]
    have hv' := (h2 v).1 hv
    change ∑ c, (u - 1) a c * (P⁻¹ *ᵥ v) c = 0
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hac : blk a < blk c
    · rw [hv' c (by omega), mul_zero]
    · rw [hu a c hac, zero_mul]
  · intro v hv
    have hv' := (h1 v).1 hv
    have hz : P⁻¹ *ᵥ ((U.val - 1) *ᵥ v) = 0 := by
      rw [hc]
      ext a
      change ∑ c, (u - 1) a c * (P⁻¹ *ᵥ v) c = 0
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hac : blk a < blk c
      · rw [hv' c (by omega), mul_zero]
      · rw [hu a c hac, zero_mul]
    have := congrArg (fun z => P *ᵥ z) hz
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hPQ, Matrix.one_mul, Matrix.mulVec_zero] at this
    exact this

theorem mul_mem {a b : Mat n} (ha : a ∈ GLs n) (hb : b ∈ GLs n) : a * b ∈ GLs n := by
  simpa [GLs, Matrix.det_mul] using And.intro ha hb

theorem contDiff_mul_left (P : Mat n) : ContDiff ℝ ∞ (fun y : Mat n => P * y) :=
  (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ P)).contDiff

theorem contDiff_mul_right (P : Mat n) : ContDiff ℝ ∞ (fun y : Mat n => y * P) :=
  (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ P)).contDiff

theorem gelFlag_of (hC : GelComm) (hN : GelN) : GelFlag := by
  intro n V _ _ W₁ W₂ hle A f hA hf hAq hfN s m x hx
  obtain ⟨P, blk, hP, hb, h1, h2⟩ := exists_adapted W₁ W₂ hle
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hQP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPQ : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hPm : P ∈ GLs n := hdet.ne_zero
  have hQm : P⁻¹ ∈ GLs n := ((Matrix.isUnit_iff_isUnit_det _).1 ((Matrix.isUnit_nonsing_inv_iff).2 hP)).ne_zero
  have hAf : ContDiffOn ℝ ∞ (fun y => A y (f y)) (GLs n) :=
    ((ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).contDiff.comp_contDiffOn hA).clm_apply hf
  have hAxf : ContDiffOn ℝ ∞ (fun y => A x (f y)) (GLs n) :=
    ((A x).restrictScalars ℝ).contDiff.comp_contDiffOn hf
  let F : Mat n → V × V := fun y => (A y (f y), A x (f y))
  have hF : ContDiffOn ℝ ∞ F (GLs n) := hAf.prodMk hAxf
  let D : Mat n → V := fun y => A y (f y) - A x (f y)
  have hD : ContDiffOn ℝ ∞ D (GLs n) := hAf.sub hAxf
  have e1 : gel s m (fun y => A y (f y)) x = (gel s m F x).1 :=
    ((hC n (V × V) V s m F hF).2 x hx).2.2 (ContinuousLinearMap.fst ℂ V V)
  have e2 : gel s m (fun y => A x (f y)) x = (gel s m F x).2 :=
    ((hC n (V × V) V s m F hF).2 x hx).2.2 (ContinuousLinearMap.snd ℂ V V)
  have e3 : gel s m D x = (gel s m F x).1 - (gel s m F x).2 :=
    ((hC n (V × V) V s m F hF).2 x hx).2.2 (ContinuousLinearMap.fst ℂ V V - ContinuousLinearMap.snd ℂ V V)
  have e4 : gel s m (fun y => A x (f y)) x = A x (gel s m f x) :=
    ((hC n V V s m f hf).2 x hx).2.2 (A x)
  set r : Mat n := P⁻¹ * x with hr
  have hrm : r ∈ GLs n := mul_mem hQm hx
  let D₁ : Mat n → V := fun y => D (P * y)
  have hD₁ : ContDiffOn ℝ ∞ D₁ (GLs n) :=
    hD.comp (contDiff_mul_left P).contDiffOn fun y hy => mul_mem hPm hy
  let h : Mat n → V := fun y => D₁ (y * r)
  have hh : ContDiffOn ℝ ∞ h (GLs n) :=
    hD₁.comp (contDiff_mul_right r).contDiffOn fun y hy => mul_mem hy hrm
  have hone : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have e5 : gel s m h 1 = gel s m D₁ (1 * r) := (((hC n V V s m D₁ hD₁).2 1 hone).2.1 r hrm).2
  have e6 : gel s m D₁ r = gel s m D (P * r) := (((hC n V V s m D hD).2 r hrm).2.1 P hPm).1
  have hPr : P * r = x := by rw [hr, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hzero : gel s m h 1 = 0 := by
    refine hN n V blk h hh ?_ ?_ s m 1 hone ?_
    · intro u hu g hg
      obtain ⟨U, hUN, hU⟩ := exists_nil hP hb h1 h2 hu
      have hUunit : IsUnit (u : Mat n) := isUnit_unip hb hu
      have hy : P * (g * r) ∈ GLs n := mul_mem hPm (mul_mem hg hrm)
      have hshift : P * (u * g * r) = U.val * (P * (g * r)) := by
        rw [hU]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P⁻¹ P, hQP, Matrix.one_mul]
      have hstab1 := map_eq (g := u) hP hUunit h1 (fun a b hab => by
        have : ¬ blk a < blk b := by omega
        have h0 := hu a b this
        have hne : a ≠ b := by rintro rfl; omega
        simpa [Matrix.sub_apply, Matrix.one_apply, hne] using h0)
      have hstab2 := map_eq (g := u) hP hUunit h2 (fun a b hab => by
        have : ¬ blk a < blk b := by omega
        have h0 := hu a b this
        have hne : a ≠ b := by rintro rfl; omega
        simpa [Matrix.sub_apply, Matrix.one_apply, hne] using h0)
      have hUm : U.val ∈ GLs n := by
        have : IsUnit U.val.det := (Matrix.isUnit_iff_isUnit_det _).1 U.isUnit
        exact this.ne_zero
      show D (P * (u * g * r)) = D (P * (g * r))
      rw [hshift]
      show A _ (f _) - A x (f _) = A _ (f _) - A x (f _)
      rw [hfN U hUN _ hy, hAq U.val hUm (by rw [hU]; exact hstab1) (by rw [hU]; exact hstab2) _ hy]
    · intro g hg hgb
      have hgu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hg)
      have hbl : ∀ a b, blk b < blk a → g a b = 0 := fun a b hab => hgb a b (by omega)
      have hq : P * g * P⁻¹ ∈ GLs n := mul_mem (mul_mem hPm hg) hQm
      have hx' : P * (g * r) = (P * g * P⁻¹) * x := by
        rw [hr]; simp only [Matrix.mul_assoc]
      show D (P * (g * r)) = 0
      rw [hx']
      show A _ (f _) - A x (f _) = 0
      rw [hAq _ hq (map_eq hP hgu h1 hbl) (map_eq hP hgu h2 hbl) x hx]
      exact sub_self _
    · intro a b hab
      exact Matrix.one_apply_ne (fun h => hab (by rw [h]))
  have e7 : gel s m D x = 0 := by
    rw [← hPr, ← e6]
    rw [Matrix.one_mul] at e5
    rw [← e5, hzero]
  have : gel s m (fun y => A y (f y)) x - A x (gel s m f x) = 0 := by
    rw [e1, ← e4, e2, ← e3, e7]
  exact sub_eq_zero.1 this

theorem gelFlag_holds : GelFlag := gelFlag_of GlobalTheory.T.gelfand_operators_commute GlobalTheory.T.gelfand_operator_normal

end GlobalTheory.CompanionTheory.GelFlagPf
