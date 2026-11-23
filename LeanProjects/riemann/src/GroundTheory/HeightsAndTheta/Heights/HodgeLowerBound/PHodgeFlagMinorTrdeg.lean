import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagMinorTrdeg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagRatioTrdeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

namespace HodgeFlagMinorTrdeg

section Blocks

variable {R : Type} [CommRing R]

def topLeft {n j : ℕ} (h : j ≤ n) (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin j) (Fin j) R :=
  M.submatrix (Fin.castLE h) (Fin.castLE h)

def botRight {n j : ℕ} (h : j ≤ n) (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n - j)) (Fin (n - j)) R :=
  M.submatrix (fun r => ⟨j + r, by have := r.2; omega⟩) (fun r => ⟨j + r, by have := r.2; omega⟩)

theorem pivotMinor_topLeft {n j : ℕ} (h : j ≤ n) (M : Matrix (Fin n) (Fin n) R) (a : Fin (j - 1)) (b : Fin j)
    (A : Fin (n - 1)) (B : Fin n) (hA : (A : ℕ) = a) (hB : (B : ℕ) = b) :
    pivotMinor M A B = pivotMinor (topLeft h M) a b := by
  obtain ⟨A, hA'⟩ := A
  obtain ⟨B, hB'⟩ := B
  simp only at hA hB
  subst hA hB
  unfold pivotMinor
  congr 1
  ext r c
  simp only [Matrix.submatrix_apply, topLeft, pivotCols]
  split_ifs <;> congr 1

theorem pivotMinor_congr {n j : ℕ} (M M' : Matrix (Fin n) (Fin n) R)
    (hM : ∀ r c : Fin n, (r : ℕ) < j → (c : ℕ) < j → M r c = M' r c) (a : Fin (n - 1)) (b : Fin n)
    (ha : (a : ℕ) < j) (hb : (b : ℕ) < j) : pivotMinor M a b = pivotMinor M' a b := by
  unfold pivotMinor
  congr 1
  ext r c
  simp only [Matrix.submatrix_apply]
  apply hM
  · simp only [Fin.val_castLE]; have := r.2; omega
  · simp only [pivotCols]; split_ifs with hc
    · simp only; omega
    · exact hb

theorem pivotMinor_eq_zero_of_block {n j : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (hz : ∀ r c : Fin n, (r : ℕ) < j → j ≤ (c : ℕ) → M r c = 0) (a : Fin (n - 1)) (b : Fin n)
    (ha : (a : ℕ) < j) (hb : j ≤ (b : ℕ)) : pivotMinor M a b = 0 := by
  unfold pivotMinor
  refine Matrix.det_eq_zero_of_column_eq_zero (Fin.last a) fun r => ?_
  simp only [Matrix.submatrix_apply, pivotCols, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true]
  exact hz _ _ (by simp only [Fin.val_castLE]; have := r.2; omega) hb

theorem pivotMinor_block {n j : ℕ} (h : j ≤ n) (M : Matrix (Fin n) (Fin n) R)
    (hz : ∀ r c : Fin n, (r : ℕ) < j → j ≤ (c : ℕ) → M r c = 0) (a : Fin (n - j - 1)) (b : Fin (n - j))
    (A : Fin (n - 1)) (B : Fin n) (hA : (A : ℕ) = j + a) (hB : (B : ℕ) = j + b) :
    pivotMinor M A B = (topLeft h M).det * pivotMinor (botRight h M) a b := by
  obtain ⟨A, hA'⟩ := A
  obtain ⟨B, hB'⟩ := B
  simp only at hA hB
  subst hA hB
  unfold pivotMinor
  let e : Fin j ⊕ Fin ((a : ℕ) + 1) ≃ Fin (j + (a : ℕ) + 1) :=
    finSumFinEquiv.trans (finCongr (Nat.add_assoc _ _ _).symm)
  rw [← Matrix.det_submatrix_equiv_self e]
  have key : (M.submatrix (Fin.castLE (by omega)) (pivotCols (⟨j + a, hA'⟩ : Fin (n - 1)) ⟨j + b, hB'⟩)).submatrix e e =
      Matrix.fromBlocks (topLeft h M) 0
        ((M.submatrix (Fin.castLE (by omega)) (pivotCols (⟨j + a, hA'⟩ : Fin (n - 1)) ⟨j + b, hB'⟩)).submatrix e e).toBlocks₂₁
        ((botRight h M).submatrix (Fin.castLE (by have := a.2; omega)) (pivotCols a b)) := by
    ext (r | r) (c | c)
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, topLeft, e, Equiv.trans_apply,
        finSumFinEquiv_apply_left, finCongr_apply, pivotCols]
      rw [dif_pos (by simp; omega)]
      congr 1
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, e, Equiv.trans_apply,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply, pivotCols]
      split_ifs with hc
      · exact hz _ _ (by simp) (by simp)
      · exact hz _ _ (by simp) (by simp)
    · rfl
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, botRight, e, Equiv.trans_apply,
        finSumFinEquiv_apply_right, finCongr_apply, pivotCols]
      split_ifs with h1 h2 h2
      · congr 1
      · simp at h1; omega
      · simp at h1; omega
      · congr 1
  rw [key, Matrix.det_fromBlocks_zero₁₂]

end Blocks

section Generic

variable (F : Type) [Field F] (Ψ : Type)

theorem renFr_inj {α β : Type} (e : α → β) (he : Function.Injective e) :
    Function.Injective ((IsScalarTower.toAlgHom F (MvPolynomial β F) (FractionRing (MvPolynomial β F))).comp
      (rename e)) := fun _ _ h =>
  rename_injective _ he (IsFractionRing.injective (MvPolynomial β F) (FractionRing (MvPolynomial β F)) h)

def renFr {α β : Type} (e : α → β) (he : Function.Injective e) :
    FractionRing (MvPolynomial α F) →ₐ[F] FractionRing (MvPolynomial β F) :=
  IsFractionRing.liftAlgHom (renFr_inj F e he)

theorem renFr_algebraMap {α β : Type} (e : α → β) (he : Function.Injective e) (p : MvPolynomial α F) :
    renFr F e he (algebraMap _ _ p) = algebraMap _ _ (rename e p) := by
  show IsFractionRing.lift (renFr_inj F e he) _ = _
  rw [IsFractionRing.lift_algebraMap]
  rfl

variable {n j : ℕ} (h : j ≤ n)

def eA : Ψ × Fin j × Fin j → Ψ × Fin n × Fin n := fun p => (p.1, Fin.castLE h p.2.1, Fin.castLE h p.2.2)

def eD : Ψ × Fin (n - j) × Fin (n - j) → Ψ × Fin n × Fin n :=
  fun p => (p.1, ⟨j + p.2.1, by have := p.2.1.2; omega⟩, ⟨j + p.2.2, by have := p.2.2.2; omega⟩)

theorem eA_inj : Function.Injective (eA Ψ h) := by
  rintro ⟨τ, a, b⟩ ⟨τ', a', b'⟩ e
  simp only [eA, Prod.mk.injEq, Fin.ext_iff, Fin.val_castLE] at e
  obtain ⟨h0, h1, h2⟩ := e
  subst h0
  rw [Fin.ext h1, Fin.ext h2]

theorem eD_inj : Function.Injective (eD Ψ h) := by
  rintro ⟨τ, a, b⟩ ⟨τ', a', b'⟩ e
  simp only [eD, Prod.mk.injEq, Fin.ext_iff] at e
  obtain ⟨h0, h1, h2⟩ := e
  subst h0
  rw [Fin.ext (by omega : (a : ℕ) = a'), Fin.ext (by omega : (b : ℕ) = b')]

def φA : GenFrac F Ψ j →ₐ[F] GenFrac F Ψ n := renFr F (eA Ψ h) (eA_inj Ψ h)

def φD : GenFrac F Ψ (n - j) →ₐ[F] GenFrac F Ψ n := renFr F (eD Ψ h) (eD_inj Ψ h)

theorem zero_block (τ : Ψ) (r c : Fin n) (hr : (r : ℕ) < j) (hc : j ≤ (c : ℕ)) : genMat0Fr F Ψ n j τ r c = 0 := by
  simp [genMat0Fr, hr, hc]

theorem topLeft_eq (τ : Ψ) : topLeft h (genMat0Fr F Ψ n j τ) = (genMatFr F Ψ j τ).map (φA F Ψ h) := by
  ext r c
  have hc : ¬ (j ≤ (Fin.castLE h c : ℕ)) := by simp
  simp only [topLeft, genMat0Fr, Matrix.submatrix_apply, Matrix.of_apply, Matrix.map_apply, genMatFr, φA,
    renFr_algebraMap, rename_X, hc, and_false, if_false]
  rfl

theorem botRight_eq (τ : Ψ) : botRight h (genMat0Fr F Ψ n j τ) = (genMatFr F Ψ (n - j) τ).map (φD F Ψ h) := by
  ext r c
  have hr : ¬ ((j + r : ℕ) < j) := by omega
  simp only [botRight, genMat0Fr, Matrix.submatrix_apply, Matrix.of_apply, Matrix.map_apply, genMatFr, φD,
    renFr_algebraMap, rename_X, hr, false_and, if_false]
  rfl

theorem det_genMatFr_ne_zero (m : ℕ) (τ : Ψ) : (genMatFr F Ψ m τ).det ≠ 0 := by
  let f : MvPolynomial (Fin m × Fin m) F →+* GenFrac F Ψ m :=
    (algebraMap (MvPolynomial (Ψ × Fin m × Fin m) F) (GenFrac F Ψ m)).comp (rename fun q => (τ, q)).toRingHom
  have hf : Function.Injective f := (IsFractionRing.injective _ _).comp (rename_injective _ (Prod.mk_right_injective τ))
  have e : genMatFr F Ψ m τ = f.mapMatrix (Matrix.mvPolynomialX (Fin m) (Fin m) F) := by
    ext a b
    simp [f, genMatFr, Matrix.mvPolynomialX]
  rw [e, ← RingHom.map_det]
  intro h0
  exact Matrix.det_mvPolynomialX_ne_zero (Fin m) F (hf (h0.trans (map_zero f).symm))

theorem pivotMinor_mapAlg {K L : Type} [CommRing K] [CommRing L] [Algebra F K] [Algebra F L] {m : ℕ}
    (f : K →ₐ[F] L) (M : Matrix (Fin m) (Fin m) K) (a : Fin (m - 1)) (b : Fin m) :
    pivotMinor (M.map f) a b = f (pivotMinor M a b) :=
  FlagRatioTrdeg.pivotMinor_map (f : K →+* L) M a b

theorem det_mapAlg {K L : Type} [CommRing K] [CommRing L] [Algebra F K] [Algebra F L] {m : ℕ}
    (f : K →ₐ[F] L) (M : Matrix (Fin m) (Fin m) K) : (M.map f).det = f M.det :=
  (AlgHom.map_det f M).symm

theorem ratio_A (τ : Ψ) (a : Fin (j - 1)) (b : Fin j) (hab : (a : ℕ) < b) (A : Fin (n - 1)) (B : Fin n)
    (hA : (A : ℕ) = a) (hB : (B : ℕ) = b) :
    pivotMinor (genMat0Fr F Ψ n j τ) A B / leadMinor (genMat0Fr F Ψ n j τ) A =
      φA F Ψ h (pivotRatio F Ψ j (τ, ⟨a, ⟨b, hab⟩⟩)) := by
  rw [pivotMinor_topLeft h _ a b A B hA hB, leadMinor,
    pivotMinor_topLeft h _ a (Fin.castLE (Nat.sub_le j 1) a) A _ hA (by simp [hA]), topLeft_eq,
    pivotMinor_mapAlg, pivotMinor_mapAlg, pivotRatio, map_div₀]
  rfl

theorem ratio_D (τ : Ψ) (a : Fin (n - j - 1)) (b : Fin (n - j)) (hab : (a : ℕ) < b) (A : Fin (n - 1)) (B : Fin n)
    (hA : (A : ℕ) = j + a) (hB : (B : ℕ) = j + b) :
    pivotMinor (genMat0Fr F Ψ n j τ) A B / leadMinor (genMat0Fr F Ψ n j τ) A =
      φD F Ψ h (pivotRatio F Ψ (n - j) (τ, ⟨a, ⟨b, hab⟩⟩)) := by
  have hz := zero_block F Ψ (n := n) (j := j) τ
  rw [pivotMinor_block h _ hz a b A B hA hB, leadMinor,
    pivotMinor_block h _ hz a (Fin.castLE (Nat.sub_le (n - j) 1) a) A _ hA (by simp [hA]),
    mul_div_mul_left _ _ (by rw [topLeft_eq, det_mapAlg]; exact (map_ne_zero_iff _ (φA F Ψ h).toRingHom.injective).2 (det_genMatFr_ne_zero F Ψ j τ)),
    botRight_eq, pivotMinor_mapAlg, pivotMinor_mapAlg, pivotRatio, map_div₀]
  rfl

end Generic

section Indep

variable (F : Type) [Field F] (Ψ : Type) {n j : ℕ} (h : j ≤ n)

abbrev IdxLe (Ψ : Type) (n j : ℕ) : Type := FlagRatioTrdeg.PivotIdxLe Ψ j ⊕ FlagRatioTrdeg.PivotIdxLe Ψ (n - j)

def wpol : IdxLe Ψ n j → MvPolynomial (Ψ × Fin n × Fin n) F :=
  Sum.elim (fun q => rename (eA Ψ h) (pivotMinor (FlagRatioTrdeg.genMatPol F Ψ j q.1) q.2.1 q.2.2.1))
    (fun q => rename (eD Ψ h) (pivotMinor (FlagRatioTrdeg.genMatPol F Ψ (n - j) q.1) q.2.1 q.2.2.1))

def sp (v : Ψ × Fin n × Fin n) : GenFrac F Ψ n :=
  if hv : (v.2.1 : ℕ) < j ∧ (v.2.2 : ℕ) < j then
    φA F Ψ h (FlagRatioTrdeg.specAll F Ψ j (v.1, ⟨v.2.1, hv.1⟩, ⟨v.2.2, hv.2⟩))
  else if hv' : j ≤ (v.2.1 : ℕ) ∧ j ≤ (v.2.2 : ℕ) then
    φD F Ψ h (FlagRatioTrdeg.specAll F Ψ (n - j)
      (v.1, ⟨v.2.1 - j, by have := v.2.1.2; omega⟩, ⟨v.2.2 - j, by have := v.2.2.2; omega⟩))
  else 0

theorem sp_eA : sp F Ψ h ∘ eA Ψ h = fun p => φA F Ψ h (FlagRatioTrdeg.specAll F Ψ j p) := by
  funext ⟨τ, a, b⟩
  simp [sp, eA]

theorem sp_eD : sp F Ψ h ∘ eD Ψ h = fun p => φD F Ψ h (FlagRatioTrdeg.specAll F Ψ (n - j) p) := by
  funext ⟨τ, a, b⟩
  simp [sp, eD]

def idx : IdxLe Ψ n j → Ψ × Fin n × Fin n :=
  Sum.elim (fun q => eA Ψ h (q.1, Fin.castLE (Nat.sub_le j 1) q.2.1, q.2.2.1))
    (fun q => eD Ψ h (q.1, Fin.castLE (Nat.sub_le (n - j) 1) q.2.1, q.2.2.1))

theorem idx_inj : Function.Injective (idx Ψ h) := by
  rintro (⟨τ, a, b, hb⟩ | ⟨τ, a, b, hb⟩) (⟨τ', a', b', hb'⟩ | ⟨τ', a', b', hb'⟩) e <;>
    simp only [idx, Sum.elim_inl, Sum.elim_inr, eA, eD, Prod.mk.injEq, Fin.ext_iff, Fin.val_castLE] at e
  · obtain ⟨h0, h1, h2⟩ := e
    subst h0
    have h1' : a = a' := Fin.ext h1
    subst h1'
    have h2' : b = b' := Fin.ext h2
    subst h2'
    rfl
  · obtain ⟨_, h1, _⟩ := e
    have := a.2
    omega
  · obtain ⟨_, h1, _⟩ := e
    have := a'.2
    omega
  · obtain ⟨h0, h1, h2⟩ := e
    subst h0
    have h1' : a = a' := Fin.ext (by omega)
    subst h1'
    have h2' : b = b' := Fin.ext (by omega)
    subst h2'
    rfl

theorem wpol_indep : AlgebraicIndependent F (wpol F Ψ h) := by
  refine AlgebraicIndependent.of_comp (aeval (sp F Ψ h)) ?_
  have hfun : ⇑(aeval (sp F Ψ h)) ∘ wpol F Ψ h =
      ⇑(IsScalarTower.toAlgHom F (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n)) ∘
        ((X : Ψ × Fin n × Fin n → MvPolynomial (Ψ × Fin n × Fin n) F) ∘ idx Ψ h) := by
    funext q
    rcases q with ⟨τ, a, b, hab⟩ | ⟨τ, a, b, hab⟩
    · simp only [Function.comp_apply, wpol, Sum.elim_inl, idx, IsScalarTower.toAlgHom_apply]
      rw [aeval_rename, sp_eA, ← comp_aeval_apply, FlagRatioTrdeg.specAll_pivotMinor F Ψ j τ a b hab]
      rw [φA, renFr_algebraMap, rename_X]
    · simp only [Function.comp_apply, wpol, Sum.elim_inr, idx, IsScalarTower.toAlgHom_apply]
      rw [aeval_rename, sp_eD, ← comp_aeval_apply, FlagRatioTrdeg.specAll_pivotMinor F Ψ (n - j) τ a b hab]
      rw [φD, renFr_algebraMap, rename_X]
  rw [hfun]
  refine AlgebraicIndependent.map' ?_ (IsFractionRing.injective _ _)
  exact (algebraicIndependent_X _ F).comp _ (idx_inj Ψ h)

def w : IdxLe Ψ n j → GenFrac F Ψ n :=
  Sum.elim (fun q => φA F Ψ h (pivotMinor (genMatFr F Ψ j q.1) q.2.1 q.2.2.1))
    (fun q => φD F Ψ h (pivotMinor (genMatFr F Ψ (n - j) q.1) q.2.1 q.2.2.1))

theorem w_indep : AlgebraicIndependent F (w F Ψ h) := by
  have hw := (wpol_indep F Ψ h).map'
    (f := IsScalarTower.toAlgHom F (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n))
    (IsFractionRing.injective _ _)
  convert hw using 1
  funext q
  rcases q with ⟨τ, a, b, hab⟩ | ⟨τ, a, b, hab⟩
  · simp only [w, wpol, Function.comp_apply, Sum.elim_inl, IsScalarTower.toAlgHom_apply]
    rw [FlagRatioTrdeg.genMatFr_eq, FlagRatioTrdeg.pivotMinor_map, φA, renFr_algebraMap]
  · simp only [w, wpol, Function.comp_apply, Sum.elim_inr, IsScalarTower.toAlgHom_apply]
    rw [FlagRatioTrdeg.genMatFr_eq, FlagRatioTrdeg.pivotMinor_map, φD, renFr_algebraMap]

def z : PivotIdx Ψ j ⊕ PivotIdx Ψ (n - j) → GenFrac F Ψ n :=
  Sum.elim (fun q => φA F Ψ h (pivotRatio F Ψ j q)) (fun q => φD F Ψ h (pivotRatio F Ψ (n - j) q))

def diagIdx (m : ℕ) (q : FlagRatioTrdeg.PivotIdxLe Ψ m) : FlagRatioTrdeg.PivotIdxLe Ψ m :=
  (q.1, ⟨q.2.1, ⟨Fin.castLE (Nat.sub_le m 1) q.2.1, by simp⟩⟩)

def inclIdx (m : ℕ) (q : PivotIdx Ψ m) : FlagRatioTrdeg.PivotIdxLe Ψ m := (q.1, ⟨q.2.1, ⟨q.2.2.1, q.2.2.2.le⟩⟩)

theorem inclIdx_inj (m : ℕ) : Function.Injective (inclIdx Ψ m) := by
  rintro ⟨τ, a, b, hb⟩ ⟨τ', a', b', hb'⟩ e
  simp only [inclIdx, Prod.mk.injEq, Sigma.mk.inj_iff] at e
  obtain ⟨h0, h1, h2⟩ := e
  subst h0 h1
  simp only [heq_eq_eq, Subtype.mk.injEq] at h2
  subst h2
  rfl

theorem diag_ne (m : ℕ) (q : PivotIdx Ψ m) : diagIdx Ψ m (inclIdx Ψ m q) ≠ inclIdx Ψ m q := by
  intro e
  have := congrArg (fun r : FlagRatioTrdeg.PivotIdxLe Ψ m => ((r.2.2.1 : Fin m) : ℕ)) e
  simp only [diagIdx, inclIdx, Fin.val_castLE] at this
  have := q.2.2.2
  omega

theorem z_indep : AlgebraicIndependent F (z F Ψ h) := by
  classical
  let δ : IdxLe Ψ n j → IdxLe Ψ n j := Sum.map (diagIdx Ψ j) (diagIdx Ψ (n - j))
  have hz := FlagRatioTrdeg.ratio_indep F (w_indep F Ψ h) δ (fun t => by rcases t with t | t <;> rfl)
  have hinj : Function.Injective (Sum.map (inclIdx Ψ j) (inclIdx Ψ (n - j))) :=
    Sum.map_injective.2 ⟨inclIdx_inj Ψ j, inclIdx_inj Ψ (n - j)⟩
  suffices e : (fun i => if δ i = i then w F Ψ h i else w F Ψ h i / w F Ψ h (δ i)) ∘
      Sum.map (inclIdx Ψ j) (inclIdx Ψ (n - j)) = z F Ψ h by
    rw [← e]
    exact hz.comp _ hinj
  funext q
  rcases q with q | q
  · have hne : δ (Sum.inl (inclIdx Ψ j q)) ≠ Sum.inl (inclIdx Ψ j q) :=
      fun e => diag_ne Ψ j q (Sum.inl_injective e)
    rw [Function.comp_apply, Sum.map_inl, if_neg hne]
    simp only [z, w, δ, Sum.map_inl, Sum.elim_inl, pivotRatio, map_div₀]
    rfl
  · have hne : δ (Sum.inr (inclIdx Ψ (n - j) q)) ≠ Sum.inr (inclIdx Ψ (n - j) q) :=
      fun e => diag_ne Ψ (n - j) q (Sum.inr_injective e)
    rw [Function.comp_apply, Sum.map_inr, if_neg hne]
    simp only [z, w, δ, Sum.map_inr, Sum.elim_inr, pivotRatio, map_div₀]
    rfl

include h in

theorem leadMinor_ne_zero (τ : Ψ) (A : Fin (n - 1)) : leadMinor (genMat0Fr F Ψ n j τ) A ≠ 0 := by
  by_cases hA : (A : ℕ) < j
  · have e := pivotMinor_congr (genMat0Fr F Ψ n j τ) (genMatFr F Ψ n τ)
      (fun r c _ hc => by simp [genMat0Fr, Nat.not_le.2 hc]) A (Fin.castLE (Nat.sub_le n 1) A) hA (by simpa using hA)
    rw [leadMinor, e]
    exact (FlagRatioTrdeg.pivot_indep F Ψ n).ne_zero (τ, ⟨A, ⟨Fin.castLE (Nat.sub_le n 1) A, by simp⟩⟩)
  · have hA' : j ≤ (A : ℕ) := Nat.le_of_not_lt hA
    let a : Fin (n - j - 1) := ⟨A - j, by have := A.2; omega⟩
    rw [leadMinor, pivotMinor_block h _ (zero_block F Ψ τ) a (Fin.castLE (Nat.sub_le (n - j) 1) a) A _
      (by simp [a]; omega) (by simp [a]; omega)]
    refine mul_ne_zero ?_ ?_
    · rw [topLeft_eq, det_mapAlg]
      exact (map_ne_zero _).2 (det_genMatFr_ne_zero F Ψ j τ)
    · rw [botRight_eq, pivotMinor_mapAlg]
      exact (map_ne_zero _).2
        ((FlagRatioTrdeg.pivot_indep F Ψ (n - j)).ne_zero (τ, ⟨a, ⟨Fin.castLE (Nat.sub_le (n - j) 1) a, by simp⟩⟩))

end Indep

theorem proof : HodgeFlagMinorTrdeg.Statement := by
  intro F _ Ψ _ n j h
  classical
  have hadj : IntermediateField.adjoin F (Set.range (flagMinorRatio0 F Ψ n j)) =
      IntermediateField.adjoin F (Set.range (z F Ψ h)) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨⟨τ, i, S⟩, rfl⟩
      refine FlagRatioTrdeg.flag_mem F (genMat0Fr F Ψ n j τ) _ (leadMinor_ne_zero F Ψ h τ) (fun a b hab => ?_) i S
      by_cases hb : (b : ℕ) < j
      · rw [ratio_A F Ψ h τ ⟨a, by omega⟩ ⟨b, hb⟩ hab a b rfl rfl]
        exact IntermediateField.subset_adjoin F _ ⟨Sum.inl (τ, ⟨⟨a, by omega⟩, ⟨⟨b, hb⟩, hab⟩⟩), rfl⟩
      · by_cases ha : j ≤ (a : ℕ)
        · have h1 : (a : ℕ) - j < n - j - 1 := by have := a.2; omega
          have h2 : (b : ℕ) - j < n - j := by have := b.2; omega
          have h3 : (a : ℕ) - j < (b : ℕ) - j := by omega
          rw [ratio_D F Ψ h τ ⟨a - j, h1⟩ ⟨b - j, h2⟩ h3 a b (by simp; omega) (by simp; omega)]
          exact IntermediateField.subset_adjoin F _ ⟨Sum.inr (τ, ⟨⟨a - j, h1⟩, ⟨⟨b - j, h2⟩, h3⟩⟩), rfl⟩
        · rw [pivotMinor_eq_zero_of_block _ (zero_block F Ψ τ) a b (by omega) (by omega), zero_div]
          exact IntermediateField.zero_mem _
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨(⟨τ, a, b, hab⟩ | ⟨τ, a, b, hab⟩), rfl⟩
      · let A : Fin (n - 1) := ⟨a, by have := a.2; omega⟩
        let B : Fin n := Fin.castLE h b
        have hAB : (A : ℕ) ≤ B := by simp only [A, B, Fin.val_castLE]; omega
        refine IntermediateField.subset_adjoin F _ ⟨(τ, ⟨A, ⟨_, card_image_pivotCols A B hAB⟩⟩), ?_⟩
        simp only [flagMinorRatio0, z, Sum.elim_inl]
        rw [← pivotMinor_eq_flagMinor _ A B hAB]
        exact ratio_A F Ψ h τ a b hab A B rfl (by simp [B])
      · let A : Fin (n - 1) := ⟨j + a, by have := a.2; omega⟩
        let B : Fin n := ⟨j + b, by have := b.2; omega⟩
        have hAB : (A : ℕ) ≤ B := by simp only [A, B]; omega
        refine IntermediateField.subset_adjoin F _ ⟨(τ, ⟨A, ⟨_, card_image_pivotCols A B hAB⟩⟩), ?_⟩
        simp only [flagMinorRatio0, z, Sum.elim_inr]
        rw [← pivotMinor_eq_flagMinor _ A B hAB]
        exact ratio_D F Ψ h τ a b hab A B rfl rfl
  rw [hadj, FlagRatioTrdeg.trdeg_adjoin_eq (z_indep F Ψ h), Cardinal.mk_fintype, Fintype.card_sum,
    FlagRatioTrdeg.card_pivotIdx, FlagRatioTrdeg.card_pivotIdx, ← mul_add]
  rfl

end HodgeFlagMinorTrdeg

theorem HodgeFlagMinorTrdeg.full : HodgeFlagMinorTrdeg.Statement := HodgeFlagMinorTrdeg.proof

end GroundTheory.Heights₂.Heights.LowerBoundFree
