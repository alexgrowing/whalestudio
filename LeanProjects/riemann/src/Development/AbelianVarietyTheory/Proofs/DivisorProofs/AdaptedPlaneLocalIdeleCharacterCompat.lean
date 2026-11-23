import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFirstApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.JacBridge.Geom

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace GlobalTheory.UnitaryInjAtPlace

section Pure

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

def mid (j : Fin n) : Fin (n + 2) := j.castSucc.succ

theorem mid_ne_zero (j : Fin n) : mid j ≠ 0 := Fin.succ_ne_zero _

theorem mid_ne_last (j : Fin n) : mid j ≠ Fin.last (n + 1) := by
  intro h
  have := congrArg Fin.val h
  simp [mid] at this
  omega

theorem idx_cases (i : Fin (n + 2)) : i = 0 ∨ i = Fin.last (n + 1) ∨ ∃ j, i = mid j := by
  by_cases h0 : i = 0
  · exact Or.inl h0
  by_cases h1 : i = Fin.last (n + 1)
  · exact Or.inr (Or.inl h1)
  have a0 : i.1 ≠ 0 := fun h => h0 (Fin.ext h)
  have a1 : i.1 ≠ n + 1 := fun h => h1 (Fin.ext h)
  refine Or.inr (Or.inr ⟨⟨i.1 - 1, by omega⟩, Fin.ext ?_⟩)
  simp [mid]
  omega

def colQ (x y : Fin (n + 2) → R) (ι : Matrix (Fin (n + 2)) (Fin n) R) : Matrix (Fin (n + 2)) (Fin (n + 2)) R :=
  Matrix.of fun r i =>
    if i.1 = 0 then x r else if i.1 + 1 = n + 2 then y r
    else if h : i.1 - 1 < n then ι r ⟨i.1 - 1, h⟩ else 0

variable (x y : Fin (n + 2) → R) (ι : Matrix (Fin (n + 2)) (Fin n) R)

@[simp] theorem colQ_zero (r : Fin (n + 2)) : colQ x y ι r 0 = x r := by simp [colQ]

@[simp] theorem colQ_last (r : Fin (n + 2)) : colQ x y ι r (Fin.last (n + 1)) = y r := by simp [colQ]

@[simp] theorem colQ_mid (r : Fin (n + 2)) (j : Fin n) : colQ x y ι r (mid j) = ι r j := by
  have := j.2
  have h : j.1 ≠ n := by omega
  simp [colQ, mid, h]

theorem colQ_map (f : R →+* S) : (colQ x y ι).map f = colQ (fun r => f (x r)) (fun r => f (y r)) (ι.map f) := by
  ext r i
  rcases idx_cases i with rfl | rfl | ⟨j, rfl⟩ <;> simp

theorem colQ_mulVec (c : Fin (n + 2) → R) :
    colQ x y ι *ᵥ c = c 0 • x + ι *ᵥ (fun j => c (mid j)) + c (Fin.last (n + 1)) • y := by
  ext r
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, Fin.succ_last, colQ_zero, colQ_last]
  have : ∀ j : Fin n, j.castSucc.succ = mid j := fun _ => rfl
  simp only [this, colQ_mid]
  ring

theorem mul_colQ_of_levi (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) (a b : R) (hx : M *ᵥ x = a • x)
    (hy : M *ᵥ y = b • y) (hι : M * ι = ι) :
    M * colQ x y ι = colQ x y ι *
      Matrix.diagonal fun i => if i = 0 then a else if i = Fin.last (n + 1) then b else 1 := by
  ext r i
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  rcases idx_cases i with rfl | rfl | ⟨j, rfl⟩
  · have := congrFun hx r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [colQ_zero, this, if_true]
    exact mul_comm _ _
  · have := congrFun hy r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    have h : Fin.last (n + 1) ≠ 0 := Fin.last_pos.ne'
    simp only [colQ_last, this, if_true, if_neg h]
    exact mul_comm _ _
  · have := congrFun (congrFun hι r) j
    rw [Matrix.mul_apply] at this
    simp [this, mid_ne_zero, mid_ne_last]

theorem unip_of_mul_colQ (M u : Matrix (Fin (n + 2)) (Fin (n + 2)) R) (h : M * colQ x y ι = colQ x y ι * u)
    (h0 : ∀ i, (u - 1) i 0 = 0) (h1 : ∀ i j, i ≠ 0 → (u - 1) i (mid j) = 0) :
    M *ᵥ x = x ∧ ∀ z, ∃ a : R, M *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x := by
  have key : ∀ c, M *ᵥ (colQ x y ι *ᵥ c) = colQ x y ι *ᵥ c + colQ x y ι *ᵥ ((u - 1) *ᵥ c) := by
    intro c
    rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, Matrix.sub_mulVec, Matrix.one_mulVec,
      add_sub_cancel]
  have hl : Fin.last (n + 1) ≠ 0 := Fin.last_pos.ne'
  constructor
  · have e : colQ x y ι *ᵥ Pi.single 0 1 = x := by ext r; simp
    have e' : (u - 1) *ᵥ Pi.single 0 1 = 0 := by
      ext r; rw [Matrix.mulVec_single_one]; exact h0 r
    have := key (Pi.single 0 1)
    rwa [e, e', Matrix.mulVec_zero, add_zero] at this
  · intro z
    let c : Fin (n + 2) → R := Fin.cons 0 (Fin.snoc (α := fun _ => R) z 0)
    have c0 : c 0 = 0 := rfl
    have c1 : c (Fin.last (n + 1)) = 0 := by
      simp only [c]; rw [← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]
    have c2 : ∀ j, c (mid j) = z j := fun j => by simp [c, mid]
    have e : colQ x y ι *ᵥ c = ι *ᵥ z := by
      rw [colQ_mulVec, c0, c1, funext c2]; simp
    have e' : ∀ i, i ≠ 0 → ((u - 1) *ᵥ c) i = 0 := by
      intro i hi
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun k _ => ?_
      rcases idx_cases k with rfl | rfl | ⟨j, rfl⟩
      · rw [c0, mul_zero]
      · rw [c1, mul_zero]
      · rw [h1 i j hi, zero_mul]
    refine ⟨((u - 1) *ᵥ c) 0, ?_⟩
    have := key c
    rw [e, colQ_mulVec x y ι ((u - 1) *ᵥ c), e' _ hl, funext fun j => e' _ (mid_ne_zero j)] at this
    rw [this]
    simp [← Pi.zero_def]

end Pure

section Field

variable {K : Type} [Field K] {n : ℕ}

theorem unipStd_entry {u : GL (Fin (n + 2)) K} (hu : GlobalTheory.JacBlock₂.IsUnipStd u) {i k : Fin (n + 2)}
    (h : k = 0 ∨ i = Fin.last (n + 1) ∨ (i ≠ 0 ∧ k ≠ Fin.last (n + 1))) : (u.1 - 1) i k = 0 := by
  by_cases hik : i = k
  · subst hik; simp [hu.1]
  rw [Matrix.sub_apply, Matrix.one_apply_ne hik, sub_zero]
  refine hu.2 i k hik ?_
  have hi := i.2
  have hk := k.2
  simp only [Fin.ext_iff, ne_eq, Fin.val_zero, Fin.val_last] at h
  unfold GlobalTheory.JacBlock₂.blk
  split_ifs <;> omega

theorem dual_unip {u : GL (Fin (n + 2)) K} (hu : GlobalTheory.JacBlock₂.IsUnipStd u) (G u' : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (hG : IsUnit G.det) (hc : ∀ i, i ≠ Fin.last (n + 1) → G i 0 = 0) (hr : ∀ j, G 0 (mid j) = 0)
    (h : u.1ᵀ * G * u' = G) :
    (∀ i, (u' - 1) i 0 = 0) ∧ ∀ i j, i ≠ 0 → (u' - 1) i (mid j) = 0 := by
  have hA : IsUnit (u.1ᵀ * G) := by
    have hd := congrArg Matrix.det h
    rw [Matrix.det_mul] at hd
    exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left (hd ▸ hG))
  have inj := Matrix.mulVec_injective_iff_isUnit.2 hA
  have hc0 : G (Fin.last (n + 1)) 0 ≠ 0 := by
    intro h0
    refine hG.ne_zero (Matrix.det_eq_zero_of_column_eq_zero 0 fun i => ?_)
    by_cases hi : i = Fin.last (n + 1)
    · rw [hi, h0]
    · exact hc i hi
  set T : Matrix (Fin (n + 2)) (Fin (n + 2)) K := (u.1 - 1)ᵀ * G with hT
  set A : Matrix (Fin (n + 2)) (Fin (n + 2)) K := u.1ᵀ * G with hA'
  have e : A * (u' - 1) = -T := by
    rw [hT, Matrix.mul_sub, h, Matrix.mul_one, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.one_mul,
      neg_sub]
  have z0 : ∀ k, T k 0 = 0 := by
    intro k
    rw [hT, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i = Fin.last (n + 1)
    · rw [Matrix.transpose_apply, unipStd_entry hu (Or.inr (Or.inl hi)), zero_mul]
    · rw [hc i hi, mul_zero]
  have g0 : ∀ k, A k 0 = G k 0 := by
    intro k
    have := z0 k
    rwa [hT, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, sub_eq_zero] at this
  have col : ∀ j, A *ᵥ (fun i => (u' - 1) i j) = fun k => -T k j := by
    intro j; ext k
    exact congrFun (congrFun e k) j
  constructor
  · intro i
    have : A *ᵥ (fun i => (u' - 1) i 0) = A *ᵥ 0 := by
      rw [col, Matrix.mulVec_zero]; ext k; simp only [z0, neg_zero, Pi.zero_apply]
    exact congrFun (inj this) i
  · intro i j hi
    set a := -T (Fin.last (n + 1)) (mid j) / G (Fin.last (n + 1)) 0 with ha
    have : A *ᵥ (fun i => (u' - 1) i (mid j)) = A *ᵥ Pi.single 0 a := by
      rw [col, Matrix.mulVec_single]; ext k
      simp only [Pi.smul_apply, Matrix.col_apply, g0, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      by_cases hk : k = Fin.last (n + 1)
      · rw [hk, ha, mul_div_cancel₀ _ hc0]
      · rw [hc k hk, zero_mul, neg_eq_zero, hT, Matrix.mul_apply]
        refine Finset.sum_eq_zero fun l _ => ?_
        by_cases hl : l = 0
        · rw [hl, hr, mul_zero]
        · rw [Matrix.transpose_apply, unipStd_entry hu (Or.inr (Or.inr ⟨hl, hk⟩)), zero_mul]
    rw [congrFun (inj this) i, Pi.single_eq_of_ne hi]

end Field

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma (hc : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hc.2.2.2, hc.2.2.2, star_star]

theorem piW_incl {v : Pl F} (t : E →ₐ[F] Fv F v) (x : E) : piW t (inclR (F := F) (AF F) x) = t x := by
  change splitProj t (compFin F E v (inclR (F := F) (AF F) x)) = t x
  rw [compFin_inclR, splitProj_inclR]

theorem piW_cA {v : Pl F} (t : E →ₐ[F] Fv F v) (a : AE F E) : piW t (cA σ a) = piW (t.comp σ) a := by
  change splitProj t (compFin F E v _) = splitProj _ (compFin F E v _)
  rw [compFin_cA, splitProj_comp]

theorem incM_map_piW {v : Pl F} (t : E →ₐ[F] Fv F v) {m n : Type} (M : Matrix m n E) :
    (incM F M).map (piW t) = M.map t := by
  refine Matrix.ext fun i j => ?_
  rw [incM, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply]
  exact piW_incl t (M i j)

theorem eq_zero_of_at (hc : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v) (a : AE F E) (ha : At (evFin F v) a)
    (h1 : piW t a = 0) (h2 : piW (t.comp σ) a = 0) : a = 0 := by
  have h : (Matrix.of fun (_ _ : Fin 1) => compFin F E v a) = 0 := by
    refine mat_split_ext hc t ?_ ?_
    · exact Matrix.ext fun i j => h1.trans (map_zero (splitProj t)).symm
    · exact Matrix.ext fun i j => h2.trans (map_zero (splitProj (t.comp σ))).symm
  have h0 : compFin F E v a = 0 := congrFun (congrFun h 0) 0
  rw [eq_tensAt_of_at v a ha, h0, map_zero]

theorem at_conj {v : Pl F} {n : ℕ} (P Z Q : Matrix (Fin n) (Fin n) (AE F E)) (h : At (evFin F v) Z) :
    At (evFin F v) (P * Z * Q) := by
  intro u hu
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, h u hu, Matrix.mul_zero, Matrix.zero_mul]

theorem form_skew (hc : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = -J i j)
    (a b : Fin n → E) : form σ J a b = -σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hJ, sigma_sigma hc, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_entry {n : ℕ} (J Q : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    (Qᵀ * J * Q.map σ) i j = form σ J (fun r => Q r i) (fun r => Q r j) := by
  rw [Matrix.mul_assoc]
  rfl

variable {B : Base F E} {d₁ r s : ℕ} {W : Spc F E (d₁ + 2)} {W₁ : Spc F E d₁} {H' : Plane E (d₁ + 2) d₁} {i₀ i₁ : ℕ}

theorem isUnit_colQ (hW : W.IsSkew σ B r s) (hH : H'.IsAdapted σ B W W₁ i₀ i₁) : IsUnit (colQ H'.x H'.y H'.ι).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
  have hle : Submodule.span E (W.L : Set (Fin (d₁ + 2) → E)) ≤ LinearMap.range (colQ H'.x H'.y H'.ι).mulVecLin := by
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨a, b, u, -, -, -, rfl⟩ := hH.split z hz
    refine ⟨Fin.cons a (Fin.snoc (α := fun _ => E) u b), ?_⟩
    rw [Matrix.mulVecLin_apply, colQ_mulVec, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]
    simp [mid]
  rw [hW.lat.span_eq_top, top_le_iff, LinearMap.range_eq_top] at hle
  exact hle

theorem det_J_ne_zero {d : ℕ} {W : Spc F E d} (hW : W.IsSkew σ B r s) : W.J.det ≠ 0 := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have h0 := det_ne_zero_of_sig (hW.sig (InfinitePlace.mk φ))
  exact fun e => h0 (by
    rw [Matrix.det_smul, show W.J.map _ = RingHom.mapMatrix _ W.J from rfl, ← RingHom.map_det, e, map_zero, mul_zero])

theorem adaptQ_eq {v : Pl F} (t : E →ₐ[F] Fv F v) : adaptQ t H' = (colQ H'.x H'.y H'.ι).map t := by
  have := colQ_map H'.x H'.y H'.ι (t : E →+* Fv F v)
  exact this.symm

theorem incM_colQ : incM F (colQ H'.x H'.y H'.ι) = colQ (incV F H'.x) (incV F H'.y) (incM F H'.ι) :=
  colQ_map _ _ _ _

theorem isUnit_map {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) {Q : Matrix (Fin n) (Fin n) R}
    (h : IsUnit Q.det) : IsUnit (Q.map f).det := by
  rw [show Q.map f = f.mapMatrix Q from rfl, ← RingHom.map_det]
  exact h.map f

theorem levi_at (hW : W.IsSkew σ B r s) (hH : H'.IsAdapted σ B W W₁ i₀ i₁) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (l : (AE F E)ˣ) (c : (Fv F v)ˣ) (h1 : piW t (l : AE F E) = c) (h2 : piW (t.comp σ) (l : AE F E) = 1)
    (h3 : At (evFin F v) ((l : AE F E) - 1)) (m : UA σ W.J) (hm : IsLevi (W₁ := W₁) H' l 1 m) :
    m ∈ UAt σ W (evFin F v) ∧
      (mat m).map (piW t) = adaptQ t H' * (GlobalTheory.JacBlock₂.diagFirst c).1 * (adaptQ t H')⁻¹ := by
  have hQ := isUnit_colQ hW hH
  have hQA : IsUnit (incM F (colQ H'.x H'.y H'.ι)).det := isUnit_map _ hQ
  have hQt : IsUnit (adaptQ t H').det := by rw [adaptQ_eq]; exact isUnit_map (t : E →+* Fv F v) hQ
  have hι : mat m * incM F H'.ι = incM F H'.ι := by
    rw [hm.2.2]; exact Matrix.mul_one _
  have key := mul_colQ_of_levi _ _ _ (mat m) _ _ hm.1 hm.2.1 hι
  rw [← incM_colQ] at key
  have hinv : piW (t.comp σ) ((l⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by
    have := map_mul (piW (t.comp σ)) (l : AE F E) ((l⁻¹ : (AE F E)ˣ) : AE F E)
    rw [Units.mul_inv, map_one, h2, one_mul] at this
    exact this.symm
  constructor
  · set D : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) (AE F E) := Matrix.diagonal fun i => if i = 0 then (l : AE F E) else
      if i = Fin.last (d₁ + 1) then cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E) else 1 with hD
    have e : mat m - 1 = incM F (colQ H'.x H'.y H'.ι) * (D - 1) * (incM F (colQ H'.x H'.y H'.ι))⁻¹ := by
      rw [Matrix.mul_sub, ← key, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hQA,
        Matrix.mul_nonsing_inv _ hQA]
    change At _ (mat m - 1)
    rw [e]
    refine at_conj _ _ _ fun u hu => ?_
    have a1 := h3 u hu
    have a2 : u • (cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E) - 1) = 0 := by
      have : ((l⁻¹ : (AE F E)ˣ) : AE F E) - 1 = -((l⁻¹ : (AE F E)ˣ) : AE F E) * ((l : AE F E) - 1) := by
        rw [neg_mul, mul_sub, Units.inv_mul, mul_one, neg_sub]
      rw [← map_one (cA σ), ← map_sub, ← map_smul, this, ← mul_smul_comm, a1, mul_zero, map_zero]
    ext i j
    rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, hD]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      split_ifs
      · exact a1
      · exact a2
      · rw [sub_self, smul_zero]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, sub_self, smul_zero]
  · have k2 := congrArg (fun M => M.map (piW t)) key
    simp only [Matrix.map_mul, incM_map_piW, ← adaptQ_eq] at k2
    rw [← Matrix.mul_nonsing_inv_cancel_right _ ((mat m).map (piW t)) hQt, k2, Matrix.diagonal_map (map_zero _)]
    congr 2
    change _ = Matrix.diagonal fun i : Fin (d₁ + 2) => if i.1 = 0 then (c : Fv F v) else 1
    congr 1
    funext i
    by_cases hi : i = 0
    · subst hi; simp [h1]
    · have : i.1 ≠ 0 := fun h => hi (Fin.ext h)
      rw [if_neg hi, if_neg this]
      split_ifs
      · rw [piW_cA, hinv]
      · exact map_one _

theorem mem_unip_of_at (hc : IsCMExt F E σ) (hW : W.IsSkew σ B r s) (hH : H'.IsAdapted σ B W W₁ i₀ i₁) {v : Pl F}
    (t : E →ₐ[F] Fv F v) (u₀ : GL (Fin (d₁ + 2)) (Fv F v)) (hu : GlobalTheory.JacBlock₂.IsUnipStd u₀) (n : UA σ W.J)
    (hn : n ∈ UAt σ W (evFin F v)) (h : (mat n).map (piW t) = adaptQ t H' * u₀.1 * (adaptQ t H')⁻¹) :
    n ∈ unip σ W H' := by
  have hQ := isUnit_colQ hW hH
  rw [adaptQ_eq] at h
  set Q := colQ H'.x H'.y H'.ι with hQdef
  have hQA : IsUnit (incM F Q).det := isUnit_map _ hQ
  have hQt : IsUnit (Q.map t).det := isUnit_map (t : E →+* Fv F v) hQ
  set u := (incM F Q)⁻¹ * mat n * incM F Q with hudef
  have key : mat n * incM F Q = incM F Q * u := by
    rw [hudef, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hQA]
  have hat : At (evFin F v) (u - 1) := by
    have : u - 1 = (incM F Q)⁻¹ * (mat n - 1) * incM F Q := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.nonsing_inv_mul _ hQA]
    rw [this]
    exact at_conj _ _ _ hn
  have k1 := congrArg (fun M => M.map (piW t)) key
  have k2 := congrArg (fun M => M.map (piW (t.comp σ))) key
  simp only [Matrix.map_mul, incM_map_piW] at k1 k2
  have k3 : (mat n).map (piW t) * Q.map t = Q.map t * u₀.1 := by
    rw [h, Matrix.nonsing_inv_mul_cancel_right _ _ hQt]
  have ut : u.map (piW t) = u₀.1 := by
    rw [← Matrix.nonsing_inv_mul_cancel_left _ (u.map (piW t)) hQt, ← k1, k3, Matrix.nonsing_inv_mul_cancel_left _ _ hQt]
  have hG : IsUnit ((Qᵀ * W.J * Q.map σ).map t).det := by
    refine isUnit_map (t : E →+* Fv F v) ?_
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact (hQ.mul (isUnit_iff_ne_zero.2 (det_J_ne_zero hW))).mul (isUnit_map (σ : E →+* E) hQ)
  have eG : (Qᵀ * W.J * Q.map σ).map t = (Q.map t)ᵀ * W.J.map t * Q.map (t.comp σ) := by
    have := Matrix.map_mul (f := (t : E →+* Fv F v)) (L := Qᵀ * W.J) (M := Q.map σ)
    rw [Matrix.map_mul (L := Qᵀ)] at this
    exact this
  have un := unitary_at_components v t n
  have hrel : u₀.1ᵀ * (Qᵀ * W.J * Q.map σ).map t * u.map (piW (t.comp σ)) = (Qᵀ * W.J * Q.map σ).map t := by
    rw [eG]
    calc _ = (Q.map t * u₀.1)ᵀ * W.J.map t * (Q.map (t.comp σ) * u.map (piW (t.comp σ))) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (Q.map t)ᵀ * (((mat n).map (piW t))ᵀ * W.J.map t * (mat n).map (piW (t.comp σ))) * Q.map (t.comp σ) := by
          rw [← k2, ← k3]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [un]
  have cx : (fun r => Q r 0) = H'.x := funext fun r => colQ_zero _ _ _ r
  have cm : ∀ j, (fun r => Q r (mid j)) = H'.ι *ᵥ Pi.single j 1 := fun j => funext fun r => by
    rw [Matrix.mulVec_single_one]; exact colQ_mid _ _ _ r j
  obtain ⟨d0, d1⟩ := dual_unip hu _ _ hG (fun i hi => by
      rw [Matrix.map_apply, gram_entry, cx]
      rcases idx_cases i with rfl | rfl | ⟨j, rfl⟩
      · rw [cx, hH.xx, map_zero]
      · exact absurd rfl hi
      · rw [cm, (hH.orth _).1, map_zero])
    (fun j => by
      rw [Matrix.map_apply, gram_entry, cx, cm, form_skew hc hW.skew, (hH.orth _).1, map_zero, neg_zero, map_zero]) hrel
  have ent : ∀ i j, (u₀.1 - 1) i j = 0 → (u.map (piW (t.comp σ)) - 1) i j = 0 → (u - 1) i j = 0 := by
    intro i j a b
    have mp : ∀ τ : E →ₐ[F] Fv F v, piW τ ((u - 1) i j) = (u.map (piW τ) - 1) i j := by
      intro τ
      rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    refine eq_zero_of_at hc t _ (fun z hz => congrFun (congrFun (hat z hz) i) j) ?_ ?_
    · rw [mp, ut, a]
    · rw [mp, b]
  rw [hQdef, incM_colQ] at key
  exact Subgroup.subset_closure (unip_of_mul_colQ _ _ _ (mat n) u key
    (fun i => ent i 0 (unipStd_entry hu (Or.inl rfl)) (d0 i))
    (fun i j hi => ent i _ (unipStd_entry hu (Or.inr (Or.inr ⟨hi, mid_ne_last j⟩))) (d1 i j hi)))

end Adelic

theorem adapted_basis_levi_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), IsCMExt F E σ →
  ∀ (d d₁ r s : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ →
  ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (w : HeightOneSpectrum (𝓞 E)) (e : (w.adicCompletion E)ˣ → (Fv F v)ˣ),
    (∀ x, piW t ((locIdele F w x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (e x : Fv F v)) →
    (∀ x, piW (t.comp σ) ((locIdele F w x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1) →
    (∀ x, At (evFin F v) (((locIdele F w x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1)) →
    IsUnit (GlobalTheory.JacBridge.adaptQ t H').det ∧
    (∀ x (m : UA σ W.J), IsLevi (W₁ := W₁) H' (locIdele F w x) 1 m → m ∈ UAt σ W (evFin F v) ∧
      (mat m).map (piW t) = GlobalTheory.JacBridge.adaptQ t H' * (GlobalTheory.JacBlock₂.diagFirst (e x)).1 * (GlobalTheory.JacBridge.adaptQ t H')⁻¹) ∧
    ∀ u₀ : GL (Fin d) (Fv F v), GlobalTheory.JacBlock₂.IsUnipStd u₀ → ∀ n : UA σ W.J, n ∈ UAt σ W (evFin F v) →
      (mat n).map (piW t) = GlobalTheory.JacBridge.adaptQ t H' * u₀.1 * (GlobalTheory.JacBridge.adaptQ t H')⁻¹ → n ∈ unip σ W H' := by
  intro F E _ _ _ _ _ σ B hc d d₁ r s W W₁ H' i₀ i₁ hW hH v t w e h1 h2 h3
  obtain rfl := hH.rank
  refine ⟨?_, fun x m hm => levi_at hW hH t _ (e x) (h1 x) (h2 x) (h3 x) m hm,
    fun u₀ hu n hn h => mem_unip_of_at hc hW hH t u₀ hu n hn h⟩
  rw [adaptQ_eq]
  exact isUnit_map (t : E →+* Fv F v) (isUnit_colQ hW hH)

end GlobalTheory.JacBridge.Geom
