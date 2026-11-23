import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ManyEdges
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.SharpRestriction.GrowthBounds.WittFrameLocaliserOrders

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G

section Col

variable {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ}

theorem mem_colSpan (G : Matrix (Fin k) (Fin k) Qq) (x : Fin k → Qq) :
    x ∈ colSpan W G ↔ ∃ y : Fin k → W, x = G.mulVec (fun c => algebraMap W Qq (y c)) := by
  unfold colSpan
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]

theorem colSpan_mul_le (G : Matrix (Fin k) (Fin k) Qq) (M : Matrix (Fin k) (Fin k) W) :
    colSpan W (G * M.map (algebraMap W Qq)) ≤ colSpan W G := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨c, rfl⟩
  rw [SetLike.mem_coe, mem_colSpan]
  refine ⟨fun b => M b c, ?_⟩
  funext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem colSpan_mul_unit (G : Matrix (Fin k) (Fin k) Qq) (M M' : Matrix (Fin k) (Fin k) W) (h : M * M' = 1) :
    colSpan W (G * M.map (algebraMap W Qq)) = colSpan W G := by
  apply le_antisymm (colSpan_mul_le G M)
  have h1 : G * M.map (algebraMap W Qq) * M'.map (algebraMap W Qq) = G := by
    rw [Matrix.mul_assoc, ← Matrix.map_mul, h]
    simp
  calc colSpan W G = colSpan W (G * M.map (algebraMap W Qq) * M'.map (algebraMap W Qq)) := by rw [h1]
    _ ≤ colSpan W (G * M.map (algebraMap W Qq)) := colSpan_mul_le _ M'

def dD (Qq : Type) [Field Qq] (p r k : ℕ) : Matrix (Fin k) (Fin k) Qq :=
  Matrix.diagonal fun c => if c.val < r then ((p : Qq))⁻¹ else 1

theorem dD_mul (p r : ℕ) (hp : (p : Qq) ≠ 0) :
    dD Qq p r k * (Matrix.diagonal fun c : Fin k => if c.val < r then (p : W) else 1).map (algebraMap W Qq) = 1 := by
  ext i j
  unfold dD
  rw [Matrix.diagonal_mul, Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i.val < r <;> simp [hi, hp]
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

theorem smul_dD (p r : ℕ) (hp : (p : Qq) ≠ 0) :
    (p : Qq) • dD Qq p r k =
      (Matrix.diagonal fun c : Fin k => if c.val < r then (1 : W) else (p : W)).map (algebraMap W Qq) := by
  ext i j
  unfold dD
  by_cases hij : i = j
  · subst hij
    by_cases hi : i.val < r <;> simp [hi, hp]
  · simp [Matrix.diagonal_apply_ne _ hij]

theorem src_le_tgt (p r : ℕ) (hp : (p : Qq) ≠ 0) (B : Matrix (Fin k) (Fin k) Qq) :
    colSpan W B ≤ colSpan W (B * dD Qq p r k) := by
  have h1 : B * dD Qq p r k * (Matrix.diagonal fun c : Fin k => if c.val < r then (p : W) else 1).map
      (algebraMap W Qq) = B := by
    rw [Matrix.mul_assoc, dD_mul (W := W) p r hp, Matrix.mul_one]
  calc colSpan W B = colSpan W (B * dD Qq p r k * (Matrix.diagonal fun c : Fin k =>
        if c.val < r then (p : W) else 1).map (algebraMap W Qq)) := by rw [h1]
    _ ≤ colSpan W (B * dD Qq p r k) := colSpan_mul_le _ _

theorem prime_smul_target_mem_source (p r : ℕ) (hp : (p : Qq) ≠ 0) (B : Matrix (Fin k) (Fin k) Qq) (x : Fin k → Qq)
    (hx : x ∈ colSpan W (B * dD Qq p r k)) : (p : W) • x ∈ colSpan W B := by
  rw [mem_colSpan] at hx
  obtain ⟨y, rfl⟩ := hx
  refine colSpan_mul_le (W := W) B
    (Matrix.diagonal fun c : Fin k => if c.val < r then (1 : W) else (p : W)) ?_
  rw [mem_colSpan]
  refine ⟨y, ?_⟩
  rw [← smul_dD (W := W) p r hp, Matrix.mul_smul]
  funext i
  simp [Matrix.mulVec, dotProduct, Algebra.smul_def, Finset.mul_sum, mul_assoc]

theorem mulVec_cancel (B : Matrix (Fin k) (Fin k) Qq) (hB : IsUnit B.det) {u v : Fin k → Qq}
    (h : B.mulVec u = B.mulVec v) : u = v := by
  have h2 := congrArg (fun w => B⁻¹.mulVec w) h
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB] using h2

theorem dD_det (p r : ℕ) (hp : (p : Qq) ≠ 0) : IsUnit (dD Qq p r k).det := by
  unfold dD
  rw [Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro c _
  split_ifs <;> simp [hp]

private theorem sum_smul_col_lemma (G : Matrix (Fin k) (Fin k) Qq) (y : Fin k → W) :
    ∑ c, y c • (fun i => G i c) = G.mulVec (fun c => algebraMap W Qq (y c)) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]

private theorem mem_src_iff_lemma_2 [IsDomain W] [IsFractionRing W Qq] (p r : ℕ) (hp0 : (p : W) ≠ 0)
    (B : Matrix (Fin k) (Fin k) Qq) (hB : IsUnit B.det) (y : Fin k → W) :
    (B * dD Qq p r k).mulVec (fun c => algebraMap W Qq (y c)) ∈ colSpan W B ↔
      ∀ c : Fin k, c.val < r → y c ∈ Ideal.span {(p : W)} := by
  have hinj : Function.Injective (algebraMap W Qq) := IsFractionRing.injective W Qq
  have hpQ : (p : Qq) ≠ 0 := by
    rw [← map_natCast (algebraMap W Qq)]
    exact fun h => hp0 (hinj (by rw [h, map_zero]))
  rw [mem_colSpan, ← Matrix.mulVec_mulVec]
  constructor
  · rintro ⟨z, hz⟩ c hc
    have h1 := congrFun (mulVec_cancel B hB hz) c
    unfold dD at h1
    simp only [Matrix.mulVec_diagonal, if_pos hc] at h1
    rw [Ideal.mem_span_singleton]
    refine ⟨z c, hinj ?_⟩
    rw [map_mul, map_natCast, ← h1, ← mul_assoc, mul_inv_cancel₀ hpQ, one_mul]
  · intro h
    have hex : ∀ c : Fin k, ∃ w : W,
        (if c.val < r then ((p : Qq))⁻¹ else 1) * algebraMap W Qq (y c) = algebraMap W Qq w := by
      intro c
      by_cases hc : c.val < r
      · obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp (h c hc)
        refine ⟨w, ?_⟩
        rw [if_pos hc, hw, map_mul, map_natCast, ← mul_assoc, inv_mul_cancel₀ hpQ, one_mul]
      · exact ⟨y c, by rw [if_neg hc, one_mul]⟩
    choose z hz using hex
    refine ⟨z, ?_⟩
    congr 1
    funext c
    unfold dD
    rw [Matrix.mulVec_diagonal]
    exact hz c

theorem isEdge_of_basis [IsDomain W] [IsFractionRing W Qq] (p n' r : ℕ) (hp0 : (p : W) ≠ 0)
    (hcard : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') (hr : r ≤ k) (e : Edge W Qq k)
    (B : Matrix (Fin k) (Fin k) Qq) (hB : IsEdgeBasis p r e B) : IsEdge p n' r e := by
  obtain ⟨hBu, hs, ht⟩ := hB
  have hinj : Function.Injective (algebraMap W Qq) := IsFractionRing.injective W Qq
  have hpQ : (p : Qq) ≠ 0 := by
    rw [← map_natCast (algebraMap W Qq)]
    exact fun h => hp0 (hinj (by rw [h, map_zero]))
  have ht' : e.tgt = colSpan W (B * dD Qq p r k) := ht
  obtain ⟨src, tgt⟩ := e
  dsimp only at hs ht'
  subst hs
  subst ht'
  have hMu : IsUnit (B * dD Qq p r k).det := by
    rw [Matrix.det_mul]
    exact hBu.mul (dD_det p r hpQ)
  unfold IsEdge IsLattice
  refine ⟨⟨B, hBu, rfl⟩, ⟨B * dD Qq p r k, hMu, rfl⟩, src_le_tgt p r hpQ B,
    fun x hx => prime_smul_target_mem_source p r hpQ B x hx, ?_⟩
  show Nat.card (↥(colSpan W (B * dD Qq p r k)) ⧸
    Submodule.comap (colSpan W (B * dD Qq p r k)).subtype (colSpan W B)) = p ^ (n' * r)
  have hli : LinearIndependent W (fun c : Fin k => fun i => (B * dD Qq p r k) i c) := by
    rw [Fintype.linearIndependent_iff]
    intro y hy
    rw [sum_smul_col_lemma] at hy
    have h0 : (B * dD Qq p r k).mulVec (fun c => algebraMap W Qq (y c)) =
        (B * dD Qq p r k).mulVec 0 := by
      rw [hy, Matrix.mulVec_zero]
    have h2 := mulVec_cancel _ hMu h0
    intro c
    exact hinj (by simpa using congrFun h2 c)
  let b : Module.Basis (Fin k) W ↥(colSpan W (B * dD Qq p r k)) := Module.Basis.span hli
  have hcoe : ∀ y : Fin k → W, ((b.equivFun.symm y : ↥(colSpan W (B * dD Qq p r k))) : Fin k → Qq) =
      (B * dD Qq p r k).mulVec (fun c => algebraMap W Qq (y c)) := by
    intro y
    rw [Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
    simp only [Submodule.coe_smul, b]
    rw [← sum_smul_col_lemma (B * dD Qq p r k) y]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    congr 1
    exact congrArg Subtype.val (Module.Basis.span_apply hli c)
  have hP : (Submodule.comap (colSpan W (B * dD Qq p r k)).subtype (colSpan W B)).map
      (b.equivFun : ↥(colSpan W (B * dD Qq p r k)) →ₗ[W] (Fin k → W)) =
      Submodule.pi Set.univ (fun c : Fin k =>
        (if c.val < r then Ideal.span {(p : W)} else ⊤ : Submodule W W)) := by
    ext y
    simp only [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.coe_subtype, LinearEquiv.coe_coe, hcoe, mem_src_iff_lemma_2 p r hp0 B hBu,
      Submodule.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h c
      by_cases hc : c.val < r
      · rw [if_pos hc]
        exact h c hc
      · rw [if_neg hc]
        exact Submodule.mem_top
    · intro h c hc
      have h' := h c
      rwa [if_pos hc] at h'
  have e1 := Submodule.Quotient.equiv _ _ b.equivFun hP
  rw [Nat.card_congr e1.toEquiv, Nat.card_congr (Submodule.quotientPi _).toEquiv, Nat.card_pi]
  have hfac : ∀ c : Fin k, Nat.card (W ⧸ (if c.val < r then Ideal.span {(p : W)} else ⊤ :
      Submodule W W)) = if c.val < r then p ^ n' else 1 := by
    intro c
    by_cases hc : c.val < r
    · simp only [hc, ↓reduceIte]
      exact hcard
    · simp only [hc, ↓reduceIte]
      exact Nat.card_unique
  rw [Finset.prod_congr rfl (fun c _ => hfac c)]
  have hcardF : (Finset.univ.filter fun c : Fin k => c.val < r).card = r := by
    have hF : (Finset.univ.filter fun c : Fin k => c.val < r) = Finset.univ.map (Fin.castLEEmb hr) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
      constructor
      · intro hc
        exact ⟨⟨c.val, hc⟩, Fin.ext rfl⟩
      · rintro ⟨a, rfl⟩
        exact a.isLt
    rw [hF, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, ← pow_mul, hcardF]

end Col

section Witt

variable {p n' : ℕ} [Fact p.Prime] {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ}

def Ng (φ : WF p n' ≃+* W) (g : Matrix (Fin k) (Fin k) (WF p n')) : Matrix (Fin k) (Fin k) W :=
  fun i c => φ (g⁻¹ c i)

theorem matQ_mul (φ : WF p n' ≃+* W) (g g' : Matrix (Fin k) (Fin k) (WF p n')) :
    matQ (Qq := Qq) φ (g * g') = matQ φ g * matQ φ g' := by
  ext a c
  simp [matQ, Matrix.mul_apply]

theorem matQ_one (φ : WF p n' ≃+* W) : matQ (Qq := Qq) φ (1 : Matrix (Fin k) (Fin k) (WF p n')) = 1 := by
  ext a b
  by_cases h : a = b <;> simp [matQ, Matrix.one_apply, h]

theorem matQ_inv (φ : WF p n' ≃+* W) (g : Matrix (Fin k) (Fin k) (WF p n')) (hg : IsGLW g) :
    ((matQ (Qq := Qq) φ g)⁻¹).transpose = (Ng φ g).map (algebraMap W Qq) := by
  have h1 : matQ (Qq := Qq) φ g * matQ φ g⁻¹ = 1 := by
    rw [← matQ_mul, Matrix.mul_nonsing_inv _ hg, matQ_one]
  rw [Matrix.inv_eq_right_inv h1]
  ext i c
  simp [matQ, Ng]

def Ngi (φ : WF p n' ≃+* W) (g : Matrix (Fin k) (Fin k) (WF p n')) : Matrix (Fin k) (Fin k) W :=
  fun i c => φ (g c i)

theorem Ng_unit (φ : WF p n' ≃+* W) (g : Matrix (Fin k) (Fin k) (WF p n')) (hg : IsGLW g) :
    Ng φ g * Ngi φ g = 1 := by
  have e1 : Ng φ g = (g⁻¹.map (φ : WF p n' →+* W)).transpose := by
    ext i c
    simp [Ng]
  have e2 : Ngi φ g = (g.map (φ : WF p n' →+* W)).transpose := by
    ext i c
    simp [Ngi]
  rw [e1, e2, ← Matrix.transpose_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hg]
  simp

theorem src_eq (φ : WF p n' ≃+* W) (g : Matrix (Fin k) (Fin k) (WF p n')) (hg : IsGLW g)
    (h : Matrix (Fin k) (Fin k) Qq) :
    colSpan W (h * ((matQ φ g)⁻¹).transpose) = colSpan W h := by
  rw [matQ_inv φ g hg]
  exact colSpan_mul_unit h (Ng φ g) (Ngi φ g) (Ng_unit φ g hg)

theorem mem_plane (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p n')) (x : Fin k → GaloisField p n') :
    x ∈ ratPlane p n' r g ↔ ∃ a : Fin k → GaloisField p n',
      x = ∑ i, a i • (if i.val < r then (fun c => WittVector.constantCoeff (g⁻¹ i c)) else 0) := by
  have hR : (Set.range fun i : Fin k =>
      if i.val < r then (fun c => WittVector.constantCoeff (g⁻¹ i c)) else 0) ⊆
      (ratPlane p n' r g : Set (Fin k → GaloisField p n')) := by
    rintro _ ⟨i, rfl⟩
    dsimp only
    by_cases hi : i.val < r
    · rw [if_pos hi]
      apply Submodule.subset_span
      exact ⟨i, hi, rfl⟩
    · rw [if_neg hi]
      exact Submodule.zero_mem _
  have hS : ratPlane p n' r g ≤ Submodule.span (GaloisField p n') (Set.range fun i : Fin k =>
      if i.val < r then (fun c => WittVector.constantCoeff (g⁻¹ i c)) else 0) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, hi, rfl⟩
    apply Submodule.subset_span
    exact ⟨i, if_pos hi⟩
  have hEq := le_antisymm hS (Submodule.span_le.mpr hR)
  rw [hEq, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩

theorem col_eq (h X : Matrix (Fin k) (Fin k) Qq) (c : Fin k) :
    (fun i => (h * X) i c) = h.mulVec (fun b => X b c) := by
  funext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem cc_p : WittVector.constantCoeff ((p : ℕ) : WF p n') = 0 := by
  rw [map_natCast]
  exact CharP.cast_eq_zero _ p

private theorem dvd_of_cc_lemma_4 (x : WF p n') (hx : WittVector.constantCoeff x = 0) :
    ∃ w : WF p n', x = (p : WF p n') * w := by
  by_cases h0 : x = 0
  · exact ⟨0, by rw [h0, mul_zero]⟩
  obtain ⟨m, b, hb, hxb⟩ := WittVector.exists_eq_pow_p_mul x h0
  cases m with
  | zero =>
    exfalso
    rw [pow_zero, one_mul] at hxb
    rw [hxb, WittVector.constantCoeff_apply] at hx
    exact hb hx
  | succ m =>
    exact ⟨(p : WF p n') ^ m * b, by rw [hxb, pow_succ', mul_assoc]⟩

private theorem cc_zero_lemma_3 (r : ℕ) (g g' : Matrix (Fin k) (Fin k) (WF p n')) (hg' : IsGLW g')
    (hpl : ratPlane p n' r g ≤ ratPlane p n' r g') (c i : Fin k) (hc : c.val < r) (hi : ¬ i.val < r) :
    WittVector.constantCoeff ((g⁻¹ * g') c i) = 0 := by
  have hmem : (fun j => WittVector.constantCoeff (g⁻¹ c j)) ∈ ratPlane p n' r g' := by
    apply hpl
    apply Submodule.subset_span
    exact ⟨c, hc, rfl⟩
  obtain ⟨a, ha⟩ := (mem_plane r g' _).mp hmem
  have hrow : ∀ j, WittVector.constantCoeff (g⁻¹ c j) =
      ∑ l, a l * (if l.val < r then WittVector.constantCoeff (g'⁻¹ l j) else 0) := by
    intro j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ite_apply, Pi.zero_apply] using
      congrFun ha j
  have hone : ∀ l : Fin k, l.val < r →
      ∑ j, WittVector.constantCoeff (g'⁻¹ l j) * WittVector.constantCoeff (g' j i) = 0 := by
    intro l hl
    have h1 : (g'⁻¹ * g') l i = 0 := by
      rw [Matrix.nonsing_inv_mul _ hg', Matrix.one_apply_ne]
      intro hli
      exact hi (hli ▸ hl)
    have h2 := congrArg WittVector.constantCoeff h1
    rw [Matrix.mul_apply, map_sum] at h2
    simpa [map_mul] using h2
  rw [Matrix.mul_apply, map_sum]
  simp only [map_mul, hrow, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun l _ => ?_)
  by_cases hl : l.val < r
  · simp only [hl, if_true, mul_assoc, ← Finset.mul_sum, hone l hl, mul_zero]
  · simp [hl]

theorem tgt_le_of_plane (φ : WF p n' ≃+* W) (r : ℕ) (hpQ : (p : Qq) ≠ 0)
    (g g' : Matrix (Fin k) (Fin k) (WF p n')) (hg : IsGLW g) (hg' : IsGLW g')
    (h : Matrix (Fin k) (Fin k) Qq) (hpl : ratPlane p n' r g ≤ ratPlane p n' r g') :
    colSpan W (h * (Ng φ g).map (algebraMap W Qq) * dD Qq p r k) ≤
      colSpan W (h * (Ng φ g').map (algebraMap W Qq) * dD Qq p r k) := by
  have hZ : ∀ i c : Fin k, ¬ i.val < r → c.val < r →
      ∃ w : W, (Ngi φ g' * Ng φ g) i c = (p : W) * w := by
    intro i c hi hc
    obtain ⟨w, hw⟩ := dvd_of_cc_lemma_4 _ (cc_zero_lemma_3 r g g' hg' hpl c i hc hi)
    refine ⟨φ w, ?_⟩
    have hZe : (Ngi φ g' * Ng φ g) i c = φ ((g⁻¹ * g') c i) := by
      simp only [Matrix.mul_apply, Ngi, Ng, map_sum, map_mul]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    rw [hZe, hw, map_mul, map_natCast]
  have hd : ∀ i c : Fin k, ∃ y : W, algebraMap W Qq ((Ngi φ g' * Ng φ g) i c) *
      (if c.val < r then ((p : Qq))⁻¹ else 1) =
        (if i.val < r then ((p : Qq))⁻¹ else 1) * algebraMap W Qq y := by
    intro i c
    by_cases hi : i.val < r
    · by_cases hc : c.val < r
      · exact ⟨(Ngi φ g' * Ng φ g) i c, by rw [if_pos hi, if_pos hc, mul_comm]⟩
      · refine ⟨(p : W) * (Ngi φ g' * Ng φ g) i c, ?_⟩
        rw [if_pos hi, if_neg hc, mul_one, map_mul, map_natCast, ← mul_assoc,
          inv_mul_cancel₀ hpQ, one_mul]
    · by_cases hc : c.val < r
      · obtain ⟨w, hw⟩ := hZ i c hi hc
        refine ⟨w, ?_⟩
        rw [if_neg hi, if_pos hc, one_mul, hw, map_mul, map_natCast, mul_comm, ← mul_assoc,
          inv_mul_cancel₀ hpQ, one_mul]
      · exact ⟨(Ngi φ g' * Ng φ g) i c, by rw [if_neg hi, if_neg hc, mul_one, one_mul]⟩
  choose Y hY using hd
  have hE : (Ngi φ g' * Ng φ g).map (algebraMap W Qq) * dD Qq p r k =
      dD Qq p r k * Matrix.map Y (algebraMap W Qq) := by
    ext i c
    unfold dD
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
    exact hY i c
  have hinv : (Ng φ g').map (algebraMap W Qq) * (Ngi φ g').map (algebraMap W Qq) = 1 := by
    rw [← Matrix.map_mul, Ng_unit φ g' hg']
    simp
  have hM : h * (Ng φ g).map (algebraMap W Qq) * dD Qq p r k =
      h * (Ng φ g').map (algebraMap W Qq) * dD Qq p r k * Matrix.map Y (algebraMap W Qq) := by
    rw [Matrix.mul_assoc (h * (Ng φ g').map (algebraMap W Qq)) (dD Qq p r k), ← hE, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((Ng φ g').map (algebraMap W Qq)), hinv, Matrix.one_mul]
  rw [hM]
  exact colSpan_mul_le _ Y

theorem plane_le_of_tgt [IsDomain W] [IsFractionRing W Qq] (φ : WF p n' ≃+* W) (r : ℕ) (hpQ : (p : Qq) ≠ 0)
    (g g' : Matrix (Fin k) (Fin k) (WF p n'))
    (h : Matrix (Fin k) (Fin k) Qq) (hh : IsUnit h.det)
    (hle : colSpan W (h * (Ng φ g).map (algebraMap W Qq) * dD Qq p r k) ≤
      colSpan W (h * (Ng φ g').map (algebraMap W Qq) * dD Qq p r k)) :
    ratPlane p n' r g ≤ ratPlane p n' r g' := by
  have hinj : Function.Injective (algebraMap W Qq) := IsFractionRing.injective W Qq
  have hcol : ∀ c : Fin k, ∃ y : Fin k → W,
      (fun i => (h * (Ng φ g).map (algebraMap W Qq) * dD Qq p r k) i c) =
        (h * (Ng φ g').map (algebraMap W Qq) * dD Qq p r k).mulVec (fun b => algebraMap W Qq (y b)) := by
    intro c
    have hc : (fun i => (h * (Ng φ g).map (algebraMap W Qq) * dD Qq p r k) i c) ∈
        colSpan W (h * (Ng φ g).map (algebraMap W Qq) * dD Qq p r k) := by
      unfold colSpan
      exact Submodule.subset_span ⟨c, rfl⟩
    exact (mem_colSpan _ _).mp (hle hc)
  choose Y hY using hcol
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨c, hc, rfl⟩
  rw [SetLike.mem_coe, mem_plane]
  refine ⟨fun i => WittVector.constantCoeff (φ.symm (Y c i)), ?_⟩
  have h1 := hY c
  rw [Matrix.mul_assoc h, Matrix.mul_assoc h, col_eq, ← Matrix.mulVec_mulVec] at h1
  have h2 := mulVec_cancel h hh h1
  funext j
  have h3 := congrFun h2 j
  simp only [dD, Matrix.mul_diagonal, Matrix.map_apply, Ng, Matrix.mulVec, dotProduct, if_pos hc] at h3
  have h5 : algebraMap W Qq (φ (g⁻¹ c j)) = (∑ i, algebraMap W Qq (φ (g'⁻¹ i j)) *
      (if i.val < r then ((p : Qq))⁻¹ else 1) * algebraMap W Qq (Y c i)) * (p : Qq) := by
    rw [← h3, mul_assoc, inv_mul_cancel₀ hpQ, mul_one]
  have h4 : algebraMap W Qq (φ (g⁻¹ c j)) = algebraMap W Qq
      (∑ i, φ (g'⁻¹ i j) * (if i.val < r then 1 else (p : W)) * Y c i) := by
    rw [h5, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : i.val < r
    · simp only [hi, if_true, map_mul, map_one, mul_one]
      rw [mul_assoc, mul_assoc, mul_left_comm ((p : Qq))⁻¹, inv_mul_cancel₀ hpQ, mul_one]
    · simp only [hi, if_false, map_mul, map_natCast, mul_one]
      ring
  have h6 := hinj h4
  have h7 : g⁻¹ c j = ∑ i, g'⁻¹ i j * (if i.val < r then 1 else (p : WF p n')) * φ.symm (Y c i) := by
    rw [← φ.symm_apply_apply (g⁻¹ c j), h6, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : i.val < r <;> simp [hi]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ite_apply, Pi.zero_apply]
  rw [h7, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : i.val < r
  · rw [if_pos hi, if_pos hi, mul_one, map_mul, mul_comm]
  · rw [if_neg hi, if_neg hi, mul_zero, map_mul, map_mul, cc_p, mul_zero, zero_mul]

end Witt

theorem edgePlane : EdgePlane := by
  intro p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS φ _ m r h hh
  have := hS.frac_alt
  have hp0 : (p : W) ≠ 0 := hS.p_unif.ne_zero
  have hpQ : (p : Qq) ≠ 0 := by
    rw [← map_natCast (algebraMap W Qq)]
    exact fun h => hp0 ((IsFractionRing.injective W Qq) (by rw [h, map_zero]))
  refine ⟨?_, ?_, ?_⟩
  · intro e he hsrc
    obtain ⟨ge, hge⟩ := LatticeSystems.lc_main p n' r (m + 1) hS.p_unif hS.res_card (by have := hS.five_le; omega)
      (by have := hS.two_le; omega) e he
    obtain ⟨hdet, hs, ht⟩ := hge
    obtain ⟨U, hU⟩ := LatticeSystems.la_factor (O := W) h ge (by rw [← hs, hsrc])
    obtain ⟨U', hU'⟩ := LatticeSystems.la_factor (O := W) ge h (by rw [← hs, hsrc])
    have hUU : U * U' = 1 := by
      have h1 : h * (U * U').map (algebraMap W Qq) = h * 1 := by
        rw [Matrix.map_mul, ← Matrix.mul_assoc, ← hU, ← hU', Matrix.mul_one]
      have h2 : (U * U').map (algebraMap W Qq) = 1 := by
        have h3 := congrArg (fun X => h⁻¹ * X) h1
        simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul h hh, Matrix.one_mul] using h3
      ext a b
      apply IsFractionRing.injective W Qq
      have h4 := congrFun (congrFun h2 a) b
      rw [Matrix.map_apply] at h4
      rw [h4, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    obtain ⟨g, hg⟩ : ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), g = fun a b => φ.symm (U' b a) := ⟨_, rfl⟩
    obtain ⟨gi, hgi⟩ : ∃ gi : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), gi = fun a b => φ.symm (U b a) :=
      ⟨_, rfl⟩
    have hggi : g * gi = 1 := by
      refine Matrix.ext fun a b => ?_
      apply φ.injective
      rw [Matrix.mul_apply, map_sum, hg, hgi]
      simp only [map_mul, RingEquiv.apply_symm_apply]
      have h1 := congrFun (congrFun hUU b) a
      rw [Matrix.mul_apply] at h1
      calc ∑ x, U' x a * U b x = ∑ x, U b x * U' x a := Finset.sum_congr rfl fun x _ => mul_comm _ _
        _ = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) W) b a := h1
        _ = φ ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) a b) := by
            rw [Matrix.one_apply, Matrix.one_apply]
            by_cases hab : a = b
            · rw [if_pos hab, if_pos hab.symm, map_one]
            · rw [if_neg hab, if_neg (Ne.symm hab), map_zero]
    have hgl : IsGLW g := by
      unfold IsGLW
      have h1 : g.det * gi.det = 1 := by rw [← Matrix.det_mul, hggi, Matrix.det_one]
      exact IsUnit.of_mul_eq_one _ h1
    have hinv : g⁻¹ = gi := Matrix.inv_eq_right_inv hggi
    have hN : (Ng φ g).map (algebraMap W Qq) = U.map (algebraMap W Qq) := by
      ext a b
      simp only [Matrix.map_apply, Ng, hinv, hgi, RingEquiv.apply_symm_apply]
    refine ⟨g, hgl, ?_⟩
    rw [matQ_inv φ g hgl, hN, ← hU]
    exact ⟨hdet, hs, ht⟩
  · intro g e hg hr he
    refine ⟨isEdge_of_basis p n' r hp0 hS.res_card hr e _ he, ?_⟩
    rw [he.2.1]
    exact src_eq φ g hg h
  · intro g g' e e' hg hg' he he'
    obtain ⟨-, hs, ht⟩ := he
    obtain ⟨-, hs', ht'⟩ := he'
    rw [src_eq φ g hg h] at hs
    rw [src_eq φ g' hg' h] at hs'
    rw [matQ_inv φ g hg] at ht
    rw [matQ_inv φ g' hg'] at ht'
    change e.tgt = colSpan W (h * (Ng φ g).map (algebraMap W Qq) * dD Qq p r (m + 1)) at ht
    change e'.tgt = colSpan W (h * (Ng φ g').map (algebraMap W Qq) * dD Qq p r (m + 1)) at ht'
    constructor
    · intro hee
      subst hee
      apply le_antisymm
      · exact plane_le_of_tgt φ r hpQ g g' h hh (by rw [← ht, ← ht'])
      · exact plane_le_of_tgt φ r hpQ g' g h hh (by rw [← ht, ← ht'])
    · intro hpl
      obtain ⟨s, t⟩ := e
      obtain ⟨s', t'⟩ := e'
      simp only at hs hs' ht ht'
      rw [Edge.mk.injEq]
      refine ⟨by rw [hs, hs'], ?_⟩
      rw [ht, ht']
      apply le_antisymm
      · exact tgt_le_of_plane φ r hpQ g g' hg hg' h hpl.le
      · exact tgt_le_of_plane φ r hpQ g' g hg' hg h hpl.ge

end Formalism.MainNotions.Pf14
