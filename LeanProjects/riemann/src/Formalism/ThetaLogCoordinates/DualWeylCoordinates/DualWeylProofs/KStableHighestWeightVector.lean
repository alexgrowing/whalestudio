import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.HighestWeightIntegral

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma qr_det_full {m : ℕ} {R : Type} [CommRing R] (A : Matrix (Fin m) (Fin m) R) {k : ℕ} (hk : k = m)
    (S : Finset (Fin m)) (hS : S.card = k) :
    (A.submatrix (S.orderEmbOfFin hS) (S.orderEmbOfFin hS)).det = A.det := by
  subst hk
  exact Matrix.det_submatrix_equiv_self
    (Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (S.orderEmbOfFin hS).injective)) A

lemma qr_det_empty {m : ℕ} {R : Type} [CommRing R] (A : Matrix (Fin m) (Fin m) R) {k : ℕ} (hk : k = 0)
    (r c : Fin k → Fin m) : (A.submatrix r c).det = 1 := by
  subst hk
  exact Matrix.det_fin_zero

section TM

variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ} {R : Type} [CommRing R]
  {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ}

lemma qr_dU_block (hb : IsBlock h g1 t) : qc_dU h = t * qc_dU g1 := by
  apply Units.ext
  rw [Units.val_mul, qc_dU_coe, qc_dU_coe, qr_det_block hb]

lemma qr_TMat_zero (hb : IsBlock h g1 t) (hn : Dominant nu) (hi : Interl lam nu) (K : TIdx lam) (I' : TIdx nu)
    (hK : ∀ K', qr_j hi K' ≠ K) : evGL h (TMat lam K (qr_j hi I')) = 0 := by
  have h1 : ∃ c : ↥(TCols lam), ¬ (Fin.last m ∈ (K c).1 ↔ colH lam c = colH nu c + 1) := by
    by_contra hcon
    obtain ⟨K', hK'⟩ := qr_j_surj hn hi K (fun c => by
      by_contra h2; exact hcon ⟨c, h2⟩)
    exact hK K' hK'
  obtain ⟨c, hc⟩ := h1
  simp only [TMat, map_mul, map_prod, qc_evGL_minorC]
  rw [Finset.prod_eq_zero (Finset.mem_univ c), mul_zero]
  exact qr_minor_zero hb _ _ _ _ _ hc

def qr_mn (g1 : GL (Fin m) R) {k : ℕ} (x y : {S : Finset (Fin m) // S.card = k}) : R :=
  (g1.val.submatrix (x.1.orderEmbOfFin x.2) (y.1.orderEmbOfFin y.2)).det

def qr_G (g1 : GL (Fin m) R) (K' I' : TIdx nu) (c : ℤ) : R := qr_mn g1 (qr_base K' c) (qr_base I' c)

lemma qr_G_low (hn : Dominant nu) (K' I' : TIdx nu) {c : ℤ} (hc : c ≤ nu (lastIdx m)) :
    qr_G g1 K' I' c = g1.val.det := by
  have h1 : c ∉ TCols nu := by
    simp only [TCols, Finset.mem_Ioc, not_and_or, not_lt]; exact Or.inl hc
  have := qr_subsing hn h1
  rw [qr_G, Subsingleton.elim (qr_base K' c) (qr_base I' c)]
  exact qr_det_full _ (qr_colH_low hn hc) _ _

lemma qr_G_high (hn : Dominant nu) (K' I' : TIdx nu) {c : ℤ} (hc : nu 0 < c) :
    qr_G g1 K' I' c = 1 :=
  qr_det_empty _ (qr_colH_high hn hc) _ _

lemma qr_prod_G (hn : Dominant nu) (hi : Interl lam nu) (K' I' : TIdx nu) :
    ∏ c ∈ TCols lam, qr_G g1 K' I' c =
      g1.val.det ^ (nu (lastIdx m) - lam (Fin.last m)).toNat *
        ∏ c : ↥(TCols nu), (g1.val.submatrix ((K' c).1.orderEmbOfFin (K' c).2)
          ((I' c).1.orderEmbOfFin (I' c).2)).det := by
  have h1 := qr_lam_last_le hi
  have h2 : nu (lastIdx m) ≤ nu 0 := qr_le_last hn 0
  have h3 := qr_nu_zero_le hi
  rw [TCols, qr_lastIdx, ← Finset.Ioc_union_Ioc_eq_Ioc h1 (h2.trans h3),
    Finset.prod_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl), ← Finset.Ioc_union_Ioc_eq_Ioc h2 h3,
    Finset.prod_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
  rw [Finset.prod_congr rfl (fun c hc => qr_G_low hn K' I' (Finset.mem_Ioc.1 hc).2), Finset.prod_const,
    Int.card_Ioc,
    Finset.prod_congr (s₁ := Finset.Ioc (nu 0) (lam 0)) rfl (fun c hc => qr_G_high hn K' I' (Finset.mem_Ioc.1 hc).1),
    Finset.prod_const_one, mul_one]
  congr 1
  rw [← Finset.prod_coe_sort]
  refine Finset.prod_congr rfl fun c _ => ?_
  have e1 := qr_base_mem K' c
  have e2 := qr_base_mem I' c
  rw [qr_G, e1, e2]
  rfl

lemma qr_card_C (hl : Dominant lam) (hn : Dominant nu) (hi : Interl lam nu) :
    (((TCols lam).filter fun c => colH lam c = colH nu c + 1).card : ℤ) =
      ∑ a, lam a - ∑ a, nu a - lam (Fin.last m) := by
  have h1 : ∀ c, ((if colH lam c = colH nu c + 1 then 1 else 0 : ℕ) : ℤ) = (colH lam c : ℤ) - colH nu c := by
    intro c
    have := qr_colH_eq hi c
    omega
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, h1]
  rw [Finset.sum_sub_distrib, TCols, qr_lastIdx,
    qr_sum_colH lam _ _ (fun a => ⟨hl (Fin.le_last a), qr_le_zero hl a⟩),
    qr_sum_colH nu _ _ (fun a => ⟨(qr_lam_last_le hi).trans (qr_le_last hn a),
      (qr_le_zero hn a).trans (qr_nu_zero_le hi)⟩)]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem qr_TMat_j (hb : IsBlock h g1 t) (hl : Dominant lam) (hn : Dominant nu) (hi : Interl lam nu)
    (K' I' : TIdx nu) :
    evGL h (TMat lam (qr_j hi K') (qr_j hi I')) =
      ((t ^ (∑ a, lam a - ∑ a, nu a) : Rˣ) : R) * evGL g1 (TMat nu K' I') := by
  simp only [TMat, map_mul, map_prod, qc_evGL_detU_zpow, qc_evGL_minorC]
  have h1 : ∀ c : ↥(TCols lam),
      (h.val.submatrix ((qr_j hi K' c).1.orderEmbOfFin (qr_j hi K' c).2)
        ((qr_j hi I' c).1.orderEmbOfFin (qr_j hi I' c).2)).det =
      (if colH lam c = colH nu c + 1 then (t : R) else 1) * qr_G g1 K' I' c := fun c =>
    qr_minor_ext hb _ _ _ (qr_base K' c).2 (qr_base I' c).2 _ _
  rw [Finset.prod_congr rfl (fun c _ => h1 c), Finset.prod_mul_distrib,
    Finset.prod_coe_sort (TCols lam) (fun c => if colH lam c = colH nu c + 1 then (t : R) else 1),
    Finset.prod_coe_sort (TCols lam) (fun c => qr_G g1 K' I' c), qr_prod_G hn hi, Finset.prod_ite,
    Finset.prod_const, Finset.prod_const_one, mul_one, qr_dU_block hb, qr_lastIdx]
  have hC := qr_card_C hl hn hi
  set N := ((TCols lam).filter fun c => colH lam c = colH nu c + 1).card
  set P := (nu (lastIdx m) - lam (Fin.last m)).toNat with hP
  have hP' : (P : ℤ) = nu (lastIdx m) - lam (Fin.last m) :=
    Int.toNat_of_nonneg (sub_nonneg.2 (qr_lam_last_le hi))
  have e1 : t ^ (∑ a, lam a - ∑ a, nu a) = t ^ lam (Fin.last m) * t ^ N := by
    rw [← zpow_natCast, ← zpow_add, hC]; congr 1; ring
  have e2 : qc_dU g1 ^ nu (lastIdx m) = qc_dU g1 ^ lam (Fin.last m) * qc_dU g1 ^ P := by
    rw [← zpow_natCast, ← zpow_add, hP']; congr 1; ring
  rw [e1, e2, mul_zpow]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, qc_dU_coe]
  ring

end TM

end Formalism.InvariantFactorPaths.ColumnFamilies
