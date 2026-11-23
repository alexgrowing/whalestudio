import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QcEvGLDetUZpow

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma qc_genMat_det_ne (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) : (genMat R n).det ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero (Fin n) R

lemma qc_isDomain (R : Type) [CommRing R] [IsDomain R] (n : ℕ) : IsDomain (GLCoord R n) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (R := MvPolynomial (Fin n × Fin n) R) (S := GLCoord R n)
    (M := Submonoid.powers (genMat R n).det)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (qc_genMat_det_ne R n))

def qc_genPt (F : Type) [CommRing F] (n : ℕ) : GL (Fin n) (GLCoord F n) :=
  Matrix.nonsingInvUnit ((algebraMap _ (GLCoord F n)).mapMatrix (genMat F n))
    (by rw [← RingHom.map_det]; exact IsLocalization.Away.algebraMap_isUnit _)

lemma qc_genPt_val (F : Type) [CommRing F] (n : ℕ) (a b : Fin n) :
    (qc_genPt F n).val a b = algebraMap (MvPolynomial (Fin n × Fin n) F) (GLCoord F n) (X (a, b)) := rfl

lemma qc_mapCoord_alg {n : ℕ} (F : Type) [CommRing F] (P : MvPolynomial (Fin n × Fin n) ℤ) :
    mapCoord (n := n) F (algebraMap _ (GLCoord ℤ n) P) =
      algebraMap _ (GLCoord F n) (MvPolynomial.map (Int.castRingHom F) P) :=
  IsLocalization.Away.lift_eq _ _ _

lemma qc_hom_ext {n : ℕ} {R : Type} [CommRing R] (f g : GLCoord ℤ n →+* R)
    (h : ∀ a b, f (algebraMap (MvPolynomial (Fin n × Fin n) ℤ) _ (X (a, b))) =
      g (algebraMap (MvPolynomial (Fin n × Fin n) ℤ) _ (X (a, b)))) : f = g := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (genMat ℤ n).det) ?_
  apply MvPolynomial.ringHom_ext
  · intro r; simp
  · rintro ⟨a, b⟩; exact h a b

lemma qc_evGL_genPt (F : Type) [CommRing F] (n : ℕ) : evGL (qc_genPt F n) = mapCoord F := by
  apply qc_hom_ext
  intro a b
  rw [qc_evGL_alg, qc_mapCoord_alg]
  simp [qc_genPt_val]

lemma qc_evGL_genPt_int (n : ℕ) : evGL (qc_genPt ℤ n) = RingHom.id _ := by
  apply qc_hom_ext
  intro a b
  rw [qc_evGL_alg]
  simp [qc_genPt_val]

lemma qc_evGL_map {n : ℕ} {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (g : GL (Fin n) R) :
    evGL (Matrix.GeneralLinearGroup.map φ g) = φ.comp (evGL g) := by
  apply qc_hom_ext
  intro a b
  rw [RingHom.comp_apply, qc_evGL_alg, qc_evGL_alg]
  simp only [coe_eval₂Hom, eval₂_X]
  rfl

lemma qc_map_span_mem {A B F : Type} [CommRing A] [CommRing B] [Field F] [Module F B] (φ : A →+* B) (S : Set A)
    (y : A) (hy : y ∈ Submodule.span ℤ S) : φ y ∈ Submodule.span F (φ '' S) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul m x _ hx => rw [map_zsmul]; exact zsmul_mem hx m

lemma qc_span_eq {A B F : Type} [CommRing A] [CommRing B] [Field F] [Module F B] (φ : A →+* B) (S T : Set A)
    (h : Submodule.span ℤ S = Submodule.span ℤ T) : Submodule.span F (φ '' S) = Submodule.span F (φ '' T) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact qc_map_span_mem φ T x (h ▸ Submodule.subset_span hx)
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact qc_map_span_mem φ S x (h.symm ▸ Submodule.subset_span hx)

section SMu

variable {n : ℕ} [NeZero n] {M : GLMod n} {mu : Fin n → ℤ} {β : M.ι → GLCoord ℤ n}

lemma qc_card_eq (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β) : Fintype.card M.ι = dMu mu := by
  classical
  have : Fintype {I : TIdx mu // StdT I} := Fintype.ofFinite _
  have h1 := finrank_span_eq_card hβ.1
  have h2 := finrank_span_eq_card (hS n mu hmu).1
  rw [hβ.2.1] at h1
  rw [(hS n mu hmu).2] at h2
  rw [dMu, Nat.card_eq_fintype_card, ← h1, ← h2]

lemma qc_li_field (hA : LemmaA) (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β) (F : Type) [Field F] :
    LinearIndependent F (fun i => mapCoord (n := n) F (β i)) := by
  classical
  have : Fintype {I : TIdx mu // StdT I} := Fintype.ofFinite _
  rw [linearIndependent_iff_card_eq_finrank_span]
  have h1 := linearIndependent_iff_card_eq_finrank_span.1 (hA n mu hmu F)
  have h2 : Set.range (fun i => mapCoord (n := n) F (β i)) = mapCoord (n := n) F '' Set.range β := by
    rw [← Set.range_comp]; rfl
  have h3 : Set.range (fun I : {I : TIdx mu // StdT I} => mapCoord (n := n) F (brk mu I.1)) =
      mapCoord (n := n) F '' Set.range (fun I : {I : TIdx mu // StdT I} => brk mu I.1) := by
    rw [← Set.range_comp]; rfl
  have h4 := qc_span_eq (F := F) (mapCoord (n := n) F) _ _ (hβ.2.1.trans (hS n mu hmu).2.symm)
  rw [Set.finrank, h2, h4, ← h3, ← Set.finrank, ← h1, qc_card_eq hS hmu hβ, dMu, Nat.card_eq_fintype_card]

lemma qc_two (hβ : IsSMu M mu β) (ph : Matrix M.ι (TIdx mu) ℤ) (hph : ∀ I, ∑ i, ph i I • β i = brk mu I)
    {R : Type} [CommRing R] (x g : GL (Fin n) R) (I : TIdx mu) :
    ∑ j, evGL g ((M.A * ph.map (Int.castRingHom (GLCoord ℤ n)) : Matrix _ _ _) j I) * evGL x (β j) =
      ∑ j, evGL g ((ph.map (Int.castRingHom (GLCoord ℤ n)) * TMat mu : Matrix _ _ _) j I) * evGL x (β j) := by
  have e1 : evGL (x * g) (brk mu I) = ∑ j, evGL g ((M.A * ph.map (Int.castRingHom (GLCoord ℤ n)) : Matrix _ _ _) j I) * evGL x (β j) := by
    rw [← hph I]
    simp only [map_sum, map_zsmul, hβ.2.2, Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul, map_mul, eq_intCast,
      map_intCast, zsmul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have e2 : evGL (x * g) (brk mu I) = ∑ j, evGL g ((ph.map (Int.castRingHom (GLCoord ℤ n)) * TMat mu : Matrix _ _ _) j I) * evGL x (β j) := by
    rw [brk, qc_TMat_mul]
    have : ∀ K, evGL x (TMat mu (canT mu) K) = ∑ j, (ph j K : R) * evGL x (β j) := by
      intro K
      show evGL x (brk mu K) = _
      rw [← hph K]
      simp only [map_sum, zsmul_eq_mul, map_mul, map_intCast]
    simp only [this, map_sum, Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul, map_mul, eq_intCast,
      map_intCast]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [← e1, e2]

theorem qc_equiv (hA : LemmaA) (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β)
    (ph : Matrix M.ι (TIdx mu) ℤ) (hph : ∀ I, ∑ i, ph i I • β i = brk mu I) :
    M.A * ph.map (Int.castRingHom _) = ph.map (Int.castRingHom _) * TMat mu := by
  have := qc_isDomain ℤ n
  let F := FractionRing (GLCoord ℤ n)
  let ψ : GLCoord ℤ n →+* GLCoord F n := (algebraMap F (GLCoord F n)).comp (algebraMap (GLCoord ℤ n) F)
  have hli := qc_li_field hA hS hmu hβ F
  ext i I
  have h := qc_two hβ ph hph (qc_genPt F n) (Matrix.GeneralLinearGroup.map ψ (qc_genPt ℤ n)) I
  rw [qc_evGL_genPt, qc_evGL_map, qc_evGL_genPt_int, RingHom.comp_id] at h
  have h' : ∑ j, (algebraMap (GLCoord ℤ n) F ((M.A * ph.map (Int.castRingHom (GLCoord ℤ n)) : Matrix _ _ _) j I) -
      algebraMap (GLCoord ℤ n) F ((ph.map (Int.castRingHom (GLCoord ℤ n)) * TMat mu : Matrix _ _ _) j I)) • mapCoord (n := n) F (β j) = 0 := by
    simp only [Algebra.smul_def, map_sub, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact h
  have h'' := Fintype.linearIndependent_iff.1 hli _ h' i
  exact IsFractionRing.injective (GLCoord ℤ n) F (sub_eq_zero.1 h'')

end SMu

end Formalism.InvariantFactorPaths.ColumnFamilies
