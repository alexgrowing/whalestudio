import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StatementA
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StatementC

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma qc_det_mul_fun {R : Type} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det := by
  have h : (A * B) = fun a => ∑ k, A a k • B k := by
    funext a b
    simp [Matrix.mul_apply, Finset.sum_apply]
  have h2 : (A * B).det = Matrix.detRowAlternating (fun a => ∑ k, A a k • B k) := by
    rw [← h]; rfl
  rw [h2]
  have h3 := (Matrix.detRowAlternating (R := R) (n := Fin i)).toMultilinearMap.map_sum
    (fun a k => A a k • B k)
  erw [h3]
  apply Finset.sum_congr rfl
  intro f _
  have h4 := (Matrix.detRowAlternating (R := R) (n := Fin i)).toMultilinearMap.map_smul_univ
    (fun a => A a (f a)) (fun a => B (f a))
  erw [h4]
  rfl

def qc_par {i N : ℕ} (p : (Σ _ : {S : Finset (Fin N) // S.card = i}, Equiv.Perm (Fin i))) :
    Fin i ↪ Fin N :=
  p.2.toEmbedding.trans (p.1.1.orderEmbOfFin p.1.2).toEmbedding

lemma qc_par_bij {i N : ℕ} : Function.Bijective (qc_par (i := i) (N := N)) := by
  constructor
  · rintro ⟨⟨S, hS⟩, σ⟩ ⟨⟨T, hT⟩, τ⟩ h
    have hST : S = T := by
      have h1 : ∀ (S : Finset (Fin N)) (hS : S.card = i) (σ : Equiv.Perm (Fin i)),
          univ.map (qc_par ⟨⟨S, hS⟩, σ⟩) = S := by
        intro S hS σ
        ext x
        simp only [qc_par, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.trans_apply,
          Equiv.coe_toEmbedding, RelEmbedding.coe_toEmbedding]
        constructor
        · rintro ⟨a, rfl⟩
          exact Finset.orderEmbOfFin_mem S hS _
        · intro hx
          have : x ∈ Set.range (S.orderEmbOfFin hS) := by
            rw [Finset.range_orderEmbOfFin]; exact hx
          obtain ⟨b, rfl⟩ := this
          exact ⟨σ.symm b, by simp⟩
      rw [← h1 S hS σ, ← h1 T hT τ, h]
    subst hST
    have : σ = τ := by
      ext a
      have h2 := DFunLike.congr_fun h a
      simp only [qc_par, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
        RelEmbedding.coe_toEmbedding] at h2
      exact congrArg Fin.val ((S.orderEmbOfFin hS).injective h2)
    subst this
    rfl
  · intro f
    have hS : (univ.map f).card = i := by simp
    have hmem : ∀ a, f a ∈ Set.range ((univ.map f).orderEmbOfFin hS) := by
      intro a
      rw [Finset.range_orderEmbOfFin]; simp
    choose τ hτ using hmem
    have hinj : Function.Injective τ := by
      intro a b hab
      apply f.injective
      rw [← hτ a, ← hτ b, hab]
    refine ⟨⟨⟨univ.map f, hS⟩, Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hinj)⟩, ?_⟩
    ext a
    simp [qc_par, hτ]

lemma qc_cb {R : Type} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ S : {S : Finset (Fin N) // S.card = i},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  classical
  rw [qc_det_mul_fun]
  set F : (Fin i → Fin N) → R := fun f => (∏ a, A a (f a)) * (B.submatrix f id).det with hF
  have h1 : ∑ f : Fin i → Fin N, F f = ∑ f : Fin i ↪ Fin N, F f := by
    have h0 : ∀ f : Fin i → Fin N, ¬ Function.Injective f → F f = 0 := by
      intro f hf
      simp only [Function.Injective, not_forall] at hf
      obtain ⟨a, b, hab, hne⟩ := hf
      have : (B.submatrix f id).det = 0 :=
        Matrix.det_zero_of_row_eq hne (by funext c; simp [Matrix.submatrix_apply, hab])
      simp [hF, this]
    rw [← Finset.sum_filter_of_ne (p := Function.Injective) (s := univ) (f := F)
      (fun f _ hne => by by_contra hc; exact hne (h0 f hc))]
    symm
    apply Finset.sum_bij (fun (f : Fin i ↪ Fin N) _ => (f : Fin i → Fin N))
    · intro f _; simp [f.injective]
    · intro f _ g _ h; exact DFunLike.coe_injective h
    · intro f hf
      exact ⟨⟨f, (Finset.mem_filter.mp hf).2⟩, Finset.mem_univ _, rfl⟩
    · intro f _; rfl
  rw [h1, ← Function.Bijective.sum_comp qc_par_bij (fun f => F f), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  rintro ⟨S, hS⟩ _
  set e := S.orderEmbOfFin hS with he
  have h2 : ∀ σ : Equiv.Perm (Fin i), F (qc_par ⟨⟨S, hS⟩, σ⟩) =
      (Equiv.Perm.sign σ : R) * (∏ a, A a (e (σ a))) * (B.submatrix e id).det := by
    intro σ
    have h3 : (B.submatrix (fun a => e (σ a)) id).det = (Equiv.Perm.sign σ : R) * (B.submatrix e id).det := by
      have := Matrix.det_permute σ (B.submatrix e id)
      rw [← this]; rfl
    show (∏ a, A a (e (σ a))) * (B.submatrix (fun a => e (σ a)) id).det = _
    rw [h3]; ring
  simp_rw [h2]
  rw [← Finset.sum_mul]
  congr 1
  rw [Matrix.det_apply', ← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin i)))]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv, Matrix.submatrix_apply, id]
  congr 1
  rw [← Equiv.prod_comp σ]
  simp

lemma qc_cb_minor {R : Type} [CommRing R] {n h : ℕ} (x g : Matrix (Fin n) (Fin n) R) (r c : Fin h → Fin n) :
    ((x * g).submatrix r c).det = ∑ S : {S : Finset (Fin n) // S.card = h},
      (x.submatrix r (S.1.orderEmbOfFin S.2)).det * (g.submatrix (S.1.orderEmbOfFin S.2) c).det := by
  have h1 : (x * g).submatrix r c = x.submatrix r id * g.submatrix id c := by
    ext a b; simp [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [h1, qc_cb]
  rfl

lemma qc_evGL_alg {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) (P : MvPolynomial (Fin n × Fin n) ℤ) :
    evGL g (algebraMap _ (GLCoord ℤ n) P) =
      MvPolynomial.eval₂Hom (Int.castRingHom R) (fun ab : Fin n × Fin n => g.val ab.1 ab.2) P :=
  IsLocalization.Away.lift_eq _ _ _

lemma qc_evGL_minorC {n h : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) (J I : Finset (Fin n))
    (hJ : J.card = h) (hI : I.card = h) :
    evGL g (minorC J I hJ hI) = (g.val.submatrix (J.orderEmbOfFin hJ) (I.orderEmbOfFin hI)).det := by
  rw [minorC, qc_evGL_alg, RingHom.map_det]
  congr 1
  ext a b
  simp [genMat]

lemma qc_detU_coe (n : ℕ) : ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = algebraMap _ _ (genMat ℤ n).det := rfl

lemma qc_evGL_detU {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) :
    evGL g ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = g.val.det := by
  rw [qc_detU_coe, qc_evGL_alg, RingHom.map_det, genMat_map_eval]

def qc_dU {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : Rˣ := Units.map (evGL g).toMonoidHom (detU n)

lemma qc_dU_coe {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : ((qc_dU g : Rˣ) : R) = g.val.det :=
  qc_evGL_detU g

lemma qc_dU_mul {n : ℕ} {R : Type} [CommRing R] (x g : GL (Fin n) R) : qc_dU (x * g) = qc_dU x * qc_dU g := by
  apply Units.ext
  rw [Units.val_mul, qc_dU_coe, qc_dU_coe, qc_dU_coe, Units.val_mul, Matrix.det_mul]

lemma qc_evGL_detU_zpow {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) (m : ℤ) :
    evGL g ((detU n ^ m : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = ((qc_dU g ^ m : Rˣ) : R) := by
  rw [qc_dU, ← map_zpow]
  rfl

theorem qc_TMat_mul {n : ℕ} [NeZero n] (mu : Fin n → ℤ) {R : Type} [CommRing R] (x g : GL (Fin n) R)
    (J I : TIdx mu) :
    evGL (x * g) (TMat mu J I) = ∑ K : TIdx mu, evGL x (TMat mu J K) * evGL g (TMat mu K I) := by
  simp only [TMat, map_mul, map_prod, qc_evGL_detU_zpow, qc_evGL_minorC, qc_dU_mul, mul_zpow, Units.val_mul]
  simp only [qc_cb_minor]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K _
  rw [Finset.prod_mul_distrib]
  ring

end Formalism.InvariantFactorPaths.ColumnFamilies
