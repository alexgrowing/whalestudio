import ReciprocityTheory.DualLattices.DiscriminantColengthStatement

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {v : Valuation C NNReal}

def sumLat {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) : Lat v (Fin n × Fin s) :=
  ⟨Matrix.reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
      (Matrix.blockDiagonal fun τ => (Mτ τ).B), by
    rw [Matrix.det_reindex_self, Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => (Mτ τ).det_ne⟩

lemma sumLat_apply {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) (x y : Fin n × Fin s) :
    (sumLat Mτ).B x y = if x.1 = y.1 then (Mτ x.1).B x.2 y.2 else 0 := by
  simp only [sumLat, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, Matrix.blockDiagonal_apply]

lemma sumLat_det {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) :
    (sumLat Mτ).B.det = ∏ τ, (Mτ τ).B.det := by
  show (Matrix.reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
      (Matrix.blockDiagonal fun τ => (Mτ τ).B)).det = _
  rw [Matrix.det_reindex_self, Matrix.det_blockDiagonal]

lemma sumLat_mulVec {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) (c : Fin n × Fin s → C) (τ : Fin n)
    (i : Fin s) : ((sumLat Mτ).B *ᵥ c) (τ, i) = ((Mτ τ).B *ᵥ fun j => c (τ, j)) i := by
  simp only [Matrix.mulVec, dotProduct, sumLat_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_eq_single τ]
  · simp
  · intro b _ hb
    exact Finset.sum_eq_zero fun j _ => if_neg (Ne.symm hb)
  · intro h; exact absurd (Finset.mem_univ τ) h

lemma sumLat_pts {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) : (sumLat Mτ).pts = sumPts Mτ := by
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩ τ
    refine ⟨fun j => c (τ, j), fun j => hc (τ, j), ?_⟩
    funext i
    exact sumLat_mulVec Mτ c τ i
  · intro hw
    choose c hc hwc using hw
    refine ⟨fun y => c y.1 y.2, fun y => hc y.1 y.2, ?_⟩
    funext ⟨τ, i⟩
    rw [sumLat_mulVec]
    exact congrFun (hwc τ) i

lemma freeMat_eq {n : ℕ} (a : Fin n → C) (s : ℕ) :
    freeMat a s = Matrix.blockDiagonal fun _ : Fin s => Matrix.vandermonde a := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [freeMat, Matrix.of_apply, Matrix.blockDiagonal_apply, Matrix.vandermonde_apply]

lemma det_freeMat {n : ℕ} (a : Fin n → C) (s : ℕ) :
    (freeMat a s).det = (Matrix.vandermonde a).det ^ s := by
  rw [freeMat_eq, Matrix.det_blockDiagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma v_det_vandermonde_sq {n : ℕ} (a : Fin n → C) :
    v (Matrix.vandermonde a).det ^ 2 = v (discr a) := by
  have hsplit : ∀ τ : Fin n, Finset.univ.erase τ = Finset.Ioi τ ∪ Finset.Iio τ := by
    intro τ
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Ioi,
      Finset.mem_Iio]
    constructor
    · intro h
      rcases lt_or_gt_of_ne h with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h | h)
      · exact h.ne'
      · exact h.ne
  have hdisj : ∀ τ : Fin n, Disjoint (Finset.Ioi τ) (Finset.Iio τ) := by
    intro τ
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact lt_asymm (Finset.mem_Ioi.1 h1) (Finset.mem_Iio.1 h2)
  rw [Matrix.det_vandermonde, discr]
  simp only [map_prod]
  have h1 : ∏ τ : Fin n, ∏ τ' ∈ Finset.univ.erase τ, v (a τ - a τ') =
      (∏ τ : Fin n, ∏ τ' ∈ Finset.Ioi τ, v (a τ - a τ')) *
        ∏ τ : Fin n, ∏ τ' ∈ Finset.Iio τ, v (a τ - a τ') := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => by rw [hsplit τ, Finset.prod_union (hdisj τ)]
  have h2 : ∏ τ : Fin n, ∏ τ' ∈ Finset.Iio τ, v (a τ - a τ') =
      ∏ τ' : Fin n, ∏ τ ∈ Finset.Ioi τ', v (a τ - a τ') :=
    Finset.prod_comm' (by intro x y; simp [Finset.mem_Iio, Finset.mem_Ioi])
  have h3 : ∏ τ : Fin n, ∏ τ' ∈ Finset.Ioi τ, v (a τ - a τ') =
      ∏ τ : Fin n, ∏ τ' ∈ Finset.Ioi τ, v (a τ' - a τ) :=
    Finset.prod_congr rfl fun _ _ => Finset.prod_congr rfl fun _ _ => Valuation.map_sub_swap v _ _
  rw [h1, h2, h3, sq]

lemma v_det_freeMat_sq {n : ℕ} (a : Fin n → C) (s : ℕ) :
    v (freeMat a s).det ^ 2 = v (discr a) ^ s := by
  rw [det_freeMat, map_pow, pow_right_comm, v_det_vandermonde_sq]

theorem colength_sq_blockVandermonde {n : ℕ} (a : Fin n → C) (s : ℕ) (F S : Lat v (Fin n × Fin s))
    (hF : F.B = freeMat a s) (hS : S.pts = sumPts (fun _ => Lat.std v (Fin s))) :
    colen F S ^ 2 = v (discr a) ^ s := by
  rw [colen_congr (L₂' := F) (L₂ := sumLat fun _ => Lat.std v (Fin s)) rfl
    (hS.trans (sumLat_pts _).symm)]
  rw [colen, sumLat_det]
  simp only [Lat.std, Matrix.det_one, map_one, Finset.prod_const_one, div_one, hF]
  exact v_det_freeMat_sq a s

end ReciprocityTheory.PGsh.Up
