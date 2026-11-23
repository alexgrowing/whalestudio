import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQHW
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowAct
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CBinet

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylReproducingSym

open Formalism.GradedWeylDivisibility GlobalTheory.WeylMinorDual

def oeEquivCard (h n : ℕ) : {S : Finset (Fin n) // S.card = h} ≃ (Fin h ↪o Fin n) where
  toFun S := S.1.orderEmbOfFin S.2
  invFun I := ⟨Finset.univ.map I.toEmbedding, by simp⟩
  left_inv S := by
    apply Subtype.ext
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact Finset.orderEmbOfFin_mem _ _ i
    · intro hx
      have : x ∈ Set.range (S.1.orderEmbOfFin S.2) := by rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨i, hi⟩ := this
      exact ⟨i, hi⟩
  right_inv I := by
    apply OrderEmbedding.range_inj.mp
    rw [Finset.range_orderEmbOfFin]
    ext x
    simp

private theorem det_mul_eq_sum_det_submatrix_mul_prod {R : Type} [CommRing R] {h n : ℕ}
    (A : Matrix (Fin h) (Fin n) R) (B : Matrix (Fin n) (Fin h) R) :
    (A * B).det = ∑ p : Fin h → Fin n, (A.submatrix id p).det * ∏ i, B (p i) i := by
  simp_rw [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.submatrix_apply, id, Finset.prod_mul_distrib]
  ring

private theorem sum_perm_det_submatrix_mul_prod_eq_det_mul_det {R : Type} [CommRing R] {h n : ℕ}
    (A : Matrix (Fin h) (Fin n) R) (B : Matrix (Fin n) (Fin h) R) (e : Fin h ↪o Fin n) :
    ∑ τ : Equiv.Perm (Fin h), (A.submatrix id (⇑e ∘ ⇑τ)).det * ∏ i, B (e (τ i)) i =
      (A.submatrix id e).det * (B.submatrix e id).det := by
  have hA : ∀ τ : Equiv.Perm (Fin h), (A.submatrix id (⇑e ∘ ⇑τ)).det =
      Equiv.Perm.sign τ * (A.submatrix id e).det := fun τ => by
    rw [← Matrix.det_permute' τ (A.submatrix id e), Matrix.submatrix_submatrix]
    rfl
  simp_rw [hA, Matrix.det_apply' (B.submatrix e id), Finset.mul_sum, Matrix.submatrix_apply, id]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring

theorem cauchyBinet_oe {R : Type} [CommRing R] {h n : ℕ}
    (A : Matrix (Fin h) (Fin n) R) (B : Matrix (Fin n) (Fin h) R) :
    (A * B).det = ∑ I : Fin h ↪o Fin n, (A.submatrix id I).det * (B.submatrix I id).det := by
  rw [det_mul_eq_sum_det_submatrix_mul_prod]
  simp_rw [← sum_perm_det_submatrix_mul_prod_eq_det_mul_det A B]
  rw [← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => ⇑x.1 ∘ ⇑x.2) (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · rintro ⟨e, τ⟩ _ _ ⟨e', τ'⟩ _ _ hx
    have hr : Set.range ⇑e = Set.range ⇑e' := by
      have h1 : Set.range (⇑e ∘ ⇑τ) = Set.range (⇑e' ∘ ⇑τ') := congrArg Set.range hx
      rwa [τ.surjective.range_comp, τ'.surjective.range_comp] at h1
    obtain rfl : e = e' := OrderEmbedding.range_inj.mp hr
    obtain rfl : τ = τ' := Equiv.ext fun i => e.injective (congrFun hx i)
    rfl
  · intro p _ hp
    have hinj : Function.Injective p := by
      intro i j hij
      by_contra hne
      apply hp
      rw [Matrix.det_zero_of_column_eq hne (fun k => by simp only [Matrix.submatrix_apply, id, hij]),
        zero_mul]
    have hc : (Finset.univ.image p).card = h := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have hmem : ∀ i, ∃ j, (Finset.univ.image p).orderEmbOfFin hc j = p i := by
      intro i
      have : p i ∈ Set.range ((Finset.univ.image p).orderEmbOfFin hc) := by
        rw [Finset.range_orderEmbOfFin]
        simp
      exact this
    choose t ht using hmem
    have tinj : Function.Injective t := by
      intro i j hij
      apply hinj
      rw [← ht i, ← ht j, hij]
    have tbij : Function.Bijective t := Finite.injective_iff_bijective.mp tinj
    have hp' : ⇑((Finset.univ.image p).orderEmbOfFin hc) ∘ ⇑(Equiv.ofBijective t tbij) = p :=
      funext ht
    refine ⟨((Finset.univ.image p).orderEmbOfFin hc, Equiv.ofBijective t tbij), Finset.mem_univ _, ?_, hp'⟩
    show (A.submatrix id (⇑((Finset.univ.image p).orderEmbOfFin hc) ∘ ⇑(Equiv.ofBijective t tbij))).det *
      ∏ i, B ((⇑((Finset.univ.image p).orderEmbOfFin hc) ∘ ⇑(Equiv.ofBijective t tbij)) i) i ≠ 0
    rw [hp']
    exact hp
  · intro x _ _
    rfl

theorem rowAct_leadMinor (N h : ℕ) (hh : h ≤ N) (x : Fin N × Fin N → ℚ) :
    rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose (initMinor ℚ (r := N) (n := N) (Fin.castLE hh) hh) =
      ∑ K : Fin h ↪o Fin N, C (eval x (initMinor ℚ (r := N) (n := N) (⇑K) hh)) *
        initMinor ℚ (r := N) (n := N) (⇑K) hh := by
  have h1 : rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose
      (initMinor ℚ (r := N) (n := N) (Fin.castLE hh) hh) =
      ((Matrix.of fun (p : Fin h) (b : Fin N) => (C (x (b, Fin.castLE hh p)) : MvPolynomial (Fin N × Fin N) ℚ)) *
        Matrix.of fun (b : Fin N) (q : Fin h) => (X (b, Fin.castLE hh q) : MvPolynomial (Fin N × Fin N) ℚ)).det := by
    rw [initMinor, AlgHom.map_det]
    congr 1
    ext p q
    simp [rowAct, Matrix.mul_apply, aeval_X]
  rw [h1, cauchyBinet_oe]
  refine Finset.sum_congr rfl fun K _ => ?_
  congr 1
  rw [initMinor, RingHom.map_det, RingHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext p q
  simp

theorem rowAct_hw_expand (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (x : Fin N × Fin N → ℚ) :
    rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose (hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) =
      ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        C (eval x (colProd ℚ N Y hY J)) * colProd ℚ N Y hY J := by
  have hb := bidet_lead ℚ N (fun c : Fin (Y.rowLen 0) => Y.colLen c) (colLen_le hY)
    (fun c => Fin.castLE (colLen_le hY c)) (fun _ _ => rfl)
  rw [shapeDeg_colLen] at hb
  rw [← hb, bideterminant, map_prod]
  simp only [rowAct_leadMinor]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  simp only [colProd, bideterminant, map_prod, Finset.prod_mul_distrib]

theorem reproducing_left : ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (f : MvPolynomial (Fin N × Fin N) ℚ),
    f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r) →
    ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f := by
  intro N Y hY f hf
  have hsum : ∀ {ι : Type} (s : Finset ι) (F : ι → MvPolynomial (Fin N × Fin N) ℚ)
      (g : MvPolynomial (Fin N × Fin N) ℚ), fockQ (∑ i ∈ s, F i) g = ∑ i ∈ s, fockQ (F i) g :=
    fun s F g => map_sum (AddMonoidHom.mk' (fun p => fockQ p g)
      (fun a b => (Formalism.GradedWeylDivisibility.fockQBilin _ a b g 0).1)) F s
  have hsmul : ∀ (c : ℚ) (p g : MvPolynomial (Fin N × Fin N) ℚ), fockQ (c • p) g = c * fockQ p g :=
    fun c p g => (Formalism.GradedWeylDivisibility.fockQBilin _ p p g c).2
  have hanti : Antitone (fun r : Fin N => Y.rowLen r) := fun a b hab => Y.rowLen_anti _ _ hab
  apply MvPolynomial.funext
  intro x
  have hev : eval (idFrame ℚ N N) (rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)) f) = eval x f := by
    have hcomp : (aeval (idFrame ℚ N N)).comp (rowAct ℚ (n := N) (Matrix.of fun a s : Fin N => x (a, s))) =
        aeval x := by
      apply MvPolynomial.algHom_ext
      intro v
      simp [rowAct, idFrame, aeval_X, Fin.val_inj]
    have h3 := congrArg (fun φ => φ f) hcomp
    simpa [MvPolynomial.coe_aeval_eq_eval] using h3
  have hmem := Formalism.GradedWeylDivisibility.dualWeylRowStable ℚ N N _ (Matrix.of fun a s : Fin N => x (a, s)) f hf
  have h1 := Formalism.GradedWeylDivisibility.fock_space_highest_weight N N le_rfl (fun r : Fin N => Y.rowLen r) hanti _ hmem
  have h2 := Formalism.GradedWeylDivisibility.fock_space_row_action N N (Matrix.of fun a s : Fin N => x (a, s)).transpose
    (hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) f
  rw [Matrix.transpose_transpose, h1, hev, rowAct_hw_expand N Y hY x, hsum] at h2
  simp only [MvPolynomial.C_mul', hsmul] at h2
  simp only [map_sum, MvPolynomial.smul_eval]
  rw [mul_comm (fockQ _ _) (eval x f), ← h2]
  exact Finset.sum_congr rfl fun J _ => mul_comm _ _

end GlobalTheory.WeylReproducingSym
