import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NfAllBrTenLe
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Matrix
open scoped ComplexOrder

section Fock

variable {σ : Type}

theorem tf_eq_sum (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ)) (hS : f.support ⊆ S) :
    Formalism.REAL.fockF f g = ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [notMem_support_iff.mp hm]
  simp

theorem tf_add_left (f f' g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (f + f') g = Formalism.REAL.fockF f g + Formalism.REAL.fockF f' g := by
  classical
  rw [tf_eq_sum (f + f') g (f.support ∪ f'.support) support_add,
    tf_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
    tf_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_add]
  ring

theorem tf_smul_left (c : ℂ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (c • f) g = c * Formalism.REAL.fockF f g := by
  rw [tf_eq_sum (c • f) g f.support support_smul, tf_eq_sum f g f.support le_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring

theorem tf_add_right (f g g' : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f (g + g') = Formalism.REAL.fockF f g + Formalism.REAL.fockF f g' := by
  unfold Formalism.REAL.fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_add, star_add]
  ring

theorem tf_smul_right (c : ℂ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f (c • g) = star c * Formalism.REAL.fockF f g := by
  unfold Formalism.REAL.fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul, star_mul']
  ring

def tfB : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) Formalism.REAL.fockF tf_add_left tf_smul_left tf_add_right tf_smul_right

theorem tfB_apply (f g : MvPolynomial σ ℂ) : tfB f g = Formalism.REAL.fockF f g := rfl

theorem tf_eq_fockS (f g : MvPolynomial σ ℂ) : Formalism.REAL.fockF f g = Formalism.L2.DIV.fockS g f := by
  classical
  rw [tf_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold Formalism.L2.DIV.mfact
  ring

theorem tf_star (f g : MvPolynomial σ ℂ) : star (Formalism.REAL.fockF f g) = Formalism.REAL.fockF g f := by
  rw [tf_eq_fockS g f]
  unfold Formalism.REAL.fockF Formalism.L2.DIV.fockS
  rw [star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold Formalism.L2.DIV.mfact
  simp only [star_mul', star_star, star_natCast]

theorem tf_quad {k : ℕ} (w : Fin k → MvPolynomial σ ℂ) (x : Fin k → ℂ) :
    star x ⬝ᵥ (Matrix.of fun i j => Formalism.REAL.fockF (w j) (w i)) *ᵥ x =
      Formalism.REAL.fockF (∑ j, x j • w j) (∑ i, x i • w i) := by
  rw [← tfB_apply]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ, tfB_apply, smul_eq_mul,
    dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [starRingEnd_apply]
  ring

theorem tf_herm {σ' : Type} {k : ℕ} (w : Fin k → MvPolynomial σ ℂ) (v : Fin k → MvPolynomial σ' ℂ) (r : ℝ) :
    (((r : ℂ) • Matrix.of fun i j => Formalism.REAL.fockF (w j) (w i)) - Matrix.of fun i j => Formalism.REAL.fockF (v j) (v i)).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, star_sub, star_mul',
    tf_star]
  rw [Complex.star_def, Complex.conj_ofReal]

theorem tf_gram_psd {k : ℕ} (w : Fin k → MvPolynomial σ ℂ) :
    (Matrix.of fun i j => Formalism.REAL.fockF (w j) (w i)).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j; simp only [conjTranspose_apply, Matrix.of_apply, tf_star]
  · rw [tf_quad, Formalism.L2.Ker.nm_fockF_self]
    exact Complex.zero_le_real.2 (Formalism.L2.Ker.nm_fockF_nonneg _)

end Fock

section Had

variable {ι : Type} [Fintype ι] {k : ℕ}

theorem tf_ones_psd : (Matrix.of fun (_ _ : Fin k) => (1 : ℂ)).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j; simp
  · have : star x ⬝ᵥ (Matrix.of fun (_ _ : Fin k) => (1 : ℂ)) *ᵥ x = star (∑ i, x i) * ∑ i, x i := by
      simp only [dotProduct, mulVec, Matrix.of_apply, one_mul, star_sum, Finset.sum_mul, Pi.star_apply]
    rw [this]
    exact star_mul_self_nonneg _

theorem tf_had_sub (A B : ι → Matrix (Fin k) (Fin k) ℂ) (hB : ∀ τ, (B τ).PosSemidef) (hAB : ∀ τ, (A τ - B τ).PosSemidef) :
    ((Matrix.of fun i j => ∏ τ, A τ i j) - Matrix.of fun i j => ∏ τ, B τ i j).PosSemidef := by
  classical
  have hA : ∀ τ, (A τ).PosSemidef := fun τ => by simpa using (hAB τ).add (hB τ)
  suffices h : ∀ s : Finset ι, ((Matrix.of fun i j => ∏ τ ∈ s, A τ i j) - Matrix.of fun i j => ∏ τ ∈ s, B τ i j).PosSemidef ∧
      (Matrix.of fun i j => ∏ τ ∈ s, A τ i j).PosSemidef from (h Finset.univ).1
  intro s
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, sub_self]
    exact ⟨PosSemidef.zero, tf_ones_psd⟩
  | insert t s ht ih =>
    have eA : (Matrix.of fun i j => ∏ τ ∈ insert t s, A τ i j) = A t ⊙ Matrix.of fun i j => ∏ τ ∈ s, A τ i j := by
      ext i j; simp [Finset.prod_insert ht, hadamard]
    have eB : (Matrix.of fun i j => ∏ τ ∈ insert t s, B τ i j) = B t ⊙ Matrix.of fun i j => ∏ τ ∈ s, B τ i j := by
      ext i j; simp [Finset.prod_insert ht, hadamard]
    have e : A t ⊙ (Matrix.of fun i j => ∏ τ ∈ s, A τ i j) - B t ⊙ (Matrix.of fun i j => ∏ τ ∈ s, B τ i j) =
        (A t - B t) ⊙ (Matrix.of fun i j => ∏ τ ∈ s, A τ i j) +
          B t ⊙ ((Matrix.of fun i j => ∏ τ ∈ s, A τ i j) - Matrix.of fun i j => ∏ τ ∈ s, B τ i j) := by
      ext i j; simp [hadamard]; ring
    refine ⟨?_, ?_⟩
    · rw [eA, eB, e]
      exact ((hAB t).hadamard ih.2).add ((hB t).hadamard ih.1)
    · rw [eA]; exact (hA t).hadamard ih.2

end Had

theorem tf_ten {ι : Type} [Fintype ι] {n : ℕ} (f g : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.REAL.fockF (Formalism.MainNotions.product_first_zeroth_parts.ten f) (Formalism.MainNotions.product_first_zeroth_parts.ten g) = ∏ τ, Formalism.REAL.fockF (f τ) (g τ) := by
  rw [tf_eq_fockS]
  have h := Formalism.L2.DIV.fockSymTensor_holds ℂ ι n g f
  refine (h.trans ?_)
  exact Finset.prod_congr rfl fun τ _ => (tf_eq_fockS _ _).symm

theorem blkFockLe : BlockFockBound := by
  intro ι _ n n' V F c hF P hP
  classical
  obtain ⟨k, a, p, hsum⟩ := Submodule.mem_span_set'.1 hP
  choose f hfV hfeq using fun i => (p i).2
  have hs : ∀ (r : ℂ) (M : Matrix (Fin k) (Fin k) ℂ) (v : Fin k → ℂ), (r • M) *ᵥ v = r • (M *ᵥ v) := by
    intro r M v; ext i
    simp only [mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hd : ∀ (r : ℂ) (v w : Fin k → ℂ), v ⬝ᵥ (r • w) = r * (v ⬝ᵥ w) := by
    intro r v w
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hP' : P = ∑ i, a i • Formalism.MainNotions.product_first_zeroth_parts.ten (f i) := by
    rw [← hsum]; exact Finset.sum_congr rfl fun i _ => by rw [hfeq i]
  have hblk : Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P = ∑ i, a i • Formalism.MainNotions.product_first_zeroth_parts.ten (fun τ => F τ (f i τ)) := by
    rw [hP', map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, Formalism.MainNotions.product_first_zeroth_parts.blk_ten]
  set G : ι → Matrix (Fin k) (Fin k) ℂ := fun τ => Matrix.of fun i j => Formalism.REAL.fockF (f j τ) (f i τ) with hG
  set H : ι → Matrix (Fin k) (Fin k) ℂ := fun τ => Matrix.of fun i j => Formalism.REAL.fockF (F τ (f j τ)) (F τ (f i τ)) with hH
  have qP : Formalism.REAL.fockF P P = star a ⬝ᵥ (Matrix.of fun i j => ∏ τ, G τ i j) *ᵥ a := by
    have := tf_quad (fun i => Formalism.MainNotions.product_first_zeroth_parts.ten (f i)) a
    simp only [tf_ten] at this
    rw [hP', ← this]
    rfl
  have qB : Formalism.REAL.fockF (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P) (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P) =
      star a ⬝ᵥ (Matrix.of fun i j => ∏ τ, H τ i j) *ᵥ a := by
    have := tf_quad (fun i => Formalism.MainNotions.product_first_zeroth_parts.ten (fun τ => F τ (f i τ))) a
    simp only [tf_ten] at this
    rw [hblk, ← this]
    rfl
  have hBpsd : ∀ τ, (H τ).PosSemidef := fun τ => tf_gram_psd (fun i => F τ (f i τ))
  have hABpsd : ∀ τ, ((((c τ ^ 2 : ℝ) : ℂ) • G τ) - H τ).PosSemidef := by
    intro τ
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨tf_herm (fun i => f i τ) (fun i => F τ (f i τ)) (c τ ^ 2), fun x => ?_⟩
    rw [sub_mulVec, dotProduct_sub, hs, hd, tf_quad, tf_quad]
    have hlin : ∑ i, x i • F τ (f i τ) = F τ (∑ i, x i • f i τ) := by rw [map_sum]; simp [map_smul]
    have hmem : ∑ i, x i • f i τ ∈ V τ := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hfV i τ)
    rw [hlin, Formalism.L2.Ker.nm_fockF_self (∑ i, x i • f i τ), Formalism.L2.Ker.nm_fockF_self (F τ (∑ i, x i • f i τ)),
      ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    exact Complex.zero_le_real.2 (sub_nonneg.2 (hF τ _ hmem))
  have key := (tf_had_sub (fun τ => ((c τ ^ 2 : ℝ) : ℂ) • G τ) H hBpsd hABpsd).dotProduct_mulVec_nonneg a
  have eA : (Matrix.of fun i j => ∏ τ, (((c τ ^ 2 : ℝ) : ℂ) • G τ) i j) =
      (((∏ τ, c τ ^ 2 : ℝ) : ℂ)) • Matrix.of fun i j => ∏ τ, G τ i j := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Complex.ofReal_prod]
  rw [eA, sub_mulVec, dotProduct_sub, hs, hd, ← qP, ← qB,
    Formalism.L2.Ker.nm_fockF_self P, Formalism.L2.Ker.nm_fockF_self (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P), ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, Complex.zero_le_real] at key
  exact sub_nonneg.1 key

theorem nfAll_brTen_le' {D : Formalism.BasicNotions.D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (Tf : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) (hB : Formalism.L2.Ker.BeOnTie D u)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) (hP : P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m)) :
    (Formalism.L2.Forms.nfAll (D.fm u).sg (Formalism.L2.Ker.brTen D u P) (Formalism.L2.Ker.brTen D u P)).re ≤
      (∏ τ, (D.fm u).beOn τ ^ 2) * (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) P P).re :=
  nfAll_brTen_le blkFockLe Tf hB P hP

end Formalism.L2.GlobalTheoryTheory.Br
