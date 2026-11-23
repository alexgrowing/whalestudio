import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ArchFinSplit

section Idem
variable {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {ι : Type} [Fintype ι] [DecidableEq ι]

def pr (e : A) (M : Matrix ι ι R) : Matrix ι ι R := e • M + (1 - e) • (1 : Matrix ι ι R)

theorem pr_mul {e : A} (he : IsIdempotentElem e) (M N : Matrix ι ι R) : pr e M * pr e N = pr e (M * N) := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := he.one_sub.eq
  simp only [pr, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, Matrix.mul_one,
    Matrix.one_mul, he.eq, h1, h2, h3, zero_smul, add_zero, zero_add]

theorem pr_one (e : A) : pr e (1 : Matrix ι ι R) = 1 := by
  simp [pr, sub_smul]

theorem pr_sub_one (e : A) (M : Matrix ι ι R) : pr e M - 1 = e • (M - 1) := by
  simp only [pr, sub_smul, one_smul, smul_sub]; abel

theorem pr_mul_pr_compl {e : A} (he : IsIdempotentElem e) (M : Matrix ι ι R) : pr e M * pr (1 - e) M = M := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := he.one_sub.eq
  simp only [pr, sub_sub_cancel, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add,
    Matrix.mul_one, Matrix.one_mul, he.eq, h1, h2, h3, zero_smul, add_zero, zero_add]
  rw [← add_smul, sub_add_cancel, one_smul]

def prU {e : A} (he : IsIdempotentElem e) (g : GL ι R) : GL ι R where
  val := pr e (g : Matrix ι ι R)
  inv := pr e ((g⁻¹ : GL ι R) : Matrix ι ι R)
  val_inv := by rw [pr_mul he, Units.mul_inv, pr_one]
  inv_val := by rw [pr_mul he, Units.inv_mul, pr_one]

theorem prU_mem {e : A} (he : IsIdempotentElem e) (c : R →ₐ[A] R) (J : Matrix ι ι R) (g : GL ι R)
    (hg : g ∈ UG c J) : prU he g ∈ UG c J := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := he.one_sub.eq
  have hg' : (g : Matrix ι ι R)ᵀ * J * (g : Matrix ι ι R).map c = J := hg
  show (pr e (g : Matrix ι ι R))ᵀ * J * (pr e (g : Matrix ι ι R)).map c = J
  have hm : (pr e (g : Matrix ι ι R)).map c = pr e ((g : Matrix ι ι R).map c) := by
    ext i j; simp [pr, Matrix.one_apply, map_add, map_smul]; split_ifs <;> simp
  rw [hm]
  simp only [pr, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, Matrix.mul_one, Matrix.one_mul, he.eq, h1, h2, h3, zero_smul,
    add_zero, zero_add, hg']
  rw [← add_smul, add_sub_cancel, one_smul]

end Idem
end GlobalTheory.ArchFinSplit

open GlobalTheory.ArchFinSplit in

theorem GlobalTheory.ArchFinSplit.split_arch_fin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (W : Spc F E n) (g : UA σ W.J), ∃ gi ∈ UAt σ W (evI F), ∃ gf ∈ UAt σ W (fun u : AF F => u.2), g = gi * gf := by
  intro F E _ _ _ _ _ σ n W g
  let a : AF F := ((1 : Ainf F), (0 : Af F))
  have ha : IsIdempotentElem a := by
    refine Prod.ext ?_ ?_
    · change (1 : Ainf F) * 1 = 1; rw [mul_one]
    · change (0 : Af F) * 0 = 0; rw [mul_zero]
  let gi : UA σ W.J := ⟨prU ha g.1, prU_mem ha _ _ g.1 g.2⟩
  let gf : UA σ W.J := ⟨prU ha.one_sub g.1, prU_mem ha.one_sub _ _ g.1 g.2⟩
  refine ⟨gi, ?_, gf, ?_, ?_⟩
  · intro u hu
    have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
    show u • (pr a (g.1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0
    rw [pr_sub_one, smul_smul]
    have : u * a = 0 := by
      refine Prod.ext ?_ ?_
      · change u.1 * 1 = 0; rw [hu1, zero_mul]
      · change u.2 * 0 = 0; rw [mul_zero]
    rw [this, zero_smul]
  · intro u hu
    show u • (pr (1 - a) (g.1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0
    rw [pr_sub_one, smul_smul]
    have : u * (1 - a) = 0 := by
      refine Prod.ext ?_ ?_
      · change u.1 * (1 - 1) = 0; rw [sub_self, mul_zero]
      · have hu2 : u.2 = 0 := hu
        change u.2 * (1 - 0) = 0; rw [hu2, zero_mul]
    rw [this, zero_smul]
  · apply Subtype.ext; apply Units.ext
    show (g.1 : Matrix (Fin n) (Fin n) (AE F E)) = pr a (g.1 : Matrix _ _ _) * pr (1 - a) (g.1 : Matrix _ _ _)
    rw [pr_mul_pr_compl ha]
