import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsRationalDblCoord
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer

noncomputable section

namespace GlobalTheory.SWAniso

section Transp

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β]

theorem symp_transpose (c : A →ₐ[R] A) (ξ : A) (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    symp c ξ JB JA xᵀ yᵀ = symp c ξ JA JB x y := by
  unfold symp hTens
  congr 2
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

def darbouxTransp {c : A →ₐ[R] A} {ξ : A} {JA : Matrix α α A} {JB : Matrix β β A}
    (d : Darboux (symp c ξ JA JB) (α × β)) : Darboux (symp c ξ JB JA) (β × α) where
  e := (Matrix.transposeLinearEquiv β α R A).trans
    (d.e.trans ((LinearEquiv.funCongrLeft R R (Equiv.prodComm β α)).prodCongr
      (LinearEquiv.funCongrLeft R R (Equiv.prodComm β α))))
  form x y := by
    have h := symp_transpose c ξ JA JB xᵀ yᵀ
    rw [Matrix.transpose_transpose, Matrix.transpose_transpose] at h
    rw [h, d.form]
    simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, Matrix.transposeLinearEquiv_apply,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
    simp only [dotProduct, Fintype.sum_prod_type, Function.comp_apply, Equiv.prodComm_apply, Prod.swap_prod_mk]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun a b => (d.e yᵀ).1 (a, b) * (d.e xᵀ).2 (a, b))]
    rfl

theorem darbouxTransp_e {c : A →ₐ[R] A} {ξ : A} {JA : Matrix α α A} {JB : Matrix β β A}
    (d : Darboux (symp c ξ JA JB) (α × β)) (x : Matrix β α A) :
    (darbouxTransp d).e x = (fun p => (d.e xᵀ).1 p.swap, fun p => (d.e xᵀ).2 p.swap) :=
  rfl

end Transp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

theorem darbouxTransp_rational {σ : E →ₐ[F] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {JA : Matrix α α E} {JB : Matrix β β E} (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) (α × β))
    (hd : ∀ x : Matrix α β E, ∃ y z : α × β → F,
      d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (x : Matrix β α E) : ∃ y z : β × α → F,
      (darbouxTransp d).e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
  obtain ⟨y, z, h⟩ := hd xᵀ
  refine ⟨fun p => y p.swap, fun p => z p.swap, ?_⟩
  have e : (incM F x)ᵀ = incM F xᵀ := (Matrix.transpose_map).symm
  rw [darbouxTransp_e, e, h]

omit [NumberField E] in

theorem exists_rational_dblCoord_right : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n m : ℕ)
    (J : Matrix (Fin m) (Fin m) E) (J' : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    J₂ = dblGram finSumFinEquiv J' →
    ∀ d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')) (Fin m × Fin n),
      (∀ x : Matrix (Fin m) (Fin n) E, ∃ y z : Fin m × Fin n → F,
        d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J₂)) (Fin m × Fin (n + n)),
      (∀ x : Matrix (Fin m) (Fin (n + n)) E, ∃ y z : Fin m × Fin (n + n) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) ∧
      (∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) := by
  intro F E _ _ _ _ _ σ n m J J' J₂ hJ d hd
  obtain ⟨co, hr, h1, h2⟩ := exists_rational_dblCoord hJ (darbouxTransp d) (darbouxTransp_rational d hd)
  refine ⟨darbouxTransp co, darbouxTransp_rational co hr, fun u hu => ?_, fun u hu => ?_⟩
  · rw [darbouxTransp_e, h1 uᵀ (by simpa only [Matrix.transpose_transpose] using hu)]
    rfl
  · rw [darbouxTransp_e, h2 uᵀ (by simpa only [Matrix.transpose_transpose] using hu)]
    rfl

end GlobalTheory.SWAniso
