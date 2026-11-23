import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace UpperTheory.HermUnipElt
open GlobalTheory.UnipMass

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem mat_mul' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g g' : UA σ J) :
    mat (g * g') = mat g * mat g' := rfl

private theorem mat_one' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

private theorem mat_inv_mul' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) :
    mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul', inv_mul_cancel, mat_one']

private theorem hA_mulVec (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (AE F E))
    (v w : Fin n → AE F E) :
    hA σ J (g *ᵥ v) (g *ᵥ w) = v ⬝ᵥ ((gᵀ * incM F J * g.map (cA σ)) *ᵥ fun i => cA σ (w i)) := by
  have hc : (fun i => cA σ ((g *ᵥ w) i)) = g.map (cA σ) *ᵥ fun i => cA σ (w i) := by
    funext i; exact RingHom.map_mulVec (cA σ).toRingHom g w i
  rw [hA, hc, ← Matrix.vecMul_transpose g v, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc]

private theorem hA_mat (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (v w : Fin n → AE F E) :
    hA σ J (mat g *ᵥ v) (mat g *ᵥ w) = hA σ J v w := by
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  rw [hA_mulVec, hg, hA]

private theorem isom_of_hA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (AE F E))
    (h : ∀ v w, hA σ J (g *ᵥ v) (g *ᵥ w) = hA σ J v w) : gᵀ * incM F J * g.map (cA σ) = incM F J := by
  ext i j
  have e : (fun k => cA σ ((Pi.single j 1 : Fin n → AE F E) k)) = Pi.single j 1 := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hA_mulVec, hA, e, single_one_dotProduct, single_one_dotProduct, Matrix.mulVec_single_one,
    Matrix.mulVec_single_one] at this
  exact this

private theorem unip_fix {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁} (u : UA σ W.J)
    (hu : u ∈ unip σ W H') : mat u *ᵥ incV F H'.x = incV F H'.x := by
  induction hu using Subgroup.closure_induction with
  | mem g hg => exact hg.1
  | one => rw [mat_one', Matrix.one_mulVec]
  | mul g g' _ _ hg hg' => rw [mat_mul', ← Matrix.mulVec_mulVec, hg', hg]
  | inv g _ hg =>
    conv_lhs => rw [← hg]
    rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]

private theorem hA_herm {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (v w : Fin n → AE F E) : cA σ (hA σ J v w) = hA σ J w v := by
  simp only [hA, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_cA hσ, incM, Matrix.map_apply, cA_inclR]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hJ y x]
  ring

private theorem hA_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : AE F E) (v w : Fin n → AE F E) :
    hA σ J (a • v) w = a * hA σ J v w := by
  simp [hA, smul_dotProduct]

private theorem hA_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : AE F E)
    (v w : Fin n → AE F E) : hA σ J v (a • w) = cA σ a * hA σ J v w := by
  simp only [hA, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show (fun i => cA σ a * cA σ (w i)) = cA σ a • fun i => cA σ (w i) from rfl, Matrix.mulVec_smul,
    dotProduct_smul, smul_eq_mul]

private theorem hA_gram (σ : E →ₐ[F] E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin m) E)
    (z z' : Fin m → AE F E) :
    hA σ J (incM F A *ᵥ z) (incM F A *ᵥ z') = hA σ (Aᵀ * J * A.map σ) z z' := by
  have hc : (fun i => cA σ ((incM F A *ᵥ z') i)) = (incM F A).map (cA σ) *ᵥ fun i => cA σ (z' i) := by
    funext i; exact RingHom.map_mulVec (cA σ).toRingHom (incM F A) z' i
  have e : (incM F A)ᵀ * incM F J * (incM F A).map (cA σ) = incM F (Aᵀ * J * A.map σ) := by
    ext i j
    simp only [incM, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_mul, cA_inclR]
  rw [hA, hA, hc, ← Matrix.vecMul_transpose (incM F A) z, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc, e]

private def gm (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x w : Fin n → AE F E) (β : AE F E) :
    Matrix (Fin n) (Fin n) (AE F E) :=
  1 + Matrix.vecMulVec (w + β • x) (incM F J *ᵥ fun i => cA σ (x i)) -
    Matrix.vecMulVec x (incM F J *ᵥ fun i => cA σ (w i))

private theorem gm_mulVec (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x w : Fin n → AE F E) (β : AE F E)
    (v : Fin n → AE F E) :
    gm σ J x w β *ᵥ v = v + hA σ J v x • w + (hA σ J v x * β - hA σ J v w) • x := by
  ext i
  simp only [gm, hA, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.add_apply,
    Matrix.vecMulVec_mulVec, Pi.smul_apply, smul_eq_mul, op_smul_eq_mul]
  rw [dotProduct_comm v, dotProduct_comm v]
  ring

private theorem gm_inv (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x w : Fin n → AE F E) (β β' : AE F E)
    (hxx : hA σ J x x = 0) (hwx : hA σ J w x = 0) (hxw : hA σ J x w = 0) (hβ : β + β' = -hA σ J w w) :
    gm σ J x w β * gm σ J x (-w) β' = 1 := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  generalize (Pi.single i 1 : Fin n → AE F E) = v
  rw [gm_mulVec, gm_mulVec]
  simp only [hA_add_left, hA_smul_left, hA_neg_left, hA_neg_right', hxx, hwx, hxw]
  have : hA σ J w w = -(β + β') := by rw [hβ, neg_neg]
  rw [this]
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

private theorem gm_isom {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (x w : Fin n → AE F E) (β : AE F E)
    (hxx : hA σ J x x = 0) (hwx : hA σ J w x = 0) (hxw : hA σ J x w = 0) (hβ : β + cA σ β = -hA σ J w w) :
    (gm σ J x w β)ᵀ * incM F J * (gm σ J x w β).map (cA σ) = incM F J := by
  refine isom_of_hA σ J _ fun v v' => ?_
  rw [gm_mulVec, gm_mulVec]
  simp only [hA_add_left, hA_smul_left, hA_add_right, hA_smul_right, hxx, hwx, hxw, map_sub, map_mul,
    hA_herm hσ hJ]
  linear_combination (hA σ J v x * hA σ J x v') * hβ

end UpperTheory.HermUnipElt

open UpperTheory.HermUnipElt GlobalTheory.UnipMass in
theorem UpperTheory.exists_unipotent_heisenberg :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ r s r₁ s₁ : ℕ),
        B.IsGood σ → X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ → H.IsAdapted σ B X X₁ j₀ j₁ →
        ∀ (z : Fin n₁ → AE F E) (β : AE F E), β + cA σ β = -GlobalTheory.UnipMass.hA σ X₁.J z z →
        ∃ u ∈ unip σ X H, mat u⁻¹ *ᵥ incV F H.y = incV F H.y + incM F H.ι *ᵥ z + β • incV F H.x ∧
          (z = 0 → ∀ v ∈ unip σ X H, u * v = v * u) := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hB hX _ hH z β hβ
  have hσ : ∀ a, σ (σ a) = a := cm_conj_conj hB.cm
  have hh := hA_herm (F := F) hσ hX.herm
  have horth : ∀ z, hA σ X.J (incM F H.ι *ᵥ z) (incV F H.x) = 0 ∧ hA σ X.J (incM F H.ι *ᵥ z) (incV F H.y) = 0 := by
    intro z
    rw [hA_incM_incV, hA_incM_incV]
    refine ⟨Finset.sum_eq_zero fun j _ => ?_, Finset.sum_eq_zero fun j _ => ?_⟩
    · have h1 := (hH.orth (Pi.single j 1)).1
      rw [Matrix.mulVec_single_one] at h1
      rw [show (fun i => H.ι i j) = H.ι.col j from rfl, h1, map_zero, mul_zero]
    · have h1 := (hH.orth (Pi.single j 1)).2
      rw [Matrix.mulVec_single_one] at h1
      rw [show (fun i => H.ι i j) = H.ι.col j from rfl, h1, map_zero, mul_zero]
  have hxx : hA σ X.J (incV F H.x) (incV F H.x) = 0 := by rw [hA_incV, hH.xx, map_zero]
  have hxy : hA σ X.J (incV F H.x) (incV F H.y) = 1 := by rw [hA_incV, hH.xy, map_one]
  have hyx : hA σ X.J (incV F H.y) (incV F H.x) = 1 := by rw [← hh, hxy, map_one]
  have hwx := (horth z).1
  have hxw : hA σ X.J (incV F H.x) (incM F H.ι *ᵥ z) = 0 := by rw [← hh, hwx, map_zero]
  have hyw : hA σ X.J (incV F H.y) (incM F H.ι *ᵥ z) = 0 := by rw [← hh, (horth z).2, map_zero]
  have hβ' : β + cA σ β = -hA σ X.J (incM F H.ι *ᵥ z) (incM F H.ι *ᵥ z) := by rw [hA_gram, hH.gram, hβ]
  set x := incV F H.x with hx
  set w := incM F H.ι *ᵥ z with hw
  have i1 := gm_inv σ X.J x w β (cA σ β) hxx hwx hxw hβ'
  have i2 := gm_inv σ X.J x (-w) (cA σ β) β hxx (by rw [hA_neg_left, hwx, neg_zero])
    (by rw [hA_neg_right', hxw, neg_zero]) (by rw [hA_neg_left, hA_neg_right', neg_neg, add_comm, hβ'])
  rw [neg_neg] at i2
  let g : UA σ X.J := ⟨⟨gm σ X.J x w β, gm σ X.J x (-w) (cA σ β), i1, i2⟩,
    gm_isom hσ hX.herm x w β hxx hwx hxw hβ'⟩
  have hg : ∀ v, mat g *ᵥ v = v + hA σ X.J v x • w + (hA σ X.J v x * β - hA σ X.J v w) • x :=
    gm_mulVec σ X.J x w β
  have hgm : g ∈ unip σ X H := by
    refine Subgroup.subset_closure ⟨?_, fun z' => ⟨-hA σ X.J (incM F H.ι *ᵥ z') w, ?_⟩⟩
    · rw [hg, hxx, hxw]; simp
    · rw [hg, (horth z').1]; simp [hx]
  refine ⟨g⁻¹, inv_mem hgm, ?_, fun hz v hv => ?_⟩
  · rw [inv_inv, hg, hyx, hyw]; simp
  · have hw0 : w = 0 := by rw [hw, hz, Matrix.mulVec_zero]
    have hc : Commute g v := by
      apply Subtype.ext
      apply Units.ext
      show mat g * mat v = mat v * mat g
      refine Matrix.ext_of_mulVec_single fun i => ?_
      generalize (Pi.single i 1 : Fin n → AE F E) = t
      have e : hA σ X.J (mat v *ᵥ t) x = hA σ X.J t x :=
        calc hA σ X.J (mat v *ᵥ t) x = hA σ X.J (mat v *ᵥ t) (mat v *ᵥ x) := by rw [unip_fix v hv]
          _ = _ := hA_mat σ v _ _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg, hg, hw0, e]
      simp only [smul_zero, add_zero, hA_zero_right, sub_zero, Matrix.mulVec_add, Matrix.mulVec_smul]
      rw [unip_fix v hv]
    exact hc.inv_left.eq

end
