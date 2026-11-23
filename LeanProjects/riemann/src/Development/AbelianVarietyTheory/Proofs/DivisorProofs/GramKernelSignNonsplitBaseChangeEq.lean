import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.UnitaryClasses.BaseChangeSign

section Gen
variable {L : Type} [Field L] (τ : L →+* L) {n : ℕ}

theorem hform_eq_mat (J : Matrix (Fin n) (Fin n) L) {ι : Type} [Fintype ι] (f : ι → Fin n → L) (i j : ι) :
    hform τ J (f i) (f j) = (cT τ (Matrix.of fun r i => f i r) * J * Matrix.of fun r i => f i r) i j := by
  simp only [hform, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_det_change (J : Matrix (Fin n) (Fin n) L) (V : Submodule L (Fin n → L)) {ι : Type} [Fintype ι]
    [DecidableEq ι] (c b : Module.Basis ι L V) :
    (Matrix.of fun i j => hform τ J (b i).1 (b j).1).det =
      τ (c.toMatrix b).det * (Matrix.of fun i j => hform τ J (c i).1 (c j).1).det * (c.toMatrix b).det := by
  have hM : (Matrix.of fun r i => ((b i : V) : Fin n → L) r) =
      (Matrix.of fun r i => ((c i : V) : Fin n → L) r) * c.toMatrix b := by
    ext r j
    simp only [Matrix.of_apply, Matrix.mul_apply]
    have h := c.sum_toMatrix_smul_self b j
    calc ((b j : V) : Fin n → L) r = ((∑ i, c.toMatrix b i j • c i : V) : Fin n → L) r := by rw [h]
      _ = _ := by
        simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have e1 : (Matrix.of fun i j => hform τ J (b i).1 (b j).1) =
      cT τ (Matrix.of fun r i => ((b i : V) : Fin n → L) r) * J * Matrix.of fun r i => ((b i : V) : Fin n → L) r := by
    ext i j; exact hform_eq_mat τ J (fun i => ((b i : V) : Fin n → L)) i j
  have e2 : (Matrix.of fun i j => hform τ J (c i).1 (c j).1) =
      cT τ (Matrix.of fun r i => ((c i : V) : Fin n → L) r) * J * Matrix.of fun r i => ((c i : V) : Fin n → L) r := by
    ext i j; exact hform_eq_mat τ J (fun i => ((c i : V) : Fin n → L)) i j
  have hdet : ∀ P : Matrix ι ι L, (cT τ P).det = τ P.det := by
    intro P; unfold cT; rw [Matrix.det_transpose, RingHom.map_det]; rfl
  rw [e1, e2, hM, cT_mul]
  set Mc := Matrix.of fun r i => ((c i : V) : Fin n → L) r
  set P := c.toMatrix b
  have : cT τ P * cT τ Mc * J * (Mc * P) = cT τ P * (cT τ Mc * J * Mc) * P := by
    simp only [Matrix.mul_assoc]
  rw [this, Matrix.det_mul, Matrix.det_mul, hdet]

theorem toMatrix_det_ne {V : Submodule L (Fin n → L)} {ι : Type} [Fintype ι] [DecidableEq ι]
    (c b : Module.Basis ι L V) : (c.toMatrix b).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (c.toMatrix_mul_toMatrix_flip b)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

end Gen

section BC
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : ℕ}

theorem mem_ker_map {A : Matrix (Fin n) (Fin n) K} {x : Fin n → K} (hx : x ∈ LinearMap.ker (Matrix.toLin' A)) :
    (φ ∘ x) ∈ LinearMap.ker (Matrix.toLin' (A.map φ)) := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hx ⊢
  funext i
  rw [← RingHom.map_mulVec, hx]; simp

theorem finrank_ker_map (A : Matrix (Fin n) (Fin n) K) :
    Module.finrank L (LinearMap.ker (Matrix.toLin' (A.map φ))) =
      Module.finrank K (LinearMap.ker (Matrix.toLin' A)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (A.map φ))
  have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
  have h3 : (A.map φ).rank = A.rank := GlobalTheory.Core.Rk.rank_map_field φ A
  change (A.map φ).rank + _ = _ at h1
  change A.rank + _ = _ at h2
  simp only [Module.finrank_fin_fun] at h1 h2
  omega

end BC

section Val
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hxy' : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
  unfold ordL
  rw [dif_neg hx', dif_neg hy', dif_neg hxy']
  have : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, WithZero.coe_unzero, map_mul]
  rw [this, toAdd_mul]; ring

theorem sign_conj_mul {τ : L →+* L} (hv : ∀ x, Valued.v (τ x) = Valued.v x) {t : L} (ht : t ≠ 0) (a : L) :
    (-1 : ℂ) ^ ordL (τ t * a * t) = (-1) ^ ordL a := by
  by_cases ha : a = 0
  · simp [ha]
  have hτ : τ t ≠ 0 := (map_ne_zero τ).2 ht
  have ho : ordL (τ t) = ordL t := by
    unfold ordL; simp only [hv]
  rw [ordL_mul (mul_ne_zero hτ ha) ht, ordL_mul hτ ha, ho,
    show ordL t + ordL a + ordL t = ordL a + 2 * ordL t by ring, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), _root_.zpow_mul]
  norm_num

end Val

section Main
variable {K L : Type} [Field K] [Field L] (σ : K →+* K) (τ : L →+* L) (φ : K →+* L) {n : ℕ}

theorem gram_det_map (hφ : ∀ x, τ (φ x) = φ (σ x)) (H A : Matrix (Fin n) (Fin n) K) :
    ∃ t : L, t ≠ 0 ∧ (gramOn τ (H.map φ) (LinearMap.ker (Matrix.toLin' (A.map φ)))).det =
      τ t * φ (gramOn σ H (LinearMap.ker (Matrix.toLin' A))).det * t := by
  letI := φ.toAlgebra
  haveI : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).2 φ.injective
  set V := LinearMap.ker (Matrix.toLin' A) with hV
  set V' := LinearMap.ker (Matrix.toLin' (A.map φ)) with hV'
  have hk : Module.finrank L V' = Module.finrank K V := finrank_ker_map φ A
  rcases isEmpty_or_nonempty (Fin (Module.finrank L V')) with he | hne
  · haveI : IsEmpty (Fin (Module.finrank K V)) := hk ▸ he
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Matrix.det_isEmpty, Matrix.det_isEmpty]; simp
  let b := Module.finBasis K V
  let v : Fin (Module.finrank L V') → V' := fun i =>
    ⟨φ ∘ ((b (Fin.cast hk i) : V) : Fin n → K), mem_ker_map φ (b (Fin.cast hk i)).2⟩
  have hli : LinearIndependent L v := by
    apply LinearIndependent.of_comp V'.subtype
    have h0 : LinearIndependent K (fun i => ((b (Fin.cast hk i) : V) : Fin n → K)) :=
      (b.linearIndependent.map' V.subtype V.ker_subtype).comp _ (Fin.cast_injective hk)
    exact linearIndependent_algebraMap_comp_iff.2 h0
  let c := basisOfLinearIndependentOfCardEqFinrank hli (Fintype.card_fin _)
  have hc : ∀ i, c i = v i := fun i => by simp [c]
  refine ⟨(c.toMatrix (Module.finBasis L V')).det, toMatrix_det_ne c _, ?_⟩
  have e1 : gramOn τ (H.map φ) V' =
      Matrix.of fun i j => hform τ (H.map φ) (Module.finBasis L V' i).1 (Module.finBasis L V' j).1 := rfl
  rw [e1, gram_det_change τ (H.map φ) V' c (Module.finBasis L V')]
  have e2 : (Matrix.of fun i j => hform τ (H.map φ) (c i).1 (c j).1) =
      ((gramOn σ H V).map φ).submatrix (finCongr hk) (finCongr hk) := by
    ext i j
    simp only [Matrix.of_apply, hc, v, Matrix.submatrix_apply, Matrix.map_apply, gramOn, hform, map_sum, map_mul,
      Function.comp_apply, hφ, finCongr_apply]
    rfl
  rw [e2, Matrix.det_submatrix_equiv_self,
    show ((gramOn σ H V).map φ).det = φ (gramOn σ H V).det from (RingHom.map_det φ _).symm]

end Main

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w →
    ∀ (n : ℕ) (H A : Matrix (Fin n) (Fin n) E),
    (-1 : ℂ) ^ ordL (gramOn (cj w) (H.map (algebraMap E (w.adicCompletion E)))
      (LinearMap.ker (Matrix.toLin' (A.map (algebraMap E (w.adicCompletion E)))))).det =
    (-1) ^ ordL (algebraMap E (w.adicCompletion E)
      (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H (LinearMap.ker (Matrix.toLin' A))).det) := by
  intro E _ _ _ hU w hw n H A
  have hc := GlobalTheory.ConjAtPlace.main E hU w
  have hφ : ∀ x : E, cj w (algebraMap E (w.adicCompletion E) x) =
      algebraMap E (w.adicCompletion E) ((IsCMField.complexConj E).toRingEquiv.toRingHom x) :=
    fun x => (hc.2.2.2.1 hw).1 x
  obtain ⟨t, ht, hdet⟩ := gram_det_map (IsCMField.complexConj E).toRingEquiv.toRingHom (cj w)
    (algebraMap E (w.adicCompletion E)) hφ H A
  rw [hdet, sign_conj_mul hc.2.2.1 ht]

end GlobalTheory.UnitaryClasses.BaseChangeSign
