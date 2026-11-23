import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Afc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma {B : Base F E} (hB : B.IsGood σ) (a : E) : σ (σ a) = a := by
  obtain ⟨-, -, -, h⟩ := hB.cm
  let τ : E →+* ℂ := Classical.arbitrary _
  apply τ.injective
  rw [h, h, star_star]

def gE {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (σ : E →ₐ[F] E) {k : ℕ} (X : Matrix (Fin m) (Fin k) E) : Matrix (Fin k) (Fin k) E :=
  Xᵀ * J * X.map σ

theorem gE_apply {m k : ℕ} (J : Matrix (Fin m) (Fin m) E) (X : Matrix (Fin m) (Fin k) E) (i j : Fin k) :
    gE J σ X i j = ∑ b, (∑ a, X a i * J a b) * σ (X b j) := by
  simp [gE, Matrix.mul_apply]

theorem gram_incM (d : SD σ) (X : Matrix (Fin d.m) (Fin d.n) E) :
    d.gram (incM F X) (incM F X) = incM F (gE d.A.J σ X) := by
  have h1 : (incM F X).map (cA σ) = incM F (X.map σ) := by ext i j; rfl
  show (incM F X)ᵀ * incM F d.A.J * (incM F X).map (cA σ) = _
  rw [h1]
  simp only [gE, incM, ← Matrix.transpose_map, ← Matrix.map_mul]

theorem cond_iff (d : SD σ) (X : Matrix (Fin d.m) (Fin d.n) E) (M : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    d.gram (incM F X) (incM F X) = (-2 : ℤ) • M ↔
      ∀ k l, inclR (F := F) (AF F) (gE d.A.J σ X k l) = (-2 : ℤ) • M k l := by
  rw [gram_incM, ← Matrix.ext_iff]
  rfl

theorem isUnit_neg_two_pow (k : ℕ) : IsUnit ((((-2 : ℤ) : AE F E)) ^ k) := by
  have h : ((-2 : ℤ) : AE F E) = inclR (F := F) (AF F) ((-2 : ℤ) : E) := (map_intCast _ _).symm
  rw [h]
  exact ((isUnit_iff_ne_zero.2 (by norm_num : ((-2 : ℤ) : E) ≠ 0)).map _).pow k

theorem orb_zero (d : SD σ) (hmn : d.m < d.n) (T : nF σ d.Y d.b) (hT : IsND T) (Φ : d.Fn) : d.orb T Φ = 0 := by
  have hE : IsEmpty {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} := by
    refine ⟨fun ⟨X, hX⟩ => ?_⟩
    rw [gram_incM] at hX
    have hdet := congrArg Matrix.det hX
    have h0 : (gE d.A.J σ X).det = 0 := by
      by_contra h
      have hu : IsUnit (gE d.A.J σ X) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
      have h1 := Matrix.rank_of_isUnit _ hu
      have h2 : (gE d.A.J σ X).rank ≤ d.m := by
        rw [gE, Matrix.mul_assoc]
        exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
      rw [h1, Fintype.card_fin] at h2
      omega
    have hm : ((gE d.A.J σ X).map (inclR (F := F) (AF F))).det = inclR (F := F) (AF F) (gE d.A.J σ X).det :=
      ((inclR (F := F) (AF F)).map_det _).symm
    rw [incM, hm, h0, map_zero, ← Int.cast_smul_eq_zsmul (AE F E), Matrix.det_smul, Fintype.card_fin] at hdet
    exact hT ((isUnit_neg_two_pow d.n).mul_right_eq_zero.1 hdet.symm)
  simp [SD.orb, tsum_empty]

section Res

variable {d : SD σ} (L : LD d)

def ext0 (X' : Matrix (Fin d.m) (Fin L.n) E) : Matrix (Fin d.m) (Fin d.n) E := fun a => Function.extend L.em (X' a) 0

theorem extend_zero_embedding (X' : Matrix (Fin d.m) (Fin L.n) E) (a : Fin d.m) (j : Fin L.n) : ext0 L X' a (L.em j) = X' a j :=
  L.inj.extend_apply _ _ _

theorem not_mem_range : L.i₀ ∉ Set.range L.em := fun h => ((L.rng L.i₀).2 h) rfl

theorem extend_zero_column_zero (X' : Matrix (Fin d.m) (Fin L.n) E) (a : Fin d.m) : ext0 L X' a L.i₀ = 0 :=
  Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => not_mem_range L ⟨j, hj⟩

theorem cases_idx (k : Fin d.n) : k = L.i₀ ∨ ∃ j, L.em j = k := by
  by_cases h : k = L.i₀
  · exact Or.inl h
  · exact Or.inr ((L.rng k).1 h)

theorem gram_extend_zero_embedded (X' : Matrix (Fin d.m) (Fin L.n) E) (i j : Fin L.n) :
    gE d.A.J σ (ext0 L X') (L.em i) (L.em j) = gE d.A.J σ X' i j := by
  simp only [gE_apply, extend_zero_embedding]

theorem gram_extend_zero_left (X' : Matrix (Fin d.m) (Fin L.n) E) (l : Fin d.n) : gE d.A.J σ (ext0 L X') L.i₀ l = 0 := by
  simp [gE_apply, extend_zero_column_zero]

theorem gram_extend_zero_right (X' : Matrix (Fin d.m) (Fin L.n) E) (k : Fin d.n) : gE d.A.J σ (ext0 L X') k L.i₀ = 0 := by
  simp [gE_apply, extend_zero_column_zero]

theorem gE_sub (X : Matrix (Fin d.m) (Fin d.n) E) (i j : Fin L.n) :
    gE d.A.J σ (X.submatrix id L.em) i j = gE d.A.J σ X (L.em i) (L.em j) := by
  simp only [gE_apply, Matrix.submatrix_apply, id]

theorem col_zero (X : Matrix (Fin d.m) (Fin d.n) E) (h : gE d.A.J σ X L.i₀ L.i₀ = 0) (a : Fin d.m) : X a L.i₀ = 0 := by
  have hA : Aniso σ d.A.J := aniso_of d.ok.good (d.ok.sign.elim (fun h => Or.inl h.1) fun h => Or.inr h.1) d.ok.aniso
  have key := hA (fun i => X i L.i₀) (by
    rw [← h, gE_apply]
    simp only [form, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    ring)
  exact congrFun key a

theorem extension_zero_sub (X : Matrix (Fin d.m) (Fin d.n) E) (h : ∀ a, X a L.i₀ = 0) : ext0 L (X.submatrix id L.em) = X := by
  ext a k
  rcases cases_idx L k with rfl | ⟨j, rfl⟩
  · rw [extend_zero_column_zero, h]
  · rw [extend_zero_embedding]; rfl

theorem submatrix_extend_zero (X' : Matrix (Fin d.m) (Fin L.n) E) : (ext0 L X').submatrix id L.em = X' := by
  ext a j
  exact extend_zero_embedding L X' a j

def eqv (T : nF σ d.Y d.b) (T' : nF σ L.Y L.b) (hs : L.IsSub T T') :
    {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} ≃
      {X : Matrix (Fin L.sd.m) (Fin L.sd.n) E // L.sd.gram (incM F X) (incM F X) = (-2 : ℤ) • T'.1.1} where
  toFun X := ⟨X.1.submatrix id L.em, by
    refine (cond_iff L.sd _ _).2 fun i j => ?_
    have h := (cond_iff d _ _).1 X.2 (L.em i) (L.em j)
    show inclR (F := F) (AF F) (gE d.A.J σ (X.1.submatrix id L.em) i j) = _
    rw [gE_sub, h, hs.2]
    rfl⟩
  invFun X' := ⟨ext0 L X'.1, by
    refine (cond_iff d _ _).2 fun k l => ?_
    rcases cases_idx L k with rfl | ⟨i, rfl⟩
    · rw [gram_extend_zero_left, (hs.1 l).1, map_zero, smul_zero]
    rcases cases_idx L l with rfl | ⟨j, rfl⟩
    · rw [gram_extend_zero_right, (hs.1 _).2, map_zero, smul_zero]
    rw [gram_extend_zero_embedded]
    have h := (cond_iff L.sd _ _).1 X'.2 i j
    refine h.trans ?_
    rw [hs.2]
    rfl⟩
  left_inv X := by
    refine Subtype.ext (extension_zero_sub L X.1 (col_zero L X.1 ?_))
    have h := (cond_iff d _ _).1 X.2 L.i₀ L.i₀
    rw [(hs.1 L.i₀).1, smul_zero] at h
    exact kfour.inclR_injective (h.trans (map_zero _).symm)
  right_inv X' := Subtype.ext (submatrix_extend_zero L X'.1)

theorem orb_res (T : nF σ d.Y d.b) (T' : nF σ L.Y L.b) (hs : L.IsSub T T') (Φ : d.Fn) (Φ' : L.sd.Fn)
    (hr : L.IsRes Φ Φ') : d.orb T Φ = L.sd.orb T' Φ' := by
  unfold SD.orb
  refine congrArg (fun f : UA σ d.A.J → ℂ => ⨍ g in d.D, f g ∂d.μ) (funext fun g => ?_)
  rw [← (eqv L T T' hs).tsum_eq]
  refine tsum_congr fun X => ?_
  have hc : ∀ a, X.1 a L.i₀ = 0 := col_zero L X.1 (by
    have h := (cond_iff d _ _).1 X.2 L.i₀ L.i₀
    rw [(hs.1 L.i₀).1, smul_zero] at h
    exact kfour.inclR_injective (h.trans (map_zero _).symm))
  have hz : ∀ a, (mat g⁻¹ * incM F X.1) a L.i₀ = 0 := fun a => by
    simp [Matrix.mul_apply, incM, hc]
  rw [← hr.2 _ hz]
  congr 1

end Res

theorem orbRes : OrbRes := fun _F _E _ _ _ _ _ _σ d =>
  ⟨fun hmn T hT Φ => orb_zero d hmn T hT Φ, fun L T T' hs Φ Φ' hr => orb_res L T T' hs Φ Φ' hr⟩

end PositivityTheory.SiegelWeilFormula.Afc

end
