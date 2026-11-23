import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.GramExtendZeroEmbedded
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseUnfoldB

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Afc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem gram_incM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Matrix (Fin d.m) (Fin d.n) E) :
    d.gram (incM F X) (incM F X) = incM F (gE d.A.J σ X) := by
  have h1 : (incM F X).map (cA σ) = incM F (X.map σ) := by ext i j; rfl
  show (incM F X)ᵀ * incM F d.A.J * (incM F X).map (cA σ) = _
  rw [h1]
  simp only [gE, incM, ← Matrix.transpose_map, ← Matrix.map_mul]
theorem cond_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Matrix (Fin d.m) (Fin d.n) E) (M : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    d.gram (incM F X) (incM F X) = (-2 : ℤ) • M ↔
      ∀ k l, inclR (F := F) (AF F) (gE d.A.J σ X k l) = (-2 : ℤ) • M k l := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.gram_incM_k, ← Matrix.ext_iff]
  rfl
theorem orb_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hmn : d.m < d.n) (T : nF σ d.Y d.b) (hT : IsND T) (Φ : d.Fn) : d.orb T Φ = 0 := by
  have hE : IsEmpty {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} := by
    refine ⟨fun ⟨X, hX⟩ => ?_⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.gram_incM_k] at hX
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
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.orb, tsum_empty]
section Res
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def extendByZeroColumns (X' : Matrix (Fin d.m) (Fin L.n) E) : Matrix (Fin d.m) (Fin d.n) E := fun a => Function.extend L.em (X' a) 0
theorem extendZeroColumn_apply_embed (X' : Matrix (Fin d.m) (Fin L.n) E) (a : Fin d.m) (j : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X' a (L.em j) = X' a j :=
  L.inj.extend_apply _ _ _
theorem not_mem_range_k : L.i₀ ∉ Set.range L.em := fun h => ((L.rng L.i₀).2 h) rfl
theorem extendZeroColumn_apply_missing (X' : Matrix (Fin d.m) (Fin L.n) E) (a : Fin d.m) : _root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X' a L.i₀ = 0 :=
  Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => _root_.PositivityTheory.SiegelWeilFormula.Afc.not_mem_range_k L ⟨j, hj⟩
theorem cases_idx_k (k : Fin d.n) : k = L.i₀ ∨ ∃ j, L.em j = k := by
  by_cases h : k = L.i₀
  · exact Or.inl h
  · exact Or.inr ((L.rng k).1 h)
theorem hermForm_extendZeroColumn_embed (X' : Matrix (Fin d.m) (Fin L.n) E) (i j : Fin L.n) :
    gE d.A.J σ (_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X') (L.em i) (L.em j) = gE d.A.J σ X' i j := by
  simp only [gE_apply, _root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_embed]
theorem hermForm_extendZeroColumn_left (X' : Matrix (Fin d.m) (Fin L.n) E) (l : Fin d.n) : gE d.A.J σ (_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X') L.i₀ l = 0 := by
  simp [gE_apply, _root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_missing]
theorem hermForm_extendZeroColumn_right (X' : Matrix (Fin d.m) (Fin L.n) E) (k : Fin d.n) : gE d.A.J σ (_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X') k L.i₀ = 0 := by
  simp [gE_apply, _root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_missing]
theorem gE_sub_k (X : Matrix (Fin d.m) (Fin d.n) E) (i j : Fin L.n) :
    gE d.A.J σ (X.submatrix id L.em) i j = gE d.A.J σ X (L.em i) (L.em j) := by
  simp only [gE_apply, Matrix.submatrix_apply, id]
theorem col_zero_k (X : Matrix (Fin d.m) (Fin d.n) E) (h : gE d.A.J σ X L.i₀ L.i₀ = 0) (a : Fin d.m) : X a L.i₀ = 0 := by
  have hA : Aniso σ d.A.J := _root_.GlobalTheory.ThK.Dbl.aniso_of_k d.ok.good (d.ok.sign.elim (fun h => Or.inl h.1) fun h => Or.inr h.1) d.ok.aniso
  have key := hA (fun i => X i L.i₀) (by
    rw [← h, gE_apply]
    simp only [form, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    ring)
  exact congrFun key a
theorem extension_by_zero_submatrix (X : Matrix (Fin d.m) (Fin d.n) E) (h : ∀ a, X a L.i₀ = 0) : _root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L (X.submatrix id L.em) = X := by
  ext a k
  rcases _root_.PositivityTheory.SiegelWeilFormula.Afc.cases_idx_k L k with rfl | ⟨j, rfl⟩
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_missing, h]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_embed]; rfl
theorem submatrix_extendZeroColumn (X' : Matrix (Fin d.m) (Fin L.n) E) : (_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X').submatrix id L.em = X' := by
  ext a j
  exact _root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_embed L X' a j
def eqv_k (T : nF σ d.Y d.b) (T' : nF σ L.Y L.b) (hs : L.IsSub T T') :
    {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} ≃
      {X : Matrix (Fin L.sd.m) (Fin L.sd.n) E // L.sd.gram (incM F X) (incM F X) = (-2 : ℤ) • T'.1.1} where
  toFun X := ⟨X.1.submatrix id L.em, by
    refine (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k L.sd _ _).2 fun i j => ?_
    have h := (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k d _ _).1 X.2 (L.em i) (L.em j)
    show inclR (F := F) (AF F) (gE d.A.J σ (X.1.submatrix id L.em) i j) = _
    rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.gE_sub_k, h, hs.2]
    rfl⟩
  invFun X' := ⟨_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X'.1, by
    refine (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k d _ _).2 fun k l => ?_
    rcases _root_.PositivityTheory.SiegelWeilFormula.Afc.cases_idx_k L k with rfl | ⟨i, rfl⟩
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.hermForm_extendZeroColumn_left, (hs.1 l).1, map_zero, smul_zero]
    rcases _root_.PositivityTheory.SiegelWeilFormula.Afc.cases_idx_k L l with rfl | ⟨j, rfl⟩
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.hermForm_extendZeroColumn_right, (hs.1 _).2, map_zero, smul_zero]
    rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.hermForm_extendZeroColumn_embed]
    have h := (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k L.sd _ _).1 X'.2 i j
    refine h.trans ?_
    rw [hs.2]
    rfl⟩
  left_inv X := by
    refine Subtype.ext (_root_.PositivityTheory.SiegelWeilFormula.Afc.extension_by_zero_submatrix L X.1 (_root_.PositivityTheory.SiegelWeilFormula.Afc.col_zero_k L X.1 ?_))
    have h := (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k d _ _).1 X.2 L.i₀ L.i₀
    rw [(hs.1 L.i₀).1, smul_zero] at h
    exact kfour.inclR_injective (h.trans (map_zero _).symm)
  right_inv X' := Subtype.ext (_root_.PositivityTheory.SiegelWeilFormula.Afc.submatrix_extendZeroColumn L X'.1)
theorem orb_res_k (T : nF σ d.Y d.b) (T' : nF σ L.Y L.b) (hs : L.IsSub T T') (Φ : d.Fn) (Φ' : L.sd.Fn)
    (hr : L.IsRes Φ Φ') : d.orb T Φ = L.sd.orb T' Φ' := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.orb
  refine congrArg (fun f : UA σ d.A.J → ℂ => ⨍ g in d.D, f g ∂d.μ) (funext fun g => ?_)
  rw [← (_root_.PositivityTheory.SiegelWeilFormula.Afc.eqv_k L T T' hs).tsum_eq]
  refine tsum_congr fun X => ?_
  have hc : ∀ a, X.1 a L.i₀ = 0 := _root_.PositivityTheory.SiegelWeilFormula.Afc.col_zero_k L X.1 (by
    have h := (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k d _ _).1 X.2 L.i₀ L.i₀
    rw [(hs.1 L.i₀).1, smul_zero] at h
    exact kfour.inclR_injective (h.trans (map_zero _).symm))
  have hz : ∀ a, (mat g⁻¹ * incM F X.1) a L.i₀ = 0 := fun a => by
    simp [Matrix.mul_apply, incM, hc]
  rw [← hr.2 _ hz]
  congr 1
end Res
theorem orbRes_k : _root_.PositivityTheory.SiegelWeilFormula.OrbRes_k := fun _F _E _ _ _ _ _ _σ d =>
  ⟨fun hmn T hT Φ => _root_.PositivityTheory.SiegelWeilFormula.Afc.orb_zero_k d hmn T hT Φ, fun L T T' hs Φ Φ' hr => _root_.PositivityTheory.SiegelWeilFormula.Afc.orb_res_k L T T' hs Φ Φ' hr⟩
end PositivityTheory.SiegelWeilFormula.Afc
end
end
