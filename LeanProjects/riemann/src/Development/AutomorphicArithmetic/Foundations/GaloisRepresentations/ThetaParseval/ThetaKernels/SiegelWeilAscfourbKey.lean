import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.NilpotentFramePartApplyZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentNilpotentMulEqZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PadMatrixLowerBlockZero

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
namespace Bq
theorem pad_j_k (g : G2 σ L.Y) : Pad (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b (L.j g)) := by
  intro r c h
  rcases h with h | h | h | h
  · exact (L.j_out g r (by simp [h]) c).1
  · exact (L.j_out g r (by simp [h]) c).1
  · exact (L.j_out g c (by simp [h]) r).2
  · exact (L.j_out g c (by simp [h]) r).2
def bp_k (β : Matrix (Fin d.n) (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  Matrix.of fun i k => if i = L.i₀ ∨ k = L.i₀ then 0 else β i k
theorem padM_n_k (β : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L (Matrix.fromBlocks 1 (-(β.submatrix L.em L.em)) 0 1) = Matrix.fromBlocks 1 (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β)) 0 1 := by
  refine Matrix.ext fun r c => ?_
  rcases r with i | i <;> rcases c with k | k
  all_goals
    by_cases hi : i = L.i₀
    · first
        | rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_row_k L _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inl_k L i hi)]
        | rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_row_k L _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inr_k L i hi)]
      subst hi
      simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, Matrix.one_apply]
    · by_cases hk : k = L.i₀
      · first
          | rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_col_k L _ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inl_k L k hk)]
          | rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_col_k L _ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inr_k L k hk)]
        subst hk
        simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, Matrix.one_apply, hi]
      · obtain ⟨a, rfl⟩ := (L.rng i).1 hi
        obtain ⟨a', rfl⟩ := (L.rng k).1 hk
        first
          | exact (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L _ (Sum.inl a) (Sum.inl a')).trans (by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, Matrix.one_apply, L.inj.eq_iff, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k])
          | exact (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L _ (Sum.inl a) (Sum.inr a')).trans (by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, Matrix.one_apply, L.inj.eq_iff, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k])
          | exact (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L _ (Sum.inr a) (Sum.inl a')).trans (by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, Matrix.one_apply, L.inj.eq_iff, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k])
          | exact (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L _ (Sum.inr a) (Sum.inr a')).trans (by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, Matrix.one_apply, L.inj.eq_iff, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k])
theorem unipotentEntry_eq_zero (u : Fin L.n → AE F E) (a k : Fin d.n) (h : a ≠ L.i₀ ∨ k = L.i₀) : _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u a k = 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.single_apply_of_ne]
  rintro ⟨h1, h2⟩
  rcases h with h | h
  · exact h h1.symm
  · exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L j (h2.trans h)
theorem nq_q_k (β : Matrix (Fin d.n) (Fin d.n) (AE F E)) (u : Fin L.n → AE F E) :
    NQ (Sum.inl L.i₀) (Sum.inr L.i₀)
      (Matrix.fromBlocks 1 β 0 1 * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k L u * Matrix.fromBlocks 1 (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β)) 0 1) := by
  set A := 1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u with hA
  set D := ((1 - _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u)ᵀ).map (cA σ) with hD
  have e : Matrix.fromBlocks 1 β 0 1 * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k L u * Matrix.fromBlocks 1 (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β)) 0 1 =
      Matrix.fromBlocks A (-(A * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β) + β * D) 0 D := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, Matrix.mul_neg, hA, hD]
    congr 1
    abel
  have hA1 : ∀ a k, a ≠ L.i₀ ∨ k = L.i₀ → (A - 1) a k = 0 := fun a k h => by
    rw [hA, add_sub_cancel_left, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.unipotentEntry_eq_zero L u a k h]
  have hD1 : ∀ a k, k ≠ L.i₀ → D a k = (1 : Matrix _ _ (AE F E)) a k := fun a k hk => by
    simp only [hD, Matrix.map_apply, Matrix.transpose_apply, Matrix.sub_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.unipotentEntry_eq_zero L u k a (Or.inl hk), sub_zero]
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases h : k = a
    · subst h; simp [map_one]
    · rw [if_neg h, if_neg (Ne.symm h), map_zero]
  rw [e]
  refine Bq.NQ.of_blocks (fun a => hA1 a L.i₀ (Or.inr rfl)) (fun a k ha => hA1 a k (Or.inl ha)) (fun a k ha hk => ?_)
    (fun a k hk => by rw [Matrix.sub_apply, hD1 a k hk, sub_self])
  have h1 : (A * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β) a k = β a k := by
    rw [Matrix.mul_apply]
    have : ∀ m, A a m * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β m k = if m = a then β a k else 0 := fun m => by
      have hAm : A a m = (1 : Matrix _ _ (AE F E)) a m := by
        have := hA1 a m (Or.inl ha); rwa [Matrix.sub_apply, sub_eq_zero] at this
      rw [hAm, Matrix.one_apply]
      by_cases hm : a = m
      · subst hm; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, ha, hk]
      · simp [hm, Ne.symm hm]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h2 : (β * D) a k = β a k := by
    rw [Matrix.mul_apply]
    simp only [hD1 _ k hk, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Matrix.add_apply, Matrix.neg_apply, h1, h2, neg_add_cancel]
theorem isPar_of_nq_k {p : d.G} (h : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b p)) :
    ∃ t, IsPar p t ∧ Matrix.GeneralLinearGroup.det t = 1 := by
  obtain ⟨-, t₀, ht₀⟩ := d.ok.frame
  set M := inFrame d.b p
  set T0 := incM F t₀.1
  set T0i := incM F (t₀⁻¹).1
  have e1 : T0 * T0i = 1 := by
    simp only [T0, T0i, incM, ← Matrix.map_mul]
    rw [show t₀.1 * (t₀⁻¹).1 = 1 from t₀.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hdet : (T0 * M.toBlocks₁₁ * T0i).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, h.upper_block_det_one, mul_one, ← Matrix.det_mul, e1, Matrix.det_one]
  have hu : IsUnit (T0 * M.toBlocks₁₁ * T0i) := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hdet]; exact isUnit_one)
  refine ⟨hu.unit, (kunf.isPar_frame ht₀ p hu.unit).2 ⟨h.projected_block_lower_sum, rfl⟩, ?_⟩
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, hdet]
end Bq
theorem key_id_pf_k {nb : nA σ d.Y d.b → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} (hnb : IsNMap d.b nb)
    (hnb' : IsNMap L.b nb') {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (h : G2 σ L.Y) (β : nA σ d.Y d.b) (u : Fin L.n → AE F E)
    (x : d.G) : ∃ p t, IsPar p t ∧ Matrix.GeneralLinearGroup.det t = 1 ∧
      L.j h * (nb β * (uM u * x)) = p * (L.j (h * nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * x) := by
  set q : d.G := nb β * uM u * L.j (nb' (-_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) with hq
  set p : d.G := L.j h * q * L.j h⁻¹ with hp
  have hinv : L.j (nb' (-_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) = (L.j (nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)))⁻¹ := by
    rw [kunf.nb_neg hnb', map_inv]
  have hid : L.j h * (nb β * (uM u * x)) = p * (L.j (h * nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * x) := by
    simp only [hp, hq, hinv, map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
  have hQ : inFrame d.b q = Matrix.fromBlocks 1 β.1 0 1 * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k L u * Matrix.fromBlocks 1 (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β.1)) 0 1 := by
    rw [hq, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hnb β, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.inFrame_uM_k L hU u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k,
      hnb' (-_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β), ← _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.padM_n_k L β.1]
    rfl
  have hJJ : inFrame d.b (L.j h) * inFrame d.b (L.j h⁻¹) = 1 := by
    rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← map_mul, mul_inv_cancel, map_one, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have hnq : Bq.NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b p) := by
    rw [hp, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hQ]
    exact Bq.NQ.conj (by simp) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.pad_j_k L h) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.pad_j_k L h⁻¹) hJJ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.nq_q_k L β.1 u)
  obtain ⟨t, ht, hdt⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.isPar_of_nq_k L hnq
  exact ⟨p, t, ht, hdt, hid⟩
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
