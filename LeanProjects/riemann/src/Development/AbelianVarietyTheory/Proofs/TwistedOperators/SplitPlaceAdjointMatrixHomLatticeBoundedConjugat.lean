import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceColumnMemCompletedLatticeIffFrameIntegStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPartMemCompletedSelfDualLatticeIffSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjMemCompletedLatticeIffDualSplitPlace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitAdjBound

variable {D : D7}

theorem cA_tmul_pair (α : Af D.host.F) (m : D.host.E) :
    cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) = pairA D.host.F 0 α ⊗ₜ[D.host.F] star m := rfl

theorem tmul_eq_mul (x : AF D.host.F) (m : D.host.E) :
    (x ⊗ₜ[D.host.F] m : AE D) = algebraMap (AF D.host.F) (AE D) x * incA D m := by
  change _ = (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] m)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem gen_conj {v : FinPl D} (π : AE D →+* Fv D.host.F v)
    (hA : ∀ y : AF D.host.F, π (algebraMap (AF D.host.F) (AE D) y) = evalV D.host.F v (sndA D.host.F y))
    (S T : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    ((Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) :
        Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose.map π =
      (evalV D.host.F v α * π (incA D (star a))) •
        ((S.gram.map fun x => π (incA D x)) * vecMulVec (fun k => π (incA D (s k))) (fun l => π (incA D (star (t l))))) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, cA_tmul_pair]
  rw [tmul_eq_mul]
  simp only [map_mul, hA, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, vecMulVec_apply, star_mul', star_sum,
    star_star, GlobalTheory.LatVac.gram_star, map_sum]
  rw [show sndA D.host.F (pairA D.host.F 0 α) = α from rfl]
  simp only [Matrix.map_apply, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem adjCo_gen {v : FinPl D} (φ : SplitProj D v)
    (hA : ∀ y : AF D.host.F, rdA φ (algebraMap (AF D.host.F) (AE D) y) = evalV D.host.F v (sndA D.host.F y))
    (hQ : ∀ x : D.host.E, rdA φ (incA D x) = rdQ φ x)
    (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v))
    (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) (i : Fin S.rank)
    (j : Fin T.rank) :
    adjCo φ S T BS BT (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j))
        i j =
      evalV D.host.F v α * rdQ φ (star a) * (((BS⁻¹).1 *ᵥ fun k => rdQ φ (s k)) i) *
        (((fun l => rdQ φ (star (t l))) ᵥ* (T.gram.map (rdQ φ) * BT.1)) j) := by
  set f : D.host.E →+* Fv D.host.F v := (rdA φ).comp (incA D) with hf
  have hGi : (S.gram⁻¹.map (incA D)).map (rdA φ) * S.gram.map (fun x => rdA φ (incA D x)) = 1 := by
    rw [Matrix.map_map]
    change S.gram⁻¹.map f * S.gram.map f = 1
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S)]
    exact Matrix.map_one _ (map_zero f) (map_one f)
  have hmid : ∀ (c : Fv D.host.F v) (V : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v)),
      (S.gram⁻¹.map (incA D)).map (rdA φ) * (c • (S.gram.map (fun x => rdA φ (incA D x)) * V)) = c • V := by
    intro c V
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, hGi, Matrix.one_mul]
  have hT : (T.gram.map (incA D)).map (rdA φ) = T.gram.map (rdQ φ) := by
    rw [Matrix.map_map]; exact congrArg _ (funext hQ)
  unfold adjCo
  rw [Matrix.map_mul, Matrix.map_mul, gen_conj (rdA φ) hA, hmid, hT]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.smul_apply,
    vecMulVec_apply, smul_eq_mul, hQ, Matrix.vecMul_vecMul, mul_assoc]

section Lin

variable {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
  (BT : GL (Fin T.rank) (Fv D.host.F v))

theorem adjCo_add (x y : WO S T) : adjCo φ S T BS BT (x + y) = adjCo φ S T BS BT x + adjCo φ S T BS BT y := by
  unfold adjCo
  rw [show ((x + y : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) + (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) from rfl,
    Matrix.map_add _ (map_add _), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, Matrix.map_add _ (map_add _),
    Matrix.mul_add, Matrix.add_mul]

theorem adjCo_neg (x : WO S T) : adjCo φ S T BS BT (-x) = -adjCo φ S T BS BT x := by
  unfold adjCo
  rw [show ((-x : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      -(x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) from rfl,
    Matrix.map_neg _ (map_neg _), Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.map_neg _ (map_neg _),
    Matrix.mul_neg, Matrix.neg_mul]

theorem adjCo_zero : adjCo φ S T BS BT 0 = 0 := by
  unfold adjCo
  rw [show ((0 : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = 0 from rfl,
    Matrix.map_zero _ (map_zero _), Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.map_zero _ (map_zero _),
    Matrix.mul_zero, Matrix.zero_mul]

end Lin

theorem mul_latHat_mem {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {w : Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ intAE D) {y : Fin n → D.host.E} (hy : y ∈ Λ) :
    (fun i => w * ((1 : Af D.host.F) ⊗ₜ[D.host.F] y i)) ∈ latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E)) := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨β, hβ, o, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨β, hβ, o • y, Λ.smul_mem o hy, ?_⟩
    funext i
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rfl
  | zero => simp only [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => simp only [add_mul]; exact add_mem hx hz
  | neg x _ hx => simp only [neg_mul]; exact neg_mem hx

theorem adjCo_bound : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, (∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ (star a')) ≤ Valued.v (rdQ φ (star a))) → ∀ u ∈ latO S T ΛS ΛT (fun _ => True), ∀ i j, Valued.v (adjCo φ S T (frCo φ βS) (frCo φ βT) u i j) ≤ Valued.v (rdQ φ (star a)) := by
  intro D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he a hmax u hu
  obtain ⟨hπ, -, hQ, -, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a', ha', s, hs, t, ht, rfl⟩ := hw
    intro i j
    rw [adjCo_gen φ hπ.2.2.1 hQ]
    have h1 := (GlobalTheory.T.splitPlace_column_mem_completedLattice_iff_frame_integral D S ΛS βS hS hfS v φ e he fun k => incA D (s k)).1 (by
      simp only [GlobalTheory.SplitHomLattice.finPart_mul_incA]
      exact mul_latHat_mem ΛS (GlobalTheory.SplitHomLattice.idem_int he.1) hs) i
    have h2 := (GlobalTheory.T.conjPart_mem_completedSelfDualLattice_iff_splitPlace D T ΛT βT hT hfT v φ e he fun k => incA D (t k)).1 (by
      simp only [GlobalTheory.SplitHomLattice.finPart_mul_incA]
      exact mul_latHat_mem ΛT (GlobalTheory.SplitHomLattice.idem_int (GlobalTheory.SplitScalar.isSplitIdem_conj he.1)) ht) j
    simp only [hQ] at h1
    simp only [GlobalTheory.SplitDualLat.cA_incA, hQ] at h2
    have h3 := hmax a' ha'
    have h4 : Valued.v (evalV D.host.F v α) ≤ 1 := by
      have := hα v
      rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this
    rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_mul]
    calc _ ≤ 1 * Valued.v (rdQ φ (star a)) * 1 * 1 := mul_le_mul' (mul_le_mul' (mul_le_mul' h4 (hmax a' ha')) h1) h2
      _ = _ := by rw [one_mul, mul_one, mul_one]
  | zero =>
    intro i j
    rw [adjCo_zero, Matrix.zero_apply, map_zero]
    exact zero_le'
  | add x y _ _ hx hy =>
    intro i j
    rw [adjCo_add, Matrix.add_apply]
    exact Valuation.map_add_le _ (hx i j) (hy i j)
  | neg x _ hx =>
    intro i j
    rw [adjCo_neg, Matrix.neg_apply, Valuation.map_neg]
    exact hx i j

end GlobalTheory.SplitAdjBound
