import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceColumnMemCompletedLatticeIffFrameIntegStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPartMemCompletedSelfDualLatticeIffSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.SplitHomOnto

open GlobalTheory.SplitHomLattice GlobalTheory.LatticeStable

variable {D : D7}

theorem rk_mem_latHat (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) {a : D.host.E} (ha : a ∈ D.host.AA)
    {s : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hs : s ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)))
    {t : Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (ht : t ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E))) :
    rk S T a s t ∈ latO S T ΛS ΛT fun _ => True := by
  change rkHom S T a s t ∈ _
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    induction ht using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hs
      obtain ⟨β, hβ, y, hy, rfl⟩ := ht
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, fun _ h => absurd trivial h, a, ha, x, hx, y, hy, ?_⟩
      · rw [map_mul]; exact mul_mem (hβ v) (hα v)
      · ext i j
        change liftFin D (_ * _ * ∑ k, (α ⊗ₜ[D.host.F] star (x k)) * _) = _
        rw [Matrix.of_apply, ← liftFin_tmul]
        congr 1
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [← TensorProduct.tmul_sum, Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem honto : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, a ∈ D.host.AA → a ≠ 0 → ∀ y : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v), (∀ i j, Valued.v (y i j) ≤ Valued.v (rdQ φ a)) → ∃ u, u ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf e u ∧ mapCo φ S T (frCo φ βS) (frCo φ βT) u = y := by
  intro D S T ΛS ΛT βS βT hSd hTd hfS hfT v φ e he a haA ha0 y hy
  obtain ⟨hπ, -, hQ, -, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  have hsi : IsSplitIdem D e := he.1
  set π : AE D →+* Fv D.host.F v := rdA φ with hπdef
  set c : Fv D.host.F v := π (incA D a) with hc
  have hc0 : c ≠ 0 := by
    intro h
    exact ha0 ((π.comp (incA D)).injective (by rw [RingHom.comp_apply, map_zero]; exact h))
  set BS : GL (Fin S.rank) (Fv D.host.F v) := frCo φ βS with hBS
  set BT : GL (Fin T.rank) (Fv D.host.F v) := frCo φ βT with hBT
  set G : Matrix (Fin S.rank) (Fin S.rank) (Fv D.host.F v) := S.gram.map (rdQ φ) with hG
  have hGπ : G = S.gram.map fun x => π (incA D x) := Matrix.ext fun i j => (hQ _).symm
  have hGu : IsUnit G.det := by
    have := (GlobalTheory.LatVac.gram_det_isUnit S).map (π.comp (incA D))
    rw [RingHom.map_det] at this
    rw [hGπ]; exact this
  choose σ hσ using hπ.1
  set Y : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) := c⁻¹ • y with hY
  have hYi : ∀ i j, Valued.v (Y i j) ≤ 1 := by
    intro i j
    have hy' := hy i j
    rw [← hQ] at hy'
    rw [hY, Matrix.smul_apply, smul_eq_mul, Valuation.map_mul, map_inv₀, hc]
    exact inv_mul_le_one_of_le₀ hy' zero_le'
  set X : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) := BT.1 * Y with hX
  set Z : Matrix (Fin S.rank) (Fin S.rank) (Fv D.host.F v) := (BS⁻¹).1 * G⁻¹ with hZ
  have hZ1 : Z * (G * BS.1) = 1 := by
    rw [hZ, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hGu, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  have hs : ∀ j, (fun k => finPart D (cA D e * cA D (σ (Z j k)))) ∈
      latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) := by
    intro j
    refine (GlobalTheory.T.conjPart_mem_completedSelfDualLattice_iff_splitPlace D S ΛS βS hSd hfS v φ e he fun k => cA D (σ (Z j k))).2 fun l => ?_
    have h1 : (fun i => rdA φ (cA D (cA D (σ (Z j i))))) = fun k => Z j k := by
      funext k; rw [GlobalTheory.DualPairCheck.cA_cA]; exact hσ _
    rw [h1]
    have : ((fun k => Z j k) ᵥ* (S.gram.map (rdQ φ) * (frCo φ βS).1)) l = (Z * (G * BS.1)) j l := rfl
    rw [this, hZ1, Matrix.one_apply]
    split_ifs <;> simp
  have ht : ∀ j, (fun k => finPart D (e * σ (X k j))) ∈
      latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) := by
    intro j
    refine (GlobalTheory.T.splitPlace_column_mem_completedLattice_iff_frame_integral D T ΛT βT hTd hfT v φ e he fun k => σ (X k j)).2 fun i => ?_
    have h1 : (fun k => rdA φ (σ (X k j))) = fun k => X k j := funext fun k => hσ _
    rw [h1]
    have : (((frCo φ βT)⁻¹ : GL (Fin T.rank) (Fv D.host.F v)).1 *ᵥ fun k => X k j) i = ((BT⁻¹).1 * X) i j := rfl
    rw [this, hX, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    exact hYi i j
  set u₀ : WO S T := ∑ j, rk S T a (fun k => finPart D (cA D e * cA D (σ (Z j k))))
    (fun k => finPart D (e * σ (X k j))) with hu₀
  have hu₀m : u₀ ∈ latO S T ΛS ΛT fun _ => True :=
    sum_mem fun j _ => rk_mem_latHat S T ΛS ΛT haA (hs j) (ht j)
  refine ⟨e • u₀, smul_mem_latO D S T _ _ _ e (idem_int hsi) _ hu₀m, fun i j => ?_, ?_⟩
  · rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hsi.1]
  · have hmap : (e • u₀).map π = c • (X * (Z * G)) := by
      refine Matrix.ext fun i l => ?_
      rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, pi_idem hsi hπ, one_mul, hu₀,
        Matrix.sum_apply, map_sum, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pi_rk hsi hπ S T a (fun k => cA D (σ (Z j k))) (fun k => σ (X k j)) i l]
      simp only [GlobalTheory.DualPairCheck.cA_cA, hσ]
      simp only [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hGπ, Matrix.map_apply]
      ring
    have hZG : Z * G = (BS⁻¹).1 := by rw [hZ, Matrix.nonsing_inv_mul_cancel_right _ _ hGu]
    have hXZG : c • (X * (Z * G)) = BT.1 * y * (BS⁻¹).1 := by
      rw [hZG, hX, hY, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc0,
        one_smul]
    show (BT⁻¹).1 * ((e • u₀).map π) * BS.1 = y
    rw [hmap, hXZG, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

end GlobalTheory.SplitHomOnto
