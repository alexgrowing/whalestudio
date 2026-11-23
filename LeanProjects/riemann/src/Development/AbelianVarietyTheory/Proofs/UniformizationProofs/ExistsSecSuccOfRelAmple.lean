import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecExtendOfNonzeroLocus

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open LBGerm

theorem IsAmpleLB.exists_sec_succ {X : Scheme.{0}} {L : LB X} (h : IsAmpleLB L) (x : X) :
    ∃ n, 1 ≤ n ∧ ∃ (a : (lbPow L n).Sec) (b : (lbPow L (n + 1)).Sec), x ∈ nonzeroLocus a ∧ x ∈ nonzeroLocus b := by
  have := h.compactSpace
  have := h.quasiSeparatedSpace
  have hL := h.isLB
  obtain ⟨i, hi⟩ := exists_chart hL x
  obtain ⟨n, hn, s, hs, hr, -⟩ := h.exists_affine_le hi
  have le : ∀ J : PUnit → L.ι, nonzeroLocus s ⊓ powChart L J ≤ L.U (J PUnit.unit) ⊓ L.U i :=
    fun J y hy => ⟨mem_powChart.1 hy.2, hr hy.1⟩
  have hg : ∀ (J : PUnit → L.ι) (y : X), y ∈ nonzeroLocus s ⊓ powChart L J →
      gs (𝟙 X) y _ (resG X (le J) (L.g (J PUnit.unit) i).val) =
        (gm (𝟙 X) y (L.U (J PUnit.unit) ⊓ L.U i) (L.g (J PUnit.unit) i)).val := fun J y hy =>
    (gs_res (𝟙 X) y _ hy _).trans (gs_unit (𝟙 X) y _ (le J hy) _)
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul (m := 1) hL s (fun J => resG X (le J) (L.g (J PUnit.unit) i).val)
    (mem_secOn_of_germ (M := lbPow L 1) _ fun y J J' h hJ hJ' => by
      rw [gm_lbPow_g 1 (𝟙 X) y J J' hJ hJ', pow_one]
      refine (hg J y ⟨h, hJ⟩).trans (Eq.trans ?_ (congrArg _ (hg J' y ⟨h, hJ'⟩)).symm)
      rw [← Units.val_mul, gm_cocycle hL (𝟙 X) y (mem_powChart.1 hJ) (mem_powChart.1 hJ') (hr h)])
  obtain ⟨u, hu⟩ := hN (N + 1) (Nat.le_succ N)
  refine ⟨n * (N + 1), Nat.mul_pos hn (Nat.succ_pos N), secPow s (N + 1), secCast (Nat.add_comm _ _) u, ?_, ?_⟩
  · rwa [nonzeroLocus_secPow s (Nat.succ_pos N)]
  · have hJ : x ∈ powChart L (fun _ => i) := mem_powChart.2 hi
    have hy : x ∈ nonzeroLocus s ⊓ powChart L (fun _ => i) := ⟨hs, hJ⟩
    have e := congrArg (gs (𝟙 X) x _) (hu fun _ => i)
    rw [gs_res _ x _ hy, gs_mul _ x _ hy, gs_pow _ x _ hy, gs_res _ x _ hy, hg _ x hy] at e
    rw [nonzeroLocus_secCast, mem_nonzeroLocus_iff_powFn u hJ, e]
    exact (((mem_nonzeroLocus_iff_powFn s hJ).1 hs).pow _).mul (Units.isUnit _)

theorem exists_sec_succ_of_relAmple : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] (L : LB X.left), L.IsLB → RelAmple X L → ∀ x : X.left, ∃ (n : ℕ) (_ : 1 ≤ n) (a : H0 L n) (b : H0 L (n + 1)), x ∈ nonzeroLocus a ∧ x ∈ nonzeroLocus b := by
  intro R _ X _ L hL hA x
  obtain ⟨n, hn, a, b, ha, hb⟩ := (isAmpleLB_of_relAmple_of_isAffine X hL hA).exists_sec_succ x
  obtain ⟨a', ha', -⟩ := exists_sec_oneTerm L (K' := Fin 1) (e' := ((n : ℕ) : ℤ)) rfl a
  obtain ⟨b', hb', -⟩ := exists_sec_oneTerm L (K' := Fin 1) (e' := ((n + 1 : ℕ) : ℤ)) rfl b
  exact ⟨n, hn, a', b', ha'.ge ha, hb'.ge hb⟩

end GlobalTheory
