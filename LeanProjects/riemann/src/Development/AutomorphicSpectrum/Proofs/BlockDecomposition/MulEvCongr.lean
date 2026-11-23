import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC
open CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.CompanionTheory.EdgeRep

theorem mul_ev_congr {R : Type} [CommRing R] {I J K : GlobalTheory.EtC.Cx R} (μ : Pair I J K) {X : Scheme.{0}} {n m k s t : ℤ}
    (h : n + m = k) (hst : s + t = k) (hs : -((0 : ℕ) : ℤ) + n = s) (ht : -((0 : ℕ) : ℤ) + m = t)
    (α : Cochain ((chains R).obj (sch.obj X)) I n) (β : Cochain ((chains R).obj (sch.obj X)) J m) :
    μ.mul X s t k hst (ev α 0 s hs X (𝟙 X)) (ev β 0 t ht X (𝟙 X)) =
      μ.mul X n m k h (ev α 0 n (by simp) X (𝟙 X)) (ev β 0 m (by simp) X (𝟙 X)) := by
  obtain rfl : s = n := by simpa using hs.symm
  obtain rfl : t = m := by simpa using ht.symm
  rfl

theorem aw_value {R : Type} [CommRing R] {I J K : GlobalTheory.EtC.Cx R} (μ : Pair I J K) {X : Scheme.{0}} {n m k : ℤ}
    (h : n + m = k) (α : Cochain ((chains R).obj (sch.obj X)) I n) (β : Cochain ((chains R).obj (sch.obj X)) J m)
    (γ : Cochain ((chains R).obj (sch.obj X)) K k) (hγ : μ.IsAW h α β γ) :
    ev γ 0 k (by simp) X (𝟙 X) = μ.mul X n m k h (ev α 0 n (by simp) X (𝟙 X)) (ev β 0 m (by simp) X (𝟙 X)) := by
  have h0 := hγ 0 k (by simp) X (𝟙 X)
  rw [Fin.sum_univ_one] at h0
  rw [h0]
  have hu : (m * ((0 : Fin 1) : ℕ)).negOnePow = 1 := by simp
  rw [hu, one_smul]
  exact mul_ev_congr μ h _ _ _ α β

theorem repCup : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.InSch → CrystallineSemistableComparison.E.RepCup := by
  intro _ _ _ _ _ R _ I J K μ X n m k h x y a b hx hy
  obtain ⟨α, rfl, rfl⟩ := hx
  obtain ⟨β, rfl, rfl⟩ := hy
  obtain ⟨γ, hγ⟩ := μ.aw_exists (sch.obj X) h α β
  exact ⟨γ, (μ.cup_spec (sch.obj X) h α β γ hγ).symm, aw_value μ h α.1 β.1 γ.1 hγ⟩

end GlobalTheory.CompanionTheory.EdgeRep

end
