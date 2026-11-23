import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem AnFr.genMove_e_zero : Φ.e 0 = 1 := (Φ.e_ker 0).2 Φ.lat.zero_mem

theorem AnFr.genMove_e_zero_left : (Φ.e 0).left = x0 ≫ eSec A := by
  rw [Φ.genMove_e_zero]
  show (toUnit (Over.mk x0) ≫ η[A]).left = _
  rw [Over.comp_left]
  rfl

theorem AnFr.genMove_e_per (z a : Fin g → ℂ) (ha : a ∈ Φ.lat) : Φ.e (z + a) = Φ.e z := by
  rw [Φ.e_add, (Φ.e_ker a).2 ha, _root_.mul_one]

theorem genMove_chart {X Z : Scheme.{0}} (M : LB X) {K : Type} [Fintype K] (φ : K → (Z ⟶ X)) (q : Sp ℂ ⟶ Z)
    (j : K → M.ι) (h : ⊤ ≤ q ⁻¹ᵁ LB.wchart M φ j) (k : K) : ⊤ ≤ (q ≫ φ k) ⁻¹ᵁ M.U (j k) :=
  fun _ hy => LB.wchart_le M φ j k (h hy)

theorem AnFr.genRd_pullGen_iff {Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L.L φ ε)) {Z' : Scheme.{0}} (h : Z' ⟶ Z) (q : Sp ℂ ⟶ Z') (p : K → Fin g → ℂ) (v : ℂ) :
    Φ.GenRd (fun k => h ≫ φ k) ε (LB.pullGen L.L φ ε t h) q p v ↔ Φ.GenRd φ ε t (q ≫ h) p v := by
  have hc : ∀ j : K → L.L.ι, (⊤ ≤ q ⁻¹ᵁ LB.wchart L.L (fun k => h ≫ φ k) j) ↔
      ⊤ ≤ (q ≫ h) ⁻¹ᵁ LB.wchart L.L φ j := fun j =>
    ⟨fun H _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (H hy) k,
      fun H _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (H hy) k⟩
  have hv : ∀ j : K → L.L.ι, (⊤ ≤ q ⁻¹ᵁ LB.wchart L.L (fun k => h ≫ φ k) j) →
      valAt' q (LB.wchart L.L (fun k => h ≫ φ k) j) ((LB.pullGen L.L φ ε t h).s j).val =
        valAt' (q ≫ h) (LB.wchart L.L φ j) (t.s j).val := fun j hp =>
    (vtf_val_res q _ hp _).trans (vtf_val_pullU _ _ _ _)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => by rw [Category.assoc]; exact h1 k, fun j hj => ?_⟩
    exact (hv j ((hc j).2 hj)).symm.trans (h2 j ((hc j).2 hj))
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => by rw [← h1 k, Category.assoc], fun j hj => ?_⟩
    exact (hv j hj).trans (h2 j ((hc j).1 hj))

theorem AnFr.genRd_period {Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L.L φ ε)) (q : Sp ℂ ⟶ Z) (p a : K → Fin g → ℂ) (v : ℂ) (ha : ∀ k, a k ∈ Φ.lat)
    (H : Φ.GenRd φ ε t q p v) :
    Φ.GenRd φ ε t q (fun k => p k + a k) (v * ∏ k, Φ.fac (a k) (p k) ^ ε k) := by
  obtain ⟨h1, h2⟩ := H
  refine ⟨fun k => by rw [Φ.genMove_e_per _ _ (ha k)]; exact h1 k, fun j hj => ?_⟩
  rw [h2 j hj, _root_.mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  have hk := genMove_chart L.L φ q j hj k
  rw [h1 k] at hk
  rw [Φ.fr_per (a k) (ha k) (j k) (p k) hk, mul_zpow]
  rfl

theorem AnFr.genRd_rigPow (k : ℤ) :
    Φ.GenRd (K := PUnit) (fun _ => eSec A) (fun _ => k) (rigPow A L.L L.rig k) x0 (fun _ => 0) 1 := by
  refine ⟨fun _ => Φ.genMove_e_zero_left.symm, fun j hj => ?_⟩
  have hk := genMove_chart L.L (K := PUnit) (fun _ => eSec A) x0 j hj PUnit.unit
  rw [← Φ.genMove_e_zero_left] at hk
  rw [_root_.one_mul, Fintype.prod_unique]
  have e := Φ.fr_0 (j PUnit.unit) hk
  show _ = Φ.fr (j PUnit.unit) 0 ^ k
  rw [e]
  exact vtf_valU x0 hj (L.rig.s j) k

end

theorem genRd_pull_period_rig : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), (∀ (Z' : Scheme.{0}) (h : Z' ⟶ Z) (q : Sp ℂ ⟶ Z') (p : K → Fin g → ℂ) (v : ℂ), Φ.GenRd (fun k => h ≫ φ k) ε (LB.pullGen L.L φ ε t h) q p v ↔ Φ.GenRd φ ε t (q ≫ h) p v) ∧ (∀ (q : Sp ℂ ⟶ Z) (p a : K → Fin g → ℂ) (v : ℂ), (∀ k, a k ∈ Φ.lat) → Φ.GenRd φ ε t q p v → Φ.GenRd φ ε t q (fun k => p k + a k) (v * ∏ k, Φ.fac (a k) (p k) ^ ε k)) ∧ ∀ k : ℤ, Φ.GenRd (K := PUnit) (fun _ => eSec A) (fun _ => k) (rigPow A L.L L.rig k) x0 (fun _ => 0) 1 :=
  fun _ _ _ _ _ _ _ Φ _ _ _ φ ε t =>
    ⟨fun _ h q p v => Φ.genRd_pullGen_iff φ ε t h q p v,
      fun q p a v ha H => Φ.genRd_period φ ε t q p a v ha H, fun k => Φ.genRd_rigPow k⟩

end GlobalTheory.AnVal
