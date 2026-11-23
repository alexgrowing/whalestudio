import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace Grp

namespace P_lamMul

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem chk_mul (ψ : kˣ →* ℂˣ) {x y : k} (hx : x ≠ 0) (hy : y ≠ 0) :
    chk ψ (x * y) = chk ψ x * chk ψ y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  unfold chk
  rw [dif_neg hxy, dif_neg hx, dif_neg hy]
  have e : Units.mk0 (x * y) hxy = Units.mk0 x hx * Units.mk0 y hy := Units.ext rfl
  rw [e, map_mul, Units.val_mul]

theorem algebraMap_unit_ne_zero (u : 𝒪[k]ˣ) : algebraMap 𝒪[k] k (u : 𝒪[k]) ≠ 0 :=
  (u.isUnit.map (algebraMap 𝒪[k] k)).ne_zero

theorem chk_unit (ψ : kˣ →* ℂˣ) (u : 𝒪[k]ˣ) :
    chk ψ (algebraMap 𝒪[k] k (u : 𝒪[k])) = ((res ψ u : ℂˣ) : ℂ) := by
  unfold chk
  rw [dif_neg (algebraMap_unit_ne_zero u)]
  have e : Units.mk0 (algebraMap 𝒪[k] k (u : 𝒪[k])) (algebraMap_unit_ne_zero u) = unitIncl k u :=
    Units.ext rfl
  rw [e]
  rfl

variable {n : ℕ} (G : Grp k n)

theorem Δ_ne_zero (hU : ModulusOnUnitsProp G) (hB : CompactConductorBoundProp G) {g : GL (Fin n) k} (hg : g ∈ G.JSet)
    (a : Fin G.s) : G.Δ a g ≠ 0 := by
  obtain ⟨u, hu⟩ := hU hB g hg a
  rw [hu]
  exact algebraMap_unit_ne_zero u

theorem Δ_last (a : Fin G.s) (ha : ¬ (a : ℕ) + 1 < G.s) (g : GL (Fin n) k) :
    G.Δ a g = (g : Matrix (Fin n) (Fin n) k).det := by
  have hall : ∀ i : Fin n, G.bl i ≤ a := by
    intro i
    have := (G.bl i).isLt
    rw [Fin.le_def]
    omega
  unfold Δ
  exact Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv hall) _

theorem factor_mul (hC : CompactConductorBasicProp (k := k)) (hU : ModulusOnUnitsProp G) (hM : ModulusMultiplicativeProp G) (hB : CompactConductorBoundProp G)
    {g h : GL (Fin n) k} (hg : g ∈ G.JSet) (hh : h ∈ G.JSet) (a : Fin G.s) :
    chk (G.μ a / G.μnext a) (G.Δ a (g * h)) =
      chk (G.μ a / G.μnext a) (G.Δ a g) * chk (G.μ a / G.μnext a) (G.Δ a h) := by
  have hgz := Δ_ne_zero G hU hB hg a
  have hhz := Δ_ne_zero G hU hB hh a
  by_cases ha : (a : ℕ) + 1 < G.s
  · obtain ⟨u, hu1, hu⟩ := hM hC hB g hg h hh a ha
    have hn : G.μnext a = G.μ ⟨a + 1, ha⟩ := by unfold μnext; rw [dif_pos ha]
    have hres : ((res (G.μ a / G.μnext a) u : ℂˣ) : ℂ) = 1 := by
      rw [hn, hB.2.2.2 a ⟨a + 1, ha⟩ u hu1, Units.val_one]
    rw [hu, chk_mul _ (mul_ne_zero hgz hhz) (algebraMap_unit_ne_zero u), chk_unit, hres, mul_one,
      chk_mul _ hgz hhz]
  · rw [Δ_last G a ha, Δ_last G a ha, Δ_last G a ha, Units.val_mul, Matrix.det_mul]
    rw [← Δ_last G a ha g, ← Δ_last G a ha h]
    exact chk_mul _ hgz hhz

theorem lam_mul_of (hC : CompactConductorBasicProp (k := k)) (hU : ModulusOnUnitsProp G) (hM : ModulusMultiplicativeProp G) (hB : CompactConductorBoundProp G)
    {g h : GL (Fin n) k} (hg : g ∈ G.JSet) (hh : h ∈ G.JSet) : G.lam (g * h) = G.lam g * G.lam h := by
  unfold lam
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun a _ => factor_mul G hC hU hM hB hg hh a

end P_lamMul

theorem step_lamMul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : LambdaMultiplicativeProp G := by
  intro hC hU hM hB g hg h hh
  exact P_lamMul.lam_mul_of G hC hU hM hB hg hh

end Grp

end UpperTheory.TNZ
