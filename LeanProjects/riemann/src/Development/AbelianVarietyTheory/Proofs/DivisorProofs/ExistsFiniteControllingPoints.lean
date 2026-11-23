import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePointsRegularDivAffineOpenStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem exists_finite_controlling_points : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∃ S : Set X, S.Finite ∧ ∀ (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → ∀ τ g : X.functionField, RegAt x τ → (∀ z ∈ S, z ⤳ x → UnitAt z τ) → RegAt x g → RegAt x (g * τ / P.loc 0 1 s i j) → RegAt x (g / P.loc 0 1 s i j) := by
  intro k _ X _ p D hX P s hs hs0
  have : IsNoetherian X := hX.isNoetherian
  have hloc0 : ∀ (i : P.L.B.ι) (j : P.A.B.ι), P.loc 0 1 s i j = s * (P.r' j : X.functionField) := by
    intro i j; simp [Pair.loc]
  have hloc : ∀ x : X, ∃ (V : X.Opens) (j : P.A.B.ι) (_ : IsAffineOpen V) (hx : x ∈ V) (a : Γ(X, V)),
      V ≤ P.A.B.U j ∧ fnOf V (gen_mem hx) a = s * (P.r' j : X.functionField) := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (P.L.isLB.cover ▸ Opens.mem_top x : x ∈ ⨆ i, P.L.B.U i)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (P.A.isLB.cover ▸ Opens.mem_top x : x ∈ ⨆ j, P.A.B.U j)
    obtain ⟨c, hc⟩ := hs x i j hi hj
    obtain ⟨U, hxU, f, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf c
    obtain ⟨V, hV, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show x ∈ U ⊓ P.A.B.U j from ⟨hxU, hj⟩)
    refine ⟨V, j, hV, hxV, resG X (hVW.trans inf_le_left) f, hVW.trans inf_le_right, ?_⟩
    rw [fnOf_resG, ← algebraMap_germ hxU, hc, hloc0]
  choose V jj hV hxV a hVj ha using hloc
  have hne : ∀ y, fnOf (V y) (gen_mem (hxV y)) (a y) ≠ 0 := by
    intro y; rw [ha]; exact mul_ne_zero hs0 (P.r' (jj y)).ne_zero
  choose T hTfin hT using fun y => GlobalTheory.T.exists_finite_points_regular_div_affineOpen X (V y) (hV y) (gen_mem (hxV y)) (a y) (hne y)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (V y : Set X)) (fun y => (V y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hxV y⟩)
  refine ⟨⋃ y ∈ t, T y, t.finite_toSet.biUnion fun y _ => hTfin y, ?_⟩
  intro x i j hi hj τ g hτ hS hg hgτ
  obtain ⟨y, hyt, hxy⟩ : ∃ y ∈ t, x ∈ V y := by
    have := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at this
    obtain ⟨y, hy, h⟩ := this
    exact ⟨y, hy, h⟩
  have hxj' : x ∈ P.A.B.U j ⊓ P.A.B.U (jj y) := ⟨hj, hVj y hxy⟩
  set w : X.functionField := fnOf _ (gen_mem hxj') (P.A.B.g j (jj y) : Γ(X, P.A.B.U j ⊓ P.A.B.U (jj y))) with hw
  have hwu : UnitAt x w := unitAt_fnOf hxj' _ _
  have hw0 : w ≠ 0 := hwu.ne_zero
  have hrel : P.loc 0 1 s i j = fnOf (V y) (gen_mem (hxV y)) (a y) * w := by
    rw [hloc0, ha, P.hr' j (jj y) (gen_mem hxj')]; ring
  rw [hrel] at hgτ ⊢
  set σ := fnOf (V y) (gen_mem (hxV y)) (a y)
  have h1 : RegAt x (g * τ / σ) := by
    have := hgτ.mul hwu.regAt
    convert this using 1
    field_simp
  have h2 := hT y x hxy τ g hτ (fun z hz hzx => hS z (Set.mem_biUnion hyt hz) hzx) hg h1
  have := h2.mul hwu.inv.regAt
  convert this using 1
  rw [div_mul_eq_div_div, div_eq_mul_inv (g / σ)]

end GlobalTheory.VolBr
