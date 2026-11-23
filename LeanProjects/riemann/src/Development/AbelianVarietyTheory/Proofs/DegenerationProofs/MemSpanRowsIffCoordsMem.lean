import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem mem_span_rows_iff_coords_mem {o Ω J : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Fintype J]
    [DecidableEq J] (A : Subalgebra o Ω) {b : Matrix J J Ω} (hb : b.det ≠ 0) (u : J → Ω) :
    u ∈ Submodule.span A (Set.range b) ↔ ∀ i, Matrix.vecMul u b⁻¹ i ∈ A := by
  have hu : IsUnit b.det := isUnit_iff_ne_zero.2 hb
  have key : ∀ c : J → A, ∑ i, c i • b i = Matrix.vecMul (fun i => (c i : Ω)) b := by
    intro c
    ext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply, Subalgebra.smul_def]
  refine (Submodule.mem_span_range_iff_exists_fun (v := fun i => b i) A).trans ?_
  constructor
  · rintro ⟨c, rfl⟩ i
    rw [key, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]
    exact (c i).2
  · intro h
    refine ⟨fun i => ⟨_, h i⟩, ?_⟩
    rw [key]
    show Matrix.vecMul (Matrix.vecMul u b⁻¹) b = u
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]

theorem RatModel.val_vecMul_eq_sum {o Ω J K : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Fintype J] [Field K]
    {M : RatModel o Ω} {y : Sp K ⟶ M.Z} {z : M.Z} (h : ∀ w, y w ⤳ z) {u : J → Ω} {c : Matrix J J Ω}
    (hu : ∀ j, u j ∈ M.O z) (hc : ∀ j i, c j i ∈ M.O z) (i : J) :
    M.val y (Matrix.vecMul u c i) = ∑ j, M.val y (u j) * M.val y (c j i) := by
  have e := map_sum (RatModel.valHomOf y z h) (fun j => (⟨u j, hu j⟩ * ⟨c j i, hc j i⟩ : M.O z)) Finset.univ
  simp only [map_mul, RatModel.valHomOf_apply] at e
  rw [← e]
  congr 1
  simp [Matrix.vecMul, dotProduct]

theorem sum_mul_mem_of_mem_span {J K : Type} [Fintype J] [Field K] (V : ValuationSubring K) (c : J → K)
    {s : Set (J → K)} (hs : ∀ w ∈ s, ∑ j, w j * c j ∈ V) {w : J → K} (hw : w ∈ Submodule.span V s) :
    ∑ j, w j * c j ∈ V := by
  induction hw using Submodule.span_induction with
  | mem w hw => exact hs w hw
  | zero => simp
  | add w w' _ _ hw hw' =>
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact add_mem hw hw'
  | smul a w _ hw =>
    have : ∑ j, (a • w) j * c j = (a : K) * ∑ j, w j * c j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
    rw [this]
    exact mul_mem a.2 hw

theorem mem_EE_iff_forall_test :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → S.IsEE M U₀ EE → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ v : S.J → Ω, (∀ j, v j ∈ M.ringOn U₀) → (v ∈ EE.E z ↔ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (fun j => M.val (gPt p ≫ y) (v j)) ∈ τ.E) := by
  intro o Ω _ _ _ _ S M U₀ EE hO hloc htest hEE z hz v hv
  refine ⟨fun h p _ y y₀ τ hc hat => ?_, fun h => ?_⟩
  · rw [← hEE.2 z p y y₀ τ hc hat]
    exact Submodule.subset_span ⟨v, h, rfl⟩
  obtain ⟨W, b, hzW, hb, hE⟩ := EE.loc z
  have hstd : ∀ z' ∈ U₀, ∀ u, u ∈ EE.E z' ↔ ∀ j, u j ∈ M.O z' := fun z' hz' u => by
    rw [hEE.1 z' hz']
    exact RatModel.Lat.mem_const_iff M
  have hrow : ∀ z' ∈ W, ∀ u, u ∈ EE.E z' ↔ ∀ i, Matrix.vecMul u b⁻¹ i ∈ M.O z' := fun z' hz' u => by
    rw [hE z' hz']
    exact mem_span_rows_iff_coords_mem _ hb u
  have hinv : ∀ z' ∈ U₀ ⊓ W, ∀ j i, b⁻¹ j i ∈ M.O z' := fun z' hz' j i => by
    have h1 := (hrow z' hz'.2 (Pi.single j 1)).1 ((hstd z' hz'.1 _).2 fun k => by
      rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]) i
    simpa using h1
  rw [hrow z hzW]
  intro i
  refine (hloc.1 (U₀ ⊓ W) inf_le_left (M.nonempty_inf hO.ne ⟨z, hzW⟩) z hz).2 _ ?_ ?_
  · exact RatModel.mem_ringOn.2 fun z' hz' =>
      (hrow z' hz'.2 v).1 ((hstd z' hz'.1 v).2 fun j => RatModel.mem_ringOn.1 (hv j) z' hz'.1) i
  intro p _ y hc
  have hc₀ : M.Cen U₀ z y := ⟨hc.1, fun w hw => (hc.2 hw).1⟩
  obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := htest z p y hc₀
  have hm := h p y y₀ τ hc₀ hat
  rw [← hEE.2 z p y y₀ τ hc₀ hat] at hm
  obtain ⟨ξ, hξU, hsp, hle⟩ : ∃ ξ ∈ U₀ ⊓ W, (∀ w, (gPt p ≫ y) w ⤳ ξ) ∧ M.O z ≤ M.O ξ :=
    ⟨(gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)), hc.2 ⟨_, rfl⟩,
      RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _),
      RatModel.O_le_of_specializes (RatModel.gPt_specializes hc.1 _)⟩
  rw [RatModel.val_vecMul_eq_sum hsp (fun j => RatModel.mem_ringOn.1 (hv j) ξ hξU.1) (hinv ξ hξU), ← mem_OO_iff]
  refine sum_mul_mem_of_mem_span (OO p) _ ?_ hm
  rintro _ ⟨u, huE, rfl⟩
  have h1 := (hrow z hzW u).1 huE
  have h2 : ∀ j, u j ∈ M.O ξ :=
    (hstd ξ hξU.1 u).1 ((hrow ξ hξU.2 u).2 fun k => hle (h1 k))
  have h3 := hc.norm_val_le_one (h1 i)
  rw [RatModel.val_vecMul_eq_sum hsp h2 (hinv ξ hξU)] at h3
  exact (mem_OO_iff _).2 h3

end GlobalTheory.ZH
