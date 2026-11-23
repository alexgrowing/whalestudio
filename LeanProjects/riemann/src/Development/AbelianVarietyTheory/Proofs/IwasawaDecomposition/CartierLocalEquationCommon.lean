import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.Cartier.CommonEqn

variable {X : Scheme.{0}} [IsIntegral X]

theorem generatesAt_add {D : CartierDiv X} {x : X} {f f' : X.functionField}
    (h : D.GeneratesAt x f) (h' : D.VanishesAt x f') : D.GeneratesAt x (f + f') := by
  obtain ⟨g, hg, a, ha, e⟩ := h
  obtain ⟨b, hb, e'⟩ := hg.vanishesAt_iff.1 h'
  refine ⟨g, hg, a + b, ?_, by rw [map_add, e, e', add_mul]⟩
  by_contra hu
  have : a + b ∈ IsLocalRing.maximalIdeal _ := hu
  exact (show a ∈ IsLocalRing.maximalIdeal _ from by simpa using sub_mem this hb) ha

theorem exists_pow_mul_eq [IsAffine X] (t : Γ(X, ⊤)) (ht : genericPoint X ∈ X.basicOpen t)
    {f : X.functionField} (h : ∀ x ∈ X.basicOpen t, RegAt x f) :
    ∃ (n : ℕ) (a : Γ(X, ⊤)), fnOf ⊤ trivial t ^ n * f = fnOf ⊤ trivial a := by
  obtain ⟨b, rfl⟩ := exists_fnOf_eq ht h
  have := (isAffineOpen_top X).isLocalization_basicOpen t
  obtain ⟨n, a, e⟩ := IsLocalization.Away.surj t b
  refine ⟨n, a, ?_⟩
  have e' := congrArg (fnOf _ ht) e
  rw [map_mul, map_pow] at e'
  have k (c : Γ(X, ⊤)) : fnOf _ ht (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen t) c) =
      fnOf ⊤ trivial c := fnOf_resG le_top ht c
  rw [k, k] at e'
  rw [← e', mul_comm]

theorem exists_regularAt [IsAffine X] {D : CartierDiv X} {x : X} {g : X.functionFieldˣ}
    (hg : D.IsEqn x g) (y : X) : ∃ s : Γ(X, ⊤), x ∈ X.basicOpen s ∧
      D.RegularAt y (fnOf ⊤ trivial s * (g : X.functionField)⁻¹) := by
  obtain ⟨U, hU, hgU⟩ := hg.exists_nhds
  obtain ⟨V, hV, g', hgV⟩ := D.exists_isEqn_nhds y
  obtain ⟨t, htU, ht⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨x, hU⟩ trivial
  obtain ⟨t', htV, ht'⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨y, hV⟩ trivial
  have hgen : genericPoint X ∈ X.basicOpen (t * t') := by
    rw [X.basicOpen_mul]; exact ⟨gen_mem ht, gen_mem ht'⟩
  obtain ⟨n, a, e⟩ := exists_pow_mul_eq (t * t') hgen
    (f := (g' : X.functionField) / g) fun z hz => by
      rw [X.basicOpen_mul] at hz
      exact ((hgU z (htU hz.1)).iff_unitAt.1 (hgV z (htV hz.2))).regAt
  have hu : UnitAt y (fnOf ⊤ trivial (t' ^ n)) := by
    refine (unitAt_fnOf_iff (U := ⊤) trivial _ _).2 ?_
    rw [X.mem_basicOpen_top, map_pow]
    exact ((X.mem_basicOpen_top _ _).1 ht').pow n
  refine ⟨t ^ n, ?_, g', hgV y hV, ?_⟩
  · rw [X.mem_basicOpen_top, map_pow]
    exact ((X.mem_basicOpen_top _ _).1 ht).pow n
  · have := (regAt_fnOf (U := ⊤) (x := y) trivial trivial a).mul hu.inv.regAt
    rw [← e] at this
    convert this using 1
    have h0 := hu.ne_zero
    rw [map_pow] at h0
    rw [map_mul, map_pow, map_pow, mul_pow]
    field_simp

theorem exists_vanishesAt [IsAffine X] {D : CartierDiv X} {x : X} {g : X.functionFieldˣ}
    (hg : D.IsEqn x g) {y : X} (hy : IsClosed ({y} : Set X)) (hxy : y ≠ x) :
    ∃ s : Γ(X, ⊤), x ∈ X.basicOpen s ∧
      D.VanishesAt y (fnOf ⊤ trivial s * (g : X.functionField)⁻¹) := by
  obtain ⟨s, hs, hreg⟩ := exists_regularAt hg y
  obtain ⟨t, htU, ht⟩ := (isAffineOpen_top X).exists_basicOpen_le
    (V := ⟨{y}ᶜ, hy.isOpen_compl⟩) ⟨x, hxy.symm⟩ trivial
  have hz : ZeroAt y (fnOf ⊤ trivial t) := zeroAt_iff.2 ⟨regAt_fnOf (U := ⊤) trivial _ _,
    fun h => htU ((unitAt_fnOf_iff (U := ⊤) trivial _ _).1 h) rfl⟩
  refine ⟨t * s, by rw [X.basicOpen_mul]; exact ⟨ht, hs⟩, ?_⟩
  obtain ⟨g', hg', hr⟩ := hreg
  refine ⟨g', hg', ?_⟩
  rw [map_mul, mul_assoc, mul_assoc, ← mul_assoc (fnOf ⊤ trivial s)]
  exact hz.mul hr

theorem exists_generatesAt_vanishesAt [IsAffine X] (D : CartierDiv X) (x : X) (T : Finset X)
    (hT : ∀ y ∈ T, IsClosed ({y} : Set X)) :
    ∃ f, D.GeneratesAt x f ∧ ∀ y ∈ T, y ≠ x → D.VanishesAt y f := by
  classical
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  suffices ∃ s : Γ(X, ⊤), x ∈ X.basicOpen s ∧ ∀ y ∈ T, y ≠ x →
      D.VanishesAt y (fnOf ⊤ trivial s * (g : X.functionField)⁻¹) by
    obtain ⟨s, hs, h⟩ := this
    refine ⟨_, ⟨g, hg, ?_⟩, h⟩
    rw [mul_assoc, inv_mul_cancel₀ g.ne_zero, mul_one]
    exact (unitAt_fnOf_iff (U := ⊤) trivial _ _).2 hs
  have key (y : X) (s t : Γ(X, ⊤))
      (h : D.VanishesAt y (fnOf ⊤ trivial s * (g : X.functionField)⁻¹)) :
      D.VanishesAt y (fnOf ⊤ trivial (s * t) * (g : X.functionField)⁻¹) := by
    obtain ⟨g', hg', hr⟩ := h
    refine ⟨g', hg', ?_⟩
    have := hr.mul (regAt_fnOf (U := ⊤) (x := y) trivial trivial t)
    convert this using 1
    rw [map_mul]; ring
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert y T _ ih =>
    obtain ⟨s, hs, h⟩ := ih fun z hz => hT z (Finset.mem_insert_of_mem hz)
    by_cases hyx : y = x
    · refine ⟨s, hs, fun z hz hzx => ?_⟩
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact (hzx hyx).elim
      · exact h z hz hzx
    obtain ⟨t, ht, h'⟩ := exists_vanishesAt hg (hT y (Finset.mem_insert_self _ _)) hyx
    refine ⟨s * t, by rw [X.basicOpen_mul]; exact ⟨hs, ht⟩, fun z hz hzx => ?_⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · rw [mul_comm s]; exact key _ _ _ h'
    · exact key _ _ _ (h z hz hzx)

theorem exists_generatesAt [IsAffine X] (D : CartierDiv X) (T : Finset X)
    (hT : ∀ y ∈ T, IsClosed ({y} : Set X)) : ∃ f, ∀ x ∈ T, D.GeneratesAt x f := by
  classical
  choose F hF hF' using fun x => exists_generatesAt_vanishesAt D x T hT
  refine ⟨∑ x ∈ T, F x, fun x hx => ?_⟩
  rw [← Finset.add_sum_erase T F hx]
  refine generatesAt_add (hF x) (Finset.sum_induction _ (D.VanishesAt x) (fun _ _ h h' => h.add h')
    (D.vanishesAt_zero x) fun y hy => hF' y x hx (Finset.ne_of_mem_erase hy).symm)

theorem exists_isEqn_of_finite [IsAffine X] (D : CartierDiv X) (S : Set X) (hS : S.Finite) :
    ∃ g : X.functionFieldˣ, ∀ z ∈ S, D.IsEqn z g := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact ⟨1, by simp⟩
  have hc (z : X) : ∃ c : X, c ∈ closure ({z} : Set X) ∧ IsClosed ({c} : Set X) :=
    isClosed_closure.exists_closed_singleton ⟨z, subset_closure rfl⟩
  choose c hc hc' using hc
  obtain ⟨f, hf⟩ := exists_generatesAt D (hS.toFinset.image c) fun y hy => by
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hy
    exact hc' z
  have hf' (z : X) (hz : z ∈ S) : D.GeneratesAt (c z) f :=
    hf _ (Finset.mem_image_of_mem c (hS.mem_toFinset.2 hz))
  have h0 := (hf' z₀ hz₀).ne_zero
  refine ⟨(Units.mk0 f h0)⁻¹, fun z hz => ?_⟩
  have h1 : D.IsEqn (c z) (Units.mk0 f h0)⁻¹ :=
    CartierDiv.isEqn_iff_generatesAt_inv.2 (by simpa using hf' z hz)
  obtain ⟨U, hU, h⟩ := h1.exists_nhds
  exact h z ((specializes_iff_mem_closure.2 (hc z)).mem_open U.isOpen hU)

theorem exists_isEqn_curve : ∀ (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] [IsAffine Z], topologicalKrullDim Z ≤ 1 → ∀ (D : CartierDiv Z) (S : Set Z), S.Finite → ∃ g : Z.functionFieldˣ, ∀ z ∈ S, D.IsEqn z g :=
  fun _ _ _ _ _ D S hS => exists_isEqn_of_finite D S hS

end GlobalTheory.Cartier.CommonEqn
