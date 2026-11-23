import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.NVRules

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem unitAt_zpow {x : X} {f : X.functionField} (h : UnitAt x f) (n : ℤ) : UnitAt x (f ^ n) := by
  have hm : Units.mk0 f h.ne_zero ∈ unitsAt x := by
    change UnitAt x ((Units.mk0 f h.ne_zero : X.functionFieldˣ) : X.functionField)
    rwa [Units.val_mk0]
  have := zpow_mem hm n
  change UnitAt x (((Units.mk0 f h.ne_zero ^ n : X.functionFieldˣ)) : X.functionField) at this
  rwa [Units.val_zpow_eq_zpow_val, Units.val_mk0] at this

theorem regAt_pow {x : X} {f : X.functionField} (h : RegAt x f) (n : ℕ) : RegAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (unitAt_one x).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem unitAt_of_pow {x : X} {f : X.functionField} (hf : RegAt x f) {n : ℕ} (hn : 1 ≤ n)
    (h : UnitAt x (f ^ n)) : UnitAt x f := by
  have hne : f ≠ 0 := fun e => h.ne_zero (by rw [e, zero_pow (by omega)])
  refine (unitAt_iff hne).2 ⟨hf, ?_⟩
  have e : f⁻¹ = f ^ (n - 1) * (f ^ n)⁻¹ := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hne), one_mul]
  rw [e]
  exact (regAt_pow hf _).mul h.inv.regAt

theorem unitAt_pow_iff {x : X} {f : X.functionField} (hf : RegAt x f) {n : ℕ} (hn : 1 ≤ n) :
    UnitAt x (f ^ n) ↔ UnitAt x f :=
  ⟨unitAt_of_pow hf hn, fun h => by simpa using unitAt_zpow h (n : ℤ)⟩

theorem unitAt_ratio {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {x : X} {i j : L.ι}
    (hi : x ∈ L.U i) (hj : x ∈ L.U j) : UnitAt x ((r i : X.functionField) / r j) := by
  have h := gen_mem (memInf hi hj)
  rw [hr i j h, mul_div_cancel_right₀ _ (Units.ne_zero _)]
  exact unitAt_fnOf (memInf hi hj) h (L.g i j)

theorem loc_eq_mul (P : Pair p) (a b : ℤ) (f : X.functionField) (i i' : P.L.B.ι) (j j' : P.A.B.ι) :
    P.loc a b f i j = P.loc a b f i' j' *
      (((P.r i : X.functionField) / P.r i') ^ a * ((P.r' j : X.functionField) / P.r' j') ^ b) := by
  have h1 : ((P.r i' : X.functionField)) ^ a ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  have h2 : ((P.r' j' : X.functionField)) ^ b ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  simp only [Pair.loc, div_zpow]
  field_simp

theorem unitAt_loc_of (P : Pair p) (a b : ℤ) (f : X.functionField) {x : X} {i i' : P.L.B.ι} {j j' : P.A.B.ι}
    (hi : x ∈ P.L.B.U i) (hi' : x ∈ P.L.B.U i') (hj : x ∈ P.A.B.U j) (hj' : x ∈ P.A.B.U j')
    (h : UnitAt x (P.loc a b f i' j')) : UnitAt x (P.loc a b f i j) := by
  rw [loc_eq_mul P a b f i i' j j']
  exact h.mul ((unitAt_zpow (unitAt_ratio P.hr hi hi') a).mul (unitAt_zpow (unitAt_ratio P.hr' hj hj') b))

theorem mem_NV_iff (P : Pair p) (a b : ℤ) (f : X.functionField) {x : X} {i : P.L.B.ι} {j : P.A.B.ι}
    (hi : x ∈ P.L.B.U i) (hj : x ∈ P.A.B.U j) : x ∈ NV P a b f ↔ UnitAt x (P.loc a b f i j) :=
  ⟨fun h => h i j hi hj, fun h _ _ hi' hj' => unitAt_loc_of P a b f hi' hi hj' hj h⟩

theorem div_eq_loc_div (P : Pair p) (a b : ℤ) (f g : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    f / g = P.loc a b f i j / P.loc a b g i j := by
  have h1 : ((P.r i : X.functionField)) ^ a ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  have h2 : ((P.r' j : X.functionField)) ^ b ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  simp only [Pair.loc]
  rw [mul_assoc f, mul_assoc g, mul_div_mul_right _ _ (mul_ne_zero h1 h2)]

theorem loc_pow (P : Pair p) (a b : ℤ) (g : X.functionField) (n : ℕ) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc (n * a) (n * b) (g ^ n) i j = P.loc a b g i j ^ n := by
  simp only [Pair.loc, mul_pow]
  rw [mul_comm (n : ℤ) a, mul_comm (n : ℤ) b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]

end GlobalTheory.HSAmp.NVRules

open GlobalTheory.HSAmp.NVRules in

theorem GlobalTheory.HSAmp.nv_rules : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (g : X.functionField), g ∈ P.H a b → IsOpen (NV P a b g) ∧ (genericPoint X ∈ NV P a b g ↔ g ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → NV P (n * a) (n * b) (g ^ n) = NV P a b g) ∧ (∀ f ∈ P.H a b, ∀ z ∈ NV P a b g, RegAt z (f / g) ∧ (z ∈ NV P a b f ↔ UnitAt z (f / g))) ∧ ∀ f ∈ P.H a b, ∀ (σ : k →+* ℂ) (y : CxPts p σ), under y ∈ NV P a b g → P.nu a b σ y f = ‖ratVal (f / g) y‖ * P.nu a b σ y g ∧ 0 < P.nu a b σ y g := by
  intro k _ X _ p P a b g hg
  have cL := fun x : X => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart P.L.isLB x
  have cA := fun x : X => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart P.A.isLB x
  have h4 : ∀ f ∈ P.H a b, ∀ z ∈ NV P a b g, RegAt z (f / g) ∧ (z ∈ NV P a b f ↔ UnitAt z (f / g)) := by
    intro f hf z hz
    obtain ⟨i, hi⟩ := cL z
    obtain ⟨j, hj⟩ := cA z
    have hu := (mem_NV_iff P a b g hi hj).1 hz
    rw [div_eq_loc_div P a b f g i j, mem_NV_iff P a b f hi hj]
    refine ⟨(hf z i j hi hj).mul hu.inv.regAt, fun h => h.mul hu.inv, fun h => ?_⟩
    have := h.mul hu
    rwa [div_mul_cancel₀ _ hu.ne_zero] at this
  refine ⟨?_, ?_, ?_, h4, ?_⟩
  · refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
    obtain ⟨i, hi⟩ := cL x
    obtain ⟨j, hj⟩ := cA x
    obtain ⟨V, hV, hVu⟩ := ((mem_NV_iff P a b g hi hj).1 hx).exists_nhds
    refine ⟨((V ⊓ P.L.B.U i ⊓ P.A.B.U j : X.Opens) : Set X), fun y hy => ?_, Opens.isOpen _, ⟨⟨hV, hi⟩, hj⟩⟩
    obtain ⟨⟨hyV, hyi⟩, hyj⟩ := hy
    exact (mem_NV_iff P a b g hyi hyj).2 (hVu y hyV)
  · obtain ⟨i, hi⟩ := cL (genericPoint X)
    obtain ⟨j, hj⟩ := cA (genericPoint X)
    rw [mem_NV_iff P a b g hi hj]
    refine ⟨fun h e => h.ne_zero (by rw [e]; simp [Pair.loc]), fun h => unitAt_genericPoint ?_⟩
    simp only [Pair.loc]
    exact mul_ne_zero (mul_ne_zero h (zpow_ne_zero _ (Units.ne_zero _))) (zpow_ne_zero _ (Units.ne_zero _))
  · intro n hn
    ext x
    obtain ⟨i, hi⟩ := cL x
    obtain ⟨j, hj⟩ := cA x
    rw [mem_NV_iff P _ _ _ hi hj, mem_NV_iff P a b g hi hj, loc_pow]
    exact unitAt_pow_iff (hg x i j hi hj) hn
  · intro f hf σ y hy
    have hi := mem_ptsIn.1 (mem_pick (P.L.φ σ).isLB y)
    have hj := mem_ptsIn.1 (mem_pick (P.A.φ σ).isLB y)
    have hu := (mem_NV_iff P a b g hi hj).1 hy
    have hq := (h4 f hf _ hy).1
    have e : P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) =
        f / g * P.loc a b g (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) := by
      rw [div_eq_loc_div P a b f g (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y), div_mul_cancel₀ _ hu.ne_zero]
    refine ⟨?_, ?_⟩
    · rw [Pair.nu, Pair.nu, e, ratVal_mul hq hu.regAt, norm_mul, mul_assoc]
    · rw [Pair.nu]
      exact mul_pos (norm_pos_iff.2 (ratVal_ne_zero hu)) (Real.exp_pos _)
