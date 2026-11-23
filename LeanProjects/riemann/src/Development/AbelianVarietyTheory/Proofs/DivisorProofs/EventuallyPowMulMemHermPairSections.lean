import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.ExtPow

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem compactSpace_of_projOver {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace Y := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem unitAt_zpow {z : X} {u : X.functionField} (h : UnitAt z u) (n : ℤ) : UnitAt z (u ^ n) := by
  have hu : u ≠ 0 := h.ne_zero
  induction n using Int.induction_on with
  | zero => rw [zpow_zero]; exact unitAt_one z
  | succ n ih => rw [zpow_add_one₀ hu]; exact ih.mul h
  | pred n ih => rw [zpow_sub_one₀ hu]; exact ih.mul h.inv

theorem loc_change (P : Pair p) (a b : ℤ) (f : X.functionField) (i i' : P.L.B.ι) (j j' : P.A.B.ι) :
    P.loc a b f i' j' = P.loc a b f i j *
      (((P.r i' : X.functionField) / P.r i) ^ a * ((P.r' j' : X.functionField) / P.r' j) ^ b) := by
  have h1 : (P.r i : X.functionField) ^ a ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  have h2 : (P.r' j : X.functionField) ^ b ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  simp only [Pair.loc, div_zpow]
  field_simp

theorem unitAt_quot (P : Pair p) (a b : ℤ) {z : X} {i i' : P.L.B.ι} {j j' : P.A.B.ι}
    (hi : z ∈ P.L.B.U i) (hi' : z ∈ P.L.B.U i') (hj : z ∈ P.A.B.U j) (hj' : z ∈ P.A.B.U j') :
    UnitAt z (((P.r i' : X.functionField) / P.r i) ^ a * ((P.r' j' : X.functionField) / P.r' j) ^ b) :=
  (unitAt_zpow (germOf_eq_iff.1 (P.hr.germOf_eq hi' hi)) a).mul
    (unitAt_zpow (germOf_eq_iff.1 (P.hr'.germOf_eq hj' hj)) b)

theorem loc_pow_mul (P : Pair p) (e a b : ℤ) (c : ℕ) (x f : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc (e * c + a) b (x ^ c * f) i j = P.loc e 0 x i j ^ c * P.loc a b f i j := by
  have h0 : (P.r i : X.functionField) ≠ 0 := Units.ne_zero _
  simp only [Pair.loc, zpow_zero, mul_one, zpow_add₀ h0, zpow_mul, zpow_natCast, mul_pow]
  ring

theorem exists_pow_mul_regAt {W : X.Opens} (hW : IsAffineOpen W) (s : Γ(X, W)) (hg : genericPoint X ∈ X.basicOpen s)
    {g : X.functionField} (h : ∀ z ∈ X.basicOpen s, RegAt z g) :
    ∃ N : ℕ, ∀ z ∈ W, RegAt z (fnOf W (X.basicOpen_le s hg) s ^ N * g) := by
  obtain ⟨a, ha⟩ := exists_fnOf_eq hg h
  have := hW.isLocalization_basicOpen s
  obtain ⟨⟨b, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) a
  obtain ⟨N, hN⟩ := m.2
  refine ⟨N, fun z hz => ?_⟩
  have e := congrArg (fnOf _ hg) hm
  simp only [map_mul] at e
  change fnOf _ hg a * fnOf _ hg (resG X (X.basicOpen_le s) (m : Γ(X, W))) =
    fnOf _ hg (resG X (X.basicOpen_le s) b) at e
  rw [fnOf_resG, fnOf_resG, ha, ← hN, map_pow] at e
  rw [mul_comm, e]
  exact regAt_fnOf hz _ b

end GlobalTheory.HSAmp.ExtPow

open GlobalTheory.HSAmp.ExtPow in

theorem GlobalTheory.HSAmp.eventually_pow_mul_mem_H : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e a b : ℤ) (x f : X.functionField), x ∈ P.H e 0 → x ≠ 0 → (∀ z ∈ NV P e 0 x, ∀ i j, z ∈ P.L.B.U i → z ∈ P.A.B.U j → RegAt z (P.loc a b f i j)) → ∀ᶠ c : ℕ in atTop, x ^ c * f ∈ P.H (e * c + a) b := by
  intro k _ X _ p D hD P e a b x f hx hx0 hf
  haveI : CompactSpace X := compactSpace_of_projOver hD.isProjOver
  have loc_ok : ∀ z : X, ∃ W : X.Opens, z ∈ W ∧ ∃ N : ℕ, ∀ c : ℕ, N ≤ c → ∀ w ∈ W, ∀ i j, w ∈ P.L.B.U i →
      w ∈ P.A.B.U j → RegAt w (P.loc (e * c + a) b (x ^ c * f) i j) := by
    intro z
    obtain ⟨i, hi⟩ := exists_chart P.L.isLB z
    obtain ⟨j, hj⟩ := exists_chart P.A.isLB z
    obtain ⟨W, hW, hzW, hWle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show z ∈ P.L.B.U i ⊓ P.A.B.U j from ⟨hi, hj⟩)
    have hgW : genericPoint X ∈ W := gen_mem hzW
    have hsW : ∀ w ∈ W, RegAt w (P.loc e 0 x i j) := fun w hw => hx w i j (hWle hw).1 (hWle hw).2
    obtain ⟨s, hs⟩ := exists_fnOf_eq hgW hsW
    have hbas : ∀ w ∈ X.basicOpen s, w ∈ NV P e 0 x := by
      intro w hw i' j' hi' hj'
      have hwW := X.basicOpen_le s hw
      have hu : UnitAt w (P.loc e 0 x i j) := hs ▸ (unitAt_fnOf_iff hwW hgW s).2 hw
      rw [loc_change P e 0 x i i' j j']
      exact hu.mul (unitAt_quot P e 0 (hWle hwW).1 hi' (hWle hwW).2 hj')
    have hne : P.loc e 0 x i j ≠ 0 :=
      mul_ne_zero (mul_ne_zero hx0 (zpow_ne_zero _ (Units.ne_zero _))) (zpow_ne_zero _ (Units.ne_zero _))
    have hg0 : genericPoint X ∈ X.basicOpen s := by
      have hu : UnitAt (genericPoint X) (fnOf W hgW s) := by rw [hs]; exact unitAt_genericPoint hne
      exact (unitAt_fnOf_iff hgW hgW s).1 hu
    obtain ⟨N, hN⟩ := exists_pow_mul_regAt hW s hg0 (g := P.loc a b f i j) fun w hw =>
      hf w (hbas w hw) i j (hWle (X.basicOpen_le s hw)).1 (hWle (X.basicOpen_le s hw)).2
    refine ⟨W, hzW, N, fun c hc w hw i' j' hi' hj' => ?_⟩
    rw [loc_change P (e * c + a) b (x ^ c * f) i i' j j', loc_pow_mul, ← hs]
    refine RegAt.mul ?_ (unitAt_quot P _ b (hWle hw).1 hi' (hWle hw).2 hj').regAt
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
    have hd := regAt_fnOf hw hgW (s ^ d)
    rw [map_pow] at hd
    rw [pow_add, mul_comm (_ ^ N) (_ ^ d), mul_assoc]
    exact hd.mul (hN w hw)
  choose W hzW N hN using loc_ok
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun z => (W z : Set X)) (fun z => (W z).isOpen)
    (fun z _ => Set.mem_iUnion.2 ⟨z, hzW z⟩)
  refine eventually_atTop.2 ⟨t.sup N, fun c hc w i j hi hj => ?_⟩
  obtain ⟨z, hz, hwz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ w))
  exact hN z c ((Finset.le_sup hz).trans hc) w hwz i j hi hj
