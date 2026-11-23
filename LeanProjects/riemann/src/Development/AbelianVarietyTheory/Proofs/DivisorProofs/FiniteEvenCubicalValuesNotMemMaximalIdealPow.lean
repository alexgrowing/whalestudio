import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSublevelOfIntQuadraticGeOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeightOneValuationsControlSubgroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.QuadTend

theorem dickson_fin {J : Type*} (n : ℕ) (f : J → Fin n → ℕ) :
    ∃ F : Finset J, ∀ i, ∃ j ∈ F, f j ≤ f i := by
  classical
  set s : Set (Fin n → ℕ) := Set.range f
  have hpwo : s.IsPWO := Set.isPWO_of_wellQuasiOrderedLE s
  set m : Set (Fin n → ℕ) := {x | Minimal (· ∈ s) x}
  have hm : m.Finite := (setOf_minimal_antichain (· ∈ s)).finite_of_partiallyWellOrderedOn
    (hpwo.mono (fun x hx => hx.prop))
  have hpre : ∀ x ∈ m, ∃ j, f j = x := fun x hx => hx.prop
  rcases isEmpty_or_nonempty J with hJ | hJ
  · exact ⟨∅, fun i => isEmptyElim i⟩
  choose! g hg using hpre
  refine ⟨hm.toFinset.image g, fun i => ?_⟩
  obtain ⟨x, hxi, hx⟩ := hpwo.exists_le_minimal (Set.mem_range_self i)
  exact ⟨g x, Finset.mem_image_of_mem g (hm.mem_toFinset.mpr hx), by rw [hg x hx]; exact hxi⟩

section Cl

variable {G X : Type*} [CommGroup G] [AddCommGroup X] (κ : X → G)

def defect (a b : X) : G := κ (a + b) / (κ a * κ b)

variable {κ}

theorem kappa_zero (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) :
    κ 0 = 1 := by
  have h := hc 0 0 0
  simp only [add_zero] at h
  have h2 : κ 0 * (κ 0 * κ 0 * κ 0) = 1 * (κ 0 * κ 0 * κ 0) := by
    rw [_root_.one_mul]; simpa only [_root_.mul_assoc] using h
  exact mul_right_cancel h2

theorem defect_add_left (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b))
    (a a' b : X) : defect κ (a + a') b = defect κ a b * defect κ a' b := by
  unfold defect
  rw [div_mul_div_comm, div_eq_div_iff_mul_eq_mul]
  have h := hc a a' b
  calc κ (a + a' + b) * (κ a * κ b * (κ a' * κ b)) = (κ (a + a' + b) * κ a * κ a' * κ b) * κ b := by
        simp only [mul_comm, _root_.mul_assoc, _root_.mul_left_comm]
    _ = (κ (a + a') * κ (a + b) * κ (a' + b)) * κ b := by rw [h]
    _ = κ (a + b) * κ (a' + b) * (κ (a + a') * κ b) := by simp only [mul_comm, _root_.mul_assoc, _root_.mul_left_comm]

theorem defect_comm (a b : X) : defect κ a b = defect κ b a := by
  unfold defect; rw [add_comm, _root_.mul_comm]

theorem defect_zero_left (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b))
    (b : X) : defect κ 0 b = 1 := by
  have h := defect_add_left hc 0 0 b
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem defect_neg_left (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b))
    (a b : X) : defect κ (-a) b = (defect κ a b)⁻¹ := by
  have h := defect_add_left hc a (-a) b
  rw [add_neg_cancel, defect_zero_left hc] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem kappa_add (a b : X) : κ (a + b) = κ a * κ b * defect κ a b := by
  unfold defect; rw [mul_div_cancel]

theorem mem_closure_of_gen (hn : ∀ a, κ (-a) = κ a)
    (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b))
    {J : Type*} (e : J → X) (he : AddSubgroup.closure (Set.range e) = ⊤) (a : X) :
    κ a ∈ Subgroup.closure (Set.range (Sum.elim (fun i => κ (e i)) (fun p : J × J => κ (e p.1 + e p.2)))) := by
  set H := Subgroup.closure (Set.range (Sum.elim (fun i => κ (e i)) (fun p : J × J => κ (e p.1 + e p.2))))
  have hk : ∀ i, κ (e i) ∈ H := fun i => Subgroup.subset_closure ⟨Sum.inl i, rfl⟩
  have hg : ∀ i j, defect κ (e i) (e j) ∈ H := fun i j =>
    H.div_mem (Subgroup.subset_closure ⟨Sum.inr (i, j), rfl⟩) (H.mul_mem (hk i) (hk j))
  have mem : ∀ x : X, x ∈ AddSubgroup.closure (Set.range e) := fun x => he ▸ AddSubgroup.mem_top x
  have step1 : ∀ i b, defect κ (e i) b ∈ H := by
    intro i b
    induction mem b using AddSubgroup.closure_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hg i j
    | zero => rw [defect_comm, defect_zero_left hc]; exact H.one_mem
    | add x y _ _ hx hy =>
      rw [defect_comm, defect_add_left hc, defect_comm x, defect_comm y]; exact H.mul_mem hx hy
    | neg x _ hx => rw [defect_comm, defect_neg_left hc, defect_comm]; exact H.inv_mem hx
  have step2 : ∀ a b, defect κ a b ∈ H := by
    intro a b
    induction mem a using AddSubgroup.closure_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact step1 j b
    | zero => rw [defect_zero_left hc]; exact H.one_mem
    | add x y _ _ hx hy => rw [defect_add_left hc]; exact H.mul_mem hx hy
    | neg x _ hx => rw [defect_neg_left hc]; exact H.inv_mem hx
  induction mem a using AddSubgroup.closure_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hk j
  | zero => rw [kappa_zero hc]; exact H.one_mem
  | add x y _ _ hx hy => rw [kappa_add (κ := κ)]; exact H.mul_mem (H.mul_mem hx hy) (step2 x y)
  | neg x _ hx => rw [hn]; exact hx

end Cl

theorem finite_not_mem_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (κ : X → (FractionRing R)ˣ), (∀ a, κ (-a) = κ a) → (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) → (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R _ s) → ∀ n : ℕ, {a | ¬ ∃ s ∈ maximalIdeal R ^ n, (κ a : FractionRing R) = algebraMap R _ s}.Finite := by
  intro R _ _ _ _ _ X _ _ κ hneg hcube hm n
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top (R := ℤ) (M := X))
  have hcl : AddSubgroup.closure (Set.range (fun x : S => (x : X))) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, Subtype.range_coe_subtype, Finset.setOf_mem, hS]; rfl
  have hΓ := mem_closure_of_gen hneg hcube (fun x : S => (x : X)) hcl
  set gg := Sum.elim (fun i : S => κ (i : X)) (fun p : S × S => κ ((p.1 : X) + p.2))
  set Γ := Subgroup.closure (Set.range gg)
  obtain ⟨s, v, hv1, hv2⟩ := GlobalTheory.T.exists_heightOne_valuations_control_subgroup R (S ⊕ (S × S)) gg
  set K := FractionRing R
  let w : Kˣ → Fin s → ℤ := fun x i => Multiplicative.toAdd (v i x)
  have wmul : ∀ x y i, w (x * y) i = w x i + w y i := fun x y i => by simp [w]
  have winv : ∀ x i, w x⁻¹ i = - w x i := fun x i => by simp [w]
  have wone : ∀ i, w 1 i = 0 := fun i => by simp [w]
  have hk0 := kappa_zero hcube
  have wκ : ∀ a i, 0 ≤ w (κ a) i := by
    intro a i
    by_cases ha : a = 0
    · rw [ha, hk0, wone]
    · obtain ⟨t, -, ht⟩ := hm a ha
      exact hv1 i (κ a) t ht

  have unitOf : ∀ x ∈ Γ, (∀ i, w x i = 0) → ∃ r : R, IsUnit r ∧ (x : K) = algebraMap R K r := by
    intro x hx h0
    obtain ⟨r, hr⟩ := hv2 x hx (fun i => (h0 i).ge)
    obtain ⟨r', hr'⟩ := hv2 x⁻¹ (Γ.inv_mem hx) (fun i => show 0 ≤ w x⁻¹ i by rw [winv, h0 i, neg_zero])
    have hrr : r * r' = 1 := IsFractionRing.injective R K (by
      rw [map_mul, ← hr, ← hr', map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
    exact ⟨r, ⟨Units.mkOfMulEqOne r r' hrr, rfl⟩, hr⟩
  let q : X → ℤ := fun a => ∑ i, w (κ a) i
  have hqneg : ∀ a, q (-a) = q a := fun a => by simp only [q, hneg]
  have hqcube : ∀ a a' b, q (a + a' + b) + q a + q a' + q b = q (a + a') + q (a + b) + q (a' + b) := by
    intro a a' b
    have h := congrArg (fun x => ∑ i, w x i) (hcube a a' b)
    simp only [wmul, Finset.sum_add_distrib] at h
    simpa only [q] using h
  have hqpos : ∀ a, a ≠ 0 → 1 ≤ q a := by
    intro a ha
    obtain ⟨t, htm, ht⟩ := hm a ha
    by_contra hlt
    have hsum0 : q a = 0 := le_antisymm (by omega) (Finset.sum_nonneg fun i _ => wκ a i)
    have hall : ∀ i, w (κ a) i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => wκ a i)).mp hsum0 i (Finset.mem_univ i)
    obtain ⟨r, hru, hr⟩ := unitOf (κ a) (hΓ a) hall
    have : t = r := IsFractionRing.injective R K (ht.symm.trans hr)
    exact (IsLocalRing.mem_maximalIdeal t).mp htm (this ▸ hru)

  let P := {x : Kˣ // x ∈ Γ ∧ (∀ i, 0 ≤ w x i) ∧ 0 < ∑ i, w x i}
  obtain ⟨F, hF⟩ := dickson_fin s (fun x : P => fun i => (w x.1 i).toNat)
  set C : ℤ := 1 + ∑ j ∈ F, ∑ i, w j.1 i
  have hC : ∀ j ∈ F, ∑ i, w j.1 i + 1 ≤ C := by
    intro j hj
    have := Finset.single_le_sum (f := fun j : P => ∑ i, w j.1 i)
      (fun j _ => Finset.sum_nonneg fun i _ => j.2.2.1 i) hj
    omega
  have hC1 : 1 ≤ C := by
    have := Finset.sum_nonneg (s := F) (f := fun j : P => ∑ i, w j.1 i) (fun j _ => Finset.sum_nonneg fun i _ => j.2.2.1 i)
    simp only [C]; omega
  have hPm : ∀ j : P, ∃ t ∈ maximalIdeal R, (j.1 : K) = algebraMap R K t := by
    intro j
    obtain ⟨t, ht⟩ := hv2 j.1 j.2.1 j.2.2.1
    refine ⟨t, ?_, ht⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨u, rfl⟩ := hu
    have hinv : ((j.1⁻¹ : Kˣ) : K) = algebraMap R K (u⁻¹ : Rˣ) := by
      rw [Units.val_inv_eq_inv_val, ht]; symm; apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, Units.inv_mul, map_one]
    have hle : ∀ i, w j.1 i ≤ 0 := fun i => by
      have := hv1 i j.1⁻¹ _ hinv
      have h2 := winv j.1 i
      simp only [w] at h2 ⊢; omega
    have := j.2.2.2
    have := Finset.sum_nonpos (s := Finset.univ) (fun i _ => hle i)
    omega
  have key : ∀ k : ℕ, ∀ x ∈ Γ, (∀ i, 0 ≤ w x i) → C * k ≤ ∑ i, w x i →
      ∃ t ∈ maximalIdeal R ^ k, (x : K) = algebraMap R K t := by
    intro k
    induction k with
    | zero =>
      intro x hx h0 _
      obtain ⟨t, ht⟩ := hv2 x hx h0
      exact ⟨t, by simp, ht⟩
    | succ k ih =>
      intro x hx h0 hsum
      have hpos : 0 < ∑ i, w x i := by push_cast at hsum; nlinarith
      obtain ⟨j, hjF, hjle⟩ := hF ⟨x, hx, h0, hpos⟩
      have hle : ∀ i, w j.1 i ≤ w x i := by
        intro i
        have h1 := hjle i
        have h2 := j.2.2.1 i
        have h3 := h0 i
        simp only at h1
        omega
      have hjC := hC j hjF
      obtain ⟨t', ht'm, ht'⟩ := ih (x * j.1⁻¹) (Γ.mul_mem hx (Γ.inv_mem j.2.1))
        (fun i => by rw [wmul, winv]; linarith [hle i])
        (by
          simp only [wmul, winv, Finset.sum_add_distrib, Finset.sum_neg_distrib]
          push_cast at hsum ⊢
          nlinarith)
      obtain ⟨t, htm, ht⟩ := hPm j
      refine ⟨t' * t, ?_, ?_⟩
      · rw [pow_succ]; exact Ideal.mul_mem_mul ht'm htm
      · rw [map_mul, ← ht', ← ht, ← Units.val_mul, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
  apply (GlobalTheory.T.finite_sublevel_of_int_quadratic_ge_one X q hqneg hqcube hqpos (C * n)).subset
  intro a ha
  by_contra hlt
  exact ha (key n (κ a) (hΓ a) (wκ a) (le_of_lt (not_le.mp hlt)))

end GlobalTheory.QuadTend
