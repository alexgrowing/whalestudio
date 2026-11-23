import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

open CompanionTheory.Rg.Fl

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeBasis

variable {G : Type} [Group G] (K : Subgroup G)

theorem lam_single (g : G) (y : G ⧸ K) (c : ℂ) :
    lam K g (Finsupp.single y c) = Finsupp.single (g • y) c := by
  simp [lam, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem lam_mul (g g' : G) (u : (G ⧸ K) →₀ ℂ) :
    lam K (g * g') u = lam K g (lam K g' u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single y c => simp [lam_single, mul_smul]

theorem lam_one (u : (G ⧸ K) →₀ ℂ) : lam K 1 u = u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single y c => simp [lam_single]

theorem lam_apply_smul (g : G) (u : (G ⧸ K) →₀ ℂ) (y : G ⧸ K) :
    lam K g u (g • y) = u y :=
  Finsupp.mapDomain_apply (MulAction.injective g) u y

def IsFixed (u : (G ⧸ K) →₀ ℂ) : Prop := ∀ k ∈ K, lam K k u = u

variable {K}

theorem lam_congr {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) {x x' : G}
    (h : (x : G ⧸ K) = x') : lam K x u = lam K x' u := by
  have hk : x⁻¹ * x' ∈ K := QuotientGroup.eq.1 h
  have : x' = x * (x⁻¹ * x') := by group
  rw [this, lam_mul, hu _ hk]

variable (K)

def op (u : (G ⧸ K) →₀ ℂ) : Module.End ℂ ((G ⧸ K) →₀ ℂ) :=
  Finsupp.lsum ℂ fun y => LinearMap.toSpanSingleton ℂ _ (lam K (Quotient.out y) u)

theorem op_single_out (u : (G ⧸ K) →₀ ℂ) (y : G ⧸ K) (c : ℂ) :
    op K u (Finsupp.single y c) = c • lam K (Quotient.out y) u := by
  simp [op, LinearMap.toSpanSingleton_apply]

variable {K}

theorem op_single {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) (x : G) (c : ℂ) :
    op K u (Finsupp.single (x : G ⧸ K) c) = c • lam K x u := by
  rw [op_single_out, lam_congr hu (QuotientGroup.out_eq' (x : G ⧸ K))]

theorem op_mem {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) : op K u ∈ Hk K := by
  rw [Hk, Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  refine Finsupp.lhom_ext' fun y => LinearMap.ext_ring ?_
  induction y using QuotientGroup.induction_on with
  | H x =>
    have hgx : g • (x : G ⧸ K) = ((g * x : G) : G ⧸ K) := rfl
    simp only [Finsupp.lsingle_apply, Module.End.mul_apply, LinearMap.comp_apply]
    rw [op_single hu, lam_single, hgx, op_single hu, lam_mul]
    simp

variable (K)

def delta : (G ⧸ K) →₀ ℂ := Finsupp.single ((1 : G) : G ⧸ K) 1

theorem lam_delta (x : G) : lam K x (delta K) = Finsupp.single (x : G ⧸ K) 1 := by
  have : x • ((1 : G) : G ⧸ K) = (x : G ⧸ K) := by
    change ((x * 1 : G) : G ⧸ K) = x
    rw [mul_one]
  rw [delta, lam_single, this]

theorem delta_fixed_eval (h : Hk K) : IsFixed K ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K)) := by
  intro k hk
  have hc : lam K k * (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) = (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) * lam K k :=
    (Subalgebra.mem_centralizer_iff ℂ).1 h.2 _ ⟨k, rfl⟩
  have hd : lam K k (delta K) = delta K := by
    have hk1 : (k : G ⧸ K) = ((1 : G) : G ⧸ K) :=
      QuotientGroup.eq.2 (by simpa using K.inv_mem hk)
    rw [lam_delta, delta, hk1]
  have := LinearMap.congr_fun hc (delta K)
  simp only [Module.End.mul_apply] at this
  rw [this, hd]

variable {K}

theorem op_delta {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) : op K u (delta K) = u := by
  rw [delta, op_single hu, lam_one, one_smul]

theorem eq_zero_of_delta (h : Hk K)
    (h0 : (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) = 0) : h = 0 := by
  apply Subtype.ext
  refine Finsupp.lhom_ext' fun y => LinearMap.ext_ring ?_
  induction y using QuotientGroup.induction_on with
  | H x =>
    have hc : lam K x * (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) = (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) * lam K x :=
      (Subalgebra.mem_centralizer_iff ℂ).1 h.2 _ ⟨x, rfl⟩
    have := LinearMap.congr_fun hc (delta K)
    simp only [Module.End.mul_apply] at this
    rw [h0, map_zero, lam_delta] at this
    simpa using this.symm

def orbitVec (hK : IsHeckePair K) (g : G) : (G ⧸ K) →₀ ℂ :=
  ∑ y ∈ (hK g).toFinset, Finsupp.single y (1 : ℂ)

open Classical in
theorem orbitVec_apply (hK : IsHeckePair K) (g : G) (z : G ⧸ K) :
    orbitVec hK g z = if z ∈ MulAction.orbit K (g : G ⧸ K) then 1 else 0 := by
  classical
  simp [orbitVec, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem lam_apply (k : G) (u : (G ⧸ K) →₀ ℂ) (z : G ⧸ K) :
    lam K k u z = u ((k⁻¹ : G) • z) := by
  have := lam_apply_smul K k u ((k⁻¹ : G) • z)
  rwa [smul_inv_smul] at this

theorem orbitVec_fixed (hK : IsHeckePair K) (g : G) : IsFixed K (orbitVec hK g) := by
  classical
  intro k hk
  ext z
  have hmem : ((k⁻¹ : G) • z ∈ MulAction.orbit K (g : G ⧸ K)) ↔
      z ∈ MulAction.orbit K (g : G ⧸ K) := by
    have e : (k⁻¹ : G) • z = (⟨k, hk⟩ : K)⁻¹ • z := rfl
    rw [e, ← MulAction.orbit_eq_iff, ← MulAction.orbit_eq_iff (a := z), MulAction.orbit_smul]
  rw [lam_apply, orbitVec_apply, orbitVec_apply]
  simp only [hmem]

theorem IsFixed.apply_of_mem_orbit {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) {x z : G ⧸ K}
    (hz : z ∈ MulAction.orbit K x) : u z = u x := by
  obtain ⟨k, rfl⟩ := hz
  have h := lam_apply_smul K (k : G) u x
  rw [hu _ k.2] at h
  exact h

def heckeOp (hK : IsHeckePair K) (g : G) : Hk K :=
  ⟨op K (orbitVec hK g), op_mem (orbitVec_fixed hK g)⟩

theorem heckeOp_delta (hK : IsHeckePair K) (g : G) :
    (heckeOp hK g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) = orbitVec hK g :=
  op_delta (orbitVec_fixed hK g)

theorem exists_mem_span_delta (hK : IsHeckePair K) (n : ℕ) :
    ∀ u : (G ⧸ K) →₀ ℂ, IsFixed K u → u.support.card ≤ n →
      ∃ t ∈ Submodule.span ℂ (Set.range (heckeOp hK)),
        (t : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) = u := by
  classical
  induction n with
  | zero =>
    intro u _ hc
    have : u = 0 := by simpa using hc
    exact ⟨0, Submodule.zero_mem _, by simp [this]⟩
  | succ n ih =>
    intro u hu hc
    by_cases h0 : u = 0
    · exact ⟨0, Submodule.zero_mem _, by simp [h0]⟩
    obtain ⟨y, hy⟩ := Finsupp.support_nonempty_iff.2 h0
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    set c := u (g : G ⧸ K) with hcdef
    have hc0 : c ≠ 0 := Finsupp.mem_support_iff.1 hy
    have hfix : IsFixed K (u - c • orbitVec hK g) := by
      intro k hk
      rw [map_sub, map_smul, hu k hk, orbitVec_fixed hK g k hk]
    have hsub : (u - c • orbitVec hK g).support ⊆ u.support.erase (g : G ⧸ K) := by
      intro z hz
      have hz' := Finsupp.mem_support_iff.1 hz
      simp only [Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        orbitVec_apply] at hz'
      refine Finset.mem_erase.2 ⟨?_, ?_⟩
      · rintro rfl
        apply hz'
        simp [MulAction.mem_orbit_self, ← hcdef]
      · refine Finsupp.mem_support_iff.2 fun hzu => hz' ?_
        have hno : z ∉ MulAction.orbit K (g : G ⧸ K) := fun hm =>
          hc0 (by rw [hcdef, ← hu.apply_of_mem_orbit hm, hzu])
        simp [hzu, hno]
    have hcard : (u - c • orbitVec hK g).support.card ≤ n := by
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hy] at this
      omega
    obtain ⟨t, ht, hte⟩ := ih _ hfix hcard
    refine ⟨t + c • heckeOp hK g,
      Submodule.add_mem _ ht (Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)), ?_⟩
    have : ((t + c • heckeOp hK g : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) =
        (t : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) +
          c • (heckeOp hK g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) := rfl
    rw [this, hte, heckeOp_delta]
    abel

theorem heckeBasis : ∀ (G : Type) [Group G] (K : Subgroup G), IsHeckePair K → ∃ T : G → Hk K, (∀ (g : G) (S : Finset (G ⧸ K)), (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K) → (T g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = ∑ y ∈ S, Finsupp.single y (1 : ℂ)) ∧ Submodule.span ℂ (Set.range T) = ⊤ ∧ ∀ h : Hk K, (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = 0 → h = 0 := by
  intro G _ K hK
  refine ⟨heckeOp hK, ?_, ?_, fun h h0 => eq_zero_of_delta h h0⟩
  · intro g S hS
    have hSe : S = (hK g).toFinset := by
      ext z
      rw [Set.Finite.mem_toFinset, ← hS, Finset.mem_coe]
    have := heckeOp_delta hK g
    rw [orbitVec, ← hSe] at this
    exact this
  · rw [eq_top_iff]
    intro h _
    obtain ⟨t, ht, hte⟩ := exists_mem_span_delta hK _
      ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K)) (delta_fixed_eval K h) le_rfl
    have : h - t = 0 := eq_zero_of_delta (h - t) (by
      have e : ((h - t : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) =
          (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) -
            (t : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) := rfl
      rw [e, hte, sub_self])
    rw [sub_eq_zero.1 this]
    exact ht

end GlobalTheory.CompanionTheory.HeckeBasis
