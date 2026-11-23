import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionKillsNonzeroWeight

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def ExtremalProjectorProperties {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (L : ℕ) : Prop :=
  ∀ (c : Fin n) (u : V), u ∈ weightSp E 0 → (∀ a b : Fin n, a < c → b < c → E a b u = 0) →
    (∀ j, j < c → E j c (extremalProjector E c L u) = 0) ∧
    (∀ a b : Fin n, a < c → b < c → E a b (extremalProjector E c L u) = 0) ∧
    extremalProjector E c L u ∈ weightSp E 0 ∧
    ∃ w : Fin n → V, extremalProjector E c L u = u + ∑ i ∈ Finset.Iio c, E c i (w i)

theorem denominator_chain_bound (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero (KK O)] (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V]
    (E : GLOps n (KK O) V) (hE : IsGLRep E) (M : Submodule O V)
    (Inv : Module.End (KK O) V) (hInv : IsInvProj E Inv) (L de : ℕ) (hA : ExtremalProjectorProperties E L)
    (hB : ∀ (c : Fin n) (y : V), y ∈ M → ((p : O) ^ (c.val * de)) • extremalProjector E c L y ∈ M)
    (x0 : V) (hx0 : x0 ∈ weightSp E 0) (hxM : x0 ∈ M) (c : ℕ) (hc : c ≤ n) :
    ∃ y, y ∈ weightSp E 0 ∧ (∀ a b : Fin n, a.val < c → b.val < c → E a b y = 0) ∧ Inv y = Inv x0 ∧
      ((p : O) ^ ((∑ i ∈ range c, i) * de)) • y ∈ M := by
  induction c with
  | zero =>
    refine ⟨x0, hx0, fun a b ha _ => absurd ha (Nat.not_lt_zero _), rfl, ?_⟩
    simpa using hxM
  | succ c ih =>
    obtain ⟨y, hy0, hyk, hyI, hyM⟩ := ih (Nat.le_of_succ_le hc)
    have hcn : c < n := hc
    obtain ⟨cf, hcf⟩ : ∃ cf : Fin n, cf.val = c := ⟨⟨c, hcn⟩, rfl⟩
    obtain ⟨hA1, hA2, hA3, w, hw⟩ := hA cf y hy0 (fun a b ha hb =>
      hyk a b (by have := Fin.lt_def.mp ha; omega) (by have := Fin.lt_def.mp hb; omega))
    refine ⟨extremalProjector E cf L y, hA3, ?_, ?_, ?_⟩
    · intro a b ha hb
      rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha' | ha' <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb' | hb'
      · exact hA2 a b (Fin.lt_def.mpr (by omega)) (Fin.lt_def.mpr (by omega))
      · have hb2 : b = cf := Fin.ext (by omega)
        subst hb2
        exact hA1 a (Fin.lt_def.mpr (by omega))
      · have ha2 : a = cf := Fin.ext (by omega)
        subst ha2
        exact weight_zero_lowering_kills_raising hE hA3 b a (by rintro rfl; omega) (hA1 b (Fin.lt_def.mpr (by omega)))
      · have ha2 : a = cf := Fin.ext (by omega)
        have hb2 : b = cf := Fin.ext (by omega)
        rw [ha2, hb2]
        have h0 := hA3
        simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at h0
        simpa using h0 cf
    · rw [hw, map_add, map_sum]
      simp only [invariant_projection_kills_operator D h2 E hE Inv hInv, Finset.sum_const_zero, add_zero]
      exact hyI
    · have hM2 := hB cf _ hyM
      rw [LinearMap.map_smul_of_tower, smul_smul, ← pow_add] at hM2
      have he : (∑ i ∈ range (c + 1), i) * de = cf.val * de + (∑ i ∈ range c, i) * de := by
        rw [Finset.sum_range_succ, hcf]; ring
      rw [he]
      exact hM2

theorem invariant_projection_denominator_bound (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero (KK O)] (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V]
    (E : GLOps n (KK O) V) (hE : IsGLRep E) (M : Submodule O V) (hM : UZStable (O := O) E M)
    (Inv : Module.End (KK O) V) (hInv : IsInvProj E Inv) (L de : ℕ) (hA : ExtremalProjectorProperties E L)
    (hB : ∀ (c : Fin n) (y : V), y ∈ M → ((p : O) ^ (c.val * de)) • extremalProjector E c L y ∈ M)
    (x : V) (hx : x ∈ M) : ((p : O) ^ (N0 n * de)) • Inv x ∈ M := by
  obtain ⟨Θ, hΘ1, hΘ2⟩ := weight_projections_integral_findim E
  obtain ⟨y, hy0, hyk, hyI, hyM⟩ := denominator_chain_bound D h2 p O n V E hE M Inv hInv L de hA hB (Θ 0 x)
    (weight_projection_mem_weightSpace E hE Θ hΘ2 0 x) (binomial_subring_preserves_lattice hM _ (hΘ1 0) x hx) n le_rfl
  have hInvy : Inv y = y := by
    by_cases hy : y = 0
    · rw [hy, map_zero]
    · apply hInv.1
      exact Submodule.subset_span ⟨1, one_mem _, y, ⟨hy, hy0, fun a b _ => hyk a b a.2 b.2⟩, rfl⟩
  rw [invariant_projection_through_zero_weight D h2 E hE Inv hInv Θ hΘ2 x, ← hyI, hInvy]
  rwa [Finset.sum_range_id] at hyM

end Formalism.MainNotions.G.GLWeightTheory
