import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

private theorem oneStep {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (Y : Submodule ℂ H)
    (hY : IsClosed (Y : Set H)) (hinv : π.IsInvariant Y) (v : H) (hvY : v ∈ Y) (hv : v ≠ 0) :
    ∃ U : Subgroup G, IsCompact (U : Set G) ∧ IsOpen (U : Set G) ∧
      ∃ y ∈ Y, y ≠ 0 ∧ ∀ u ∈ U, π u y = y := by
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖v‖ / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrv : r < ‖v‖ := by rw [hr]; linarith
  have hnhds : {g : G | ‖π g v - v‖ < r} ∈ nhds (1 : G) := by
    have hc : Continuous fun g : G => ‖π g v - v‖ :=
      ((π.continuous_orbit v).sub continuous_const).norm
    have ho : IsOpen {g : G | ‖π g v - v‖ < r} := isOpen_lt hc continuous_const
    refine ho.mem_nhds ?_
    simpa using hr0
  obtain ⟨K, hKc, hKU⟩ := exists_openSubgroup_isCompact_subset hnhds
  refine ⟨(K : Subgroup G), hKc, K.isOpen, ?_⟩
  letI := InnerProductSpace.rclikeToReal ℂ H
  obtain ⟨C, hC⟩ : ∃ C : Set H, C = (Y : Set H) ∩ ⋂ u ∈ (K : Subgroup G), Metric.closedBall (π u v) r :=
    ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ C ↔ x ∈ Y ∧ ∀ u ∈ (K : Subgroup G), ‖x - π u v‖ ≤ r := by
    intro x
    simp [hC, dist_eq_norm]
  have hCcl : IsClosed C := by
    rw [hC]
    exact hY.inter (isClosed_biInter fun u _ => Metric.isClosed_closedBall)
  have hconv : Convex ℝ C := by
    rw [hC]
    refine Convex.inter ?_ (convex_iInter₂ fun u _ => convex_closedBall _ _)
    intro a ha b hb s t _ _ _
    exact Y.add_mem (Y.smul_mem (s : ℂ) ha) (Y.smul_mem (t : ℂ) hb)
  have hvC : v ∈ C := by
    refine (hmem v).2 ⟨hvY, fun u hu => ?_⟩
    have : ‖π u v - v‖ < r := hKU hu
    rw [norm_sub_rev]
    exact this.le
  have h0 : (0 : H) ∉ C := by
    intro h
    have := ((hmem 0).1 h).2 1 (one_mem _)
    simp only [UnitaryRep.map_one_apply, zero_sub, norm_neg] at this
    linarith
  have hstab : ∀ x ∈ C, ∀ g ∈ (K : Subgroup G), π g x ∈ C := by
    intro x hx g hg
    obtain ⟨hxY, hxb⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨hinv g x hxY, fun u hu => ?_⟩
    have e : π g x - π u v = π g (x - π (g⁻¹ * u) v) := by
      rw [map_sub, ← UnitaryRep.map_mul_apply, mul_inv_cancel_left]
    rw [e, UnitaryRep.norm_map]
    exact hxb _ (mul_mem (inv_mem hg) hu)
  obtain ⟨y, hyC, hy⟩ := exists_norm_eq_iInf_of_complete_convex ⟨v, hvC⟩ hCcl.isComplete hconv (0 : H)
  have hmin : ∀ w ∈ C, ‖y‖ ≤ ‖w‖ := by
    intro w hw
    have h1 := ciInf_le (f := fun w : C => ‖(0 : H) - (w : H)‖)
      ⟨0, by rintro _ ⟨a, rfl⟩; exact norm_nonneg _⟩ ⟨w, hw⟩
    rw [← hy] at h1
    simpa using h1
  refine ⟨y, ((hmem y).1 hyC).1, fun h => h0 (h ▸ hyC), fun g hg => ?_⟩
  have hz : π g y ∈ C := hstab y hyC g hg
  have hm : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • π g y ∈ C :=
    hconv hyC hz (by norm_num) (by norm_num) (by norm_num)
  have h2 : ‖y‖ ≤ ‖(1 / 2 : ℝ) • y + (1 / 2 : ℝ) • π g y‖ := hmin _ hm
  rw [← smul_add, norm_smul] at h2
  have h3 : 2 * ‖y‖ ≤ ‖y + π g y‖ := by
    have : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    rw [this] at h2
    linarith
  have hp := parallelogram_law_with_norm ℂ y (π g y)
  rw [UnitaryRep.norm_map] at hp
  have h4 : ‖y - π g y‖ * ‖y - π g y‖ ≤ 0 := by
    nlinarith [norm_nonneg y, norm_nonneg (y + π g y)]
  have h5 : ‖y - π g y‖ = 0 := by
    nlinarith [norm_nonneg (y - π g y)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp h5)).symm

theorem UpperTheory.exists_compactOpen_family_inf_fixed_ne_bot :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : ∀ i, UnitaryRep (G i) H), (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → ∀ Z : Submodule ℂ H, IsClosed (Z : Set H) → (∀ i, (π i).IsInvariant Z) → Z ≠ ⊥ → ∃ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) ∧ (Z ⊓ ⨅ i, fixU (π i) (U i)) ≠ ⊥ := by
  intro r G _ _ _ _ _ _ H _ _ _ π hcomm Z hZ hinv hne
  classical
  have key : ∀ s : Finset (Fin r), ∃ U : ∀ i, Subgroup (G i),
      (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) ∧
        ∃ w ∈ Z, w ≠ 0 ∧ ∀ i ∈ s, ∀ u ∈ U i, π i u w = w := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h0 : ∀ i, ∃ K : Subgroup (G i), IsCompact (K : Set (G i)) ∧ IsOpen (K : Set (G i)) :=
        fun i => by
          obtain ⟨K, hK, -⟩ := exists_openSubgroup_isCompact_subset (G := G i) (U := Set.univ)
            Filter.univ_mem
          exact ⟨K, hK, K.isOpen⟩
      choose U hU using h0
      obtain ⟨w, hw, hw0⟩ := Z.ne_bot_iff.mp hne
      exact ⟨U, hU, w, hw, hw0, by simp⟩
    | insert j s hj ih =>
      obtain ⟨U, hU, w, hwZ, hw0, hwf⟩ := ih
      obtain ⟨Y, hYdef⟩ : ∃ Y : Submodule ℂ H, Y = Z ⊓ ⨅ i ∈ s, fixU (π i) (U i) := ⟨_, rfl⟩
      have hmemY : ∀ x, x ∈ Y ↔ x ∈ Z ∧ ∀ i ∈ s, ∀ u ∈ U i, π i u x = x := by
        intro x
        simp [hYdef, Submodule.mem_inf, Submodule.mem_iInf, mem_fixU]
      have hYc : IsClosed (Y : Set H) := by
        have e : (Y : Set H) = (Z : Set H) ∩ ⋂ i ∈ s, (fixU (π i) (U i) : Set H) := by
          ext x
          simp [hYdef, Submodule.mem_inf, Submodule.mem_iInf]
        rw [e]
        exact hZ.inter (isClosed_biInter fun i _ => isClosed_fixU _ _)
      have hYinv : (π j).IsInvariant Y := by
        intro g x hx
        rw [hmemY] at hx ⊢
        refine ⟨hinv j g x hx.1, fun i hi u hu => ?_⟩
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        rw [hcomm i j hij, hx.2 i hi u hu]
      obtain ⟨K, hKc, hKo, y, hyY, hy0, hyf⟩ :=
        oneStep (π j) Y hYc hYinv w ((hmemY w).2 ⟨hwZ, hwf⟩) hw0
      have hyY' := (hmemY y).1 hyY
      refine ⟨Function.update U j K, ?_, y, hyY'.1, hy0, ?_⟩
      · intro i
        by_cases h : i = j
        · subst h
          simpa using And.intro hKc hKo
        · simpa [Function.update_of_ne h] using hU i
      · intro i hi u hu
        by_cases h : i = j
        · subst h
          exact hyf u (by simpa using hu)
        · have hi' : i ∈ s := (Finset.mem_insert.mp hi).resolve_left h
          exact hyY'.2 i hi' u (by simpa [Function.update_of_ne h] using hu)
  obtain ⟨U, hU, w, hwZ, hw0, hwf⟩ := key Finset.univ
  refine ⟨U, hU, fun hbot => hw0 ?_⟩
  have hw : w ∈ Z ⊓ ⨅ i, fixU (π i) (U i) := by
    refine Submodule.mem_inf.mpr ⟨hwZ, ?_⟩
    rw [Submodule.mem_iInf]
    intro i
    exact mem_fixU.mpr (hwf i (Finset.mem_univ i))
  rw [hbot] at hw
  simpa using hw
