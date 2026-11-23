import Development.EtaleCohomology.EtaleSheaves.StandardChartsLineZero

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.AlgGlue₂

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

theorem mS_mul (S : Subalgebra A K) {x b : K} (hx : x ∈ mS S) (hb : b ∈ S) : x * b ∈ mS S := by
  unfold mS at hx ⊢
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha s hs
    rw [smul_mul_assoc]
    exact Submodule.smul_mem_smul ha (S.mul_mem hs hb)
  · intro x y hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy

theorem unit_case (S : Subalgebra A K) {u h e : K} (hu : u ∈ S) (hh : h ∈ S) (huh : u * h = 1)
    (he : e ∈ S) (hue : u - e ∈ mS S) (hee : e * e - e ∈ mS S) : e - 1 ∈ mS S := by
  have key : e - 1 = (e * e - e) * h + (u - e) * ((e - 1) * h) := by
    linear_combination (1 - e) * huh
  rw [key]
  exact Submodule.add_mem _ (mS_mul S hee hh)
    (mS_mul S hue (S.mul_mem (S.sub_mem he (S.one_mem)) hh))

theorem nonunit_case (S : Subalgebra A K) {u h e : K} (hu : u ∈ S) (hh : h ∈ S) (huh : (1 - u) * h = 1)
    (he : e ∈ S) (hue : u - e ∈ mS S) (hee : e * e - e ∈ mS S) : e ∈ mS S := by
  have h1 := unit_case S (u := 1 - u) (e := 1 - e) (S.sub_mem S.one_mem hu) hh huh
    (S.sub_mem S.one_mem he)
    (by
      have : (1 - u) - (1 - e) = (u - e) * (-1) := by ring
      rw [this]; exact mS_mul S hue (S.neg_mem S.one_mem))
    (by
      have : (1 - e) * (1 - e) - (1 - e) = e * e - e := by ring
      rw [this]; exact hee)
  have : e = (1 - e - 1) * (-1) := by ring
  rw [this]; exact mS_mul S h1 (S.neg_mem S.one_mem)

theorem AlgGlue_of (hL : IdemLift) (hF : LateralTheory.E.LZProperCut.LZHensFinite) : AlgGlue := by
  intro A _ _ _ K _ _ B C t hc hint e f hef
  obtain ⟨heB, hfC, hee, hff, hd⟩ := hef
  obtain ⟨g, hgB, hgC, hge, hgf⟩ := hL A K B C t hc e f ⟨heB, hfC, hee, hff, hd⟩
  set R : Subalgebra A K := Algebra.adjoin A {g} with hR
  have hRB : R ≤ B := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hgB)
  have hRC : R ≤ C := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hgC)
  have hgi : IsIntegral A g := hint g hgB hgC
  have : Module.Finite A R := Algebra.finite_adjoin_simple_of_isIntegral hgi
  have : IsDomain R := inferInstance
  have : ConnectedSpace ↑(Spec (CommRingCat.of R)) := by
    change ConnectedSpace (PrimeSpectrum R)
    infer_instance
  have : IsLocalRing R := hF A R this
  have hgR : g ∈ R := Algebra.self_mem_adjoin_singleton A g
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨g, hgR⟩ : R) with hu | hu
  · obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hv' : g * (v : K) = 1 := by
      have := congrArg Subtype.val hv; simpa using this
    right
    exact ⟨unit_case B hgB (hRB v.2) hv' heB hge hee, unit_case C hgC (hRC v.2) hv' hfC hgf hff⟩
  · obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hv' : (1 - g) * (v : K) = 1 := by
      have := congrArg Subtype.val hv; simpa using this
    left
    exact ⟨nonunit_case B hgB (hRB v.2) hv' heB hge hee, nonunit_case C hgC (hRC v.2) hv' hfC hgf hff⟩

end LateralTheory.E.AlgGlue₂
