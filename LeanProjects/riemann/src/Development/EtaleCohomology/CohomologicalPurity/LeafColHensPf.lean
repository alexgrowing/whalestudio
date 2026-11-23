import Development.EtaleCohomology.CohomologicalPurity.LeafHensCutDef

noncomputable section
open CategoryTheory Limits Polynomial

namespace LateralTheory.CohomologicalPurity.Hz

theorem evalMapHom {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (p : R[X]) (x : R) :
    (p.map f).eval (f x) = f (p.eval x) := by
  rw [eval_map, eval₂_at_apply]

theorem Diag.leg_comp_map {A : Type} [CommRing A] {I : Ideal A} (Δ : Diag A I) (c : Cocone Δ.D) {j k : Δ.J}
    (e : j ⟶ k) : (Δ.leg c k).comp (Δ.D.map e).hom = Δ.leg c j :=
  congrArg CommRingCat.Hom.hom (c.w e)

theorem LeafColHens_of (hS : LeafStage) (hI : LeafInv) (hR : LeafRoot) : LeafColHens := by
  classical
  intro A _ I Δ c hc η hη
  have st := hS A I Δ c hc η hη
  have push : ∀ j (S : Type) [CommRing S] (φ : Δ.D.obj j →+* S), Good φ (I.map (Δ.s j)) →
      ∃ π : S →+* c.pt, π.comp φ = Δ.leg c j := by
    intro j S _ φ hφ
    obtain ⟨k, e, ρ, hρ⟩ := Δ.exh j S φ hφ
    exact ⟨(Δ.leg c k).comp ρ, by rw [RingHom.comp_assoc, hρ, Δ.leg_comp_map]⟩
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [Ideal.mem_jacobson_bot]
    intro y
    have hzy : z * y ∈ I.map η := Ideal.mul_mem_right y _ hz
    obtain ⟨j, hj⟩ := st.1 {z * y}
    obtain ⟨x, hx⟩ := hj (z * y) (Finset.mem_singleton_self _)
    have hx' : x ∈ I.map (Δ.s j) := st.2 j x (by rw [hx]; exact hzy)
    obtain ⟨S, _, φ, hφ, hu⟩ := hI (Δ.D.obj j) (I.map (Δ.s j)) x hx'
    obtain ⟨π, hπ⟩ := push j S φ hφ
    have h := hu.map π
    rw [← RingHom.comp_apply, hπ, map_add, map_one, hx, add_comm] at h
    exact h
  · intro f hf a₀ ha₀ hu
    obtain ⟨u, hu'⟩ := Ideal.Quotient.mk_surjective (↑hu.unit⁻¹ : c.pt ⧸ I.map η)
    have hdu : f.derivative.eval a₀ * u - 1 ∈ I.map η := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hu', map_one, IsUnit.mul_val_inv, sub_self]
    let T : Finset c.pt := insert a₀ (insert u (f.support.image f.coeff))
    obtain ⟨j, hj⟩ := st.1 T
    obtain ⟨a, ha⟩ := hj a₀ (Finset.mem_insert_self _ _)
    obtain ⟨v, hv⟩ := hj u (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hco : ∀ n, f.coeff n ∈ Set.range (Δ.leg c j) := by
      intro n
      by_cases hn : n ∈ f.support
      · exact hj _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hn)))
      · exact ⟨0, by rw [map_zero, notMem_support_iff.1 hn]⟩
    obtain ⟨g, hg, -, hgm⟩ := lifts_and_natDegree_eq_and_monic ((lifts_iff_coeff_lifts f).2 hco) hf
    have h1 : g.eval a ∈ I.map (Δ.s j) := st.2 j _ (by rw [← evalMapHom, hg, ha]; exact ha₀)
    have h2 : g.derivative.eval a * v - 1 ∈ I.map (Δ.s j) := st.2 j _ (by
      rw [map_sub, map_mul, map_one, ← evalMapHom, ← derivative_map, hg, ha, hv]; exact hdu)
    have h3 : IsUnit (Ideal.Quotient.mk (I.map (Δ.s j)) (g.derivative.eval a)) :=
      IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ v)
        (by rw [← map_mul, ← map_one (Ideal.Quotient.mk (I.map (Δ.s j)))]; exact Ideal.Quotient.eq.2 h2)
    obtain ⟨S, _, φ, b, hφ, hb, hba⟩ := hR (Δ.D.obj j) (I.map (Δ.s j)) g a hgm h1 h3
    obtain ⟨π, hπ⟩ := push j S φ hφ
    refine ⟨π b, ?_, ?_⟩
    · have h := hb.map (f := π)
      rwa [Polynomial.map_map, hπ, hg] at h
    · have h := Ideal.mem_map_of_mem π hba
      rw [Ideal.map_map, Ideal.map_map, hπ, hη, map_sub, ← RingHom.comp_apply, hπ, ha] at h
      exact h

end LateralTheory.CohomologicalPurity.Hz
