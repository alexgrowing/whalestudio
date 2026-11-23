import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdCoordsOfDefiniteParallelogramForm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finite_free_of_definite_form_of_rank_le :
    ∀ (H : Type) [AddCommGroup H] (Q : H → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f, Q f = 0 → f = 0) → ∀ r : ℕ, (∀ (n : ℕ) (u : Fin n → H), LinearIndependent ℤ u → n ≤ r) → Module.Finite ℤ H ∧ Module.Free ℤ H ∧ Module.finrank ℤ H ≤ r := by
  intro H _ Q hQ hpos hdef r hr
  classical
  have h0 : Q 0 = 0 := by
    have := hQ 0 0
    simp only [add_zero, sub_zero] at this
    omega
  have htf : ∀ (k : ℤ) (f : H), k ≠ 0 → k • f = 0 → f = 0 := by
    intro k f hk hkf
    apply hdef
    have h1 := parallelogram_zsmul Q hQ k f
    rw [hkf, h0] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero 2 hk)
  let P : ℕ → Prop := fun n => ∃ u : Fin n → H, LinearIndependent ℤ u
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.findGreatest P r := ⟨_, rfl⟩
  have hPn : P n := hn ▸
    Nat.findGreatest_spec (P := P) (m := 0) (Nat.zero_le r) ⟨Fin.elim0, linearIndependent_empty_type⟩
  obtain ⟨u, hu⟩ := hPn
  have hmax : ¬ P (n + 1) := by
    rintro ⟨v, hv⟩
    have hlt : Nat.findGreatest P r < n + 1 := by omega
    exact Nat.findGreatest_is_greatest (P := P) (n := r) hlt (hr _ v hv) ⟨v, hv⟩
  have hspan : ∀ h : H, ∃ k : ℕ, 0 < k ∧ ∃ m : Fin n → ℤ, k • h = ∑ i, m i • u i := by
    intro h
    by_contra hne
    push_neg at hne
    apply hmax
    refine ⟨Fin.cons h u, LinearIndependent.finCons' h u hu fun c y hy hcy => ?_⟩
    by_contra hc
    obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy
    have hpos' : 0 < c.natAbs := Int.natAbs_pos.2 hc
    rcases Int.natAbs_eq c with hc' | hc'
    · apply hne c.natAbs hpos' (fun i => - m i)
      rw [← natCast_zsmul, ← hc']
      simp only [neg_smul, Finset.sum_neg_distrib, hm]
      exact eq_neg_of_add_eq_zero_left hcy
    · apply hne c.natAbs hpos' m
      rw [← natCast_zsmul, hm]
      have : c • h = - ((c.natAbs : ℤ) • h) := by
        conv_lhs => rw [hc']
        rw [neg_smul]
      rw [this] at hcy
      exact (neg_add_eq_zero.mp hcy)
  obtain ⟨e, he, hdiv⟩ := exists_dvd_coords_of_definite_form H ⊤ Q hQ hpos
    (fun f _ => hdef f) n u (fun _ => trivial) hu
  have hmem : ∀ h : H, (e : ℤ) • h ∈ Submodule.span ℤ (Set.range u) := by
    intro h
    obtain ⟨k, hk, m, hkm⟩ := hspan h
    have hd := hdiv k m h trivial hkm
    choose m' hm' using hd
    have hz : (k : ℤ) • ((e : ℤ) • h - ∑ i, m' i • u i) = 0 := by
      rw [smul_sub, smul_comm (k : ℤ) (e : ℤ) h, natCast_zsmul h k, hkm, Finset.smul_sum, Finset.smul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [smul_smul, smul_smul, ← hm' i, sub_self]
    have := htf k _ (by exact_mod_cast hk.ne') hz
    rw [sub_eq_zero.mp this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let f : H →ₗ[ℤ] Submodule.span ℤ (Set.range u) :=
    LinearMap.codRestrict _ ((e : ℤ) • LinearMap.id) hmem
  have hinj : Function.Injective f := by
    intro a b hab
    have h' : (e : ℤ) • a = (e : ℤ) • b := congrArg Subtype.val hab
    have : (e : ℤ) • (a - b) = 0 := by rw [smul_sub, h', sub_self]
    exact sub_eq_zero.mp (htf e _ (by exact_mod_cast he.ne') this)
  have : Module.Finite ℤ (Submodule.span ℤ (Set.range u)) :=
    Module.Finite.span_of_finite ℤ (Set.finite_range u)
  have hfin : Module.Finite ℤ H := Module.Finite.of_injective f hinj
  have : Module.IsTorsionFree ℤ H := Module.IsTorsionFree.of_smul_eq_zero fun k x hkx => by
    by_cases hk : k = 0
    · exact Or.inl hk
    · exact Or.inr (htf k x hk hkx)
  have hfree : Module.Free ℤ H := Module.free_of_finite_type_torsion_free'
  refine ⟨hfin, hfree, ?_⟩
  exact hr _ _ (Module.finBasis ℤ H).linearIndependent

end GlobalTheory
