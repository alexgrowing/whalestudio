import Mathlib
import GroundTheory.AutomorphicForms.SmoothRep
import GroundTheory.AutomorphicForms.HeckeIrreducible
import ReciprocityTheory.BurnsideSurjectivity.Burnside

noncomputable section

namespace DiscreteGroups.sglob.LConvU

open GroundTheory.Automorphic Set

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  (hρ : IsSmooth ρ) {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

include hρ hKc hKo

theorem fixedProj_eq_avg {L : Subgroup G} (hLK : L ≤ K) (hLo : IsOpen (L : Set G)) :
    ∃ (N : ℕ) (r : Fin N → G), 0 < N ∧ (∀ i, r i ∈ K) ∧
      ∀ v : V, v ∈ fixedVectors ρ L →
        (fixedProj ρ hρ hKc hKo v : V) = (N : ℂ)⁻¹ • ∑ i, ρ (r i) v := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hHo : IsOpen ((L.subgroupOf K : Subgroup K) : Set K) := hLo.preimage continuous_subtype_val
  have : Finite (K ⧸ L.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hHo
  let _ : Fintype (K ⧸ L.subgroupOf K) := Fintype.ofFinite _
  have hNpos : 0 < Fintype.card (K ⧸ L.subgroupOf K) :=
    Fintype.card_pos_iff.mpr ⟨QuotientGroup.mk (1 : K)⟩
  let eQ := Fintype.equivFin (K ⧸ L.subgroupOf K)
  refine ⟨Fintype.card (K ⧸ L.subgroupOf K), fun i => ((Quotient.out (eQ.symm i) : K) : G), hNpos,
    fun i => (Quotient.out (eQ.symm i)).2, ?_⟩
  intro v hv
  obtain ⟨s, hs⟩ : ∃ s : V, s = ∑ q : K ⧸ L.subgroupOf K, ρ ((Quotient.out q : K) : G) v := ⟨_, rfl⟩
  have hreidx : ∑ i, ρ ((Quotient.out (eQ.symm i) : K) : G) v = s := by
    rw [hs]
    exact Fintype.sum_equiv eQ.symm _ _ (fun _ => rfl)
  have hsK : s ∈ fixedVectors ρ K := by
    intro k hk
    have key : ∀ q : K ⧸ L.subgroupOf K, ρ k (ρ ((Quotient.out q : K) : G) v) =
        ρ ((Quotient.out ((⟨k, hk⟩ : K) • q) : K) : G) v := by
      intro q
      rw [← Module.End.mul_apply, ← map_mul]
      have h1 : (((⟨k, hk⟩ : K) * Quotient.out q : K) : G) = k * ((Quotient.out q : K) : G) := rfl
      rw [← h1]
      apply act_eq_of_mk_eq ρ hv
      rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
    rw [hs, map_sum, Finset.sum_congr rfl (fun q _ => key q)]
    exact Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ (fun _ => rfl)
  have hsub : s - ((Fintype.card (K ⧸ L.subgroupOf K) : ℕ) : ℂ) • v ∈ coinvariantsKer ρ K := by
    have h1 : s - ((Fintype.card (K ⧸ L.subgroupOf K) : ℕ) : ℂ) • v =
        ∑ q : K ⧸ L.subgroupOf K, (ρ ((Quotient.out q : K) : G) v - v) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul, hs]
    rw [h1]
    exact Submodule.sum_mem _ fun q _ => sub_mem_coinvariantsKer (Quotient.out q).2 v
  have h1 : (fixedProj ρ hρ hKc hKo s : V) = s := fixedProj_apply_of_mem hρ hKc hKo hsK
  have h2 := fixedProj_apply_of_mem_coinvariantsKer hρ hKc hKo hsub
  rw [map_sub, map_smul, sub_eq_zero] at h2
  have h3 : ((Fintype.card (K ⧸ L.subgroupOf K) : ℕ) : ℂ) • (fixedProj ρ hρ hKc hKo v : V) = s := by
    rw [← h1, h2, Submodule.coe_smul]
  rw [hreidx, ← h3, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hNpos.ne'), one_smul]

theorem map_fixedProj_of_invariant {U : Type*} [AddCommGroup U] [Module ℂ U] (f : V →ₗ[ℂ] U)
    (v : V) (hf : ∀ k ∈ K, f (ρ k v) = f v) : f (fixedProj ρ hρ hKc hKo v : V) = f v := by
  have hLo : IsOpen ((K ⊓ stabilizerOf ρ v : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKo.inter (hρ v)
  obtain ⟨N, r, hN, hr, h⟩ := fixedProj_eq_avg hρ hKc hKo (L := K ⊓ stabilizerOf ρ v) inf_le_left hLo
  rw [h v (fun l hl => hl.2), map_smul, map_sum, Finset.sum_congr rfl (fun i _ => hf (r i) (hr i)),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast hN.ne'), one_smul]

variable (ρ) in

def hop (g : G) : Module.End ℂ (fixedVectors ρ K) :=
  (fixedProj ρ hρ hKc hKo) ∘ₗ (ρ g) ∘ₗ (fixedVectors ρ K).subtype

theorem hop_apply (g : G) (w : fixedVectors ρ K) :
    hop ρ hρ hKc hKo g w = fixedProj ρ hρ hKc hKo (ρ g w) := rfl

theorem hop_of_mem {κ : G} (hκ : κ ∈ K) : hop ρ hρ hKc hKo κ = 1 := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  rw [hop_apply, fixedProj_apply_act hρ hKc hKo hκ, Module.End.one_apply,
    fixedProj_apply_of_mem hρ hKc hKo w.2]

theorem hop_one : hop ρ hρ hKc hKo 1 = 1 := hop_of_mem hρ hKc hKo K.one_mem

theorem hop_mul {g h : G}
    (H : ∀ w ∈ fixedVectors ρ K, ∀ κ ∈ K,
      fixedProj ρ hρ hKc hKo (ρ (g * κ * h) w) = fixedProj ρ hρ hKc hKo (ρ (g * h) w)) :
    hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo h = hop ρ hρ hKc hKo (g * h) := by
  refine LinearMap.ext fun w => ?_
  show fixedProj ρ hρ hKc hKo (ρ g (fixedProj ρ hρ hKc hKo (ρ h w) : V)) =
    fixedProj ρ hρ hKc hKo (ρ (g * h) w)
  have key := map_fixedProj_of_invariant hρ hKc hKo ((fixedProj ρ hρ hKc hKo) ∘ₗ ρ g) (ρ h w)
    (fun κ hκ => by
      simp only [LinearMap.comp_apply]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, H w w.2 κ hκ,
        map_mul, Module.End.mul_apply])
  simp only [LinearMap.comp_apply] at key
  rw [key, map_mul, Module.End.mul_apply]

theorem hop_mul_mem_span (g h : G) :
    hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo h ∈
      Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) := by
  let L : Subgroup G := K ⊓ K.comap (MulAut.conj h⁻¹).toMonoidHom
  have hLo : IsOpen (L : Set G) := by
    have hc : Continuous fun x : G => h⁻¹ * x * h⁻¹⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    exact hKo.inter (hKo.preimage hc)
  obtain ⟨N, r, hN, -, hav⟩ := fixedProj_eq_avg hρ hKc hKo (L := L) inf_le_left hLo
  have hfix : ∀ w : fixedVectors ρ K, ρ h (w : V) ∈ fixedVectors ρ L := by
    intro w l hl
    have hl2 : h⁻¹ * l * h ∈ K := by
      have := hl.2
      simpa [Subgroup.mem_comap, MulAut.conj_apply] using this
    calc ρ l (ρ h w) = ρ h (ρ (h⁻¹ * l * h) w) := by
          rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]; congr 2; group
      _ = ρ h w := by rw [w.2 _ hl2]
  have heq : hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo h =
      (N : ℂ)⁻¹ • ∑ i, hop ρ hρ hKc hKo (g * r i * h) := by
    refine LinearMap.ext fun w => ?_
    show fixedProj ρ hρ hKc hKo (ρ g (fixedProj ρ hρ hKc hKo (ρ h w) : V)) = _
    rw [hav _ (hfix w), map_smul, map_smul, map_sum, map_sum, LinearMap.smul_apply,
      LinearMap.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = fixedProj ρ hρ hKc hKo (ρ (g * r i * h) w)
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, rfl⟩)

theorem span_hop_mul_mem {a b : Module.End ℂ (fixedVectors ρ K)}
    (ha : a ∈ Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)))
    (hb : b ∈ Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo))) :
    a * b ∈ Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨h, rfl⟩ := hy
      exact hop_mul_mem_span hρ hKc hKo g h
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem span_hop_eq_top [ρ.IsIrreducible] [FiniteDimensional ℂ (fixedVectors ρ K)]
    [Nontrivial (fixedVectors ρ K)] :
    Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) = ⊤ := by
  have hone : (1 : Module.End ℂ (fixedVectors ρ K)) ∈
      Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) := by
    rw [← hop_one hρ hKc hKo]; exact Submodule.subset_span ⟨1, rfl⟩
  let A : Subalgebra ℂ (Module.End ℂ (fixedVectors ρ K)) :=
    Submodule.toSubalgebra _ hone (fun a b ha hb => span_hop_mul_mem hρ hKc hKo ha hb)
  have hirr : ∀ U : Submodule ℂ (fixedVectors ρ K),
      (∀ a : A, ∀ w ∈ U, A.val a w ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    right
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    have hT : ∀ g, hop ρ hρ hKc hKo g u ∈ U := fun g =>
      hU ⟨hop ρ hρ hKc hKo g, Submodule.subset_span ⟨g, rfl⟩⟩ u huU
    rw [eq_top_iff]
    intro w _
    have hu0' : (u : V) ≠ 0 := fun h => hu0 (Subtype.ext h)
    have hw := HeckeAlgebra.mem_span_orbit (ρ := ρ) hu0' (w : V)
    have hww : w = fixedProj ρ hρ hKc hKo (w : V) :=
      Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo w.2).symm
    rw [hww]
    have hle : Submodule.map (fixedProj ρ hρ hKc hKo)
        (Submodule.span ℂ (Set.range fun g => ρ g (u : V))) ≤ U := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      exact hT g
    exact hle ⟨_, hw, rfl⟩
  have hsurj := ReciprocityTheory.GC.burnside_surj_of_irred (k := ℂ) A.val hirr
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha⟩ := hsurj x
  rw [← ha]
  exact a.2

end DiscreteGroups.sglob.LConvU
