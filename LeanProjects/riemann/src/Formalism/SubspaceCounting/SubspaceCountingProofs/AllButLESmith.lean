import Formalism.SubspaceCounting.StatementD
import Formalism.SubspaceCounting.SubspaceCountingProofs.LengthLayers

noncomputable section

open scoped BigOperators
open Module

namespace Formalism.G0

namespace AllButLESmithP

variable {O M ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [AddCommGroup M] [Module O M] [Fintype ι]

theorem pow_succ_dvd_of_not_dvd {π : O} (hπ : Irreducible π) {a : O} {E : ℕ}
    (h : ¬ a ∣ π ^ E) : π ^ (E + 1) ∣ a := by
  by_cases ha : a = 0
  · simp [ha]
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  by_contra hc
  apply h
  have hk : k ≤ E := by
    by_contra hk
    apply hc
    rw [hu]
    exact Dvd.dvd.mul_left (pow_dvd_pow π (not_le.mp hk)) _
  rw [hu]
  exact (Units.mul_left_dvd).mpr (pow_dvd_pow π hk)

variable {P : Submodule O M} {n : ℕ}

theorem down (snf : Basis.SmithNormalForm P ι n) (π : O) (g E : ℕ) (S : Finset ι)
    (hS : ∀ j, j ∉ S → ∃ i, snf.f i = j ∧ snf.a i ∣ π ^ E) (hcard : S.card ≤ g) :
    AllButLE π ⊤ P g E := by
  classical
  refine ⟨S.image snf.bM, by simp, Finset.card_image_le.trans hcard, ?_⟩
  intro x _
  rw [← snf.bM.sum_repr x, Finset.smul_sum]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  by_cases hj : j ∈ S
  · apply Submodule.mem_sup_right
    rw [smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hj)))
  · obtain ⟨i, rfl, t, ht⟩ := hS j hj
    apply Submodule.mem_sup_left
    have : π ^ E • (snf.bM.repr x (snf.f i) • snf.bM (snf.f i)) =
        (snf.bM.repr x (snf.f i) * t) • (snf.bN i : M) := by
      rw [snf.snf i, smul_smul, smul_smul, ht]
      congr 1
      ring
    rw [this]
    exact Submodule.smul_mem _ _ (snf.bN i).2

theorem up (snf : Basis.SmithNormalForm P ι n) (π : O) (hπ : Irreducible π) (g E : ℕ)
    (S : Finset ι) (hS : ∀ i, snf.f i ∈ S → ¬ snf.a i ∣ π ^ E)
    (h : AllButLE π ⊤ P g E) : S.card ≤ g := by
  classical
  obtain ⟨C, -, hCg, hC⟩ := h
  let K : Ideal O := Ideal.span {π ^ (E + 1)}
  let φ : M →ₗ[O] (↥S → O ⧸ K) :=
    LinearMap.pi (fun j : ↥S => K.mkQ ∘ₗ snf.bM.coord (j : ι))
  have hφb : ∀ i, φ (snf.bN i : M) = 0 := by
    intro i
    funext j
    simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Basis.coord_apply, snf.snf i,
      map_smul, Basis.repr_self, Pi.zero_apply]
    rw [Finsupp.single_apply]
    split_ifs with hij
    · rw [← map_smul, smul_eq_mul, mul_one, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        Ideal.mem_span_singleton]
      have hmem : snf.f i ∈ S := by rw [hij]; exact j.2
      exact pow_succ_dvd_of_not_dvd hπ (hS i hmem)
    · simp
  have hφP : ∀ p ∈ P, φ p = 0 := by
    intro p hp
    have hsum := snf.bN.sum_repr ⟨p, hp⟩
    have hp' : p = ∑ i, snf.bN.repr ⟨p, hp⟩ i • (snf.bN i : M) := by
      have := congrArg Subtype.val hsum
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    rw [hp', map_sum]
    simp only [map_smul, hφb, smul_zero, Finset.sum_const_zero]
  have hsurj : Function.Surjective φ := by
    intro t
    choose r hr using fun j => K.mkQ_surjective (t j)
    refine ⟨snf.bM.equivFun.symm (fun k => if hk : k ∈ S then r ⟨k, hk⟩ else 0), ?_⟩
    funext j
    have hrep : snf.bM.repr (snf.bM.equivFun.symm
        (fun k => if hk : k ∈ S then r ⟨k, hk⟩ else 0)) (j : ι) = r j := by
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      simp
    simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Basis.coord_apply, hrep, hr]
  have hmemC : ∀ x : M, π ^ E • φ x ∈ Submodule.span O ((C.image φ : Finset _) : Set _) := by
    intro x
    obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp (hC x Submodule.mem_top)
    rw [← map_smul, ← hpw, map_add, hφP p hp, zero_add, Finset.coe_image, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hw
  have hkill : ∀ w : ↥S → O ⧸ K, π ^ (E + 1) • w = 0 := by
    intro w
    funext j
    obtain ⟨r, hr⟩ := K.mkQ_surjective (w j)
    rw [Pi.smul_apply, Pi.zero_apply, ← hr, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      smul_eq_mul, Ideal.mem_span_singleton]
    exact dvd_mul_right _ _

  have hker : Ideal.span {π} ≤ LinearMap.ker ((π ^ E) • K.mkQ) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show (π ^ E) • K.mkQ π = 0
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      ← pow_succ]
    exact Ideal.mem_span_singleton_self _
  let g0 : (O ⧸ Ideal.span {π}) →ₗ[O] (O ⧸ K) := (Ideal.span {π}).liftQ ((π ^ E) • K.mkQ) hker
  have hg0 : Function.Injective g0 := by
    rw [← LinearMap.ker_eq_bot]
    apply Submodule.ker_liftQ_eq_bot
    intro r hr
    rw [LinearMap.mem_ker, LinearMap.smul_apply, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mem_span_singleton, pow_succ] at hr
    rw [Ideal.mem_span_singleton]
    exact (mul_dvd_mul_iff_left (pow_ne_zero E hπ.ne_zero)).mp hr
  let ι' : (↥S → O ⧸ Ideal.span {π}) →ₗ[O] (↥S → O ⧸ K) :=
    LinearMap.pi (fun j : ↥S => g0 ∘ₗ LinearMap.proj j)
  have hinj : Function.Injective ι' := by
    intro u v huv
    funext j
    exact hg0 (congrFun huv j)
  have hV : LinearMap.range ι' ≤ Submodule.span O ((C.image φ : Finset _) : Set _) := by
    rintro _ ⟨u, rfl⟩
    choose r hr using fun j => (Ideal.span {π} : Submodule O O).mkQ_surjective (u j)
    obtain ⟨x, hx⟩ := hsurj (fun j => K.mkQ (r j))
    have : ι' u = π ^ E • φ x := by
      funext j
      rw [hx]
      simp only [ι', LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, ← hr,
        Pi.smul_apply, g0]
      rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.smul_apply]
    rw [this]
    exact hmemC x
  have hs : ∀ v ∈ LinearMap.range ι', π ^ 1 • v ∈ (⊥ : Submodule O (↥S → O ⧸ K)) := by
    rintro _ ⟨u, rfl⟩
    rw [Submodule.mem_bot]
    obtain ⟨r, hr⟩ : ∃ w, ι' u = π ^ E • w := by
      choose r hr using fun j => (Ideal.span {π} : Submodule O O).mkQ_surjective (u j)
      refine ⟨fun j => K.mkQ (r j), ?_⟩
      funext j
      simp only [ι', LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, ← hr,
        Pi.smul_apply, g0]
      rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.smul_apply]
    rw [hr, smul_smul, ← pow_add, add_comm]
    exact hkill r
  have hlay := LengthLayersP.layer π hπ (⊥ : Submodule O (↥S → O ⧸ K)) (LinearMap.range ι')
    bot_le (C.image φ) g 1 (Finset.card_image_le.trans hCg) hV hs
  rw [Module.length_bot, zero_add, ← (LinearEquiv.ofInjective ι' hinj).length_eq,
    Module.length_pi_of_fintype] at hlay
  simp only [LengthLayersP.length_residue π hπ, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul, mul_one] at hlay
  exact_mod_cast hlay

theorem key (snf : Basis.SmithNormalForm P ι n) (π : O) (hπ : Irreducible π) (g E : ℕ)
    (B : Finset (Fin n)) (hB : ∀ i, i ∈ B ↔ ¬ snf.a i ∣ π ^ E) :
    AllButLE π ⊤ P g E ↔ B.card + (Fintype.card ι - n) ≤ g := by
  classical
  let S : Finset ι := B.map snf.f ∪ (Finset.univ.map snf.f)ᶜ
  have hcard : S.card = B.card + (Fintype.card ι - n) := by
    rw [Finset.card_union_of_disjoint, Finset.card_map, Finset.card_compl, Finset.card_map,
      Finset.card_univ, Fintype.card_fin]
    rw [Finset.disjoint_left]
    intro j hj hj'
    rw [Finset.mem_compl] at hj'
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hj
    exact hj' (Finset.mem_map_of_mem _ (Finset.mem_univ i))
  have hin : ∀ i, snf.f i ∈ S → ¬ snf.a i ∣ π ^ E := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · obtain ⟨i', hi', he⟩ := Finset.mem_map.mp h
      rw [snf.f.injective he] at hi'
      exact (hB i).mp hi'
    · exact absurd (Finset.mem_map_of_mem _ (Finset.mem_univ i)) (Finset.mem_compl.mp h)
  have hout : ∀ j, j ∉ S → ∃ i, snf.f i = j ∧ snf.a i ∣ π ^ E := by
    intro j hj
    have h1 : j ∈ Finset.univ.map snf.f := by
      by_contra h
      exact hj (Finset.mem_union_right _ (Finset.mem_compl.mpr h))
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp h1
    refine ⟨i, rfl, ?_⟩
    by_contra h
    exact hj (Finset.mem_union_left _ (Finset.mem_map_of_mem _ ((hB i).mpr h)))
  rw [← hcard]
  exact ⟨up snf π hπ g E S hin, down snf π g E S hout⟩

end AllButLESmithP

theorem all_but_le_smith : AllButLESmith := by
  unfold AllButLESmith
  intro O M ι _ _ _ _ _ _ π hπ P n snf g E
  exact AllButLESmithP.key snf π hπ g E _ (fun i => by simp)

end Formalism.G0
