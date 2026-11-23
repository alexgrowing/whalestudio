import Mathlib
import GroundTheory.TateCohomology.InducedNorm
import GroundTheory.TateCohomology.TateAddEquivAbelianizationTateClass
import GroundTheory.TateCohomology.PGroupFixed
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits groupHomology Representation Finsupp
open scoped MonoidAlgebra

universe u

section Naturality

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G} (f : A ⟶ B)

theorem d₁₀_mapRange (y : G →₀ A) :
    d₁₀ B (Finsupp.mapRange.linearMap f.hom.toLinearMap y) = f.hom (d₁₀ A y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single g a =>
    rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, d₁₀_single, d₁₀_single,
      map_sub, Rep.hom_comm_apply]
    rfl

theorem d₂₁_mapRange (c : G × G →₀ A) :
    d₂₁ B (Finsupp.mapRange.linearMap f.hom.toLinearMap c) =
      Finsupp.mapRange.linearMap f.hom.toLinearMap (d₂₁ A c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single g a =>
    rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, d₂₁_single, d₂₁_single,
      map_add, map_sub, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.mapRange_single,
      Finsupp.mapRange_single,
      show f.hom.toLinearMap (A.ρ g.1⁻¹ a) = B.ρ g.1⁻¹ (f.hom.toLinearMap a) from
        Rep.hom_comm_apply f g.1⁻¹ a]

end Naturality

section Chains

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G}

theorem d₁₀_apply_eq_sum (z : G →₀ A) :
    d₁₀ A z = ∑ g ∈ z.support, (A.ρ g⁻¹ (z g) - z g) := by
  change (Finsupp.lsum k fun g => A.ρ g⁻¹ - LinearMap.id) z = _
  rw [Finsupp.lsum_apply, Finsupp.sum]
  rfl

theorem exists_chain_ker_of_isZero_groupHomology_one (f : A ⟶ B)
    (hsurj : Function.Surjective f.hom) (hB : IsZero (groupHomology B 1)) {x : A}
    (hx : f.hom x = 0) (hxI : x ∈ Coinvariants.ker A.ρ) :
    ∃ z : G →₀ A, (∀ g, f.hom (z g) = 0) ∧ d₁₀ A z = x := by
  have hsurj' : Function.Surjective f.hom.toLinearMap := hsurj
  obtain ⟨y, hy⟩ : x ∈ LinearMap.range (d₁₀ A).hom := by
    rw [range_d₁₀_eq_coinvariantsKer]
    exact hxI
  let L := Finsupp.mapRange.linearMap (α := G) f.hom.toLinearMap
  have hY : L y ∈ cycles₁ B := by
    change d₁₀ B (L y) = 0
    rw [d₁₀_mapRange f y]
    change f.hom (d₁₀ A y) = 0
    rw [show d₁₀ A y = x from hy]
    exact hx
  have h0 : H1π B ⟨L y, hY⟩ = 0 :=
    @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero hB) _ _
  obtain ⟨c, hc⟩ := (H1π_eq_zero_iff _).mp h0
  obtain ⟨c', rfl⟩ := Finsupp.mapRange_surjective f.hom.toLinearMap (map_zero _) hsurj' c
  refine ⟨y - d₂₁ A c', fun g => ?_, ?_⟩
  · have h2 : L (d₂₁ A c') = L y := (d₂₁_mapRange f c').symm.trans hc
    have h4 : L (y - d₂₁ A c') = 0 := by
      have h5 : L (y - d₂₁ A c') = L y - L (d₂₁ A c') := map_sub L y _
      rw [h5, h2, sub_self]
    have := congrArg (fun w => w g) h4
    simpa [L] using this
  · have h3 : d₁₀ A (d₂₁ A c') = 0 := by simp
    have h5 : d₁₀ A (y - d₂₁ A c') = d₁₀ A y - d₁₀ A (d₂₁ A c') := map_sub (d₁₀ A).hom y _
    rw [h5, h3, sub_zero]
    exact hy

end Chains

section PGroup

variable {k G : Type u} [Field k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]

theorem injective_of_isZero_groupHomology_one (hG : IsPGroup p G) {A B : Rep.{u} k G} (f : A ⟶ B)
    (hsurj : Function.Surjective f.hom) (hB : IsZero (groupHomology B 1))
    (hker : ∀ x, f.hom x = 0 → x ∈ Coinvariants.ker A.ρ) : Function.Injective f.hom := by
  let K := LinearMap.ker f.hom.toLinearMap
  have hK : ∀ g, K ≤ K.comap (A.ρ g) := fun g x hx => by
    have hx' : f.hom x = 0 := LinearMap.mem_ker.mp hx
    refine LinearMap.mem_ker.mpr ?_
    change f.hom (A.ρ g x) = 0
    rw [Rep.hom_comm_apply, hx', map_zero]
  let ρK : @Representation k G K _ _ AddCommGroup.toAddCommMonoid _ := A.ρ.subrepresentation K hK
  have hKI : Coinvariants.ker (k := k) (G := G) (V := K) ρK = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx0 : f.hom x = 0 := LinearMap.mem_ker.mp hx
    obtain ⟨z, hz, hdz⟩ := exists_chain_ker_of_isZero_groupHomology_one f hsurj hB hx0 (hker x hx0)
    have hzK : ∀ g, z g ∈ K := fun g => LinearMap.mem_ker.mpr (hz g)
    have hmem : (⟨x, hx⟩ : K) = ∑ g ∈ z.support, (ρK g⁻¹ ⟨z g, hzK g⟩ - ⟨z g, hzK g⟩) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      change x = _
      rw [← hdz, d₁₀_apply_eq_sum]
      rfl
    rw [hmem]
    exact Submodule.sum_mem _ fun g _ => Coinvariants.sub_mem_ker g⁻¹ _
  have hKs : Subsingleton K := by
    apply subsingleton_of_coinvariantsKer_eq_top hG ρK
    exact hKI
  intro x y hxy
  have hxy' : x - y ∈ K := LinearMap.mem_ker.mpr (by
    change f.hom (x - y) = 0
    rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp (congrArg Subtype.val (Subsingleton.elim (⟨x - y, hxy'⟩ : K) 0))

theorem exists_iso_free_of_isZero_groupHomology_one (hG : IsPGroup p G) (M : Rep.{u} k G)
    (hM : IsZero (groupHomology M 1)) : ∃ ι : Type u, Nonempty (Rep.free k G ι ≅ M) := by
  classical

  let ι := Module.Free.ChooseBasisIndex k (Coinvariants M.ρ)
  let b : Module.Basis ι k (Coinvariants M.ρ) := Module.Free.chooseBasis k (Coinvariants M.ρ)
  choose e he using fun i => Coinvariants.mk_surjective M.ρ (b i)
  let π : Rep.free k G ι ⟶ M := Rep.freeLift (k := k) (G := G) (A := M) e
  have hπ : ∀ i g r, π.hom (single i (MonoidAlgebra.single g r)) = r • M.ρ g (e i) :=
    fun i g r => by simp [π]

  have hsurj : Function.Surjective π.hom := by
    have hr : LinearMap.range π.hom.toLinearMap = ⊤ := by
      apply eq_top_of_sup_coinvariantsKer_eq_top hG M.ρ
      · rintro g _ ⟨y, rfl⟩
        exact LinearMap.mem_range.mpr ⟨(Rep.free k G ι).ρ g y, Rep.hom_comm_apply π g y⟩
      · rw [eq_top_iff]
        intro x _
        have hx : Coinvariants.mk M.ρ x ∈ Submodule.span k (Set.range b) :=
          b.span_eq ▸ Submodule.mem_top
        have hmap : Submodule.span k (Set.range b) ≤
            (LinearMap.range π.hom.toLinearMap).map (Coinvariants.mk M.ρ) := by
          rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          exact Submodule.mem_map.mpr ⟨e i, LinearMap.mem_range.mpr
            ⟨single i (MonoidAlgebra.single 1 1), by simpa using hπ i 1 1⟩, he i⟩
        obtain ⟨w, hw, hwx⟩ := Submodule.mem_map.mp (hmap hx)
        have hxw : x - w ∈ Coinvariants.ker M.ρ := (Coinvariants.mk_eq_iff M.ρ).mp hwx.symm
        rw [show x = w + (x - w) by abel]
        exact Submodule.add_mem_sup hw hxw
    exact LinearMap.range_eq_top.mp hr

  let lam : M.V →ₗ[k] (ι →₀ k) := b.repr.toLinearMap ∘ₗ Coinvariants.mk M.ρ
  let s : (ι →₀ k) →ₗ[k] (ι →₀ k[G]) := Finsupp.mapRange.linearMap (MonoidAlgebra.lsingle 1)
  have hlam : ∀ y, y - s (lam (π.hom y)) ∈ Coinvariants.ker (Representation.free k G ι) := by
    intro y
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, add_sub_add_comm]
      exact add_mem h₁ h₂
    | single i a =>
      induction a using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a₁ a₂ h₁ h₂ =>
        rw [Finsupp.single_add, map_add, map_add, map_add, add_sub_add_comm]
        exact add_mem h₁ h₂
      | single g r =>
        refine Coinvariants.mem_ker_of_eq g (single i (MonoidAlgebra.single 1 r)) _ ?_
        rw [hπ]
        simp [lam, s, he]
  have hker : ∀ x, π.hom x = 0 → x ∈ Coinvariants.ker (Rep.free k G ι).ρ := fun x hx => by
    simpa [hx] using hlam x

  have hinj : Function.Injective π.hom :=
    injective_of_isZero_groupHomology_one hG π hsurj hM hker
  let eqv : (Representation.free k G ι).Equiv M.ρ :=
    Representation.Equiv.mk (LinearEquiv.ofBijective π.hom.toLinearMap ⟨hinj, hsurj⟩) fun g =>
      LinearMap.ext fun y => Rep.hom_comm_apply π g y
  exact ⟨ι, ⟨Rep.mkIso eqv⟩⟩

theorem free_asModule_of_iso_free {k G : Type u} [CommRing k] [Group G] {M : Rep.{u} k G}
    {ι : Type u} (e : Rep.free k G ι ≅ M) : Module.Free k[G] M.ρ.asModule := by
  let φ := Representation.equivOfIso e
  have := Representation.free_asModule_free k G ι
  exact Module.Free.of_equiv (LinearEquiv.ofLinearMap
    (IntertwiningMap.equivLinearMapAsModule (ρ := (Rep.free k G ι).ρ) (σ := M.ρ) φ.toIntertwiningMap)
    (IntertwiningMap.equivLinearMapAsModule (ρ := M.ρ) (σ := (Rep.free k G ι).ρ)
      φ.symm.toIntertwiningMap)
    (LinearMap.ext fun x => φ.apply_symm_apply x) (LinearMap.ext fun x => φ.symm_apply_apply x))

end PGroup

end GroundTheory.GroupCoh
