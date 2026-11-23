import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PiTensorSubmoduleEqTopOfAbsolutelyIrreducibleSta

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TensorDecomp

open GlobalTheory.Chain.IoLift Module

section Cyclic

variable {ι : Type} {W : Type} [AddCommGroup W] [Module ℂ W] {G : ι → Type}
  (a : ∀ i, G i → Module.End ℂ W)

def alg (i : ι) : Subalgebra ℂ (Module.End ℂ W) := Algebra.adjoin ℂ (Set.range (a i))

def ev (i : ι) (w : W) : alg a i →ₗ[ℂ] W :=
  LinearMap.applyₗ w ∘ₗ (alg a i).val.toLinearMap

def cyc (i : ι) (w : W) : Submodule ℂ W := LinearMap.range (ev a i w)

variable {a}

theorem mem_cyc {i : ι} {w v : W} : v ∈ cyc a i w ↔ ∃ α ∈ alg a i, α w = v := by
  simp only [cyc, LinearMap.mem_range]
  constructor
  · rintro ⟨⟨α, hα⟩, rfl⟩
    exact ⟨α, hα, rfl⟩
  · rintro ⟨α, hα, rfl⟩
    exact ⟨⟨α, hα⟩, rfl⟩

theorem gen_mem_alg (i : ι) (g : G i) : a i g ∈ alg a i := Algebra.subset_adjoin ⟨g, rfl⟩

theorem self_mem_cyc (i : ι) (w : W) : w ∈ cyc a i w := mem_cyc.2 ⟨1, (alg a i).one_mem, Module.End.one_apply w⟩

theorem apply_mem_cyc {i : ι} {w v : W} (hv : v ∈ cyc a i w) {β : Module.End ℂ W} (hβ : β ∈ alg a i) :
    β v ∈ cyc a i w := by
  obtain ⟨α, hα, rfl⟩ := mem_cyc.1 hv
  exact mem_cyc.2 ⟨β * α, (alg a i).mul_mem hβ hα, rfl⟩

theorem alg_stable {i : ι} (N : Submodule ℂ W) (hN : ∀ g, ∀ x ∈ N, a i g x ∈ N)
    {α : Module.End ℂ W} (hα : α ∈ alg a i) : ∀ x ∈ N, α x ∈ N := by
  unfold alg at hα
  induction hα using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact hN g
  | algebraMap r =>
    intro x hx
    rw [Module.algebraMap_end_apply]
    exact N.smul_mem r hx
  | add x y _ _ h1 h2 =>
    intro z hz
    rw [LinearMap.add_apply]
    exact N.add_mem (h1 z hz) (h2 z hz)
  | mul x y _ _ h1 h2 =>
    intro z hz
    rw [Module.End.mul_apply]
    exact h1 _ (h2 z hz)

theorem cyc_le {i : ι} {w : W} (N : Submodule ℂ W) (hN : ∀ g, ∀ x ∈ N, a i g x ∈ N) (hw : w ∈ N) :
    cyc a i w ≤ N := by
  intro v hv
  obtain ⟨α, hα, rfl⟩ := mem_cyc.1 hv
  exact alg_stable N hN hα w hw

theorem commute_alg (hc : ∀ i j, i ≠ j → ∀ g h, a i g * a j h = a j h * a i g) {i j : ι} (hij : i ≠ j)
    {α β : Module.End ℂ W} (hα : α ∈ alg a i) (hβ : β ∈ alg a j) : Commute α β := by
  unfold alg at hα hβ
  induction hβ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    induction hα using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      exact hc i j hij g h
    | algebraMap r => exact Algebra.commute_algebraMap_left r _
    | add y z _ _ h1 h2 => exact h1.add_left h2
    | mul y z _ _ h1 h2 => exact h1.mul_left h2
  | algebraMap r => exact Algebra.commute_algebraMap_right r _
  | add y z _ _ h1 h2 => exact h1.add_right h2
  | mul y z _ _ h1 h2 => exact h1.mul_right h2

theorem cyc_apply_le (hc : ∀ i j, i ≠ j → ∀ g h, a i g * a j h = a j h * a i g) {i j : ι} (hij : i ≠ j)
    {α : Module.End ℂ W} (hα : α ∈ alg a i) (w : W) : cyc a j (α w) ≤ (cyc a j w).map α := by
  intro v hv
  obtain ⟨β, hβ, rfl⟩ := mem_cyc.1 hv
  rw [Submodule.mem_map]
  refine ⟨β w, mem_cyc.2 ⟨β, hβ, rfl⟩, ?_⟩
  exact LinearMap.congr_fun (commute_alg hc hij hα hβ).eq w

theorem eq_cyc_of_min [Fintype ι] [FiniteDimensional ℂ W]
    (hc : ∀ i j, i ≠ j → ∀ g h, a i g * a j h = a j h * a i g) {w₀ : W}
    (hmin : ∀ w : W, w ≠ 0 → ∑ i, finrank ℂ (cyc a i w₀) ≤ ∑ i, finrank ℂ (cyc a i w))
    (i : ι) (N : Submodule ℂ W) (hle : N ≤ cyc a i w₀) (hN : ∀ g, ∀ x ∈ N, a i g x ∈ N) (hne : N ≠ ⊥) :
    N = cyc a i w₀ := by
  classical
  obtain ⟨w, hwN, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨α, hα, hαw⟩ := mem_cyc.1 (hle hwN)
  have h1 : cyc a i w ≤ N := cyc_le N hN hwN
  have hle' : ∀ j ∈ (Finset.univ : Finset ι), finrank ℂ (cyc a j w) ≤ finrank ℂ (cyc a j w₀) := by
    intro j _
    by_cases hij : i = j
    · subst hij
      exact Submodule.finrank_mono (h1.trans hle)
    · rw [← hαw]
      exact (Submodule.finrank_mono (cyc_apply_le hc hij hα w₀)).trans (Submodule.finrank_map_le _ _)
  have heq := (Finset.sum_eq_sum_iff_of_le hle').1 (le_antisymm (Finset.sum_le_sum hle') (hmin w hw0))
  have hi := Submodule.eq_of_le_of_finrank_eq (h1.trans hle) (heq i (Finset.mem_univ i))
  exact le_antisymm hle (hi ▸ h1)

theorem absIrr_of_irr {K : Type} [AddCommGroup K] [Module ℂ K] [FiniteDimensional ℂ K] [Nontrivial K]
    {H : Type} (b : H → Module.End ℂ K)
    (hb : ∀ N : Submodule ℂ K, (∀ g, ∀ x ∈ N, b g x ∈ N) → N = ⊥ ∨ N = ⊤) : AbsIrr b := by
  refine ⟨hb, fun T hT => ?_⟩
  obtain ⟨c, hcT⟩ := Module.End.exists_eigenvalue T
  refine ⟨c, ?_⟩
  have hstab : ∀ g, ∀ x ∈ LinearMap.ker (T - c • LinearMap.id), b g x ∈ LinearMap.ker (T - c • LinearMap.id) := by
    intro g x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have h := LinearMap.congr_fun (hT g) x
    have h2 := congrArg (b g) hx
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_sub, map_smul, map_zero] at hx h h2 ⊢
    rw [h]
    exact h2
  rcases hb _ hstab with h | h
  · exfalso
    obtain ⟨v, hv⟩ := hcT.exists_hasEigenvector
    have hv0 : v ≠ 0 := hv.2
    apply hv0
    have hmem : v ∈ LinearMap.ker (T - c • LinearMap.id) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        hv.apply_eq_smul, sub_self]
    rw [h] at hmem
    exact (Submodule.mem_bot ℂ).1 hmem
  · ext x
    have hx : x ∈ LinearMap.ker (T - c • LinearMap.id) := by
      rw [h]
      exact Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx
    exact hx

end Cyclic

section Prod

variable {ι : Type} [Fintype ι] {W : Type} [AddCommGroup W] [Module ℂ W] {G : ι → Type}
  {a : ∀ i, G i → Module.End ℂ W} (hc : ∀ i j, i ≠ j → ∀ g h, a i g * a j h = a j h * a i g)
  {w₀ : W} (s : ∀ i, cyc a i w₀ →ₗ[ℂ] alg a i)

def prodAt (x : ∀ i, cyc a i w₀) (S : Finset ι) : Module.End ℂ W :=
  S.noncommProd (fun i => (s i (x i) : Module.End ℂ W))
    (fun i _ j _ hij => commute_alg hc hij (s i (x i)).2 (s j (x j)).2)

theorem prodAt_univ_eq [DecidableEq ι] (x : ∀ i, cyc a i w₀) (i : ι) :
    prodAt hc s x Finset.univ = prodAt hc s x (Finset.univ.erase i) * (s i (x i) : Module.End ℂ W) := by
  unfold prodAt
  exact (Finset.noncommProd_erase_mul _ (Finset.mem_univ i) _ _).symm

theorem prodAt_erase_update {dec : DecidableEq ι} (x : ∀ i, cyc a i w₀) (i : ι) (v : cyc a i w₀) :
    prodAt hc s (Function.update x i v) (Finset.univ.erase i) = prodAt hc s x (Finset.univ.erase i) := by
  unfold prodAt
  apply Finset.noncommProd_congr rfl
  intro j hj
  show ((s j (Function.update x i v j) : alg a j) : Module.End ℂ W) = s j (x j)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem prodAt_erase_commute [DecidableEq ι] (x : ∀ i, cyc a i w₀) (i : ι) {α : Module.End ℂ W}
    (hα : α ∈ alg a i) : Commute α (prodAt hc s x (Finset.univ.erase i)) := by
  unfold prodAt
  apply Finset.noncommProd_commute
  intro j hj
  exact commute_alg hc (Finset.ne_of_mem_erase hj).symm hα (s j (x j)).2

variable (hs : ∀ i y, (s i y : Module.End ℂ W) w₀ = y)
include hs

theorem prodAt_univ_apply [DecidableEq ι] (x : ∀ i, cyc a i w₀) (i : ι) :
    prodAt hc s x Finset.univ w₀ = prodAt hc s x (Finset.univ.erase i) (x i : W) := by
  rw [prodAt_univ_eq hc s x i, Module.End.mul_apply, hs]

theorem prodAt_univ_update {dec : DecidableEq ι} (x : ∀ i, cyc a i w₀) (i : ι) (v : cyc a i w₀) :
    prodAt hc s (Function.update x i v) Finset.univ w₀ = prodAt hc s x (Finset.univ.erase i) (v : W) := by
  rw [prodAt_univ_apply hc s hs (Function.update x i v) i, prodAt_erase_update hc s, Function.update_self]

omit hs in
theorem prodAt_empty (x : ∀ i, cyc a i w₀) : prodAt hc s x ∅ = 1 := by
  unfold prodAt
  exact Finset.noncommProd_empty _ _

omit hs in
theorem prodAt_insert [DecidableEq ι] (x : ∀ i, cyc a i w₀) {j : ι} {S : Finset ι} (hj : j ∉ S) :
    prodAt hc s x (insert j S) = (s j (x j) : Module.End ℂ W) * prodAt hc s x S := by
  unfold prodAt
  exact Finset.noncommProd_insert_of_notMem _ _ _ _ hj

theorem prodAt_base (S : Finset ι) :
    prodAt hc s (fun i => ⟨w₀, self_mem_cyc i w₀⟩) S w₀ = w₀ := by
  classical
  refine Finset.induction_on S ?_ ?_
  · rw [prodAt_empty hc s, Module.End.one_apply]
  · intro j S hj ih
    rw [prodAt_insert hc s _ hj, Module.End.mul_apply, ih, hs]

omit hs in

def res (a : ∀ i, G i → Module.End ℂ W) (i : ι) (w₀ : W) (g : G i) : Module.End ℂ (cyc a i w₀) :=
  (a i g).restrict (fun _ hx => apply_mem_cyc hx (gen_mem_alg i g))

omit hs in
theorem res_apply (i : ι) (g : G i) (y : cyc a i w₀) : ((res a i w₀ g y : cyc a i w₀) : W) = a i g y := rfl

def mu : MultilinearMap ℂ (fun i => cyc a i w₀) W where
  toFun x := prodAt hc s x Finset.univ w₀
  map_update_add' x i u v := by
    rw [prodAt_univ_update hc s hs, prodAt_univ_update hc s hs, prodAt_univ_update hc s hs,
      Submodule.coe_add, map_add]
  map_update_smul' x i c u := by
    rw [prodAt_univ_update hc s hs, prodAt_univ_update hc s hs, Submodule.coe_smul, map_smul]

theorem mu_apply (x : ∀ i, cyc a i w₀) : mu hc s hs x = prodAt hc s x Finset.univ w₀ := rfl

theorem mu_update {dec : DecidableEq ι} (x : ∀ i, cyc a i w₀) (i : ι) (g : G i) :
    mu hc s hs (Function.update x i (res a i w₀ g (x i))) = a i g (mu hc s hs x) := by
  rw [mu_apply, mu_apply, prodAt_univ_update hc s hs, res_apply, prodAt_univ_apply hc s hs x i]
  exact (LinearMap.congr_fun (prodAt_erase_commute hc s x i (gen_mem_alg i g)).eq (x i : W)).symm

end Prod

theorem tensor_decomp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] (G : ι → Type) (a : ∀ i, G i → Module.End ℂ W), (∀ i j, i ≠ j → ∀ g h, a i g * a j h = a j h * a i g) → (∀ N : Submodule ℂ W, (∀ i g, ∀ x ∈ N, a i g x ∈ N) → N = ⊥ ∨ N = ⊤) → ∃ (X : ι → Type) (_ : ∀ i, AddCommGroup (X i)) (_ : ∀ i, Module ℂ (X i)) (_ : ∀ i, FiniteDimensional ℂ (X i)) (b : ∀ i, G i → Module.End ℂ (X i)) (m : ∀ i, X i →ₗ[ℂ] W) (e : (⨂[ℂ] i, X i) ≃ₗ[ℂ] W), (∀ i, Function.Injective (m i)) ∧ (∀ i g x, m i (b i g x) = a i g (m i x)) ∧ (∀ i, ∀ N : Submodule ℂ (X i), (∀ g, ∀ x ∈ N, b i g x ∈ N) → N = ⊥ ∨ N = ⊤) ∧ ∀ i g (x : ∀ i, X i), e (PiTensorProduct.tprod ℂ (Function.update x i (b i g (x i)))) = a i g (e (PiTensorProduct.tprod ℂ x)) := by
  intro ι _ _ W _ _ _ _ G a hc hirr
  classical
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : W)
  have hex : ∃ n, ∃ w : W, w ≠ 0 ∧ ∑ i, finrank ℂ (cyc a i w) = n := ⟨_, v₀, hv₀, rfl⟩
  obtain ⟨w₀, hw₀, hw₀n⟩ := Nat.find_spec hex
  have hmin : ∀ w : W, w ≠ 0 → ∑ i, finrank ℂ (cyc a i w₀) ≤ ∑ i, finrank ℂ (cyc a i w) := by
    intro w hw
    rw [hw₀n]
    exact Nat.find_min' hex ⟨w, hw, rfl⟩
  have hsec : ∀ i, ∃ t : cyc a i w₀ →ₗ[ℂ] alg a i, (ev a i w₀).rangeRestrict ∘ₗ t = LinearMap.id :=
    fun i => (ev a i w₀).rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
  choose s hs0 using hsec
  have hs : ∀ i y, (s i y : Module.End ℂ W) w₀ = y := by
    intro i y
    exact congrArg Subtype.val (LinearMap.congr_fun (hs0 i) y)
  have hirr_i : ∀ i, ∀ N : Submodule ℂ (cyc a i w₀), (∀ g, ∀ x ∈ N, res a i w₀ g x ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro i N hN
    by_cases hN0 : N = ⊥
    · exact Or.inl hN0
    right
    have hmap : N.map (cyc a i w₀).subtype = cyc a i w₀ := by
      refine eq_cyc_of_min hc hmin i _ (Submodule.map_subtype_le _ _) ?_ ?_
      · rintro g _ ⟨y, hy, rfl⟩
        exact ⟨res a i w₀ g y, hN g y hy, rfl⟩
      · intro h
        exact hN0 (Submodule.map_injective_of_injective (cyc a i w₀).injective_subtype
          (h.trans (Submodule.map_bot _).symm))
    apply Submodule.map_injective_of_injective (cyc a i w₀).injective_subtype
    rw [hmap, Submodule.map_subtype_top]
  have habs : ∀ i, AbsIrr (res a i w₀) := by
    intro i
    haveI : Nontrivial (cyc a i w₀) :=
      ⟨⟨⟨w₀, self_mem_cyc i w₀⟩, 0, fun h => hw₀ (congrArg Subtype.val h)⟩⟩
    exact absIrr_of_irr _ (hirr_i i)
  obtain ⟨e0, he0⟩ : ∃ e0 : (⨂[ℂ] i, cyc a i w₀) →ₗ[ℂ] W,
      ∀ x, e0 (PiTensorProduct.tprod ℂ x) = mu hc s hs x :=
    ⟨PiTensorProduct.lift (mu hc s hs), fun x => PiTensorProduct.lift.tprod x⟩
  have hint : ∀ i g, e0 ∘ₗ intersection_update_fsHerm_neg_one i (res a i w₀ g) = a i g ∘ₗ e0 := by
    intro i g
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, position_tprod, he0]
    exact mu_update hc s hs x i g
  have hbase : e0 (PiTensorProduct.tprod ℂ (fun i => (⟨w₀, self_mem_cyc i w₀⟩ : cyc a i w₀))) = w₀ := by
    rw [he0, mu_apply]
    exact prodAt_base hc s hs Finset.univ
  have hsurj : LinearMap.range e0 = ⊤ := by
    have hstab : ∀ i g, ∀ x ∈ LinearMap.range e0, a i g x ∈ LinearMap.range e0 := by
      rintro i g _ ⟨t, rfl⟩
      have h := LinearMap.congr_fun (hint i g) t
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
      exact LinearMap.mem_range.2 ⟨_, h⟩
    rcases hirr _ hstab with h | h
    · exfalso
      apply hw₀
      have hm : w₀ ∈ LinearMap.range e0 := ⟨_, hbase⟩
      rw [h] at hm
      exact (Submodule.mem_bot ℂ).1 hm
    · exact h
  have hker : LinearMap.ker e0 = ⊥ := by
    by_contra hne
    have hstab : ∀ i g, ∀ x ∈ LinearMap.ker e0, intersection_update_fsHerm_neg_one i (res a i w₀ g) x ∈ LinearMap.ker e0 := by
      intro i g x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have h := LinearMap.congr_fun (hint i g) x
      simp only [LinearMap.comp_apply] at h
      rw [h, hx, map_zero]
    have htop := GlobalTheory.TensorIrr.eq_top_of_stable ι (fun i => cyc a i w₀) G (fun i => res a i w₀) habs
      (LinearMap.ker e0) hstab hne
    apply hw₀
    rw [← hbase]
    have hm : PiTensorProduct.tprod ℂ (fun i => (⟨w₀, self_mem_cyc i w₀⟩ : cyc a i w₀)) ∈ LinearMap.ker e0 := by
      rw [htop]
      exact Submodule.mem_top
    exact LinearMap.mem_ker.1 hm
  let e := LinearEquiv.ofBijective e0 ⟨LinearMap.ker_eq_bot.1 hker, LinearMap.range_eq_top.1 hsurj⟩
  refine ⟨fun i => cyc a i w₀, fun i => inferInstance, fun i => inferInstance, fun i => inferInstance,
    fun i => res a i w₀, fun i => (cyc a i w₀).subtype, e, fun i => (cyc a i w₀).injective_subtype,
    fun i g x => rfl, hirr_i, ?_⟩
  intro i g x
  show e0 _ = a i g (e0 _)
  rw [he0, he0]
  exact mu_update hc s hs x i g

end GlobalTheory.TensorDecomp
