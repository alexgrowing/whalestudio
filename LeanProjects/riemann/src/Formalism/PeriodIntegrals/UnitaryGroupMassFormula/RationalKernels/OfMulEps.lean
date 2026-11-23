import Mathlib
import Formalism.PeriodIntegrals.SameFormAllLevels

noncomputable section

namespace PI.Dv.RK

open MonoidAlgebra

variable {K : Type} [Field K] {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G] {T : GoodSet K G}
  {EE : Type} [AddCommGroup EE] [Module ℂ EE] {ρE : Representation ℂ G EE}

lemma rep_apply {W : Type} [AddCommGroup W] [Module K W] (ρ : Representation K G W)
    (z : MonoidAlgebra K G) : ρ.asAlgebraHom z = ∑ g, z.coeff g • ρ g := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  exact Finsupp.sum_fintype _ _ (fun g => zero_smul _ _)

lemma of_mul_eps (P : Pair K G) (h : P.H) :
    MonoidAlgebra.of K G (h : G) * eps P = ((P.chi h : Kˣ) : K) • eps P := by
  unfold eps
  rw [mul_smul_comm, smul_comm ((P.chi h : Kˣ) : K)]
  congr 1
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (h : G)) _ _ fun x => ?_
  by_cases hx : x ∈ P.H
  · have hhx : (Equiv.mulLeft (h : G)) x ∈ P.H := P.H.mul_mem h.2 hx
    rw [dif_pos hx, dif_pos hhx, mul_smul_comm, smul_smul, ← map_mul (MonoidAlgebra.of K G)]
    congr 1
    have e : P.chi ⟨(Equiv.mulLeft (h : G)) x, hhx⟩ = P.chi h * P.chi ⟨x, hx⟩ := by
      rw [← map_mul]; rfl
    rw [e]
    simp only [mul_inv_rev, Units.val_mul]
    rw [mul_left_comm, Units.mul_inv, mul_one]
  · have hhx : (Equiv.mulLeft (h : G)) x ∉ P.H := fun hm => hx (by
      have := P.H.mul_mem (P.H.inv_mem h.2) hm
      simpa using this)
    rw [dif_neg hx, dif_neg hhx, mul_zero, smul_zero]

variable (M : GMap K σ G T EE ρE)

def L (z : MonoidAlgebra K G) : Module.End ℂ M.V := ∑ g, σ (z.coeff g) • M.rho g

lemma L_j (z : MonoidAlgebra K G) (x : M.VK) :
    L M z (M.j x) = M.j (M.rhoK.asAlgebraHom z x) := by
  simp only [L, rep_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    LinearMap.map_smulₛₗ, M.j_eq]

lemma L_mul (a b : MonoidAlgebra K G) : L M (a * b) = L M a * L M b :=
  LinearMap.ext_on_range M.j_span fun x => by
    rw [Module.End.mul_apply, L_j, L_j, L_j, map_mul, Module.End.mul_apply]

lemma L_eG : L M (eG T) = 1 :=
  LinearMap.ext_on_range M.j_span fun x => by
    rw [L_j, M.good, Module.End.one_apply, Module.End.one_apply]

lemma L_zero : L M 0 = 0 := by simp [L]

lemma L_add (a b : MonoidAlgebra K G) : L M (a + b) = L M a + L M b := by
  simp [L, add_smul, Finset.sum_add_distrib]

lemma L_neg (a : MonoidAlgebra K G) : L M (-a) = - L M a := by
  simp [L, neg_smul, Finset.sum_neg_distrib]

lemma L_ker (z : MonoidAlgebra K G) {v : M.V} (hv : v ∈ LinearMap.ker M.io) :
    L M z v ∈ LinearMap.ker M.io := by
  rw [L, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun g _ => ?_
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [LinearMap.mem_ker] at hv ⊢
  rw [M.io_eq, hv, map_zero]

lemma L_eps_mem (P : Pair K G) (v : M.V) : L M (eps P) v ∈ eigP σ P M.rho := by
  rw [eigP, Submodule.mem_iInf]
  intro h
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  have hK : M.rhoK (h : G) * M.rhoK.asAlgebraHom (eps P) =
      ((P.chi h : Kˣ) : K) • M.rhoK.asAlgebraHom (eps P) := by
    rw [← Representation.asAlgebraHom_of, ← map_mul, of_mul_eps, map_smul]
  have hL : M.rho (h : G) * L M (eps P) = σ ((P.chi h : Kˣ) : K) • L M (eps P) := by
    refine LinearMap.ext_on_range M.j_span fun x => ?_
    have hx := LinearMap.congr_fun hK x
    rw [Module.End.mul_apply, LinearMap.smul_apply] at hx
    rw [Module.End.mul_apply, L_j, ← M.j_eq, hx, LinearMap.smul_apply, L_j, LinearMap.map_smulₛₗ]
  exact LinearMap.congr_fun hL v

theorem rat_ker (P0 : Pair K G)
    (hF : eG T ∈ AddSubgroup.closure {w | ∃ a b : MonoidAlgebra K G, w = a * eps P0 * b})
    (hR : M.IsRat (LinearMap.ker M.io ⊓ eigP σ P0 M.rho)) : M.IsRat (LinearMap.ker M.io) := by
  unfold GMap.IsRat at hR ⊢
  have hRN : Submodule.span ℂ (M.j '' {x | M.j x ∈ LinearMap.ker M.io}) ≤ LinearMap.ker M.io :=
    Submodule.span_le.mpr (by rintro _ ⟨x, hx, rfl⟩; exact hx)
  have hLa : ∀ a : MonoidAlgebra K G, ∀ u ∈ LinearMap.ker M.io ⊓ eigP σ P0 M.rho,
      L M a u ∈ Submodule.span ℂ (M.j '' {x | M.j x ∈ LinearMap.ker M.io}) := by
    intro a u hu
    rw [← hR] at hu
    have hle : Submodule.span ℂ (M.j '' {x | M.j x ∈ LinearMap.ker M.io ⊓ eigP σ P0 M.rho}) ≤
        (Submodule.span ℂ (M.j '' {x | M.j x ∈ LinearMap.ker M.io})).comap (L M a) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, L_j]
      apply Submodule.subset_span
      refine ⟨_, ?_, rfl⟩
      show M.j _ ∈ LinearMap.ker M.io
      rw [← L_j]
      exact L_ker M a hx.1
    exact hle hu
  have hZ : ∀ v ∈ LinearMap.ker M.io,
      L M (eG T) v ∈ Submodule.span ℂ (M.j '' {x | M.j x ∈ LinearMap.ker M.io}) := by
    refine AddSubgroup.closure_induction (p := fun z _ => ∀ v ∈ LinearMap.ker M.io,
      L M z v ∈ Submodule.span ℂ (M.j '' {x | M.j x ∈ LinearMap.ker M.io})) ?_ ?_ ?_ ?_ hF
    · rintro z ⟨a, b, rfl⟩ v hv
      rw [L_mul, L_mul, Module.End.mul_apply, Module.End.mul_apply]
      exact hLa a _ ⟨L_ker M _ (L_ker M b hv), L_eps_mem M P0 _⟩
    · intro v _
      rw [L_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy v hv
      rw [L_add, LinearMap.add_apply]
      exact Submodule.add_mem _ (hx v hv) (hy v hv)
    · intro x _ hx v hv
      rw [L_neg, LinearMap.neg_apply]
      exact Submodule.neg_mem _ (hx v hv)
  refine le_antisymm hRN fun v hv => ?_
  have := hZ v hv
  rwa [L_eG, Module.End.one_apply] at this

theorem form_eq (P0 : Pair K G)
    (hF : eG T ∈ AddSubgroup.closure {w | ∃ a b : MonoidAlgebra K G, w = a * eps P0 * b}) :
    M.form 1 = (AddSubgroup.closure {z | ∃ g, ∃ y ∈ M.form (eps P0), z = ρE g y} : Set EE) := by
  set Y := AddSubgroup.closure {z | ∃ g, ∃ y ∈ M.form (eps P0), z = ρE g y} with hY
  have hgen : ∀ (a : MonoidAlgebra K G) (w : M.VK),
      M.io (M.j (M.rhoK.asAlgebraHom a (M.rhoK.asAlgebraHom (eps P0) w))) ∈ Y := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      intro w
      apply AddSubgroup.subset_closure
      refine ⟨g, _, ⟨w, rfl⟩, ?_⟩
      rw [Representation.asAlgebraHom_of, M.j_eq, M.io_eq]
    | add a b ha hb =>
      intro w
      rw [map_add, LinearMap.add_apply, map_add, map_add]
      exact Y.add_mem (ha w) (hb w)
    | smul r a ha =>
      intro w
      rw [map_smul, LinearMap.smul_apply, ← map_smul (M.rhoK.asAlgebraHom a),
        ← map_smul (M.rhoK.asAlgebraHom (eps P0))]
      exact ha (r • w)
  have hall : ∀ x : M.VK, M.io (M.j (M.rhoK.asAlgebraHom (eG T) x)) ∈ Y := by
    refine AddSubgroup.closure_induction (p := fun z _ => ∀ x : M.VK,
      M.io (M.j (M.rhoK.asAlgebraHom z x)) ∈ Y) ?_ ?_ ?_ ?_ hF
    · rintro z ⟨a, b, rfl⟩ x
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      exact hgen a _
    · intro x
      rw [map_zero, LinearMap.zero_apply, map_zero, map_zero]
      exact Y.zero_mem
    · intro x y _ _ hx hy w
      rw [map_add, LinearMap.add_apply, map_add, map_add]
      exact Y.add_mem (hx w) (hy w)
    · intro x _ hx w
      rw [map_neg, LinearMap.neg_apply, map_neg, map_neg]
      exact Y.neg_mem (hx w)
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    have := hall x
    rw [M.good] at this
    simpa using this
  · intro z hz
    have hle : Y ≤ (M.io.toAddMonoidHom.comp M.j.toAddMonoidHom).range := by
      rw [hY, AddSubgroup.closure_le]
      rintro _ ⟨g, _, ⟨w, rfl⟩, rfl⟩
      exact ⟨M.rhoK g (M.rhoK.asAlgebraHom (eps P0) w), by simp [M.j_eq, M.io_eq]⟩
    obtain ⟨x, hx⟩ := hle hz
    exact ⟨x, by simpa using hx⟩

end PI.Dv.RK
