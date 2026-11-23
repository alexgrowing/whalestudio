import Mathlib
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable

noncomputable section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC

namespace GlobalTheory.FunctorialityH2

section Functor

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
variable {M'' : Type*} [AddCommGroup M''] [Module R M''] [TopologicalSpace M'']
  [IsTopologicalAddGroup M''] [ContinuousConstSMul R M'']
variable (rho : Representation R G M) (rho' : Representation R G M')
  (rho'' : Representation R G M'')

theorem map_H2_congr {u v : M →ₗ[R] M'} (huv : u = v) (hu : Continuous u)
    (hue : ∀ g m, u (rho g m) = rho' g (u m)) (hv : Continuous v)
    (hve : ∀ g m, v (rho g m) = rho' g (v m)) :
    mapH2 rho rho' u hu hue = mapH2 rho rho' v hv hve := by
  subst huv; rfl

theorem map_H2_id :
    mapH2 rho rho LinearMap.id continuous_id (fun _ _ => rfl) = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
  rfl

theorem map_H2_comp (u : M →ₗ[R] M') (hu : Continuous u)
    (hue : ∀ g m, u (rho g m) = rho' g (u m)) (v : M' →ₗ[R] M'') (hv : Continuous v)
    (hve : ∀ g m, v (rho' g m) = rho'' g (v m)) (hvu : Continuous (v ∘ₗ u))
    (hvue : ∀ g m, (v ∘ₗ u) (rho g m) = rho'' g ((v ∘ₗ u) m)) :
    mapH2 rho rho'' (v ∘ₗ u) hvu hvue =
      mapH2 rho' rho'' v hv hve ∘ₗ mapH2 rho rho' u hu hue := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
  rfl

theorem map_H2_zero (h0 : Continuous (0 : M →ₗ[R] M'))
    (h0e : ∀ g m, (0 : M →ₗ[R] M') (rho g m) = rho' g ((0 : M →ₗ[R] M') m)) :
    mapH2 rho rho' 0 h0 h0e = 0 := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
  rfl

theorem map_H2_add (u v : M →ₗ[R] M') (hu : Continuous u)
    (hue : ∀ g m, u (rho g m) = rho' g (u m)) (hv : Continuous v)
    (hve : ∀ g m, v (rho g m) = rho' g (v m)) (huv : Continuous (u + v))
    (huve : ∀ g m, (u + v) (rho g m) = rho' g ((u + v) m)) :
    mapH2 rho rho' (u + v) huv huve = mapH2 rho rho' u hu hue + mapH2 rho rho' v hv hve := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
  rfl

theorem map_H2_smul (c : R) (u : M →ₗ[R] M') (hu : Continuous u)
    (hue : ∀ g m, u (rho g m) = rho' g (u m)) (hcu : Continuous (c • u))
    (hcue : ∀ g m, (c • u) (rho g m) = rho' g ((c • u) m)) :
    mapH2 rho rho' (c • u) hcu hcue = c • mapH2 rho rho' u hu hue := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
  rfl

theorem map_H2_sum {ι : Type*} (s : Finset ι) (u : ι → M →ₗ[R] M') (hu : ∀ j, Continuous (u j))
    (hue : ∀ j g m, u j (rho g m) = rho' g (u j m))
    (hs : Continuous ((∑ j ∈ s, u j : M →ₗ[R] M') : M → M'))
    (hse : ∀ g m, (∑ j ∈ s, u j) (rho g m) = rho' g ((∑ j ∈ s, u j) m)) :
    mapH2 rho rho' (∑ j ∈ s, u j) hs hse = ∑ j ∈ s, mapH2 rho rho' (u j) (hu j) (hue j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact map_H2_zero rho rho' _ _
  | insert a s ha ih =>
    have hc : Continuous ((∑ j ∈ s, u j : M →ₗ[R] M') : M → M') := by
      have := continuous_finset_sum s (fun j _ => hu j)
      convert this using 1; ext x; simp
    have he : ∀ g m, (∑ j ∈ s, u j) (rho g m) = rho' g ((∑ j ∈ s, u j) m) := by
      intro g m; simp only [LinearMap.sum_apply, map_sum, hue]
    rw [map_H2_congr rho rho' (Finset.sum_insert ha) hs hse
        ((hu a).add hc) (fun g m => by simp only [LinearMap.add_apply, hue, he, map_add]),
      map_H2_add rho rho' _ _ (hu a) (hue a) hc he, ih hc he, Finset.sum_insert ha]

end Functor

section Phi

variable {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ)

theorem cont_span (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [ContinuousSMul O M] (m : M) : Continuous (LinearMap.toSpanSingleton O M m) :=
  continuous_id.smul continuous_const

theorem span_twist (M : Type) [AddCommGroup M] [Module O M] (m : M) (g : G) (a : O) :
    LinearMap.toSpanSingleton O M m (twist ε O g a) =
      twist ε M g (LinearMap.toSpanSingleton O M m a) := by
  show ((ε g : O) • a) • m = (ε g : O) • (a • m)
  rw [smul_assoc]

variable (z : H2 (twist ε O))

def phi (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul O M] [ContinuousSMul O M] : M →ₗ[O] H2 (twist ε M) where
  toFun m := mapH2 (twist ε O) (twist ε M) (LinearMap.toSpanSingleton O M m) (cont_span M m)
    (span_twist ε M m) z
  map_add' m m' := by
    rw [map_H2_congr (twist ε O) (twist ε M) (LinearMap.ext fun a => by simp [smul_add] :
        LinearMap.toSpanSingleton O M (m + m') =
          LinearMap.toSpanSingleton O M m + LinearMap.toSpanSingleton O M m')
      (cont_span M _) (span_twist ε M _) ((cont_span M m).add (cont_span M m'))
      (fun g a => by simp only [LinearMap.add_apply, span_twist, map_add]),
      map_H2_add _ _ _ _ (cont_span M m) (span_twist ε M m) (cont_span M m') (span_twist ε M m')]
    rfl
  map_smul' c m := by
    rw [map_H2_congr (twist ε O) (twist ε M) (LinearMap.ext fun a => by simp [smul_comm a c m] :
        LinearMap.toSpanSingleton O M (c • m) = c • LinearMap.toSpanSingleton O M m)
      (cont_span M _) (span_twist ε M _) ((cont_span M m).const_smul c)
      (fun g a => by simp only [LinearMap.smul_apply, span_twist, map_smul]),
      map_H2_smul _ _ c _ (cont_span M m) (span_twist ε M m)]
    rfl

theorem phi_apply (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [ContinuousSMul O M] (m : M) :
    phi ε z M m = mapH2 (twist ε O) (twist ε M) (LinearMap.toSpanSingleton O M m)
      (cont_span M m) (span_twist ε M m) z := rfl

theorem phi_natural (M M' : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [ContinuousSMul O M]
    [AddCommGroup M'] [Module O M'] [TopologicalSpace M']
    [IsTopologicalAddGroup M'] [ContinuousConstSMul O M'] [ContinuousSMul O M']
    (f : M →ₗ[O] M') (hf : Continuous f) (hfe : ∀ g m, f (twist ε M g m) = twist ε M' g (f m))
    (m : M) : mapH2 (twist ε M) (twist ε M') f hf hfe (phi ε z M m) = phi ε z M' (f m) := by
  rw [phi_apply, phi_apply, ← LinearMap.comp_apply,
    ← map_H2_comp (twist ε O) (twist ε M) (twist ε M') _ (cont_span M m) (span_twist ε M m) f hf hfe
      (hf.comp (cont_span M m)) (fun g a => by simp only [LinearMap.comp_apply, span_twist, hfe])]
  exact congrArg (fun L : H2 (twist ε O) →ₗ[O] H2 (twist ε M') => L z)
    (map_H2_congr _ _ (LinearMap.ext fun a => by simp) _ _ _ _)

theorem phi_self (a : O) : phi ε z O a = a • z := by
  rw [phi_apply, map_H2_congr (twist ε O) (twist ε O)
    (show LinearMap.toSpanSingleton O O a = a • LinearMap.id from
      LinearMap.ext fun b => by simp [mul_comm])
    _ _ (continuous_id.const_smul a) (fun g b => by
      show a * ((ε g : O) * b) = (ε g : O) * (a * b); ring),
    map_H2_smul _ _ a _ continuous_id (fun _ _ => rfl), map_H2_id]
  rfl

end Phi

section Retract

variable {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ) (z : H2 (twist ε O))

theorem twist_equiv {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (f : M →ₗ[O] M') (g : G) (m : M) : f (twist ε M g m) = twist ε M' g (f m) := by
  show f ((ε g : O) • m) = (ε g : O) • f m
  exact map_smul f _ m

theorem cont_sum {ι M M' : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [AddCommGroup M'] [Module O M'] [TopologicalSpace M'] [IsTopologicalAddGroup M']
    (s : Finset ι) (u : ι → M →ₗ[O] M') (hu : ∀ j, Continuous (u j)) :
    Continuous ((∑ j ∈ s, u j : M →ₗ[O] M') : M → M') := by
  have := continuous_finset_sum s (fun j _ => hu j)
  convert this using 1; ext x; simp

theorem bijective_of_retract (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [ContinuousSMul O M]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (N : ι → Type) [∀ j, AddCommGroup (N j)] [∀ j, Module O (N j)] [∀ j, TopologicalSpace (N j)]
    [∀ j, IsTopologicalAddGroup (N j)] [∀ j, ContinuousConstSMul O (N j)]
    [∀ j, ContinuousSMul O (N j)]
    (N' : κ → Type) [∀ i, AddCommGroup (N' i)] [∀ i, Module O (N' i)] [∀ i, TopologicalSpace (N' i)]
    [∀ i, IsTopologicalAddGroup (N' i)] [∀ i, ContinuousConstSMul O (N' i)]
    [∀ i, ContinuousSMul O (N' i)]
    (p : ∀ j, M →ₗ[O] N j) (s : ∀ j, N j →ₗ[O] M) (p' : ∀ i, M →ₗ[O] N' i)
    (s' : ∀ i, N' i →ₗ[O] M) (hp : ∀ j, Continuous (p j)) (hs : ∀ j, Continuous (s j))
    (hp' : ∀ i, Continuous (p' i)) (hs' : ∀ i, Continuous (s' i))
    (hid : ∀ m, ∑ j, s j (p j m) + ∑ i, s' i (p' i m) = m)
    (hN : ∀ j, Function.Bijective (phi ε z (N j)))
    (hN' : ∀ i, Function.Bijective (phi ε z (N' i))) :
    Function.Bijective (phi ε z M) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro m hm
    have h1 : ∀ j, p j m = 0 := fun j => (injective_iff_map_eq_zero _).1 (hN j).1 _ (by
      rw [← phi_natural ε z M (N j) (p j) (hp j) (twist_equiv ε (p j)), hm, map_zero])
    have h2 : ∀ i, p' i m = 0 := fun i => (injective_iff_map_eq_zero _).1 (hN' i).1 _ (by
      rw [← phi_natural ε z M (N' i) (p' i) (hp' i) (twist_equiv ε (p' i)), hm, map_zero])
    rw [← hid m]
    simp [h1, h2]
  · intro w
    choose n hn using fun j =>
      (hN j).2 (mapH2 (twist ε M) (twist ε (N j)) (p j) (hp j) (twist_equiv ε (p j)) w)
    choose n' hn' using fun i =>
      (hN' i).2 (mapH2 (twist ε M) (twist ε (N' i)) (p' i) (hp' i) (twist_equiv ε (p' i)) w)
    refine ⟨∑ j, s j (n j) + ∑ i, s' i (n' i), ?_⟩
    have k1 : ∀ j, phi ε z M (s j (n j)) = mapH2 (twist ε M) (twist ε M) (s j ∘ₗ p j)
        ((hs j).comp (hp j)) (twist_equiv ε _) w := by
      intro j
      rw [← phi_natural ε z (N j) M (s j) (hs j) (twist_equiv ε (s j)), hn j,
        map_H2_comp (twist ε M) (twist ε (N j)) (twist ε M) (p j) (hp j) (twist_equiv ε _) (s j)
          (hs j) (twist_equiv ε _)]
      rfl
    have k2 : ∀ i, phi ε z M (s' i (n' i)) = mapH2 (twist ε M) (twist ε M) (s' i ∘ₗ p' i)
        ((hs' i).comp (hp' i)) (twist_equiv ε _) w := by
      intro i
      rw [← phi_natural ε z (N' i) M (s' i) (hs' i) (twist_equiv ε (s' i)), hn' i,
        map_H2_comp (twist ε M) (twist ε (N' i)) (twist ε M) (p' i) (hp' i) (twist_equiv ε _) (s' i)
          (hs' i) (twist_equiv ε _)]
      rfl
    rw [map_add, map_sum, map_sum, Finset.sum_congr rfl (fun j _ => k1 j),
      Finset.sum_congr rfl (fun i _ => k2 i), ← LinearMap.sum_apply, ← LinearMap.sum_apply,
      ← map_H2_sum (twist ε M) (twist ε M) _ _ _ _ (cont_sum _ _ fun j => (hs j).comp (hp j))
        (twist_equiv ε _),
      ← map_H2_sum (twist ε M) (twist ε M) _ _ _ _ (cont_sum _ _ fun i => (hs' i).comp (hp' i))
        (twist_equiv ε _),
      ← LinearMap.add_apply,
      ← map_H2_add (twist ε M) (twist ε M) _ _ _ _ _ _
        ((cont_sum _ _ fun j => (hs j).comp (hp j)).add
          (cont_sum _ _ fun i => (hs' i).comp (hp' i))) (twist_equiv ε _),
      map_H2_congr (twist ε M) (twist ε M)
        (LinearMap.ext fun m => by simpa using hid m : (∑ j, s j ∘ₗ p j) + ∑ i, s' i ∘ₗ p' i =
          LinearMap.id) _ _ continuous_id (fun _ _ => rfl), map_H2_id]
    rfl

end Retract

end GlobalTheory.FunctorialityH2
