import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.MatrixCoeff
import GroundTheory.AutomorphicForms.TensorProductTheorem.Irreducible
import GroundTheory.AutomorphicForms.TensorProductTheorem.LocalComponent

noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open Filter Function Module Set

open scoped RestrictedProduct

variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] {K : ∀ v, Subgroup (G v)}

section Group

variable [DecidableEq ι]

variable (K) in

def singleHom (v : ι) : G v →* Πʳ w, [G w, K w] where
  toFun := RestrictedProduct.mulSingle K v
  map_one' := RestrictedProduct.mulSingle_one K v
  map_mul' x y := RestrictedProduct.mulSingle_mul K v x y

theorem singleHom_apply_self (v : ι) (x : G v) : singleHom K v x v = x :=
  RestrictedProduct.mulSingle_eq_same K v x

theorem singleHom_apply_of_ne {v w : ι} (x : G v) (h : w ≠ v) : singleHom K v x w = 1 :=
  RestrictedProduct.mulSingle_eq_of_ne K x h

theorem commute_of_forall {a b : Πʳ w, [G w, K w]} (h : ∀ w, a w = 1 ∨ b w = 1) :
    a * b = b * a := by
  ext w
  simp only [RestrictedProduct.mul_apply]
  rcases h w with h | h <;> simp [h]

def eraseAt (v : ι) (g : Πʳ w, [G w, K w]) : Πʳ w, [G w, K w] :=
  (singleHom K v (g v))⁻¹ * g

theorem eraseAt_apply_self (v : ι) (g : Πʳ w, [G w, K w]) : eraseAt v g v = 1 := by
  simp [eraseAt, RestrictedProduct.mul_apply, RestrictedProduct.inv_apply, singleHom_apply_self]

theorem eraseAt_apply_of_ne {v w : ι} (g : Πʳ w, [G w, K w]) (h : w ≠ v) :
    eraseAt v g w = g w := by
  simp [eraseAt, RestrictedProduct.mul_apply, RestrictedProduct.inv_apply,
    singleHom_apply_of_ne _ h]

theorem single_mul_eraseAt (v : ι) (g : Πʳ w, [G w, K w]) :
    singleHom K v (g v) * eraseAt v g = g := by
  simp [eraseAt]

theorem eraseAt_mem_boxSubgroup {K' : ∀ v, Subgroup (G v)} (v : ι) {g : Πʳ w, [G w, K w]}
    (hg : g ∈ boxSubgroup K K') : eraseAt v g ∈ boxSubgroup K K' := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [eraseAt_apply_self]
    exact (K' w).one_mem
  · rw [eraseAt_apply_of_ne _ hw]
    exact hg w

theorem singleHom_mem_boxSubgroup {K' : ∀ v, Subgroup (G v)} {v : ι} {x : G v}
    (hx : x ∈ K' v) : singleHom K v x ∈ boxSubgroup K K' := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [singleHom_apply_self]
    exact hx
  · rw [singleHom_apply_of_ne _ hw]
    exact (K' w).one_mem

theorem commute_singleHom {v : ι} (x : G v) {b : Πʳ w, [G w, K w]} (hb : b v = 1) :
    singleHom K v x * b = b * singleHom K v x :=
  commute_of_forall fun w => by
    by_cases hw : w = v
    · subst hw; exact Or.inr hb
    · exact Or.inl (singleHom_apply_of_ne _ hw)

end Group

variable [∀ v, TopologicalSpace (G v)] [∀ v, IsTopologicalGroup (G v)]
  [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)] [∀ v, TotallyDisconnectedSpace (G v)]
  [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))] [hKc : ∀ v, CompactSpace (K v)]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (Πʳ v, [G v, K v]) V}
  (hρ : IsSmooth ρ) {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
  (hK'o : ∀ v, IsOpen (K' v : Set (G v))) (hK'e : ∀ᶠ v in cofinite, K' v = K v)

section Window

variable [DecidableEq ι]

omit hK'c hK'o hK'e in

theorem apply_eq_apply_single (v : ι) {u : V}
    (hu : ∀ h ∈ boxSubgroup K K', h v = 1 → ρ h u = u) {h : Πʳ w, [G w, K w]}
    (hh : h ∈ boxSubgroup K K') : ρ h u = ρ (singleHom K v (h v)) u := by
  conv_lhs => rw [← single_mul_eraseAt v h]
  rw [map_mul, Module.End.mul_apply, hu _ (eraseAt_mem_boxSubgroup v hh) (eraseAt_apply_self v h)]

omit hK'c hK'o hK'e in

theorem apply_single_fixed (v : ι) (x : G v) {m : V} (hm : m ∈ fixedVectors ρ (boxSubgroup K K'))
    {h : Πʳ w, [G w, K w]} (hh : h ∈ boxSubgroup K K') (hv : h v = 1) :
    ρ h (ρ (singleHom K v x) m) = ρ (singleHom K v x) m := by
  rw [← Module.End.mul_apply, ← map_mul, ← commute_singleHom x hv, map_mul, Module.End.mul_apply,
    hm h hh]

include hK'c hK'o hK'e in

theorem heckeOp_single_mul (v : ι) (x : G v) {b : Πʳ w, [G w, K w]} (hb : b v = 1) :
    heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)
        (singleHom K v x * b) =
      heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)
          (singleHom K v x) *
        heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e) b := by
  ext m
  rw [Module.End.mul_apply, heckeOp_mul_apply]
  intro h hh
  refine ⟨eraseAt v h, eraseAt_mem_boxSubgroup v hh, ?_, ?_⟩
  · exact (commute_singleHom x (eraseAt_apply_self v h)).symm
  · have h1 : (eraseAt v h)⁻¹ * h = singleHom K v (h v) := by
      have hc := commute_singleHom (K := K) (h v) (eraseAt_apply_self v h)
      calc (eraseAt v h)⁻¹ * h = (eraseAt v h)⁻¹ * (singleHom K v (h v) * eraseAt v h) := by
            rw [single_mul_eraseAt]
        _ = singleHom K v (h v) := by rw [hc, inv_mul_cancel_left]
    rw [h1]
    exact commute_singleHom (h v) hb

def placeOps (v : ι) : Set (End ℂ (fixedVectors ρ (boxSubgroup K K'))) :=
  range fun x : G v => heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e)
    (isOpen_boxSubgroup hK'o hK'e) (singleHom K v x)

theorem commute_placeOps {v w : ι} (hvw : v ≠ w) :
    ∀ a ∈ placeOps hρ hK'c hK'o hK'e v, ∀ b ∈ placeOps hρ hK'c hK'o hK'e w, Commute a b := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  have h1 := heckeOp_single_mul hρ hK'c hK'o hK'e v x (b := singleHom K w y)
    (singleHom_apply_of_ne y hvw)
  have h2 := heckeOp_single_mul hρ hK'c hK'o hK'e w y (b := singleHom K v x)
    (singleHom_apply_of_ne x hvw.symm)
  show _ * _ = _ * _
  rw [← h1, ← h2, commute_singleHom x (singleHom_apply_of_ne y hvw)]

theorem heckeOp_mem_adjoin (s : Finset ι) {g : Πʳ w, [G w, K w]} (hg : ∀ v ∉ s, g v ∈ K' v) :
    heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e) g ∈
      Algebra.adjoin ℂ (⋃ v ∈ s, placeOps hρ hK'c hK'o hK'e v) := by
  induction s using Finset.induction_on generalizing g with
  | empty =>
    rw [heckeOp_of_mem _ _ _ (show g ∈ boxSubgroup K K' from fun v => hg v (Finset.notMem_empty v))]
    exact Subalgebra.one_mem _
  | insert a s has ih =>
    have herase : ∀ v ∉ s, eraseAt a g v ∈ K' v := by
      intro v hv
      by_cases hva : v = a
      · subst hva; rw [eraseAt_apply_self]; exact (K' v).one_mem
      · rw [eraseAt_apply_of_ne _ hva]
        exact hg v (by simp [hva, hv])
    have hmono : Algebra.adjoin ℂ (⋃ v ∈ s, placeOps hρ hK'c hK'o hK'e v) ≤
        Algebra.adjoin ℂ (⋃ v ∈ insert a s, placeOps hρ hK'c hK'o hK'e v) :=
      Algebra.adjoin_mono (biUnion_subset_biUnion_left (by simp))
    rw [← single_mul_eraseAt a g, heckeOp_single_mul hρ hK'c hK'o hK'e a (g a)
      (eraseAt_apply_self a g)]
    refine Subalgebra.mul_mem _ (Algebra.subset_adjoin ?_) (hmono (ih herase))
    exact mem_biUnion (Finset.mem_insert_self a s) ⟨g a, rfl⟩

theorem fixedProj_single_eq (v : ι) (hρv : IsSmooth (ρ.comp (singleHom K v))) {u : V}
    (hu : ∀ h ∈ boxSubgroup K K', h v = 1 → ρ h u = u) :
    (fixedProj (ρ.comp (singleHom K v)) hρv (hK'c v) (hK'o v) u : V) =
      fixedProj ρ hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e) u :=
  fixedProj_comp_eq (singleHom K v) hρ hρv _ _ (hK'c v) (hK'o v)
    (fun k hk => singleHom_mem_boxSubgroup hk)
    (fun h hh => ⟨h v, hh v, apply_eq_apply_single v hu hh⟩)

end Window

end RestrictedTensor

end GroundTheory.Automorphic
