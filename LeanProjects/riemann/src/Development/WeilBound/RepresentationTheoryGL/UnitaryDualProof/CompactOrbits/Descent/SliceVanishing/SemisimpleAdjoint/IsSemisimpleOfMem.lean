import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.T.Desc.SLF.CRAdj

open PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem isSemisimple_of_mem (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) {a : Matrix (Fin n) (Fin n) k}
    (ha : a ∈ Z) : Module.End.IsSemisimple (Matrix.toLin' a) := by
  haveI : IsReduced Z := hZ.2
  let a' : Z := ⟨a, ha⟩
  have hint : IsIntegral k a' := .of_finite k a'
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    ((minpoly.isRadical k a').squarefree (minpoly.ne_zero hint)) ?_
  have h1 : aeval a (minpoly k a') = 0 := by
    have := congrArg (Subalgebra.val Z) (minpoly.aeval k a')
    rwa [← Polynomial.aeval_algHom_apply, map_zero] at this
  have e : Matrix.toLin' a = (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _) a := rfl
  rw [e, Polynomial.aeval_algHom_apply, h1, map_zero]

theorem comm_gen (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) {s : Matrix (Fin n) (Fin n) k}
    (hs : s ∈ Bz Z) : ∀ a ∈ insert s (Z : Set (Matrix (Fin n) (Fin n) k)),
      ∀ b ∈ insert s (Z : Set (Matrix (Fin n) (Fin n) k)), a * b = b * a := by
  have hs' : ∀ a ∈ Z, a * s = s * a := hs
  intro a ha b hb
  rcases Set.mem_insert_iff.mp ha with h1 | h1 <;> rcases Set.mem_insert_iff.mp hb with h2 | h2
  · rw [h1, h2]
  · rw [h1]
    exact (hs' b h2).symm
  · rw [h2]
    exact hs' a h1
  · exact hZ.1 a h1 b h2

theorem adj_comm (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) {s : Matrix (Fin n) (Fin n) k}
    (hs : s ∈ Bz Z) : ∀ a ∈ adj Z s, ∀ b ∈ adj Z s, a * b = b * a := by
  intro a ha b hb
  have h1 : ∀ c ∈ insert s (Z : Set (Matrix (Fin n) (Fin n) k)), Commute c b := fun c hc =>
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb (fun d hd => comm_gen Z hZ hs c hc d hd)
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha (fun c hc => (h1 c hc).symm)).symm.eq

private theorem lin_comm_lemma {a b : Matrix (Fin n) (Fin n) k} (h : a * b = b * a) :
    Commute (Matrix.toLin' a) (Matrix.toLin' b) :=
  (show Commute a b from h).map (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _)

theorem cr_adj [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (s : Matrix (Fin n) (Fin n) k)
    (hs : s ∈ Bz Z) (hss : Module.End.IsSemisimple (Matrix.toLin' s)) : CR (adj Z s) := by
  have hsem : ∀ x (hx : x ∈ adj Z s), Module.End.IsSemisimple (Matrix.toLin' x) := by
    intro x hx
    change x ∈ Algebra.adjoin k (insert s (Z : Set (Matrix (Fin n) (Fin n) k))) at hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rcases Set.mem_insert_iff.mp hy with rfl | hy
      · exact hss
      · exact isSemisimple_of_mem Z hZ hy
    | algebraMap r =>
      rw [show Matrix.toLin' (algebraMap k (Matrix (Fin n) (Fin n) k) r) =
          algebraMap k (Module.End k (Fin n → k)) r from
        (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _).commutes r]
      exact Module.End.IsSemisimple.of_mem_adjoin_pair (Commute.refl _) hss hss
        (Subalgebra.algebraMap_mem _ r)
    | add y z hy hz ihy ihz =>
      rw [map_add]
      exact Module.End.IsSemisimple.add_of_commute (lin_comm_lemma (adj_comm Z hZ hs y hy z hz)) ihy ihz
    | mul y z hy hz ihy ihz =>
      rw [show Matrix.toLin' (y * z) = Matrix.toLin' y * Matrix.toLin' z from
        map_mul (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _) y z]
      exact Module.End.IsSemisimple.mul_of_commute (lin_comm_lemma (adj_comm Z hZ hs y hy z hz)) ihy ihz
  refine ⟨adj_comm Z hZ hs, ⟨fun x hx => ?_⟩⟩
  have hN : IsNilpotent (Matrix.toLin' (x : Matrix (Fin n) (Fin n) k)) :=
    (hx.map (adj Z s).val).map (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _)
  have h0 := Module.End.eq_zero_of_isNilpotent_isSemisimple hN (hsem x x.2)
  apply Subtype.ext
  have h2 : (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _) (x : Matrix (Fin n) (Fin n) k) = 0 := h0
  simpa using h2

end PositivityTheory.RgUd.T.Desc.SLF.CRAdj
