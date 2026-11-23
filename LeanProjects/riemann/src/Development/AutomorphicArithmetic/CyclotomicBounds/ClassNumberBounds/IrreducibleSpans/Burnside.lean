import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BurnsideEnd

namespace KStar.Schema

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {G : Type*} [Group G]

private theorem burnside_end {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (hirr : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, f v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S :=
  _root_.UpperTheory.Reformulated.B.Qj3.burnside_end S hirr f

theorem span_eq_top_of_irreducible {K : Type*} [Field K] [IsAlgClosed K] (ρ : G →* Matrix n n K)
    (hirr : ∀ N : Submodule K (n → K), (∀ g, ∀ v ∈ N, ρ g *ᵥ v ∈ N) → N = ⊥ ∨ N = ⊤) :
    Submodule.span K (Set.range ρ) = ⊤ := by
  let T : Subalgebra K (Matrix n n K) := Algebra.adjoin K (Set.range ρ)
  have hT : Subalgebra.toSubmodule T = Submodule.span K (Set.range ρ) := by
    apply Algebra.adjoin_eq_span_of_subset
    intro x hx
    have : x ∈ MonoidHom.mrange ρ := by
      refine (Submonoid.closure_le.mpr ?_ : Submonoid.closure (Set.range ρ) ≤ MonoidHom.mrange ρ) hx
      intro y hy
      exact hy
    exact Submodule.subset_span this
  let e : Matrix n n K ≃ₐ[K] Module.End K (n → K) := Matrix.toLinAlgEquiv'
  rw [eq_top_iff, ← hT]
  intro m _
  have h := burnside_end (T.map e.toAlgHom) (fun N hN => hirr N fun g v hv =>
    hN (e (ρ g)) ⟨ρ g, Algebra.subset_adjoin ⟨g, rfl⟩, rfl⟩ v hv) (e m)
  obtain ⟨m', hm', h'⟩ := h
  have : m' = m := e.injective h'
  rw [← this]; exact hm'

private noncomputable def entryBasis (n : Type*) [Fintype n] (R : Type*) [CommRing R] :
    Module.Basis (n × n) R (Matrix n n R) :=
  Module.Basis.ofEquivFun
    { toFun := fun m p => m p.1 p.2
      invFun := fun f => Matrix.of fun i j => f (i, j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem span_eq_top_of_residue {A K : Type*} [CommRing A] [IsLocalRing A] [Field K]
    (π : A →+* K) (hπ : RingHom.ker π = IsLocalRing.maximalIdeal A) (s : Set (Matrix n n A))
    (hs : Submodule.span K ((fun m : Matrix n n A => m.map π) '' s) = ⊤) :
    Submodule.span A s = ⊤ := by
  classical
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent K ((fun m : Matrix n n A => m.map π) '' s)
  rw [hs] at hsp
  let B : Module.Basis b K (Matrix n n K) := Module.Basis.mk hli (by
    rw [Subtype.range_coe, hsp])
  let B' := B.reindex (B.indexEquiv (entryBasis n K))
  have hmem : ∀ p, ∃ w ∈ s, w.map π = B' p := fun p => by
    apply hb
    simp only [B', B, Module.Basis.reindex_apply, Module.Basis.mk_apply]
    exact Subtype.property _
  choose w hw hwπ using hmem
  have hu : IsUnit ((entryBasis n K).det B') := (entryBasis n K).isUnit_det B'
  have hdet : π ((entryBasis n A).det w) = (entryBasis n K).det B' := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
    congr 1
    ext p q
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply,
      Module.Basis.toMatrix_apply, ← hwπ]
    rfl
  have hu' : IsUnit ((entryBasis n A).det w) := by
    by_contra hn
    have : (entryBasis n A).det w ∈ RingHom.ker π := by
      rw [hπ]; exact hn
    rw [RingHom.mem_ker, hdet] at this
    exact hu.ne_zero this
  have h2 := ((entryBasis n A).is_basis_iff_det.mpr hu').2
  rw [eq_top_iff, ← h2]
  apply Submodule.span_mono
  rintro _ ⟨p, rfl⟩
  exact hw p

end KStar.Schema
