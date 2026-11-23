import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

noncomputable section

open CategoryTheory GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

def reindexAdd {α β : Type} (P : β → Type) [∀ b, AddCommGroup (P b)] (e : α ≃ β) :
    (∀ a, P (e a)) ≃+ (∀ b, P b) :=
  { Equiv.piCongrLeft P e with
    map_add' := fun f g => by
      funext b
      obtain ⟨a, rfl⟩ := e.surjective b
      simp only [Equiv.toFun_as_coe, Pi.add_apply, Equiv.piCongrLeft_apply_apply] }

theorem reindexAdd_apply {α β : Type} (P : β → Type) [∀ b, AddCommGroup (P b)] (e : α ≃ β)
    (f : ∀ a, P (e a)) (a : α) : reindexAdd P e f (e a) = f a :=
  Equiv.piCongrLeft_apply_apply P e f a

theorem reindexAdd_symm_apply {α β : Type} (P : β → Type) [∀ b, AddCommGroup (P b)] (e : α ≃ β)
    (g : ∀ b, P b) (a : α) : (reindexAdd P e).symm g a = g (e a) := by
  have h := reindexAdd_apply P e ((reindexAdd P e).symm g) a
  rw [AddEquiv.apply_symm_apply] at h
  exact h.symm

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

theorem ptLocalDualMap_reindex [Fintype ι] {κ : Type} [Fintype κ] (e : κ ≃ ι)
    (D : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep D] (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    [Finite M] (inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ) {r s : ℕ}
    (h : r + s = 2) (ξ : ∀ k, cohomology (Rep.res (φ (e k)).toMonoidHom M) r)
    (y : cohomology (dualRep D M) s) :
    ptLocalDualMap φ D M inv h
        (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e ξ) y =
      ∑ k, ptLocalPairing φ D M inv (e k) h (ξ k) (ptRes φ (dualRep D M) (e k) s y) := by
  rw [ptLocalDualMap_apply]
  refine (Fintype.sum_equiv e _ _ (fun k => ?_)).symm
  rw [reindexAdd_apply]

theorem ptGlobalToLocal_reindex {κ : Type} (e : κ ≃ ι) (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    (r : ℕ) (x : cohomology M r) (k : κ) :
    (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e).symm
      ((ptGlobalToLocal φ M r).hom x) k = ptRes φ M (e k) r x := by
  rw [reindexAdd_symm_apply, ptGlobalToLocal_apply]

theorem locSq_reindex {κ : Type} (e : κ ≃ ι) (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M] (r : ℕ)
    {X : Type} [AddCommGroup X] {Xk : κ → Type} [∀ k, AddCommGroup (Xk k)]
    (res : ∀ k, X →+ Xk k) (E : X ≃+ cohomology M r)
    (Ev : ∀ k, Xk k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) r)
    (sq : ∀ k x, Ev k (res k x) = ptRes φ M (e k) r (E x)) (x : X) :
    (ptGlobalToLocal φ M r).hom (E x) =
      reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e (fun k => Ev k (res k x)) := by
  apply (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e).symm.injective
  rw [AddEquiv.symm_apply_apply]
  funext k
  rw [ptGlobalToLocal_reindex, sq]

theorem trSq_reindex [Fintype ι] {κ : Type} [Fintype κ] (e : κ ≃ ι)
    (D : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep D] (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    [Finite M] (inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ) {r s : ℕ}
    (h : r + s = 2) {N : ℕ} [NeZero N] {Xk : κ → Type} [∀ k, AddCommGroup (Xk k)]
    [∀ k, Module (ZMod N) (Xk k)] {Y : Type} [AddCommGroup Y] [Module (ZMod N) Y]
    {Yk : κ → Type} [∀ k, AddCommGroup (Yk k)] [∀ k, Module (ZMod N) (Yk k)]
    (resY : ∀ k, Y →ₗ[ZMod N] Yk k) (P : ∀ k, Xk k →ₗ[ZMod N] Yk k →ₗ[ZMod N] ZMod N)
    (Ex : ∀ k, Xk k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) r)
    (Ey : Y ≃+ cohomology (dualRep D M) s)
    (Eyk : ∀ k, Yk k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom (dualRep D M)) s)
    (hres : ∀ k y, Eyk k (resY k y) = ptRes φ (dualRep D M) (e k) s (Ey y)) (ε : ℤ)
    (hQ : ∀ k a b, ptLocalPairing φ D M inv (e k) h (Ex k a) (Eyk k b) = ε • zmodToQZ N (P k a b))
    (x : ∀ k, Xk k) (y : cohomology (dualRep D M) s) :
    ptLocalDualMap φ D M inv h
        (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e (fun k => Ex k (x k))) y =
      ε • zmodToQZ N (∑ k, P k (x k) (resY k (Ey.symm y))) := by
  rw [ptLocalDualMap_reindex, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hQ, hres, AddEquiv.apply_symm_apply]

def finsetCoeEquiv {α : Type} (S : Finset α) : S ≃ (S : Set α) where
  toFun v := ⟨v.1, Finset.mem_coe.2 v.2⟩
  invFun w := ⟨w.1, Finset.mem_coe.1 w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem ptRes_comp_reindex {κ : Type} (e : κ ≃ ι) (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    (k : κ) (r : ℕ) (x : cohomology M r) :
    ptRes (fun k => φ (e k)) M k r x = ptRes φ M (e k) r x := rfl

end PositivityTheory.Lit1.PTN
