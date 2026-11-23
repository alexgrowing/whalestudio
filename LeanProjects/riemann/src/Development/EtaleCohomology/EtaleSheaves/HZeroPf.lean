import Development.EtaleCohomology.EtaleSheaves.LineHigh

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.HZeroPf

open LateralTheory.E.t_E2Cut

def RootAIC : Prop := ∀ (q : ℕ) (X : Scheme.{0}), AICSch X → IsUnit (q : Γ(X, ⊤)) → Nonempty (Prim q Γ(X, ⊤))

def ResBij : Prop := ∀ (q : ℕ) (i : ℤ) {Y X : Scheme.{0}} (f : Y ⟶ X), ConnectedSpace Y → ConnectedSpace X →
  Nonempty (Prim q Γ(X, ⊤)) → Function.Bijective (Sec.res (F := tw q i) f)

theorem connected_of_AICSch {X : Scheme.{0}} (h : AICSch X) : ConnectedSpace X := by
  have := h.1
  infer_instance

theorem HZero_of (hR : RootAIC) (hB : ResBij) : LateralTheory.E.t_E2Cut.HZero := by
  intro hyp q Y X f hX hY hq i
  obtain ⟨_, e, he, _⟩ := hyp.a9 (ZMod q) (tw q i)
  have := connected_of_AICSch hX
  have hres := hB q i f hY (connected_of_AICSch hX) (hR q X hX hq)
  have key : (pull (ZMod q) (sch.map f) (tw q i) 0) = (e Y).toAddMonoidHom.comp
      ((AddMonoidHom.mk' (Sec.res (F := tw q i) f) (fun a b => map_add _ a b)).comp (e X).symm.toAddMonoidHom) := by
    ext x
    obtain ⟨s, rfl⟩ := (e X).surjective x
    simp [he]
  rw [key]
  exact (e Y).bijective.comp (hres.comp (e X).symm.bijective)

end LateralTheory.E.HZeroPf
