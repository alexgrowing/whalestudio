import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsCompletionAt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField TensorProduct

namespace GlobalTheory.LevDict

open GlobalTheory.UPel.HT GlobalTheory.VDiv GlobalTheory.VDefo GlobalTheory.DrinLev.HT GlobalTheory.UPel.HT.WPart

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {Ow : Type} [CommRing Ow] [Algebra ℤ_[p] Ow] {b : Base D Ow}
  {i₀ : Fin D.a} {πw : WProj D b i₀} {N : ℕ} {T : Type} [CommRing T] [Algebra Ow T]
  {o : Obj b N (spMap (algebraMap Ow T))} {H : VarpiDivModule p Ow T}

def ptImg (wp : WPart πw o H) {k : ℕ} (h : H.G.A k →ₐ[T] T) : Sp T ⟶ o.A.left :=
  spMap ((h.comp (wp.iH.app k : wp.G.A k →ₐ[T] H.G.A k)).toRingHom) ≫ (wp.t.y k).left

end GlobalTheory.LevDict

namespace GlobalTheory.LevDict

open GlobalTheory.UPel.HT GlobalTheory.DrinLev.HT

theorem isFullSet_comp_equiv {S : Scheme.{0}} {Z : Over S} {J J' : Type} {P : J → (𝟙_ (Over S) ⟶ Z)}
    (h : GlobalTheory.DrinLev.IsFullSet Z P) (e : J' ≃ J) : GlobalTheory.DrinLev.IsFullSet Z (P ∘ e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨(Equiv.finite_iff e).2 h1, ?_, fun c f => ?_⟩
  · rw [Nat.card_congr e]; exact h2
  · rw [h3 c f]
    exact (finprod_comp_equiv e (f := fun i => c.ev (P i) f)).symm

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}}
  {s : S ⟶ Sp R}

def htLevelAct {o : Obj b N s} {w : Ideal (𝓞 D.F)} {m : ℕ} {e : D.O} (L : HTLevel o w m e)
    (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) : HTLevel o w m e where
  α x := L.α (g.val.mulVec x)
  map_add x y := by rw [Matrix.mulVec_add]; exact L.map_add _ _
  map_smul c x := by rw [Matrix.mulVec_smul]; exact L.map_smul _ _
  full := by
    obtain ⟨G, β, hβ, hf⟩ := L.full
    exact ⟨G, fun x => β (GlobalTheory.VDiv.glEquiv g x), fun x => hβ (GlobalTheory.VDiv.glEquiv g x), isFullSet_comp_equiv hf (GlobalTheory.VDiv.glEquiv g).toEquiv⟩

@[simp] theorem htLevelAct_α {o : Obj b N s} {w : Ideal (𝓞 D.F)} {m : ℕ} {e : D.O} (L : HTLevel o w m e)
    (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) (x : Fin D.n → 𝓞 D.F ⧸ w ^ m) :
    (htLevelAct L g).α x = L.α (g.val.mulVec x) := rfl

end GlobalTheory.LevDict
