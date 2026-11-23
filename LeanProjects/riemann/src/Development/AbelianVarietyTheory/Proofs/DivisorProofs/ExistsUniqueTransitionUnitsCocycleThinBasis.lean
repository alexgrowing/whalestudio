import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBTrans

variable {X : Scheme.{0}}

theorem res_comp {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a) =
    (X.presheaf.map (homOfLE (h'.trans h)).op).hom a
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem units_eq_of_local {U : X.Opens} (a b : Γ(X, U)ˣ)
    (h : ∀ x ∈ U, ∃ (W : X.Opens) (hW : W ≤ U), x ∈ W ∧ res hW a = res hW b) : a = b := by
  let J := {W : X.Opens // ∃ hW : W ≤ U, res hW a = res hW b}
  have hc : U ≤ ⨆ j : J, j.1 := fun x hx => by
    obtain ⟨W, hW, hx', e⟩ := h x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW, e⟩, hx'⟩
  apply Units.ext
  refine X.sheaf.eq_of_locally_eq' (fun j : J => j.1) U (fun j => homOfLE j.2.1) hc _ _ (fun j => ?_)
  exact congrArg Units.val j.2.2

theorem glue_units {J : Type} (V : X.Opens) (W : J → X.Opens) (hW : ∀ i, W i ≤ V) (hc : V ≤ iSup W)
    (u : ∀ i, Γ(X, W i)ˣ)
    (hh : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (u i) = res inf_le_right (u j)) :
    ∃ s : Γ(X, V)ˣ, ∀ i, res (hW i) s = u i := by
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => (u i).val) (fun i j => congrArg Units.val (hh i j))
  obtain ⟨s', hs', -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => ((u i)⁻¹).val) (fun i j => congrArg Units.val
      (show res (inf_le_left : W i ⊓ W j ≤ W i) (u i)⁻¹ = res inf_le_right (u j)⁻¹ by
        rw [map_inv, map_inv, hh]))
  have e : (show Γ(X, V) from s) * (show Γ(X, V) from s') = 1 := by
    apply X.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc
    intro i
    show (X.presheaf.map (homOfLE (hW i)).op).hom _ = (X.presheaf.map (homOfLE (hW i)).op).hom _
    rw [map_mul, map_one]
    exact (congrArg₂ (· * ·) (hs i) (hs' i)).trans (u i).mul_inv
  exact ⟨⟨s, s', e, (mul_comm _ _).trans e⟩, fun i => Units.ext (hs i)⟩

variable {C : Type} [Category.{0} C] {V : C → X.Opens} {hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T}
  {u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ}

theorem res_quot (hu : IsCoc V hV u) {T₁ T₂ T T'' : C} (a : T₁ ⟶ T) (b : T₂ ⟶ T) (c : T ⟶ T'') :
    res (hV c) (u T₂ T b * (u T₁ T a)⁻¹) = u T₂ T'' (b ≫ c) * (u T₁ T'' (a ≫ c))⁻¹ := by
  rw [hu b c, hu a c, map_mul, map_inv, mul_inv_rev, _root_.mul_assoc, mul_inv_cancel_left]

theorem transition_units (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [thin : Quiver.IsThin C]
    (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) :
    IsBas V → IsCoc V hV u → ∀ T₁ T₂ : C, ∃! g : Γ(X, V T₁ ⊓ V T₂)ˣ,
      ∀ (T : C) (a : T₁ ⟶ T) (b : T₂ ⟶ T), res (le_inf (hV a) (hV b)) g * u T₁ T a = u T₂ T b := by
  intro hB hu T₁ T₂
  have sub : ∀ {T T' : C} (f f' : T ⟶ T'), f = f' := fun f f' => @Subsingleton.elim _ (thin _ _) f f'
  let J := {T : C // Nonempty (T₁ ⟶ T) ∧ Nonempty (T₂ ⟶ T)}
  let W : J → X.Opens := fun j => V j.1
  have hW : ∀ j : J, W j ≤ V T₁ ⊓ V T₂ := fun j => le_inf (hV j.2.1.some) (hV j.2.2.some)
  let w : ∀ j : J, Γ(X, W j)ˣ := fun j => u T₂ j.1 j.2.2.some * (u T₁ j.1 j.2.1.some)⁻¹
  have hw : ∀ (j : J) (a : T₁ ⟶ j.1) (b : T₂ ⟶ j.1), w j = u T₂ j.1 b * (u T₁ j.1 a)⁻¹ :=
    fun j a b => by simp only [w]; rw [sub j.2.2.some b, sub j.2.1.some a]
  have hc : V T₁ ⊓ V T₂ ≤ iSup W := fun x hx => by
    obtain ⟨T, ⟨a⟩, ⟨b⟩, hxT, -⟩ := hB.2 T₁ T₂ x (V T₁ ⊓ V T₂) hx hx.1 hx.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨T, ⟨a⟩, ⟨b⟩⟩, hxT⟩
  have hh : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (w i) = res inf_le_right (w j) := by
    intro i j
    apply units_eq_of_local
    intro x hx
    obtain ⟨T, ⟨c⟩, ⟨d⟩, hxT, hle⟩ := hB.2 i.1 j.1 x (W i ⊓ W j) hx hx.1 hx.2
    refine ⟨V T, hle, hxT, ?_⟩
    rw [res_comp, res_comp]
    have e1 := res_quot hu i.2.1.some i.2.2.some c
    have e2 := res_quot hu j.2.1.some j.2.2.some d
    change res (hV c) (w i) = res (hV d) (w j)
    simp only [w]
    rw [e1, e2, sub (i.2.1.some ≫ c) (j.2.1.some ≫ d), sub (i.2.2.some ≫ c) (j.2.2.some ≫ d)]
  obtain ⟨s, hs⟩ := glue_units (V T₁ ⊓ V T₂) W hW hc w hh
  have key : ∀ (g : Γ(X, V T₁ ⊓ V T₂)ˣ) (T : C) (a : T₁ ⟶ T) (b : T₂ ⟶ T),
      res (le_inf (hV a) (hV b)) g * u T₁ T a = u T₂ T b ↔
        res (le_inf (hV a) (hV b)) g = u T₂ T b * (u T₁ T a)⁻¹ :=
    fun g T a b => (eq_mul_inv_iff_mul_eq).symm
  refine ⟨s, fun T a b => (key s T a b).2 ?_, fun g hg => ?_⟩
  · have := hs ⟨T, ⟨a⟩, ⟨b⟩⟩
    rw [hw ⟨T, ⟨a⟩, ⟨b⟩⟩ a b] at this
    exact this
  · apply units_eq_of_local
    intro x hx
    obtain ⟨T, ⟨a⟩, ⟨b⟩, hxT, -⟩ := hB.2 T₁ T₂ x (V T₁ ⊓ V T₂) hx hx.1 hx.2
    refine ⟨V T, le_inf (hV a) (hV b), hxT, ?_⟩
    rw [(key g T a b).1 (hg T a b)]
    have := hs ⟨T, ⟨a⟩, ⟨b⟩⟩
    rw [hw ⟨T, ⟨a⟩, ⟨b⟩⟩ a b] at this
    exact this.symm

end GlobalTheory.LBTrans
