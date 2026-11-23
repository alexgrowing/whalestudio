import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.TupleGlue

private theorem rr {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    resG X h₂ (resG X h₁ s) = resG X (h₂.trans h₁) s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

variable {X : Scheme.{0}} {N : X.Opens} {J : Type}

private theorem isUnit_res (s : Γ(X, N)) {W : X.Opens} (h : W ≤ X.basicOpen s) :
    IsUnit (resG X (h.trans (X.basicOpen_le s)) s) := by
  have hu : IsUnit (resG X (X.basicOpen_le s) s) := X.toRingedSpace.isUnit_res_basicOpen s
  have := hu.map (resG X h)
  rwa [rr] at this

theorem eq_of_mul_eq (v : J → Γ(X, N)) (hv : N ≤ ⨆ i, X.basicOpen (v i)) {a b : Γ(X, N)}
    (h : ∀ i, a * v i = b * v i) : a = b := by
  refine X.sheaf.eq_of_locally_eq' (fun i => X.basicOpen (v i)) N
    (fun i => homOfLE (X.basicOpen_le _)) hv a b fun i => ?_
  change resG X (X.basicOpen_le (v i)) a = resG X (X.basicOpen_le (v i)) b
  apply (isUnit_res (v i) le_rfl).mul_right_cancel
  have := congrArg (resG X (X.basicOpen_le (v i))) (h i)
  rwa [map_mul, map_mul] at this

theorem exists_mul (u v : J → Γ(X, N)) (hv : N ≤ ⨆ i, X.basicOpen (v i))
    (h : ∀ i j, u i * v j = u j * v i) : ∃ r : Γ(X, N), ∀ j, u j = r * v j := by
  have hq : ∀ i, ∃ q : Γ(X, X.basicOpen (v i)), resG X (X.basicOpen_le (v i)) (u i) =
      q * resG X (X.basicOpen_le (v i)) (v i) := fun i =>
    ⟨resG X (X.basicOpen_le (v i)) (u i) * ↑(isUnit_res (v i) le_rfl).unit⁻¹, by
      rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]⟩
  choose q hq using hq
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun i => X.basicOpen (v i)) q := by
    intro i j
    change resG X (inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _) (q i) =
      resG X (inf_le_right : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _) (q j)
    have e1 := congrArg (resG X (inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)) (hq i)
    have e2 := congrArg (resG X (inf_le_right : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)) (hq j)
    rw [map_mul, rr, rr] at e1 e2
    have e3 := congrArg (resG X ((inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _).trans
      (X.basicOpen_le (v i)))) (h i j)
    rw [map_mul, map_mul, e1, e2] at e3
    have ui := isUnit_res (v i) (inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)
    have uj := isUnit_res (v j) (inf_le_right : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)
    apply (ui.mul uj).mul_right_cancel
    linear_combination e3
  obtain ⟨r₀, hr, -⟩ := X.sheaf.existsUnique_gluing' (fun i => X.basicOpen (v i)) N
    (fun i => homOfLE (X.basicOpen_le _)) hv q hcomp
  let r : Γ(X, N) := r₀
  refine ⟨r, fun j => ?_⟩
  refine X.sheaf.eq_of_locally_eq' (fun i => X.basicOpen (v i)) N
    (fun i => homOfLE (X.basicOpen_le _)) hv (u j) (r * v j) fun i => ?_
  change resG X (X.basicOpen_le (v i)) (u j) = resG X (X.basicOpen_le (v i)) (r * v j)
  have hri : resG X (X.basicOpen_le (v i)) r = q i := hr i
  rw [map_mul, hri]
  apply (isUnit_res (v i) le_rfl).mul_right_cancel
  have e3 := congrArg (resG X (X.basicOpen_le (v i))) (h i j)
  rw [map_mul, map_mul, hq i] at e3
  linear_combination -e3

theorem exists_unit_mul (u v : J → Γ(X, N)) (hu : N ≤ ⨆ i, X.basicOpen (u i))
    (hv : N ≤ ⨆ i, X.basicOpen (v i))
    (h : ∀ i j, u i * v j = u j * v i) : ∃ r : Γ(X, N)ˣ, ∀ j, u j = r * v j := by
  obtain ⟨r, hr⟩ := exists_mul u v hv h
  obtain ⟨r', hr'⟩ := exists_mul v u hu fun i j => by linear_combination h j i
  have h1 : r * r' = 1 := eq_of_mul_eq u hu fun i => by
    rw [_root_.mul_assoc, ← hr', ← hr, _root_.one_mul]
  exact ⟨⟨r, r', h1, by rw [_root_.mul_comm, h1]⟩, hr⟩

private theorem cover_res {U : X.Opens} (e : N ≤ U) (v : J → Γ(X, U))
    (hv : U ≤ ⨆ i, X.basicOpen (v i)) : N ≤ ⨆ i, X.basicOpen (resG X e (v i)) := by
  intro x hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hv (e hx))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  erw [Scheme.basicOpen_res]
  exact ⟨hx, hi⟩

theorem exists_sections : ∀ (X : Scheme.{0}) (A J : Type) (V : A → X.Opens) (t : ∀ a, J → Γ(X, V a)), (∀ a, V a ≤ ⨆ i, X.basicOpen (t a i)) → (∀ a a' i j, resG X (inf_le_left : V a ⊓ V a' ≤ V a) (t a i) * resG X (inf_le_right : V a ⊓ V a' ≤ V a') (t a' j) = resG X (inf_le_left : V a ⊓ V a' ≤ V a) (t a j) * resG X (inf_le_right : V a ⊓ V a' ≤ V a') (t a' i)) → ∃ (g : ∀ a a', Γ(X, V a ⊓ V a')ˣ) (T : J → LB.Sec (⟨A, V, g⟩ : LB X)), ∀ i a, (T i).f a = t a i := by
  intro X A J V t hV h
  choose g hg using fun a a' => exists_unit_mul
    (fun i => resG X (inf_le_left : V a ⊓ V a' ≤ V a) (t a i))
    (fun i => resG X (inf_le_right : V a ⊓ V a' ≤ V a') (t a' i))
    (cover_res _ _ (hV a)) (cover_res _ _ (hV a')) (h a a')
  exact ⟨g, fun i => ⟨fun a => t a i, fun a a' => hg a a' i⟩, fun _ _ => rfl⟩

end GlobalTheory.TupleGlue
