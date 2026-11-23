import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LogKS.Glue

variable {Z : Scheme.{0}}

theorem resG_resG {U V W : Z.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (f : Γ(Z, U)) :
    resG Z h2 (resG Z h1 f) = resG Z (h2.trans h1) f := by
  change (Z.presheaf.map (homOfLE h1).op ≫ Z.presheaf.map (homOfLE h2).op).hom f = _
  rw [← Functor.map_comp]
  rfl

variable {J : Type} (V : J → Z.Opens) (e : J → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O))

def loc (O : Z.Opens) (f : Γ(Z, O)) (i : J) : Γ(Z, O ⊓ V i) :=
  e i (O ⊓ V i) (resG Z inf_le_left f)

open Classical in

def glue (O : Z.Opens) (f : Γ(Z, O)) : Γ(Z, O) :=
  if h : ∃ s : Γ(Z, O), ∀ i, resG Z (inf_le_left : O ⊓ V i ≤ O) s = loc V e O f i then h.choose else 0

variable {V e}

theorem compat (he : ∀ i, IsField (V i) (e i))
    (hc : ∀ i j (O : Z.Opens), O ≤ V i → O ≤ V j → ∀ f, e i O f = e j O f) (O : Z.Opens) (f : Γ(Z, O)) :
    TopCat.Presheaf.IsCompatible Z.sheaf.1 (fun i => O ⊓ V i) (loc V e O f) := by
  intro i j
  change resG Z (inf_le_left : (O ⊓ V i) ⊓ (O ⊓ V j) ≤ O ⊓ V i) (loc V e O f i) =
    resG Z (inf_le_right : (O ⊓ V i) ⊓ (O ⊓ V j) ≤ O ⊓ V j) (loc V e O f j)
  simp only [loc]
  rw [← (he i).2.2 (O ⊓ V i) _ inf_le_left inf_le_right, ← (he j).2.2 (O ⊓ V j) _ inf_le_right inf_le_right,
    resG_resG, resG_resG]
  exact hc i j _ (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) _

theorem glue_ex (he : ∀ i, IsField (V i) (e i))
    (hc : ∀ i j (O : Z.Opens), O ≤ V i → O ≤ V j → ∀ f, e i O f = e j O f) {O : Z.Opens}
    (hO : O ≤ ⨆ i, V i) (f : Γ(Z, O)) :
    ∃! s : Γ(Z, O), ∀ i, resG Z (inf_le_left : O ⊓ V i ≤ O) s = loc V e O f i :=
  Z.sheaf.existsUnique_gluing' (fun i => O ⊓ V i) O (fun i => homOfLE inf_le_left)
    ((le_inf le_rfl hO).trans (inf_iSup_eq _ _).le) (loc V e O f) (compat he hc O f)

theorem glue_eq (he : ∀ i, IsField (V i) (e i))
    (hc : ∀ i j (O : Z.Opens), O ≤ V i → O ≤ V j → ∀ f, e i O f = e j O f) {O : Z.Opens}
    (hO : O ≤ ⨆ i, V i) (f : Γ(Z, O)) (s : Γ(Z, O))
    (hs : ∀ i, resG Z (inf_le_left : O ⊓ V i ≤ O) s = loc V e O f i) : glue V e O f = s := by
  obtain ⟨t, -, hu⟩ := glue_ex he hc hO f
  have h : ∃ s : Γ(Z, O), ∀ i, resG Z (inf_le_left : O ⊓ V i ≤ O) s = loc V e O f i := ⟨s, hs⟩
  rw [glue, dif_pos h]
  exact (hu _ h.choose_spec).trans (hu _ hs).symm

theorem res_glue (he : ∀ i, IsField (V i) (e i))
    (hc : ∀ i j (O : Z.Opens), O ≤ V i → O ≤ V j → ∀ f, e i O f = e j O f) {O : Z.Opens}
    (hO : O ≤ ⨆ i, V i) (f : Γ(Z, O)) (i : J) :
    resG Z (inf_le_left : O ⊓ V i ≤ O) (glue V e O f) = loc V e O f i := by
  obtain ⟨t, ht, -⟩ := glue_ex he hc hO f
  rw [glue_eq he hc hO f t ht]
  exact ht i

end GlobalTheory.LogKS.Glue

theorem GlobalTheory.LogKS.isField_glue : ∀ (Z : Scheme.{0}) (J : Type) (V : J → Z.Opens) (e : J → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), (∀ i, IsField (V i) (e i)) → (∀ i j (O : Z.Opens), O ≤ V i → O ≤ V j → ∀ f, e i O f = e j O f) → ∃ d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField (⨆ i, V i) d ∧ ∀ i (O : Z.Opens), O ≤ V i → ∀ f, d O f = e i O f := by
  intro Z J V e he hc
  open GlobalTheory.LogKS.Glue in
  refine ⟨glue V e, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro W hW f f'
    refine glue_eq he hc hW _ _ fun i => ?_
    rw [map_add, res_glue he hc hW f, res_glue he hc hW f']
    simp only [loc, map_add]
    exact ((he i).1 _ inf_le_right _ _).symm
  · intro W hW f f'
    refine glue_eq he hc hW _ _ fun i => ?_
    rw [map_add, map_mul, map_mul, res_glue he hc hW f, res_glue he hc hW f']
    simp only [loc, map_mul]
    exact ((he i).2.1 _ inf_le_right _ _).symm
  · intro W W' h hW f
    refine glue_eq he hc (h.trans hW) _ _ fun i => ?_
    rw [resG_resG, ← resG_resG (inf_le_left : W ⊓ V i ≤ W) (inf_le_inf_right (V i) h), res_glue he hc hW f]
    simp only [loc]
    rw [← (he i).2.2 _ _ (inf_le_inf_right (V i) h) inf_le_right, resG_resG, resG_resG]
  · intro i O hO f
    refine glue_eq he hc (hO.trans (le_iSup V i)) _ _ fun j => ?_
    simp only [loc]
    rw [← (he i).2.2 O (O ⊓ V j) inf_le_left hO f]
    exact hc i j _ (inf_le_left.trans hO) inf_le_right _
