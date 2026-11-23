import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TopLeAlgOverHom
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIsGenOfInvariant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AddCurve

namespace GlobalTheory.TangentCob

section Schemes
variable {X Y : Scheme.{0}}

theorem top_le_stalk_iff (f : Y ⟶ X) (y : Y) (U : X.Opens) :
    ⊤ ≤ (Y.fromSpecStalk y ≫ f) ⁻¹ᵁ U ↔ f y ∈ U := by
  refine (top_le_iff_cpt (A := Y.presheaf.stalk y) _ U).trans ?_
  rw [Scheme.Hom.comp_apply,
    show Y.fromSpecStalk y (cpt (Y.presheaf.stalk y)) = y from Scheme.fromSpecStalk_closedPoint]

theorem valR_stalk (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    valR (A := Y.presheaf.stalk y) (Y.fromSpecStalk y ≫ f) U a = gs f y U a := by
  rw [gs_eq f y U h]
  exact (GlobalTheory.HolHom.valR_comp (A := Y.presheaf.stalk y) _ f U a).trans
    (GlobalTheory.FormalValue.valR_fromSpecStalk y (f ⁻¹ᵁ U) h _)

theorem exists_unit (p : Y ⟶ X) (e : Γ(Y, ⊤)) (he : e * e = 0) (U : X.Opens) (a : Γ(X, U)) :
    ∃ u : Γ(Y, p ⁻¹ᵁ U)ˣ, ∀ y, p y ∈ U →
      (gm (𝟙 Y) y (p ⁻¹ᵁ U) u).val = 1 + gs (𝟙 Y) y ⊤ e * gs p y U a := by
  let e' : Γ(Y, p ⁻¹ᵁ U) := (Y.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ U ≤ ⊤)).op).hom e
  have he' : e' * e' = 0 := by rw [← map_mul, he, map_zero]
  let b : Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom a
  refine ⟨⟨1 + e' * b, 1 - e' * b, by linear_combination (-(b * b)) * he', by linear_combination (-(b * b)) * he'⟩,
    fun y hy => ?_⟩
  have hy' : (𝟙 Y : Y ⟶ Y) y ∈ p ⁻¹ᵁ U := hy
  rw [← gs_unit _ y _ hy']
  show gs (𝟙 Y) y (p ⁻¹ᵁ U) (1 + e' * b) = _
  rw [gs_add _ y _ hy', gs_mul _ y _ hy', gs_res _ y _ hy', gs_pull (𝟙 Y) p y U hy, Category.id_comp,
    gs_eq _ y _ hy', map_one, map_one]

theorem commGroup_coboundary_relation_identity {G : Type} [CommGroup G] {a b c d f g u v : G} (h : a * v = b * u) (h₁ : c * d = f)
    (h₂ : g * a = f) : g * u = c ^ (1 : ℤ) * b ^ (-1 : ℤ) * (d * v) := by
  rw [zpow_one, zpow_neg, zpow_one, _root_.mul_mul_mul_comm, h₁, ← h₂, _root_.mul_assoc, _root_.mul_left_comm a,
    h, inv_mul_cancel_left]

theorem exists_isGen (L : LB X) (hL : L.IsLB) (m p : Y ⟶ X) (e : Γ(Y, ⊤)) (he : e * e = 0) (H : ∀ j, Γ(X, L.U j))
    (hmp : ∀ (y : Y) (U : X.Opens), p y ∈ U → m y ∈ U)
    (h : ∀ (y : Y) (j j' : L.ι), p y ∈ L.U j → p y ∈ L.U j' → gs m y (L.U j ⊓ L.U j') (L.g j j').val =
      gs p y (L.U j ⊓ L.U j') (L.g j j').val *
        (1 + gs (𝟙 Y) y ⊤ e * (gs p y (L.U j) (H j) - gs p y (L.U j') (H j')))) :
    ∃ c : LB.Gen (LB.LinComb L (K := Fin 2) ![m, p] ![1, -1]), c.IsGen := by
  choose u hu using fun j => exists_unit p e he (L.U j) (H j)
  have h0 : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![m, p] j → m y ∈ L.U (j 0) :=
    fun j y hy => LB.wchart_le L ![m, p] j 0 hy
  have h1 : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![m, p] j → p y ∈ L.U (j 1) :=
    fun j y hy => LB.wchart_le L ![m, p] j 1 hy
  let s : ∀ j : Fin 2 → L.ι, Γ(Y, LB.wchart L ![m, p] j)ˣ := fun j =>
    res (show LB.wchart L ![m, p] j ≤ m ⁻¹ᵁ (L.U (j 0) ⊓ L.U (j 1)) from
      fun y hy => ⟨h0 j y hy, hmp y _ (h1 j y hy)⟩) (pullU m _ (L.g (j 0) (j 1))) *
    res (show LB.wchart L ![m, p] j ≤ p ⁻¹ᵁ L.U (j 1) from fun y hy => h1 j y hy) (u (j 1))
  have hs : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![m, p] j → gm (𝟙 Y) y _ (s j) =
      gm m y _ (L.g (j 0) (j 1)) * gm (𝟙 Y) y _ (u (j 1)) := fun j y hy => by
    have hy' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L ![m, p] j := hy
    rw [map_mul, gm_res _ y _ hy', gm_res _ y _ hy',
      gm_pull (𝟙 Y) m y (L.U (j 0) ⊓ L.U (j 1)) ⟨h0 j y hy, hmp y _ (h1 j y hy)⟩, Category.id_comp]
  refine ⟨⟨s⟩, fun j j' => unit_ext fun y hy => ?_⟩
  have hy' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L ![m, p] j ⊓ LB.wchart L ![m, p] j' := hy
  refine ((gm_res _ y _ hy' _).trans (hs j y hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linComb L ![m, p] ![1, -1] (𝟙 Y) y j j' hy.1 hy.2) ((gm_res _ y _ hy' _).trans (hs j' y hy.2)))).symm)
  have a0 := h0 j y hy.1
  have a1 := h1 j y hy.1
  have b0 := h0 j' y hy.2
  have b1 := h1 j' y hy.2
  have key : gm m y _ (L.g (j 1) (j' 1)) * gm (𝟙 Y) y _ (u (j' 1)) =
      gm p y _ (L.g (j 1) (j' 1)) * gm (𝟙 Y) y _ (u (j 1)) := by
    apply Units.ext
    have hee : gs (𝟙 Y) y ⊤ e * gs (𝟙 Y) y ⊤ e = 0 := by
      rw [← gs_mul (𝟙 Y) y ⊤ trivial, he, gs_eq (𝟙 Y) y ⊤ trivial, map_zero, map_zero]
    rw [Units.val_mul, Units.val_mul, hu _ y a1, hu _ y b1, ← gs_unit m y (L.U (j 1) ⊓ L.U (j' 1)) ⟨hmp y _ a1, hmp y _ b1⟩,
      ← gs_unit p y (L.U (j 1) ⊓ L.U (j' 1)) ⟨a1, b1⟩, h y _ _ a1 b1]
    linear_combination (gs p y (L.U (j 1) ⊓ L.U (j' 1)) (L.g (j 1) (j' 1)).val *
      (gs p y (L.U (j 1)) (H (j 1)) - gs p y (L.U (j' 1)) (H (j' 1))) * gs p y (L.U (j' 1)) (H (j' 1))) * hee
  have c1 := gm_cocycle hL m y a0 b0 (hmp y _ b1)
  have c2 := gm_cocycle hL m y a0 (hmp y _ a1) (hmp y _ b1)
  rw [Fin.prod_univ_two]
  exact commGroup_coboundary_relation_identity key c1 c2

end Schemes

variable {k : Type} [CommRing k] {B : Over (Sp k)}

theorem exists_alg (D : Type) [CommRing D] [Algebra k D] {S : Type} [CommRing S] (r : Sp S ⟶ (algOver k D ⊗ B).left) :
    ∃ (_ : Algebra k S) (φ : D →ₐ[k] S) (r' : algOver k S ⟶ algOver k D ⊗ B), r'.left = r ∧
      r' ≫ fst _ _ = algOverHom φ ∧ ∀ d : D, φ d =
        valR (r ≫ (fst (algOver k D) B).left) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of D)).inv.hom d) := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := CommRingCat.of D) (S := CommRingCat.of S) (r ≫ (fst (algOver k D) B).left)
  letI : Algebra k S := (ψ.hom.comp (algebraMap k D)).toAlgebra
  refine ⟨this, ⟨ψ.hom, fun _ => rfl⟩, Over.homMk r ?_, rfl, Over.OverMorphism.ext hψ.symm, fun d => ?_⟩
  · rw [← Over.w (fst (algOver k D) B), ← Category.assoc]
    erw [← hψ]
    exact (Spec.map_comp _ _).symm
  · erw [← hψ]
    have := GlobalTheory.HolHom.valR_spMap ψ.hom (𝟙 (Sp D)) ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of D)).inv.hom d)
    rw [Category.comp_id, GlobalTheory.HolHom.valR_eq (𝟙 (Sp D)) ⊤ le_top] at this
    refine Eq.trans ?_ this.symm
    refine congrArg ψ.hom ?_
    simp [GlobalTheory.HolHom.evalHom, Scheme.Hom.appLE]

end GlobalTheory.TangentCob

namespace GlobalTheory
open TangentCob

end GlobalTheory
