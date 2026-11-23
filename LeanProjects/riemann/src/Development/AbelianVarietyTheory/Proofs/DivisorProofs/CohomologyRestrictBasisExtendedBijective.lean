import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitMpTenExtIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepOfFactoringCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueCommaOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCoboundaryOfBasisFunctor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaDescentRestrictionEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictPull1InjectiveOfSepGlue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Pull1RestrictSurjectiveOfComma
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaDescentInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocOAff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BasisExt

section Retract

variable {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {C C' : Type} [Category.{0} C] [Category.{0} C']
  (F₁ : C ⥤ CommAlgCat.{0} R₁) (F₂ : C ⥤ CommAlgCat.{0} R₂) (G : C' ⥤ C)

theorem sep_of_retract (i : ∀ T, F₁.obj T →+ F₂.obj T) (r : ∀ T, F₂.obj T →+ F₁.obj T)
    (hri : ∀ T x, r T (i T x) = x) (hi : ∀ {T S : C} (u : T ⟶ S) x, i S (mp F₁ u x) = mp F₂ u (i T x))
    (hs : ∀ (T : C) (x : F₂.obj T), (∀ (t : C') (u : T ⟶ G.obj t), mp F₂ u x = 0) → x = 0) :
    ∀ (T : C) (x : F₁.obj T), (∀ (t : C') (u : T ⟶ G.obj t), mp F₁ u x = 0) → x = 0 := by
  intro T x hx
  rw [← hri T x, hs T (i T x) fun t u ↦ by rw [← hi, hx, map_zero], map_zero]

theorem glue_of_retract (i : ∀ T, F₁.obj T →+ F₂.obj T) (r : ∀ T, F₂.obj T →+ F₁.obj T)
    (hri : ∀ T x, r T (i T x) = x) (hi : ∀ {T S : C} (u : T ⟶ S) x, i S (mp F₁ u x) = mp F₂ u (i T x))
    (hr : ∀ {T S : C} (u : T ⟶ S) x, r S (mp F₂ u x) = mp F₁ u (r T x))
    (hg : ∀ (T : C) (s : (t : C') → (T ⟶ G.obj t) → F₂.obj (G.obj t)),
      (∀ (t t' : C') (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F₂ (G.map a) (s t u)) →
        ∃ x, ∀ (t : C') (u : T ⟶ G.obj t), mp F₂ u x = s t u) :
    ∀ (T : C) (s : (t : C') → (T ⟶ G.obj t) → F₁.obj (G.obj t)),
      (∀ (t t' : C') (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F₁ (G.map a) (s t u)) →
        ∃ x, ∀ (t : C') (u : T ⟶ G.obj t), mp F₁ u x = s t u := by
  intro T s hs
  obtain ⟨x, hx⟩ := hg T (fun t u ↦ i _ (s t u)) fun t t' u a ↦ by rw [hs, hi]
  exact ⟨r T x, fun t u ↦ by rw [← hr, hx, hri]⟩

theorem cocycleOne_vanishing_of_natural_additive_retract (i : ∀ T, F₁.obj T →+ F₂.obj T) (r : ∀ T, F₂.obj T →+ F₁.obj T)
    (hri : ∀ T x, r T (i T x) = x) (hi : ∀ {T S : C} (u : T ⟶ S) x, i S (mp F₁ u x) = mp F₂ u (i T x))
    (hr : ∀ {T S : C} (u : T ⟶ S) x, r S (mp F₂ u x) = mp F₁ u (r T x))
    (hv : ∀ (T : C) (y : (t t' : C') → (T ⟶ G.obj t) → (t ⟶ t') → F₂.obj (G.obj t')),
      (∀ (t t' t'' : C') (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''),
        y t t'' u (a ≫ b) = mp F₂ (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) →
      ∃ g : (t : C') → (T ⟶ G.obj t) → F₂.obj (G.obj t), ∀ (t t' : C') (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp F₂ (G.map a) (g t u) = y t t' u a) :
    ∀ (T : C) (y : (t t' : C') → (T ⟶ G.obj t) → (t ⟶ t') → F₁.obj (G.obj t')),
      (∀ (t t' t'' : C') (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''),
        y t t'' u (a ≫ b) = mp F₁ (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) →
      ∃ g : (t : C') → (T ⟶ G.obj t) → F₁.obj (G.obj t), ∀ (t t' : C') (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp F₁ (G.map a) (g t u) = y t t' u a := by
  intro T y hy
  obtain ⟨g, hg⟩ := hv T (fun t t' u a ↦ i _ (y t t' u a)) fun t t' t'' u a b ↦ by rw [hy, map_add, hi]
  exact ⟨fun t u ↦ r _ (g t u), fun t t' u a ↦ by rw [← hr, ← map_sub, hg, hri]⟩

theorem cocycleTwo_vanishing_of_natural_additive_retract (i : ∀ T, F₁.obj T →+ F₂.obj T) (r : ∀ T, F₂.obj T →+ F₁.obj T)
    (hri : ∀ T x, r T (i T x) = x) (hi : ∀ {T S : C} (u : T ⟶ S) x, i S (mp F₁ u x) = mp F₂ u (i T x))
    (hr : ∀ {T S : C} (u : T ⟶ S) x, r S (mp F₂ u x) = mp F₁ u (r T x))
    (hv : ∀ (T : C) (z : (t t' t'' : C') → (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F₂.obj (G.obj t'')),
      (∀ (t t' t'' t''' : C') (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''),
        mp F₂ (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c =
          z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) →
      ∃ y : (t t' : C') → (T ⟶ G.obj t) → (t ⟶ t') → F₂.obj (G.obj t'), ∀ (t t' t'' : C') (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''),
        mp F₂ (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) :
    ∀ (T : C) (z : (t t' t'' : C') → (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F₁.obj (G.obj t'')),
      (∀ (t t' t'' t''' : C') (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''),
        mp F₁ (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c =
          z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) →
      ∃ y : (t t' : C') → (T ⟶ G.obj t) → (t ⟶ t') → F₁.obj (G.obj t'), ∀ (t t' t'' : C') (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''),
        mp F₁ (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b := by
  intro T z hz
  obtain ⟨y, hy⟩ := hv T (fun t t' t'' u a b ↦ i _ (z t t' t'' u a b)) fun t t' t'' t''' u a b c ↦ by
    rw [← hi, ← map_add, ← map_add, hz]
  exact ⟨fun t t' u a ↦ r _ (y t t' u a), fun t t' t'' u a b ↦ by
    rw [← hr, ← map_sub, ← map_add, hy, hri]⟩

end Retract

end GlobalTheory.Obs.BasisExt

namespace GlobalTheory.Obs.BasisExt

section Ext

variable {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] {C : Type} [Category.{0} C]
  (F : C ⥤ CommAlgCat.{0} R₀)

def incl (T : C) : R₁ ⊗[R₀] F.obj T →+ TrivSqZeroExt (F.obj T) (F.obj T ⊗[R₀] R₁) :=
  (TrivSqZeroExt.inrHom (F.obj T) (F.obj T ⊗[R₀] R₁)).toAddMonoidHom.comp
    (TensorProduct.comm R₀ R₁ (F.obj T)).toLinearMap.toAddMonoidHom

def proj (T : C) : TrivSqZeroExt (F.obj T) (F.obj T ⊗[R₀] R₁) →+ R₁ ⊗[R₀] F.obj T :=
  (TensorProduct.comm R₀ R₁ (F.obj T)).symm.toLinearMap.toAddMonoidHom.comp
    (TrivSqZeroExt.sndHom (F.obj T) (F.obj T ⊗[R₀] R₁)).toAddMonoidHom

theorem proj_incl (T : C) (x : R₁ ⊗[R₀] F.obj T) : proj R₁ F T (incl R₁ F T x) = x := by
  simp [proj, incl]

theorem comm_ext {T S : C} (u : T ⟶ S) (x : R₁ ⊗[R₀] F.obj T) :
    TensorProduct.comm R₀ R₁ (F.obj S) (extHom R₁ (mp F u) x) =
      LinearMap.rTensor R₁ (mp F u).toLinearMap (TensorProduct.comm R₀ R₁ (F.obj T) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem incl_mp {T S : C} (u : T ⟶ S) (x : R₁ ⊗[R₀] F.obj T) :
    incl R₁ F S (mp (ext R₁ F) u x) = mp (TenExt.tenExt R₁ F) u (incl R₁ F T x) := by
  change incl R₁ F S (mp (ext R₁ F) u x) = TenExt.tenMap R₁ F u (incl R₁ F T x)
  apply TrivSqZeroExt.ext
  · rw [TenExt.fst_tenMap]; simp [incl]
  · rw [TenExt.snd_tenMap]
    simp only [incl, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      LinearEquiv.coe_coe, TrivSqZeroExt.inrHom_apply, TrivSqZeroExt.snd_inr]
    exact comm_ext R₁ F u x

theorem proj_mp {T S : C} (u : T ⟶ S) (c : TrivSqZeroExt (F.obj T) (F.obj T ⊗[R₀] R₁)) :
    proj R₁ F S (mp (TenExt.tenExt R₁ F) u c) = mp (ext R₁ F) u (proj R₁ F T c) := by
  change proj R₁ F S (TenExt.tenMap R₁ F u c) = mp (ext R₁ F) u (proj R₁ F T c)
  simp only [proj, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
    LinearEquiv.coe_coe, TrivSqZeroExt.sndHom_apply]
  rw [TenExt.snd_tenMap]
  apply (TensorProduct.comm R₀ R₁ (F.obj S)).injective
  rw [LinearEquiv.apply_symm_apply]
  change _ = TensorProduct.comm R₀ R₁ (F.obj S) (extHom R₁ (mp F u) _)
  rw [comm_ext, LinearEquiv.apply_symm_apply]

theorem extMap_restrict {C' : Type} [Category.{0} C'] (G : C' ⥤ C) :
    extMap R₁ (CoefMap.restrict F G) = CoefMap.restrict (ext R₁ F) G := by
  have h : ∀ T, extHom R₁ (coefHom (CoefMap.restrict F G) T) = AlgHom.id R₁ (R₁ ⊗[R₀] F.obj (G.obj T)) :=
    fun T ↦ by
      apply Algebra.TensorProduct.ext'
      intro a b
      rfl
  unfold extMap CoefMap.restrict
  congr 1
  funext T
  exact RingHom.ext fun x ↦ DFunLike.congr_fun (h T) x

end Ext

end GlobalTheory.Obs.BasisExt

namespace GlobalTheory.Obs.BasisExt

section Cover

variable {R₀ : Type} [CommRing R₀] {X : Scheme.{0}} (s : X ⟶ Sp R₀)

theorem cover_of_local (P : X.Opens → Prop) (T : AffOp X)
    (hP : ∀ x ∈ T.unop.1, ∃ V : X.Opens, P V ∧ x ∈ V) :
    ∃ (n : ℕ) (b : Fin n → (OAff s).obj T), Ideal.span (Set.range b) = ⊤ ∧
      ∀ (i : Fin n) (S : AffOp X) (u : T ⟶ S), IsUnit (mp (OAff s) u (b i)) →
        ∃ V : X.Opens, P V ∧ S.unop.1 ≤ V := by
  have hT : IsAffineOpen T.unop.1 := T.unop.2
  let Gs : Set Γ(X, T.unop.1) := {f | ∃ V : X.Opens, P V ∧ X.basicOpen f ≤ V}
  have hG : Ideal.span Gs = ⊤ := by
    rw [← hT.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨V, hV, hxV⟩ := hP x hx
    obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := V) ⟨x, hxV⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, V, hV, hf⟩, hxf⟩
  obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite Gs).1 hG
  refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
  · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(X, T.unop.1)) := by
      ext f
      constructor
      · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
      · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
    exact hR ▸ hF
  · intro i S u hu
    obtain ⟨V, hV, hfV⟩ := hFG (F.equivFin.symm i).2
    refine ⟨V, hV, le_trans ?_ hfV⟩
    set f : Γ(X, T.unop.1) := (F.equivFin.symm i).1
    have h1 : X.basicOpen (X.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
      X.basicOpen_of_isUnit hu
    rw [Scheme.basicOpen_res] at h1
    rw [← h1]; exact inf_le_right

theorem hcov_of_basis {C' : Type} [Category.{0} C'] (G : C' ⥤ AffOp X)
    (h1 : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C', x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U) :
    ∀ T : AffOp X, ∃ (n : ℕ) (b : Fin n → (OAff s).obj T), Ideal.span (Set.range b) = ⊤ ∧
      ∀ (i : Fin n) (S : AffOp X) (u : T ⟶ S), IsUnit (mp (OAff s) u (b i)) →
        ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u := by
  intro T
  obtain ⟨n, b, hb, h⟩ := cover_of_local s
    (fun V ↦ ∃ t : C', V = (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ T.unop.1) T
    (fun x hx ↦ by
      obtain ⟨t, hxt, htT⟩ := h1 x _ hx
      exact ⟨_, ⟨t, rfl, htT⟩, hxt⟩)
  refine ⟨n, b, hb, fun i S u hu ↦ ?_⟩
  obtain ⟨V, ⟨t, rfl, htT⟩, hSV⟩ := h i S u hu
  exact ⟨t, (homOfLE (show (G.obj t).unop ≤ T.unop from htT)).op,
    (homOfLE (show S.unop ≤ (G.obj t).unop from hSV)).op, Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩

theorem hdir_of_basis {C' : Type} [Category.{0} C'] (G : C' ⥤ AffOp X)
    (h2 : ∀ (t₁ t₂ : C') (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 → x ∈ (G.obj t₂).unop.1 →
      ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U) :
    ∀ (t₁ t₂ : C') (S : AffOp X), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s).obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X) (u : S ⟶ S'), IsUnit (mp (OAff s) u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S') := by
  intro t₁ t₂ S a₁ a₂
  obtain ⟨n, b, hb, h⟩ := cover_of_local s
    (fun V ↦ ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ V = (G.obj t₃).unop.1) S
    (fun x hx ↦ by
      obtain ⟨t₃, e₁, e₂, hx3, -⟩ := h2 t₁ t₂ x S.unop.1 hx
        ((leOfHom a₁.unop : S.unop ≤ (G.obj t₁).unop) hx) ((leOfHom a₂.unop : S.unop ≤ (G.obj t₂).unop) hx)
      exact ⟨_, ⟨t₃, e₁, e₂, rfl⟩, hx3⟩)
  refine ⟨n, b, hb, fun i S' u hu ↦ ?_⟩
  obtain ⟨V, ⟨t₃, e₁, e₂, rfl⟩, hSV⟩ := h i S' u hu
  exact ⟨t₃, e₁, e₂, ⟨(homOfLE (show S'.unop ≤ (G.obj t₃).unop from hSV)).op⟩⟩

end Cover

end GlobalTheory.Obs.BasisExt

namespace GlobalTheory.Obs.BasisExt

theorem restrict_ext_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X : Scheme.{0})
    (s : X ⟶ Sp R₀) (C' : Type) [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X),
    (∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C', x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U) →
    (∀ (t₁ t₂ : C') (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 → x ∈ (G.obj t₂).unop.1 →
      ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U) →
    Function.Bijective (extMap R₁ (CoefMap.restrict (OAff s) G)).pull1 ∧
      Function.Bijective (extMap R₁ (CoefMap.restrict (OAff s) G)).pull2 := by
  intro R₀ R₁ _ _ _ X s C' _ _ G h1 h2
  have H := hasLoc_OAff s
  have hcov := hcov_of_basis s G h1
  have hdir := hdir_of_basis s G h2
  have HE := TenExt.hasLoc_tenExt R₁ (OAff s) H
  have unitE : ∀ {S S' : AffOp X} (u : S ⟶ S') (b : (OAff s).obj S),
      IsUnit (mp (TenExt.tenExt R₁ (OAff s)) u (TrivSqZeroExt.inl b)) → IsUnit (mp (OAff s) u b) :=
    fun u b h ↦ ((TenExt.isUnit_mp_tenExt_iff R₁ (OAff s) u _).1 h)
  have hcovE : ∀ T : AffOp X, ∃ (n : ℕ) (b : Fin n → (TenExt.tenExt R₁ (OAff s)).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X) (u : T ⟶ S),
        IsUnit (mp (TenExt.tenExt R₁ (OAff s)) u (b i)) →
          ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u :=
    fun T ↦ by
      obtain ⟨n, b, hb, h⟩ := hcov T
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), TenExt.span_inl_eq_top R₁ (OAff s) hb,
        fun i S u hu ↦ h i S u (unitE u _ hu)⟩
  have hdirE : ∀ (t₁ t₂ : C') (S : AffOp X), (G.obj t₁ ⟶ S) →
      (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (TenExt.tenExt R₁ (OAff s)).obj S),
        Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X) (u : S ⟶ S'),
          IsUnit (mp (TenExt.tenExt R₁ (OAff s)) u (b i)) →
            ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S') :=
    fun t₁ t₂ S a₁ a₂ ↦ by
      obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S a₁ a₂
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), TenExt.span_inl_eq_top R₁ (OAff s) hb,
        fun i S' u hu ↦ h i S' u (unitE u _ hu)⟩
  have hsE := _root_.GlobalTheory.sep_of_factoring_cover (TenExt.tenExt R₁ (OAff s)) G HE hcovE
  have hgE := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (TenExt.tenExt R₁ (OAff s)) G HE hcovE hdirE
  have hvE := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (TenExt.tenExt R₁ (OAff s)) G HE hcovE hdirE
  have hv2E := _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.twoCocycle_coboundary_of_basisFunctor_alt (TenExt.tenExt R₁ (OAff s)) G HE hcovE hdirE
  have hs := sep_of_retract (ext R₁ (OAff s)) (TenExt.tenExt R₁ (OAff s)) G (incl R₁ (OAff s))
    (proj R₁ (OAff s)) (proj_incl R₁ (OAff s)) (incl_mp R₁ (OAff s)) hsE
  have hg := glue_of_retract (ext R₁ (OAff s)) (TenExt.tenExt R₁ (OAff s)) G (incl R₁ (OAff s))
    (proj R₁ (OAff s)) (proj_incl R₁ (OAff s)) (incl_mp R₁ (OAff s)) (proj_mp R₁ (OAff s)) hgE
  have hv := cocycleOne_vanishing_of_natural_additive_retract (ext R₁ (OAff s)) (TenExt.tenExt R₁ (OAff s)) G (incl R₁ (OAff s))
    (proj R₁ (OAff s)) (proj_incl R₁ (OAff s)) (incl_mp R₁ (OAff s)) (proj_mp R₁ (OAff s)) hvE
  have hv2 := cocycleTwo_vanishing_of_natural_additive_retract (ext R₁ (OAff s)) (TenExt.tenExt R₁ (OAff s)) G (incl R₁ (OAff s))
    (proj R₁ (OAff s)) (proj_incl R₁ (OAff s)) (incl_mp R₁ (OAff s)) (proj_mp R₁ (OAff s)) hv2E
  rw [extMap_restrict]
  exact ⟨⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
      _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩,
    ⟨_root_.GlobalTheory.CatCoh.pull2_restrict_injective_of_comma _ _ hs hg hv,
      _root_.GlobalTheory.CatCoh.Desc.pull2_surjective_of_comma _ _ hs hg hv hv2⟩⟩

end GlobalTheory.Obs.BasisExt
