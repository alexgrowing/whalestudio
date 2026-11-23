import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourTermComplexRestrictionBijectiveCollapseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoproductThickeningAffineLiftPoincareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourTermComplexQuasiIsoAtFormalPropertiesStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.LevLift

variable (D : Data) (Λ : Lift D) (n : ℕ)

abbrev CC : Type 1 := (LevE D.κ D.t D.i (n + 1)).FullSubcategory

variable {D n}

theorem hom_ext' {T T' : CC D n} {f g : T ⟶ T'} (h : f.hom.hom.1 = g.hom.hom.1) : f = g :=
  ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ (Subtype.ext h))

def opn (T : CC D n) : AffOp D.X := Opposite.op ⟨T.obj.obj.U, T.obj.property⟩

variable (D n) in

def qq : CC D n ⥤ AffOp D.X where
  obj T := opn T
  map f := (homOfLE (show (⟨_, _⟩ : D.X.affineOpens) ≤ ⟨_, _⟩ from f.hom.hom.2)).op
  map_id _ := rfl
  map_comp _ _ := rfl

theorem mem_of_hom {T T' : Thick D.κ D.t} (f : T ⟶ T') {U : D.X.Opens} (h : ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U) :
    ⊤ ≤ (T'.x ≫ D.i) ⁻¹ᵁ U := by
  rw [← f.pt, Category.assoc, Scheme.Hom.comp_preimage, top_le_iff.1 h, Scheme.Hom.preimage_top]

theorem cop_ex (T : CC D n) : ∃ (G : Thick D.κ D.t) (l : T.obj.obj.T ⟶ G) (r : Λ.L.obj ((qq D n).obj T) ⟶ G),
    IsCop (n + 1) l r ∧ (KK D.κ D.t).QAt l :=
  GlobalTheory.T.exists_coproduct_thickening_affine_lift_poincare D Λ n ((qq D n).obj T) T.obj.obj.T T.property T.obj.obj.mem

def GG (T : CC D n) : Thick D.κ D.t := (cop_ex Λ T).choose

def ll (T : CC D n) : T.obj.obj.T ⟶ GG Λ T := (cop_ex Λ T).choose_spec.choose

def rr (T : CC D n) : Λ.L.obj ((qq D n).obj T) ⟶ GG Λ T := (cop_ex Λ T).choose_spec.choose_spec.choose

theorem isCop (T : CC D n) : IsCop (n + 1) (ll Λ T) (rr Λ T) :=
  (cop_ex Λ T).choose_spec.choose_spec.choose_spec.1

theorem qat_ll (T : CC D n) : (KK D.κ D.t).QAt (ll Λ T) :=
  (cop_ex Λ T).choose_spec.choose_spec.choose_spec.2

def SObj (T : CC D n) : CC D n :=
  ⟨⟨⟨GG Λ T, T.obj.obj.U, T.obj.obj.hU, mem_of_hom (ll Λ T) T.obj.obj.mem⟩, T.obj.property⟩, (isCop Λ T).1⟩

theorem smap_ex {T T' : CC D n} (f : T ⟶ T') : ∃! c : GG Λ T ⟶ GG Λ T',
    ll Λ T ≫ c = f.hom.hom.1 ≫ ll Λ T' ∧ rr Λ T ≫ c = Λ.L.map ((qq D n).map f) ≫ rr Λ T' :=
  (isCop Λ T).2 (GG Λ T') (isCop Λ T').1 _ _

def smap {T T' : CC D n} (f : T ⟶ T') : GG Λ T ⟶ GG Λ T' := (smap_ex Λ f).exists.choose

theorem smap_spec {T T' : CC D n} (f : T ⟶ T') :
    ll Λ T ≫ smap Λ f = f.hom.hom.1 ≫ ll Λ T' ∧ rr Λ T ≫ smap Λ f = Λ.L.map ((qq D n).map f) ≫ rr Λ T' :=
  (smap_ex Λ f).exists.choose_spec

theorem smap_uniq {T T' : CC D n} (f : T ⟶ T') (c : GG Λ T ⟶ GG Λ T')
    (h1 : ll Λ T ≫ c = f.hom.hom.1 ≫ ll Λ T') (h2 : rr Λ T ≫ c = Λ.L.map ((qq D n).map f) ≫ rr Λ T') :
    c = smap Λ f :=
  (smap_ex Λ f).unique ⟨h1, h2⟩ (smap_spec Λ f)

def SS : CC D n ⥤ CC D n where
  obj := SObj Λ
  map f := ObjectProperty.homMk (ObjectProperty.homMk ⟨smap Λ f, f.hom.hom.2⟩)
  map_id T := hom_ext' (smap_uniq Λ (𝟙 T) (𝟙 _) (by simp; rfl)
    (by rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]; simp)).symm
  map_comp {T T' T''} f g := hom_ext' (smap_uniq Λ (f ≫ g) (smap Λ f ≫ smap Λ g)
    (by rw [← Category.assoc, (smap_spec Λ f).1, Category.assoc, (smap_spec Λ g).1, ← Category.assoc]; rfl)
    (by rw [← Category.assoc, (smap_spec Λ f).2, Category.assoc, (smap_spec Λ g).2, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp])).symm

def uu : 𝟭 (CC D n) ⟶ SS Λ where
  app T := ObjectProperty.homMk (ObjectProperty.homMk ⟨ll Λ T, le_rfl⟩)
  naturality {T T'} f := hom_ext' (smap_spec Λ f).1.symm

variable (h : ∀ U, LevE D.κ D.t D.i (n + 1) (Λ.toE.obj U))

abbrev ell : AffOp D.X ⥤ CC D n := (LevE D.κ D.t D.i (n + 1)).lift Λ.toE h

def ww : qq D n ⋙ ell Λ h ⟶ SS Λ where
  app T := ObjectProperty.homMk (ObjectProperty.homMk ⟨rr Λ T, le_rfl⟩)
  naturality {T T'} f := hom_ext' (smap_spec Λ f).2.symm

def eps : 𝟭 (AffOp D.X) ⟶ ell Λ h ⋙ qq D n where
  app U := 𝟙 U
  naturality _ _ _ := rfl

abbrev KL : Cx (CC D n) := (((KK D.κ D.t).res (pE D.κ D.t D.i)).res (LevE D.κ D.t D.i (n + 1)).ι)

theorem qat_iff {T T' : CC D n} (φ : T ⟶ T') : (KL (D := D) (n := n)).QAt φ ↔ (KK D.κ D.t).QAt φ.hom.hom.1 :=
  Iff.rfl

theorem qat_rr (U : AffOp D.X) : (KK D.κ D.t).QAt (rr Λ ((ell Λ h).obj U)) := by
  set T := (ell Λ h).obj U
  have hc := isCop Λ T
  obtain ⟨σ, ⟨h1, h2⟩, -⟩ := hc.2 (GG Λ T) hc.1 (rr Λ T) (ll Λ T)
  have hσ : σ ≫ σ = 𝟙 _ := by
    obtain ⟨c, -, hu⟩ := hc.2 (GG Λ T) hc.1 (ll Λ T) (rr Λ T)
    exact (hu (σ ≫ σ) ⟨(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ σ) h1).trans h2),
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ σ) h2).trans h1)⟩).trans
      (hu (𝟙 _) ⟨Category.comp_id _, Category.comp_id _⟩).symm
  have hi : IsIso σ := ⟨σ, hσ, hσ⟩
  obtain ⟨hiso, hcomp, -⟩ := GlobalTheory.T.fourTermComplex_quasiIsoAt_formal_properties (Thick D.κ D.t) (KK D.κ D.t)
  exact h1 ▸ hcomp _ _ _ _ _ (qat_ll Λ T) (hiso _ _ σ)

theorem qat_map_id (U : AffOp D.X) {B : Thick D.κ D.t} (f : Λ.L.obj U ⟶ B) (hf : (KK D.κ D.t).QAt f) :
    (KK D.κ D.t).QAt (Λ.L.map (𝟙 U) ≫ f) := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact hf

theorem resMap_bij : (KL (D := D) (n := n)).resMap (ell Λ h) |>.Bij := by
  refine GlobalTheory.T.fourTermComplex_restriction_bijective_collapse (CC D n) (AffOp D.X) KL (ell Λ h) (qq D n) (SS Λ) (uu Λ) (ww Λ h) (eps Λ h)
    (fun T ↦ qat_ll Λ T) (fun U ↦ ?_)
  rw [qat_iff]
  exact qat_map_id Λ U _ (qat_rr Λ h U)

end GlobalTheory.PDForm.LevLift

theorem GlobalTheory.PDForm.levLift_resMap_bij : ∀ (D : Data) (Λ : Lift D) (n : ℕ) (h : ∀ U, LevE D.κ D.t D.i (n + 1) (Λ.toE.obj U)),
    ((((KK D.κ D.t).res (pE D.κ D.t D.i)).res (LevE D.κ D.t D.i (n + 1)).ι).resMap
      ((LevE D.κ D.t D.i (n + 1)).lift Λ.toE h)).Bij :=
  fun _ Λ _ h ↦ GlobalTheory.PDForm.LevLift.resMap_bij Λ h
