import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open GlobalTheory.FlagMod (FlagCover FlagModel Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IsFrameAt {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) {R : Type} [CommRing R]
    {φ : c.F →+* R} (z : Sp R ⟶ Z) (k : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (g : EigFrame Y φ (z ≫ π)) : Prop :=
  ∀ σ i, g.v σ i = (tv (F.vecAt k z hz rfl σ i)).left

def Rel {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)
    (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K] (z : Sp K ⟶ Z) (p : Sp K ⟶ C.Y.X) : Prop :=
  ∃ (φ : c.F →+* K) (k : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (g : EigFrame Y φ (z ≫ π)),
    z ≫ π ≫ Y.s = spMap φ ∧ IsFrameAt F z k hz g ∧ C.Carries p g

def FramesExist {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : c.F →+* R) (z : Sp R ⟶ X.YY) (k : X.F.J) (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k),
    z ≫ X.π ≫ Y.s = spMap φ → ∃ g : EigFrame Y φ (z ≫ X.π), IsFrameAt X.F z k hz g

def CarriesTri {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) : Prop :=
  ∀ (K : Type) [Field K] (φ φ' : c.F →+* K) (x : Sp K ⟶ Y.X) (p : Sp K ⟶ C.Y.X) (g : EigFrame Y φ x)
    (g' : EigFrame Y φ' x), C.Carries p g → C.Carries p g' → ∃ t, g.Tri (RingHom.id K) g' t

def Vo {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) : C.Y.X.Opens :=
  C.π ⁻¹ᵁ ⟨Set.range Y.jQ, (haveI := Y.jQ_open; Y.jQ.isOpenEmbedding.isOpen_range)⟩

open GlobalTheory.Toroidal (gen genι genStr) in

instance isIso_genι {Y : Model Xo c (RingHom.id c.F)} : IsIso (genι Y) := by
  have : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (𝟙 _))
    infer_instance
  exact inferInstanceAs (IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))))

end GlobalTheory.VarFlag
