import Development.WeilBound.CoreStatements.SesquilinearFractions.IntegralLieModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.cm_lie_model_action

open PositivityTheory.Xgf.isogeny_decomposition_product

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n}
  {Z : ∀ b : Bool, Curve0 H (sgnRt H b)} {P : (FU.Di i).La →+ (Fin g → ℂ)} {hP : IsPeriod (FU.Di i) ty P}

def ImageIff (X : CMPack Z c FU i hP) : Prop := ∀ b a u, X.IsImage b a u ↔ u = (Mm X).pt (lam X b a)

def LamSmul (X : CMPack Z c FU i hP) : Prop := ∀ b (s : 𝓞 E) a, lam X b (s • a) = ρm X s (lam X b a)

def LamAdd (X : CMPack Z c FU i hP) : Prop := ∀ b a a', lam X b (a + a') = lam X b a + lam X b a'

def LamRt (X : CMPack Z c FU i hP) : Prop :=
  ∀ b (s : X.K) a, (s : ℂ) = sgnRt H b → ρm X H.rt (lam X b a) = s • lam X b a

def CMVecIff (X : CMPack Z c FU i hP) : Prop :=
  ∀ b (τ : E →+* ℂ) a v, X.IsCMVec b τ a v ↔ v = (Mm X).pt (HT.eigProj (ρm X) (X.β.comp (tauE c τ)) (lam X b a))

end PositivityTheory.Xgf.cm_lie_model_action

namespace PositivityTheory.Xgf

open PositivityTheory.Xgf.cm_lie_model_action in
theorem cm_pack_lie_properties (h : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty)
    (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP),
      ImageIff X ∧ LamSmul X ∧ LamAdd X ∧ LamRt X ∧ CMVecIff X) :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP), ∃ (M : LieModel Xo.univ.t.G (under X.y) (Fin g → X.K)) (ρ : 𝓞 E →+* Module.End X.K (Fin g → X.K)) (lam : ∀ b, PureType.lat hP (sgnRt H b) → Fin g → X.K), M.IsActOf Xo.univ.t.act.act ρ ∧ (∀ b a u, X.IsImage b a u ↔ u = M.pt (lam b a)) ∧ (∀ b (s : 𝓞 E) a, lam b (s • a) = ρ s (lam b a)) ∧ (∀ b a a', lam b (a + a') = lam b a + lam b a') ∧ (∀ b (s : X.K) a, (s : ℂ) = sgnRt H b → ρ H.rt (lam b a) = s • lam b a) ∧ ∀ b (τ : E →+* ℂ) a v, X.IsCMVec b τ a v ↔ v = M.pt (HT.eigProj ρ (X.β.comp (tauE c τ)) (lam b a)) := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X
  obtain ⟨h1, h2, h3, h4, h5⟩ := h E H D l Xo c g ty FU i Z P hP X
  exact ⟨Mm X, ρm X, lam X, hρm X, h1, h2, h3, h4, h5⟩

end PositivityTheory.Xgf

end
