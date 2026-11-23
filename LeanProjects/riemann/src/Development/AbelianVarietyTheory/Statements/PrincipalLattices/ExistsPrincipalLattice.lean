import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsEmptyCmLatZero
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM

def TensorObjSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k → D.p = 0 ∨ D.q = 0 →
    ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hk : KA l ≤ K₁) (ω : 𝓞 K₁) (C : Ell H (𝓞 K₁) ω) (ε : ℤˣ)
      (h : D.La → D.La → OK H) (T : PAT H (Sp (𝓞 K₁)))
      (o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion hk).toRingHom)),
      k ≤ K₁ ∧ C.IsPrincipalAt ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁)) ∧
      IsKForm D ε h ∧ Nonempty (IsTen C D h T) ∧ Nonempty (SABMap o.t T.t (spMap (algebraMap (𝓞 K₁) K₁)))

def CMExistsSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (Z : CMLat hP D.p D.q)
    (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k →
    ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hk : KA l ≤ K₁) (ρ : 𝓞 K₁)
      (X : CMObj H K₁ ρ (algebraMap K₁ ℂ) D.p D.q) (y : Sp K₁ ⟶ Xo.X) (t₀ : SAB H (Sp K₁))
      (m : SABMap t₀ Xo.univ.t y) (m' : SABMap t₀ X.B.t (spMap (algebraMap (𝓞 K₁) K₁)))
      (gA : Bool → ℕ) (tyA : ∀ b, Fin (gA b) → (E →+* ℂ)) (PA : ∀ b, (Z.D₁ b).La →+ (Fin (gA b) → ℂ))
      (e : ∀ b, (Fin (gA b) → ℂ) → (Over.mk (spMap ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁))) ⟶ (X.A b).t.G))
      (F : ∀ j : Fin D.p ⊕ Fin D.q, (Fin (gA j.isLeft) → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      k ≤ K₁ ∧ ((ρ : K₁) : ℂ) = H.rt0 ∧ X.hh = Z.hh ∧
      y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe ∧
      (∀ b, IsTypeFn H (Z.D₁ b).p (Z.D₁ b).q (tyA b) ∧ IsExp (X.A b) _ (Z.D₁ b) (tyA b) (PA b) (e b)) ∧
      (∀ j a, F j (PA _ a) = Pe (Z.f j a)) ∧
      ∀ (j : Fin D.p ⊕ Fin D.q) (z : Fin (gA j.isLeft) → ℂ) (x : Sp ℂ ⟶ t₀.G.left), x ≫ t₀.G.hom = spMap (algebraMap K₁ ℂ) →
        x ≫ m'.φ = (e _ z ≫ X.φ j).left → x ≫ m.φ = (FU.ex i Pe (F j z)).left

namespace ExSt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem hypotheses_of_datum (h₁ : N1ab) (h₂ : N1c) (D : Datum H) (hp : D.p = 1) (hq : D.q = 0) (l : Level H) :
    ∃ (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
      (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (Z : CMLat hP D.p D.q),
      Nontrivial (FU.Di i).La ∧ ∀ j, Function.Injective (Z.f j) ∧ Z.hh j = 1 := by
  obtain ⟨Xo⟩ := h₁ E H D l (by omega)
  obtain ⟨g, ty, hty⟩ := PureTypeModel.exists_isTypeFn H D.p D.q
  obtain ⟨FU⟩ := h₂ E H D l Xo (algebraMap (KA l) ℂ) g ty (by omega) rfl hty
  let i : Fin FU.n := ⟨0, FU.n_pos⟩
  obtain ⟨a, b⟩ := FU.sig i
  obtain ⟨Pe, hP⟩ := PeriodNonempty.exists_isPeriod E H (FU.Di i) g ty (by rw [a, b]; exact hty)
  have key : ∀ p q : ℕ, p = 1 → q = 0 → IsTypeFn H p q ty →
      ∃ Z : CMLat hP p q, ∀ j, Function.Injective (Z.f j) ∧ Z.hh j = 1 := by
    rintro _ _ rfl rfl hty
    refine ⟨LatModel.selfLat (a.trans hp) (b.trans hq) hP hty, fun j => ?_⟩
    rcases j with j | j
    · exact ⟨fun _ _ h => h, rfl⟩
    · exact j.elim0
  obtain ⟨Z, hZ⟩ := key _ _ hp hq hty
  refine ⟨Xo, g, ty, FU, i, Pe, hP, Z, ?_, hZ⟩
  refine Module.nontrivial_of_finrank_pos (R := 𝓞 E) ?_
  rw [(FU.Di i).rank, a, hp]
  omega

theorem hypotheses_inhabited :
    (∃ (D : Datum LatModel.host) (_ : Level LatModel.host), D.p = 0 ∧ D.q = 1) ∧
    ∃ (D : Datum LatModel.host) (l : Level LatModel.host), D.p = 1 ∧ D.q = 0 ∧ (N1ab → N1c →
      ∃ (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (LatModel.CyclotomicFieldTwentyEight →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty)
        (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (Z : CMLat hP D.p D.q),
        Nontrivial (FU.Di i).La ∧ ∀ j, Function.Injective (Z.f j) ∧ Z.hh j = 1) := by
  obtain ⟨D, hp, hq⟩ := LatModel.exists_datum
  obtain ⟨l⟩ : Nonempty (Level LatModel.host) := inferInstance
  exact ⟨⟨LatModel.negDatum D, l, hq, hp⟩, D, l, hp, hq, fun h₁ h₂ => hypotheses_of_datum h₁ h₂ D hp hq l⟩

theorem existsUnique_point {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {B : SAB H (Sp (𝓞 K))}
    {t₀ : SAB H (Sp K)} (m' : SABMap t₀ B (spMap (algebraMap (𝓞 K) K)))
    (w : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ B.G) :
    ∃! x : Sp ℂ ⟶ t₀.G.left, x ≫ t₀.G.hom = spMap σ ∧ x ≫ m'.φ = w.left := by
  have hw : w.left ≫ B.G.hom = spMap σ ≫ spMap (algebraMap (𝓞 K) K) := by
    rw [Over.w w]
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]; rfl
  refine ⟨m'.cart.1.lift _ _ hw, ⟨m'.cart.1.lift_snd _ _ _, m'.cart.1.lift_fst _ _ _⟩, fun x hx => ?_⟩
  apply m'.cart.1.hom_ext
  · rw [m'.cart.1.lift_fst]; exact hx.2
  · rw [m'.cart.1.lift_snd]; exact hx.1

end ExSt

end GlobalTheory.CM
end
