import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.CM.ExStModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def zeroDatum (H : Host E) : Datum H where
  La := PUnit
  fin := inferInstance
  proj := inferInstance
  EF := 0
  alt _ := rfl
  unimod := ⟨fun _ _ _ => rfl, fun f => ⟨0, by ext x; rw [Subsingleton.elim x 0, map_zero, map_zero]⟩⟩
  adj _ _ _ := rfl
  p := 0
  q := 0
  rank := Module.finrank_zero_of_subsingleton
  dom := by
    have hs : Subsingleton (ℝ ⊗[ℤ] PUnit.{1}) := inferInstance
    refine ⟨0, fun x => Subsingleton.elim _ _, fun x y => by simp, fun x hx => absurd (Subsingleton.elim _ _) hx, ?_⟩
    intro a A t _ ht
    rw [Subsingleton.elim A 0, ht]
    simp

theorem unit_comp {S S' T : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (s : T ⟶ S')
    (s₀ : T ⟶ S) (h : s ≫ f = s₀) :
    (1 : Over.mk s ⟶ t'.G).left ≫ m.φ = (1 : Over.mk s₀ ⟶ t.G).left := by
  subst h
  have e1 : (1 : Over.mk s ⟶ t'.G).left = s ≫ eSec t'.G := by
    rw [Hom.one_def]; simp [eSec]
  have e2 : (1 : Over.mk (s ≫ f) ⟶ t.G).left = (s ≫ f) ≫ eSec t.G := by
    rw [Hom.one_def]; simp [eSec]
  have e3 := m.cm.e_comm
  rw [m.base] at e3
  rw [e1, e2]
  simp only [Category.assoc]
  exact congrArg (s ≫ ·) e3

theorem hh_real {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} {hP : IsPeriod D ty Pe}
    {p q : ℕ} (Z : CMLat hP p q) (j : Fin p ⊕ Fin q) (a : (Z.D₁ j.isLeft).La) : H.bar (Z.hh j) • a = Z.hh j • a := by
  have skew : ∀ (D : Datum H) (x y : D.La), D.EF x y = -D.EF y x := fun D x y => by
    have := D.alt (x + y)
    simp only [map_add, LinearMap.add_apply, D.alt] at this
    linarith
  apply (Z.D₁ j.isLeft).unimod.1
  ext b
  rw [skew, ← Datum.adj, ← Z.form, ← Z.form, ← skew]

theorem phi_ne_one (hS : CMExistsSt) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (Z : CMLat hP D.p D.q) :
    ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (ρ : 𝓞 K₁) (X : CMObj H K₁ ρ (algebraMap K₁ ℂ) D.p D.q),
      X.hh = Z.hh ∧ ∀ j, Z.f j ≠ 0 → X.φ j ≠ 1 := by
  obtain ⟨K₁, hK, hk, ρ, X, y, t₀, m, m', gA, tyA, PA, e, F, -, -, hh, -, hy, -, hF, hx⟩ :=
    hS E H D l Xo g ty FU i Pe hP Z ⊥ inferInstance
  refine ⟨K₁, hK, ρ, X, hh, fun j hj h1 => hj ?_⟩
  have hmem : ∀ z, F j z ∈ Pe.range := fun z => by
    rw [← FU.ex_ker i Pe hP]
    have hc : spMap (algebraMap K₁ ℂ) ≫ spMap (algebraMap (𝓞 K₁) K₁) =
        spMap ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁)) := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]; rfl
    have := hx j z (1 : Over.mk (spMap (algebraMap K₁ ℂ)) ⟶ t₀.G).left (Over.w _) (by
      rw [unit_comp m' _ _ hc, h1]; simp)
    rw [unit_comp m _ _ hy] at this
    exact Over.OverMorphism.ext this.symm
  have hz : ∀ z, F j z = 0 := fun z => by
    haveI := hP.2.2.1
    have hcont : Continuous fun c : ℂ => (⟨F j (c • z), hmem _⟩ : Pe.range) := by
      refine Continuous.subtype_mk ?_ _
      simp only [map_smul]
      fun_prop
    have := PreconnectedSpace.constant inferInstance hcont (x := 1) (y := 0)
    simpa using this
  ext a
  apply hP.2.1
  rw [← hF, hz]; simp

theorem kForm_diag {D : Datum H} {ε : ℤˣ} {h : D.La → D.La → OK H} (hh : IsKForm D ε h) (x : D.La) :
    ((h x x : OK H) : 𝓞 E) = (((ε : ℤ) * D.EF (H.w0 • x) x : ℤ) : 𝓞 E) := by
  rw [hh, D.alt]; simp

end GlobalTheory.CM.ExStModel
end
