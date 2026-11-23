import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorObjectExistence

def TensorExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (M : Type) [Field M] [NumberField M] (ω : 𝓞 M)
    (C : Ell H (𝓞 M) ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), IsKForm D ε h →
    (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) →
    ∃ T : PAT H (Sp (𝓞 M)), Nonempty (IsTen C D h T)

def TensorIsObject : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (M : Type) [Field M] [NumberField M] (ω : 𝓞 M)
    (C : Ell H (𝓞 M) ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (T : PAT H (Sp (𝓞 M))), IsKForm D ε h →
    Nonempty (IsTen C D h T) →
    ∀ (l : Level H) (K' : Type) [Field K'] [NumberField K'] (β : 𝓞 M →+* K') (κ : KA l →+* K'),
      (D.q = 0 ∧ κ (baseKA l).ρ = β (2 * ω - 1)) ∨ (D.p = 0 ∧ κ (baseKA l).ρ = -β (2 * ω - 1)) →
      ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (j : K' →+* K₁)
        (o : Obj D l (baseKA l) (spMap (j.comp κ))), Nonempty (SABMap o.t T.t (spMap (j.comp β)))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsExpAt {S : Scheme.{0}} (t : SAB H S) (x : Sp ℂ ⟶ S) (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (Pe : D.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk x ⟶ t.G)) : Prop :=
  IsPeriod D ty Pe ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧
    (∀ z, e z = 1 ↔ z ∈ Pe.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧
    ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • Pe a)) (e ((k : ℂ)⁻¹ • Pe b)) (unitOn c)

def TiedToLattices {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} {hP : IsPeriod D ty Pe}
    {p q : ℕ} (Z : CMLat hP p q) {K : Type} [Field K] [NumberField K] {ρ : 𝓞 K} {σ₁ : K →+* ℂ} (X : CMObj H K ρ σ₁ p q)
    (eB : (Fin g → ℂ) → (Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G)) : Prop :=
  IsExp X.B (σ₁.comp (algebraMap (𝓞 K) K)) D ty Pe eB ∧ X.hh = Z.hh ∧
    ∃ (g₁ : Bool → ℕ) (ty₁ : ∀ b, Fin (g₁ b) → (E →+* ℂ)) (P₁ : ∀ b, (Z.D₁ b).La →+ (Fin (g₁ b) → ℂ))
      (e₁ : ∀ b, (Fin (g₁ b) → ℂ) → (Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A b).t.G)),
      (∀ b, IsTypeFn H (Z.D₁ b).p (Z.D₁ b).q (ty₁ b) ∧
        IsExp (X.A b) (σ₁.comp (algebraMap (𝓞 K) K)) (Z.D₁ b) (ty₁ b) (P₁ b) (e₁ b)) ∧
      ∀ j : Fin p ⊕ Fin q, ∃ F : (Fin (g₁ j.isLeft) → ℂ) →ₗ[ℂ] (Fin g → ℂ),
        (∀ a, F (P₁ j.isLeft a) = Pe (Z.f j a)) ∧ ∀ z, e₁ j.isLeft z ≫ X.φ j = eB (F z)

def PointCarriesObject : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (K' : Type) [Field K'] [NumberField K'] (κ : KA l →+* K') (σ' : K' →+* ℂ) (x : Sp ℂ ⟶ Xo.X)
    (D' : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D'.La →+ (Fin g → ℂ)) (hP : IsPeriod D' ty Pe)
    (e : (Fin g → ℂ) → (Over.mk x ⟶ Xo.univ.t.G)) (Z : CMLat hP D.p D.q),
    1 ≤ D.p + D.q → σ' (κ (baseKA l).ρ) = H.rt0 → x ≫ Xo.s = spMap (σ'.comp κ) → D'.p = D.p → D'.q = D.q → IsTypeFn H D.p D.q ty →
    IsExpAt Xo.univ.t x D' ty Pe e →
    ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (j : K' →+* K₁) (σ₁ : K₁ →+* ℂ) (ρ : 𝓞 K₁)
      (X : CMObj H K₁ ρ σ₁ D.p D.q) (y : Sp K₁ ⟶ Xo.X) (o : Obj D l (baseKA l) (spMap (j.comp κ)))
      (mU : ObjMap o Xo.univ y) (mB : SABMap o.t X.B.t (spMap (algebraMap (𝓞 K₁) K₁)))
      (eB : (Fin g → ℂ) → (Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K₁) K₁))) ⟶ X.B.t.G)),
      σ₁.comp j = σ' ∧ (ρ : K₁) = j (κ (baseKA l).ρ) ∧ y ≫ Xo.s = spMap (j.comp κ) ∧ spMap σ₁ ≫ y = x ∧
      (∀ z, ∃ w : Over.mk (spMap σ₁) ⟶ o.t.G,
        w.left ≫ mU.toSABMap.φ = (e z).left ∧ w.left ≫ mB.φ = (eB z).left) ∧
      TiedToLattices Z X eB

def CMExists : Prop := (TensorExists ∧ TensorIsObject) ∧ PointCarriesObject

theorem isExpAt_of_familyUnif {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) (i : Fin U.n) (Pe : (U.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (U.Di i) ty Pe) : IsExpAt Xo.univ.t (U.u i Pe) (U.Di i) ty Pe (U.ex i Pe) := by
  refine ⟨hP, fun V f => ?_, U.ex_add i Pe hP, U.ex_onto i Pe hP, U.ex_ker i Pe hP, U.ex_lin i Pe hP,
    U.ex_weil i Pe hP⟩
  obtain ⟨h₁, h₂⟩ := (U.hol i 0 Set.univ (fun _ => Pe) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2 V f
  have hd : Differentiable ℂ fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z) := by fun_prop
  refine ⟨?_, ?_⟩
  · simpa using h₁.preimage hd.continuous
  · have h₃ := DifferentiableOn.comp (s := {z ∈ Set.univ | ⊤ ≤ (U.ex i Pe z).left ⁻¹ᵁ V}) h₂ hd.differentiableOn
      fun z hz => Set.mem_sep (Set.mk_mem_prod (Set.mem_univ _) (Set.mem_univ _)) hz.2
    simpa only [Function.comp_def] using h₃

example (D : Datum H) (ε : ℤˣ) : ∃ h : D.La → D.La → OK H, IsKForm D ε h :=
  ⟨fun x y => (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : OK H) + (((ε : ℤ) * D.EF x y : ℤ) : OK H) * wK H,
    fun x y => by simp [wK]⟩

end GlobalTheory.IndefiniteRowSideFullHecke.TensorObjectExistence
end
