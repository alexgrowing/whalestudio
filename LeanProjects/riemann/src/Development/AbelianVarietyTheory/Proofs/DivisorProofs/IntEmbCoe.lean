import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FrobeniusTwistEigen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistEigen

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CurveRootGeometry

section Defs

variable {O : Type} [CommRing O]

def IsActPull {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] (i' : OAct O G') (i : OAct O G)
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) : Prop :=
  IsGrpPullback G' G f φ ∧ ∀ a, (i'.act a).left ≫ φ = φ ≫ (i.act a).left

def IsCover (k : Type) [Field k] {C C' : Scheme.{0}} [Algebra k Γ(C, ⊤)] [Algebra k Γ(C', ⊤)] (π : C' ⟶ C) : Prop :=
  IsFinite π ∧ Surjective π ∧ π ≫ strHom k C = strHom k C'

def IsRosati (c : O →+* O) {S : Scheme.{0}} (P : Out.PolAV S) (j : OAct O P.A) : Prop :=
  ∀ a, Out.RosatiAdj P.A P.L (j.act a) (j.act (c a))

def PolPart (c : O →+* O) {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (i : OAct O G) : Prop :=
  ∃ (T : TorusExtension G) (P : Out.PolAV (Sp K)) (e : T.B ≅ P.A) (j : OAct O P.A),
    IsMonHom (T.q ≫ e.hom) ∧ (∀ a, i.act a ≫ T.q ≫ e.hom = (T.q ≫ e.hom) ≫ j.act a) ∧ IsRosati c P j

def genPt (C : Scheme.{0}) [IsIntegral C] : Sp C.functionField ⟶ C := C.fromSpecStalk (genericPoint C)

def geomGenPt (C : Scheme.{0}) [IsIntegral C] : Sp (AlgebraicClosure C.functionField) ⟶ C :=
  spMap (algebraMap C.functionField (AlgebraicClosure C.functionField)) ≫ genPt C

def PolGen (c : O →+* O) {C : Scheme.{0}} [IsIntegral C] {G : Over C} [GrpObj G] (i : OAct O G) : Prop :=
  ∃ (G' : Over (Sp (AlgebraicClosure C.functionField))) (_ : GrpObj G') (i' : OAct O G') (φ : G'.left ⟶ G.left),
    IsActPull i' i (geomGenPt C) φ ∧ PolPart c i'

def AbGen (c : O →+* O) {C : Scheme.{0}} [IsIntegral C] {G : Over C} [GrpObj G] (i : OAct O G) : Prop :=
  ∃ (P : Out.PolAV (Sp C.functionField)) (j : OAct O P.A) (φ : P.A.left ⟶ G.left),
    IsActPull j i (genPt C) φ ∧ IsRosati c P j

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
  {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G)

def HasDieu : Prop :=
  ∃ (D : C.Modules) (g : ℕ) (ρ : O →+* End D) (a : omega G ⟶ D) (b : D ⟶ Lie G)
    (u : frobTwist q k (Lie G) ⟶ D) (v : D ⟶ frobTwist q k (omega G)) (w₁ : a ≫ b = 0) (w₂ : u ≫ v = 0),
    IsVB (omega G) g ∧ IsVB D (2 * g) ∧ (ShortComplex.mk a b w₁).ShortExact ∧ (ShortComplex.mk u v w₂).ShortExact ∧
    IsEquivariant (omegaAct i) ρ a ∧ IsEquivariant ρ ((lieAct i).comp c) b ∧
    IsEquivariant (pullAct ((lieAct i).comp c) (frob C q (natCast_eq_zero C q k))) ρ u ∧
    IsEquivariant ρ (pullAct (omegaAct i) (frob C q (natCast_eq_zero C q k))) v

def HasSeq : Prop :=
  ∃ (H : (O →+* k) → C.Modules) (rL rH : (O →+* k) → ℕ) (D : C.Modules) (g : ℕ),
    (∀ σ, IsVB (lieSub i (scal C σ)) (rL σ)) ∧ (∀ σ, IsVB (H σ) (rH σ)) ∧
    (∀ σ, IsExtension (dual (lieSub i (scal C σ))) (H σ) (lieSub i (scal C (σ.comp c)))) ∧
    (∀ σ, IsExtension (frobTwist q k (lieSub i (scal C (σ.comp c)))) (H ((frobenius k q).comp σ))
      (frobTwist q k (dual (lieSub i (scal C σ))))) ∧
    IsVB (Lie G) g ∧ IsVB D (2 * g) ∧ IsExtension (dual (Lie G)) D (Lie G) ∧
    (∃ v : frobTwist q k (Lie G) ⟶ D, Mono v) ∧
    Nonempty (Lie G ≅ ∐ fun σ : O →+* k => lieSub i (scal C (σ.comp c)))

def DegRel [IsIntegral C] {C' : Scheme.{0}} [Algebra k Γ(C', ⊤)] [IsIntegral C'] {G' : Over C'} [GrpObj G']
    [QuasiSeparated G'.hom] (i' : OAct O G') (m : ℕ) : Prop :=
  (∀ σ : O →+* k, deg k (lieSub i' (scal C' σ)) = m * deg k (lieSub i (scal C σ))) ∧
    ∀ d ∈ subDegs k (Lie G), ∃ d' ∈ subDegs k (Lie G'), m * d ≤ d'

end Defs

def Splits (O k : Type) [CommRing O] [Field k] : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (τ : κ → (O →+* k)), IsSplitBy τ

def intEmb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) (τ : E →+* ℂ) :
    𝓞 E →+* 𝓞 c.F := RingOfIntegers.mapRingHom (Formalism.L2.Pj.embF c τ)

section Lemmas

variable {O : Type} [CommRing O]

theorem IsActPull.comp {S S' S'' : Scheme.{0}} {G'' : Over S''} [GrpObj G''] {G' : Over S'} [GrpObj G'] {G : Over S}
    [GrpObj G] {i'' : OAct O G''} {i' : OAct O G'} {i : OAct O G} {g : S'' ⟶ S'} {f : S' ⟶ S} {φ' : G''.left ⟶ G'.left}
    {φ : G'.left ⟶ G.left} (h' : IsActPull i'' i' g φ') (h : IsActPull i' i f φ) : IsActPull i'' i (g ≫ f) (φ' ≫ φ) :=
  ⟨h'.1.comp h.1, fun a => by rw [← Category.assoc, h'.2, Category.assoc, h.2, Category.assoc]⟩

theorem DegRel.trans {k : Type} [Field k] {C C' C'' : Scheme.{0}} [Algebra k Γ(C, ⊤)] [Algebra k Γ(C', ⊤)]
    [Algebra k Γ(C'', ⊤)] [IsIntegral C] [IsIntegral C'] [IsIntegral C''] {G : Over C} [GrpObj G] [QuasiSeparated G.hom]
    {G' : Over C'} [GrpObj G'] [QuasiSeparated G'.hom] {G'' : Over C''} [GrpObj G''] [QuasiSeparated G''.hom]
    {i : OAct O G} {i' : OAct O G'} {i'' : OAct O G''} {m n : ℕ} (h : DegRel k i i' m) (h' : DegRel k i' i'' n) :
    DegRel k i i'' (n * m) := by
  refine ⟨fun σ => by rw [h'.1, h.1]; push_cast; ring, fun d hd => ?_⟩
  obtain ⟨d', hd', e⟩ := h.2 d hd
  obtain ⟨d'', hd'', e'⟩ := h'.2 d' hd'
  refine ⟨d'', hd'', le_trans ?_ e'⟩
  push_cast
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left e (Nat.cast_nonneg _)

theorem DegRel.refl {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] [IsIntegral C] {G : Over C} [GrpObj G]
    [QuasiSeparated G.hom] (i : OAct O G) : DegRel k i i 1 :=
  ⟨fun _ => by simp, fun d hd => ⟨d, hd, by simp⟩⟩

example (k : Type) [Field k] : Splits ℤ k :=
  ⟨Unit, inferInstance, fun _ => Int.castRingHom k, isSplitBy_of_injective (fun _ _ _ => rfl) (by simp)⟩

end Lemmas

end GlobalTheory.CurveRootGeometry
