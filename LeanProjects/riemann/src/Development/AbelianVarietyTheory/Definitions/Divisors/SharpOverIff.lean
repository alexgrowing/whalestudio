import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Eq8

section Char

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D' : DegData V (maximalIdeal V)}
  {A' : PolAV (Sp (FractionRing V))} {G' : Over (Sp V)} [GrpObj G'] [IsCommMonObj G']

def EndChar (U : Unif (maximalIdeal R) D A G) (f : G ⟶ G) (m : D.toPre.X →+ D.toPre.X) : Prop :=
  ∀ (κ : Type) [Field κ] (a : R →+* κ) (ha : ∀ x ∈ maximalIdeal R ^ (0 + 1), a x = 0) (G₀ : Over (Sp κ)) [GrpObj G₀]
    (φ : G₀.left ⟶ G.left) (h : IsGrpPullback G₀ G (spMap a) φ) (f₀ : G₀ ⟶ G₀), f₀.left ≫ φ = φ ≫ f.left →
    GlobalTheory.TorusPart.gtTorus (U.gt 0) ha h ≫ f₀ =
      GlobalTheory.SplitTorus.torusMap (Sp κ) m ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) ha h

def CoordMap (D : DegPre R) (D' : DegPre V) (g : R →+* V) (ρ : D.X →+ D'.X) : Prop :=
  ∀ y r r', PsiCoord D y r → PsiCoord D' (ρ y) r' → Associated (g r) r'

def EquivMap (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal V) D' A' G') (β : G'.left ⟶ G.left)
    (ρ : D.toPre.X →+ D'.toPre.X) : Prop :=
  ∀ (f : G ⟶ G) (f' : G' ⟶ G'), IsMonHom f → IsMonHom f' → f'.left ≫ β = β ≫ f.left →
    ∀ m m', EndChar U f m → EndChar U' f' m' → ∀ y, ρ (m y) = m' (ρ y)

end Char

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

def SharpBy (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) {T : Scheme.{0}} (P : PolAV T) (u : T ⟶ F.X)
    (c : SiegPre g n ζ (u ≫ F.s)) (pr : Fin 8 → (P.A ⟶ c.A)) : Prop :=
  SiegPB c F.univ u ∧ (∀ a, IsMonHom (pr a)) ∧
    (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y a) ∧
    LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2))

theorem sharpOver_iff (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) {T : Scheme.{0}} (P : PolAV T) (u : T ⟶ F.X) :
    SharpOver F W P u ↔ ∃ c pr, SharpBy F W P u c pr :=
  ⟨fun ⟨c, h, pr, h'⟩ => ⟨c, pr, h, h'⟩, fun ⟨c, pr, h, h'⟩ => ⟨c, h, pr, h'⟩⟩

def MatEnd {T : Scheme.{0}} {B C : Over T} [GrpObj B] [GrpObj C] (pr : Fin 8 → (B ⟶ C)) (a b : Fin 8) (f : B ⟶ B) : Prop :=
  IsMonHom f ∧ ∀ w, f ≫ pr w = if w = a then pr b else 1

def MatRel (W : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (a b : Fin 8) (y y' : Fin 8 → X) : Prop :=
  ∀ v, ∑ u, (W + W.transpose) v u • y' u = if v = b then ∑ u, (W + W.transpose) a u • y u else 0

def IsCpl {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] (j : O →+* R) : Prop :=
  ∃ e : AdicCompletion (maximalIdeal O) O ≃+* R, ∀ a, e (algebraMap O _ a) = j a

theorem isCpl_self (O : Type) [CommRing O] [IsLocalRing O] :
    IsCpl (algebraMap O (AdicCompletion (maximalIdeal O) O)) :=
  ⟨RingEquiv.refl _, fun _ => rfl⟩

open Classical in

def MatOn {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω}
    {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {C : Over (Sp S.R)} [GrpObj C] (pr : Fin 8 → (ρ.P.A ⟶ C))
    (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) : Prop :=
  IsMonHom f ∧ ∃ f₁ : ρ.P.A ⟶ ρ.P.A, MatEnd pr a b f₁ ∧
    ((Over.pullback FinalForm.u₀).map f₁).left ≫ FinalForm.φ = FinalForm.φ ≫ f.left

end GlobalTheory.Poinc.Eq8
