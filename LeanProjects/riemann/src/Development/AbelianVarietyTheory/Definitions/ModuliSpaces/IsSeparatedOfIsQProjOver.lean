import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

structure SFam (h k : ℕ) {o : Type} [CommRing o] (ζ : o) where

  X : Scheme.{0}

  s : X ⟶ Sp o

  smooth : SmoothOfRelativeDimension (h * (h + 1) / 2) s

  qproj : IsQProjOver s

  univ : SiegPre h k ζ s

  princ : univ.Principal

  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (c : SiegPre h k ζ s'), IsReduced S → Dense {x : S | (s' x).asIdeal = ⊥} →
    c.Principal → ∃ f : S ⟶ X, f ≫ s = s' ∧ SiegPB c univ f

  inj : ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ X) (s' : Sp R ⟶ Sp o) (c : SiegPre h k ζ s'),
    x ≫ s = y ≫ s → SiegPB c univ x → SiegPB c univ y → x = y

def SRep {h p M : ℕ} (Ag : SiegelFamily h p M) : Prop :=
  IsSeparated Ag.s ∧ ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (ZP p M)) (c : SiegPre h M (zetaZP p M) s'), IsReduced S →
    Dense {x : S | (s' x).asIdeal = ⊥} → c.Principal → ∃ f : S ⟶ Ag.X, f ≫ Ag.s = s' ∧ SiegPB c Ag.univ f

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def LevUnder (D : Datum H) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (t : TObj g k J b s) (τ : SAB H S)
    (lev : D.La → (𝟙_ (Over S) ⟶ τ.G)) : Prop :=
  ∃ φ : τ.G ≅ t.A, IsMonHom φ.hom ∧ LBIso τ.PP.L (t.L.pull φ.hom.left) ∧
    (∀ j, τ.act.act (a j) ≫ φ.hom = φ.hom ≫ t.act j) ∧ (∀ x y, lev (x + y) = lev x * lev y) ∧
    ∀ i, (lev (bas (Pi.single i 1)) ≫ φ.hom).left = (t.pt i).left

def TSieg {La : Type} [AddCommGroup La] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La)
    (t : TObj g k J b s) {B : Type} [CommRing B] {ζ : B} {s' : S ⟶ Sp B} (c : SiegPre g k ζ s') : Prop :=
  letI := t.ab.comm
  ∃ φ : c.A ≅ t.A, IsMonHom φ.hom ∧ LBIso c.P ((abelian₂ t.A t.L).pull (φ.hom ⊗ₘ φ.hom).left) ∧
    ∀ i, (c.lev (bas'.symm (bas (Pi.single i 1))) ≫ φ.hom).left = (t.pt i).left

structure PELRep (D : Datum H) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (t : TObj g k J b s) :
    Prop where

  qproj : IsQProjOver s

  flat : Flat s

  red : IsReduced S

  rep : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (β : o →+* V) (t' : TObj g k J b (spMap β))
    (τ' : SAB H (Sp V)), Function.Injective β → IsPEL D a bas ρ t' τ' → ∃ f : Sp V ⟶ S, f ≫ s = spMap β ∧ TMap t' t f

  inj : ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ S) (s' : Sp R ⟶ Sp o) (t' : TObj g k J b s'),
    x ≫ s = y ≫ s → TMap t' t x → TMap t' t y → x = y

theorem isSeparated_of_isQProjOver {X : Scheme.{0}} {f : X ⟶ Sp o} (h : IsQProjOver f) : IsSeparated f := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have : IsImmersion i := hi
  unfold PSpace.str
  infer_instance

theorem SFam.isSeparated {h : ℕ} {ζ : o} (F : SFam h k ζ) : IsSeparated F.s := isSeparated_of_isQProjOver F.qproj

theorem SFam.eq_constPt {h : ℕ} {ζ : o} (F : SFam h k ζ) (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ F.X)
    (c : SiegPre h k ζ (x ≫ F.s)) (hs : x ≫ F.s = constPt x ≫ F.s) (h₁ : SiegPB c F.univ x)
    (h₂ : SiegPB c F.univ (constPt x)) : x = constPt x := F.inj (DualNumber K) x (constPt x) (x ≫ F.s) c hs h₁ h₂

theorem SFam.sRep {h p M : ℕ} (F : SFam h M (zetaZP p M))
    (sm : SmoothOfRelativeDimension (h * (h + 1) / 2) F.s) (qc : QuasiCompact F.s) (pr : F.univ.Principal) (pts unr) :
    SRep (⟨F.X, F.s, sm, qc, F.univ, pr, pts, unr⟩ : SiegelFamily h p M) := ⟨F.isSeparated, fun S s' c hS hd hc => F.rep S s' c hS hd hc⟩

theorem PELRep.isSeparated {D : Datum H} {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {ρ : o}
    {t : TObj g k J b s} (h : PELRep D a bas ρ t) : IsSeparated s := isSeparated_of_isQProjOver h.qproj

theorem LevUnder.lev_zero {D : Datum H} {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {t : TObj g k J b s}
    {τ : SAB H S} {lev : D.La → (𝟙_ (Over S) ⟶ τ.G)} (h : LevUnder D a bas t τ lev) : lev 0 = 1 := by
  obtain ⟨-, -, -, -, hadd, -⟩ := h
  have h0 : lev 0 * lev 0 = lev 0 * 1 := by rw [← hadd, add_zero, _root_.mul_one]
  exact _root_.mul_left_cancel h0

theorem LevUnder.lev_bas_pow {D : Datum H} {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {t : TObj g k J b s}
    {τ : SAB H S} {lev : D.La → (𝟙_ (Over S) ⟶ τ.G)} (h : LevUnder D a bas t τ lev) (i : Fin (2 * g)) :
    lev (bas (Pi.single i 1)) ^ k = 1 := by
  obtain ⟨φ, hφ, -, -, -, hpt⟩ := h
  haveI := hφ
  have e : lev (bas (Pi.single i 1)) ≫ φ.hom = t.pt i := Over.OverMorphism.ext (hpt i)
  apply (cancel_mono φ.hom).1
  rw [MonObj.pow_comp, e, t.torsion i, MonObj.one_comp]

end GlobalTheory.ZM
end
