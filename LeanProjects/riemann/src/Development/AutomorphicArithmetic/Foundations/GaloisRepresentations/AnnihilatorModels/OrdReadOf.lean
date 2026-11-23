import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.FrobKill
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.crystallineComparison.Mod

def LiftPt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)] (B : Type) [CommRing B] [Algebra V B]
    [Module.Finite V B] [Module.Free V B] (χ : B →+* IsLocalRing.ResidueField V), χ.comp (algebraMap V B) = IsLocalRing.residue V →
    ∃ z : B →ₐ[V] V, (IsLocalRing.residue V).comp z.toRingHom = χ

def ResClosed : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)], IsAlgClosed (IsLocalRing.ResidueField V)

def SplitAlg : Prop :=
  ∀ (κ B Λ : Type) [Field κ] [CommRing B] [Algebra κ B] [Module.Finite κ B] [CommRing Λ] [IsLocalRing Λ] [Algebra κ Λ],
    Nat.card (B →ₐ[κ] κ) = Module.finrank κ B → ∀ (ε : Λ →ₐ[κ] κ) (g : B →ₐ[κ] Λ), g = (Algebra.ofId κ Λ).comp (ε.comp g)

def RingHomog : Prop :=
  ∀ (κ B : Type) [Field κ] [IsAlgClosed κ] [CommRing B] [Algebra κ B] [Module.Finite κ B] (ε₀ : B →ₐ[κ] κ)
    [(RingHom.ker ε₀.toRingHom).IsPrime], (∀ ε : B →ₐ[κ] κ, ∃ τ : B ≃ₐ[κ] B, ε₀.comp τ.toAlgHom = ε) →
    Module.finrank κ B = Nat.card (B →ₐ[κ] κ) * Module.finrank κ (Localization.AtPrime (RingHom.ker ε₀.toRingHom))

def CotanOne : Prop :=
  ∀ (κ B : Type) [Field κ] [CommRing B] [Algebra κ B] (ε : B →ₐ[κ] κ) (v₀ : B →ₐ[κ] DualNumber κ),
    (∀ v : B →ₐ[κ] DualNumber κ, (TrivSqZeroExt.fstHom κ κ κ).comp v = ε → ∃ c : κ, ∀ x, (v x).snd = c * (v₀ x).snd) →
    ∃ t ∈ RingHom.ker ε.toRingHom, RingHom.ker ε.toRingHom ≤ Ideal.span {t} ⊔ RingHom.ker ε.toRingHom ^ 2

def ChainLoc : Prop :=
  ∀ (κ Λ : Type) [Field κ] [CommRing Λ] [IsLocalRing Λ] [Algebra κ Λ] [Module.Finite κ Λ] (ε : Λ →ₐ[κ] κ) (t : Λ),
    IsLocalRing.maximalIdeal Λ = Ideal.span {t} → ∀ (J : Ideal Λ) (q : ℕ), Module.finrank κ (Λ ⧸ J) = q → J = Ideal.span {t ^ q}

def ChainRing : Prop :=
  ∀ (κ B B' Λ : Type) [Field κ] [CommRing B] [Algebra κ B] [Module.Finite κ B] [CommRing B'] [Algebra κ B'] [CommRing Λ] [IsLocalRing Λ]
    [Algebra κ Λ] (π : B →ₐ[κ] B') (ε' : B' →ₐ[κ] κ) [(RingHom.ker ε'.toRingHom).IsPrime] (q : ℕ), Function.Surjective π →
    Module.finrank κ (Localization.AtPrime (RingHom.ker ε'.toRingHom)) = q →
    (∃ t ∈ RingHom.ker (ε'.comp π).toRingHom,
      RingHom.ker (ε'.comp π).toRingHom ≤ Ideal.span {t} ⊔ RingHom.ker (ε'.comp π).toRingHom ^ 2) →
    ∀ (εΛ : Λ →ₐ[κ] κ) (g : B →ₐ[κ] Λ), εΛ.comp g = ε'.comp π →
      ((∀ x, π x = 0 → g x = 0) ↔ ∀ x, ε' (π x) = 0 → g x ^ q = 0)

def RedPts : Prop :=
  ∀ (k H X : Type) [Field k] [Finite k] [AddCommGroup H] [Module k H] [Module.Finite k H] (C : Submodule k H) (ρ : H → X),
    (∀ a b, ρ a = ρ b ↔ a - b ∈ C) → ∀ D : Submodule k H,
    Nat.card (ρ '' (D : Set H)) = Nat.card k ^ Module.finrank k (D.map C.mkQ) ∧
      ∀ D' : Submodule k H, D.map C.mkQ = D'.map C.mkQ → ρ '' (D : Set H) = ρ '' (D' : Set H)

def OrdReadOf : Prop :=
  ∀ (q n : ℕ) (P : Type) (F : P → P) (I : Fin (n + 1) → Type) (v : ∀ j, I j → P) (k H : Type) [Field k] [Finite k] [AddCommGroup H]
    [Module k H] [Module.Finite k H] (C : Submodule k H) (e : ∀ j, I j ≃ Gr k H j), Nat.card k = q → Module.finrank k H = n →
    Module.finrank k C = 1 →
    (∀ j z z', ¬ C ≤ (e j z).1 → ¬ C ≤ (e j z').1 → (e j z).1.map C.mkQ = (e j z').1.map C.mkQ → v j z = v j z') →
    (∀ (j j' : Fin (n + 1)) z z', (j : ℕ) = j' + 1 → C ≤ (e j z).1 → ¬ C ≤ (e j' z').1 →
      (e j z).1.map C.mkQ = (e j' z').1.map C.mkQ → v j z = F (v j' z')) → OrdRead q n F v

def GrCard : Prop :=
  ∀ (k H : Type) [Field k] [AddCommGroup H] [Module k H] [Module.Finite k H] (n j : ℕ), Module.finrank k H = n →
    Nat.card (Gr k H j) = Nat.card (Gr k (Fin n → k) j)

def AlgOf : Prop :=
  ∀ (S K : Scheme.{0}) (h : K ⟶ S), IsFinite h → Flat h → ∀ (V : Type) [CommRing V] [IsLocalRing V] (z : Sp V ⟶ S),
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra V B) (k : Sp B ⟶ K), Module.Finite V B ∧ Module.Free V B ∧
      IsPullback k (spMap (algebraMap V B)) h z

def LiftFF : Prop :=
  ∀ (S K : Scheme.{0}) (h : K ⟶ S), IsFinite h → Flat h →
    ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)] (z : Sp V ⟶ S)
      (g : Sp (IsLocalRing.ResidueField V) ⟶ K), g ≫ h = resPt V ≫ z → ∃ g' : Sp V ⟶ K, g' ≫ h = z ∧ resPt V ≫ g' = g

def ValPtsX : Prop :=
  ∀ (S K : Scheme.{0}) (h : K ⟶ S), IsProper h → ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (z : Sp V ⟶ S),
    (∀ g g' : Sp V ⟶ K, g ≫ h = z → g' ≫ h = z →
      spMap (algebraMap V (FractionRing V)) ≫ g = spMap (algebraMap V (FractionRing V)) ≫ g' → g = g') ∧
    ∀ g : Sp (FractionRing V) ⟶ K, g ≫ h = spMap (algebraMap V (FractionRing V)) ≫ z →
      ∃ g' : Sp V ⟶ K, g' ≫ h = z ∧ spMap (algebraMap V (FractionRing V)) ≫ g' = g

def RepOfFF : Prop :=
  ∀ (κ : Type) [Field κ] (A : Over (Sp κ)) (P : ∀ T : Over (Sp κ), (T ⟶ A) → Prop), RepFF A P → ∃ d, RepAlg A P d

def FFRead : Prop :=
  ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : ∀ T : Over S, (T ⟶ A) → Prop), RepFF A P →
    ∀ c : ℕ, (∀ T g, P T g → g ^ c = 1) →
    ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)], (c : V) ≠ 0 → ∀ (z : Sp V ⟶ S)
      (A' : Over (Sp (IsLocalRing.ResidueField V))) (φ : A'.left ⟶ A.left), IsPullback φ A'.hom A.hom (resPt V ≫ z) →
    ∀ P' : ∀ T : Over (Sp (IsLocalRing.ResidueField V)), (T ⟶ A') → Prop,
      (∀ T (g : T ⟶ A') (g₀ : Over.mk (T.hom ≫ resPt V ≫ z) ⟶ A), g₀.left = g.left ≫ φ → (P' T g ↔ P _ g₀)) →
      RepAlg A' P' (Nat.card {g : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ A // P _ g})

def KillLocal : Prop :=
  ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (A A' : Over (Sp κ)) [GrpObj A] [GrpObj A'] (χ : A ⟶ A'), IsMonHom χ →
    ∀ (P : ∀ T : Over (Sp κ), (T ⟶ A) → Prop) (d : ℕ), RepAlg A P d → IsSub A P →
    (∀ g : 𝟙_ (Over (Sp κ)) ⟶ A, P _ g → g ≫ χ = 1) →
    (∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra κ Λ] (ε : Λ →ₐ[κ] κ) (g : algPt κ Λ ⟶ A), P _ g → Inf ε g → g ≫ χ = 1) →
    ∀ T g, P T g → g ≫ χ = 1

def InfE : Prop :=
  ∀ (κ : Type) [Field κ] (A : Over (Sp κ)) [GrpObj A] (P : ∀ T : Over (Sp κ), (T ⟶ A) → Prop) (d : ℕ), RepAlg A P d →
    Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ A // P _ g} = d →
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra κ Λ] (ε : Λ →ₐ[κ] κ) (g : algPt κ Λ ⟶ A), P _ g → Inf ε g → g = 1

def RepHomog : Prop :=
  ∀ (κ : Type) [Field κ] (A : Over (Sp κ)) [GrpObj A] (P : ∀ T : Over (Sp κ), (T ⟶ A) → Prop), IsSub A P →
    ∀ (B : Type) [CommRing B] [Algebra κ B] (i : algPt κ B ⟶ A), Mono i → (∀ T g, InSub i g ↔ P T g) →
    Nat.card (B →ₐ[κ] κ) = Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ A // P _ g} ∧
    ∃ ε₀ : B →ₐ[κ] κ, Inf ε₀ i ∧ ∀ ε : B →ₐ[κ] κ, ∃ τ : B ≃ₐ[κ] B, ε₀.comp τ.toAlgHom = ε

def FrobRing : Prop :=
  ∀ (p f : ℕ) (hp : p.Prime) (κ : Type) [Field κ] [CharP κ p] (A : Over (Sp κ)) [GrpObj A] (B Λ : Type) [CommRing B] [Algebra κ B]
    [CommRing Λ] [Algebra κ Λ] (i : algPt κ B ⟶ A), Mono i → ∀ ε₀ : B →ₐ[κ] κ, Inf ε₀ i → ∀ (ν : B →ₐ[κ] Λ) (g : algPt κ Λ ⟶ A),
    g.left = spMap ν.toRingHom ≫ i.left → (FrobKill p f hp g ↔ ∀ x, ε₀ x = 0 → ν x ^ p ^ f = 0)

def InfW : Prop :=
  ∀ (p f : ℕ) (hp : p.Prime) (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p] (A : Over (Sp κ)) [GrpObj A]
    (P P' : ∀ T : Over (Sp κ), (T ⟶ A) → Prop) (d d' : ℕ), RepAlg A P (p ^ f * d) → IsSub A P →
    Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ A // P _ g} = d → 0 < d → RepAlg A P' d' → (∀ T g, P T g → P' T g) → TanLe A P' →
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra κ Λ] (ε : Λ →ₐ[κ] κ) (g : algPt κ Λ ⟶ A), P' _ g → Inf ε g →
      (P _ g ↔ FrobKill p f hp g)

def DivC : Prop :=
  ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B], IsAbelianScheme A → ∀ c : ℕ, 0 < c →
    (∀ h : A ⟶ B, IsMonHom h → (∀ (T : Over S) (g : T ⟶ A), g ^ c = 1 → g ≫ h = 1) → ∃ ν : A ⟶ B, IsMonHom ν ∧ ν ^ c = h) ∧
    ∀ ν ν' : A ⟶ B, IsMonHom ν → IsMonHom ν' → ν ^ c = ν' ^ c → ν = ν'

def TorsFree : Prop :=
  ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B], IsAbelianScheme A →
    IsAbelianScheme B → ∀ (L : LB (A ⊗ B).left) (hL : L.IsLB), IsAdditive L → IsAdditive (swap L) → ∀ c : ℕ, 0 < c →
    c • GlobalTheory.CechPic.cls L hL = 0 → GlobalTheory.CechPic.cls L hL = 0

def ConstSub : Prop :=
  ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsSeparated A.hom → ∀ (Γ : Subgroup (𝟙_ (Over (Sp K)) ⟶ A)), Finite Γ →
    ∃ (G : Over (Sp K)) (_ : GrpObj G) (i : G ⟶ A), IsMonHom i ∧ Mono i ∧ IsFinite G.hom ∧ Etale G.hom ∧
      IsIsogDeg (toUnit G) (Nat.card Γ) ∧ (∀ g : 𝟙_ (Over (Sp K)) ⟶ A, InSub i g ↔ g ∈ Γ) ∧
      (∀ α : A ⟶ A, (∀ g ∈ Γ, g ≫ α = 1) → i ≫ α = 1) ∧ ∀ α : A ⟶ A, (∀ g ∈ Γ, g ≫ α ∈ Γ) → ∃ ν : G ⟶ G, ν ≫ i = i ≫ α

def FrobHom : Prop :=
  ∀ (p f : ℕ) (hp : p.Prime) (κ : Type) [Field κ] [CharP κ p] (φ : κ →+* κ), (∀ a, φ a = a ^ p ^ f) →
    ∀ (A A' : Over (Sp κ)) [GrpObj A] [GrpObj A'] (ψ : A'.left ⟶ A.left), IsGrpPullback A' A (spMap φ) ψ →
    ∀ h : (p : Γ(A.left, ⊤)) = 0, ∃ F : A ⟶ A', IsMonHom F ∧ F.left ≫ ψ = GlobalTheory.SS.FrobField.absFrob A.left p f hp h ∧
      ∀ (T : Over (Sp κ)) (g : T ⟶ A), g ≫ F = 1 ↔ FrobKill p f hp g

def FrobFin : Prop :=
  ∀ (p f : ℕ) (hp : p.Prime) (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p] (X : Scheme.{0}) (s : X ⟶ Sp κ), LocallyOfFiniteType s →
    ∀ h : (p : Γ(X, ⊤)) = 0, IsFinite (GlobalTheory.SS.FrobField.absFrob X p f hp h) ∧ Surjective (GlobalTheory.SS.FrobField.absFrob X p f hp h)

def PicFrob : Prop :=
  ∀ (p f : ℕ) (hp : p.Prime) (X : Scheme.{0}) (h : (p : Γ(X, ⊤)) = 0) (c : GlobalTheory.CechPic.Pic X),
    GlobalTheory.CechPic.pull (GlobalTheory.SS.FrobField.absFrob X p f hp h) c = (p ^ f) • c

def GenDown : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (X Y : Scheme.{0}) (s : X ⟶ Sp O)
    (h : Y ⟶ X), Flat h → ∀ y : Y, GenPt (fn (h ≫ s) ϖ) y → s (h y) = IsLocalRing.closedPoint O ∧
      ∀ z' : X, s z' = IsLocalRing.closedPoint O → z' ⤳ h y → z' = h y

end UpperTheory.Gal.crystallineComparison.Mod
