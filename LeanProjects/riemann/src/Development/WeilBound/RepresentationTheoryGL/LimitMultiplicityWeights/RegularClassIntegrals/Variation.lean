import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIsoFrameFirstCols

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

abbrev NF {k : ℕ} (C : Matrix (Fin n) (Fin k) E) : Subgroup (GAd σ J) := ratPts σ J ⊓ unipRad σ J C

variable {σ J}

def nsum (Γ : Subgroup (GAd σ J)) (f : GAd σ J → ℂ) (z g : GAd σ J) : ℂ := ∑' ν : Γ, f (z * ν * g)

def Van (N : Subgroup (GAd σ J)) (f : GAd σ J → ℂ) : Prop :=
  ∀ (ν : Measure N) [ν.IsHaarMeasure] (x y : GAd σ J), ∫ m : N, f (x * m * y) ∂ν = 0

end

def SmOf : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ f ∈ CcAd σ J, GlobalTheory.UAut.IsSm σ J f

def DerMem : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ f ∈ CcAd σ J, ∀ b : ℝ → GAd σ J, IsRealLine σ J b → lineDer b f ∈ CcAd σ J

def DerVan : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ N : Subgroup (GAd σ J), IsClosed (N : Set (GAd σ J)) → ∀ f ∈ CcAd σ J, ∀ b : ℝ → GAd σ J, IsRealLine σ J b →
      Van N f → Van N (lineDer b f)

def Level : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ f ∈ CcAd σ J, ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, f (g * k) = f g

def SumSm : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ Γ : Subgroup (GAd σ J), Γ ≤ ratPts σ J → ∀ f ∈ CcAd σ J, ∀ z, GlobalTheory.UAut.IsSm σ J (nsum Γ f z) ∧
      ∀ b : ℝ → GAd σ J, IsRealLine σ J b → lineDer b (nsum Γ f z) = nsum Γ (lineDer b f) z

def Variation : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (k : ℕ) (C : Matrix (Fin n) (Fin k) E), GlobalTheory.UAut.IsIsoCols σ J C → ∀ f : GAd σ J → ℂ, Continuous f →
      HasCompactSupport f → Van (unipRad σ J C) f → ∀ (z g : GAd σ J) (e : ℝ),
      (∀ m ∈ unipRad σ J C, ‖nsum (NF σ J C) f z (m * g) - nsum (NF σ J C) f z g‖ ≤ e) → ‖nsum (NF σ J C) f z g‖ ≤ e

def NearCusp : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Cm : Set (GAd σ J)) (c : ℝ)
      (U : Subgroup (GAd σ J)), IsCompact Cm → 0 < c → IsOpen (U : Set (GAd σ J)) → ∀ s : Fin r,
      ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ∀ m ∈ unipRad σ J (pre X s),
        ∃ γ ∈ NF σ J (pre X s), ∃ u κ : GAd σ J, CloseInf σ J u (M / ratio t s) ∧ κ ∈ U ∧ κ ∈ finPts σ J ∧
          m * (a * k) = γ * (a * k) * u * κ

def Base : Prop :=
  ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∃ A : ℕ,
    ∀ Γ : Subgroup (GAd D.sp.cm.sig V.gram), Γ ≤ ratPts D.sp.cm.sig V.gram →
    ∀ f : GAd D.sp.cm.sig V.gram → ℂ, Continuous f → HasCompactSupport f →
    ∀ C W : Set (GAd D.sp.cm.sig V.gram), IsCompact C → IsCompact W → ∃ B : ℝ, ∀ t ∈ cone r c, ∀ a,
      IsTorusElt D.sp.cm.sig V.gram X Y t a → ∀ x ∈ C, ∀ y ∈ W,
        ‖nsum Γ f (x * a⁻¹) (a * y)‖ ≤ B * (∏ i, max (t i) 1) ^ A

def Core : Prop :=
  ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ s : Fin r, ∃ A : ℕ, ∀ m : ℕ,
    ∀ f ∈ CcAd D.sp.cm.sig V.gram, Van (unipRad D.sp.cm.sig V.gram (pre X s)) f →
    ∀ C W : Set (GAd D.sp.cm.sig V.gram), IsCompact C → IsCompact W → ∃ B : ℝ, ∀ t ∈ cone r c, ∀ a,
      IsTorusElt D.sp.cm.sig V.gram X Y t a → ∀ x ∈ C, ∀ y ∈ W,
        ‖nsum (NF D.sp.cm.sig V.gram (pre X s)) f (x * a⁻¹) (a * y)‖ ≤ B * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m

def Bridge : Prop :=
  ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r),
    NA (frameFlag (isIsoFrame_firstCols hW j)) = unipRad D.sp.cm.sig V.gram (pre X j)

def Decay : Prop :=
  ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (c : ℝ), 0 < c → ∀ (j : Fin r) (f : GA D V → ℂ), f ∈ CcGA V →
    GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.UnipIntegralsVanish (frameFlag (isIsoFrame_firstCols hW j)) f →
    ∀ C W : Set (GA D V), IsCompact C → IsCompact W → ∃ A : ℕ, ∀ m : ℕ, ∃ B : ℝ,
      ∀ t ∈ cone r c, ∀ a : GA D V, IsTorusElt D.sp.cm.sig V.gram X Y t a → ∀ x ∈ C, ∀ y ∈ W,
        ‖∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, f (x * (a⁻¹ * rat V ν * a) * y)‖ ≤
          B * (∏ i, max (t i) 1) ^ A * (root t j)⁻¹ ^ m

end MainStatements.WeightKernel.Dec

end
