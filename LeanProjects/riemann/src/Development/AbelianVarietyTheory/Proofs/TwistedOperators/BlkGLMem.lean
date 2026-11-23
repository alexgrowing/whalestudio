import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareComm

variable {D : D7}

theorem blkGL_mem (V V₁ : HSp D) (g : GA D V × GA D V₁) :
    blkGL finSumFinEquiv (g.1.1, g.2.1) ∈ HR (AF D.host.F) D.sp.cm.sig (hsum V V₁).gram := by
  have hJ : JR (F := D.host.F) (AF D.host.F) (hsum V V₁).gram =
      blkMat finSumFinEquiv (JR (F := D.host.F) (AF D.host.F) V.gram) (JR (F := D.host.F) (AF D.host.F) V₁.gram) := by
    unfold JR
    rw [gram_hsum]
    exact blkMat_map _ _ (map_zero _) _ _
  unfold HR
  rw [hJ]
  exact (blkGL_mem_UJ finSumFinEquiv).2 ⟨g.1.2, g.2.2⟩

def blk (V V₁ : HSp D) : GA D V × GA D V₁ →* GA D (hsum V V₁) where
  toFun g := ⟨blkGL finSumFinEquiv (g.1.1, g.2.1), blkGL_mem V V₁ g⟩
  map_one' := Subtype.ext (map_one (blkGL finSumFinEquiv))
  map_mul' g h := Subtype.ext (map_mul (blkGL finSumFinEquiv) (g.1.1, g.2.1) (h.1.1, h.2.1))

theorem mt_blk (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁) :
    Formalism.L2.Theta.mt (hsum V V₁) (blk V V₁ (g, g₁)) =
      blkMat finSumFinEquiv (Formalism.L2.Theta.mt V g) (Formalism.L2.Theta.mt V₁ g₁) := rfl

theorem continuous_blk (V V₁ : HSp D) : Continuous (blk V V₁) := by
  apply Continuous.subtype_mk
  exact (continuous_blkGL finSumFinEquiv).comp (continuous_subtype_val.prodMap continuous_subtype_val)

def frSgn (ε : Bool) {V : HSp D} (A : Fr V) : Fr (sgn ε V) where
  ε τ a := xor ε (A.ε τ a)
  fr := A.fr
  fr_unit := A.fr_unit
  fr_gram τ := by
    cases ε
    · simp only [Bool.false_xor]; exact A.fr_gram τ
    · have e : gramAt D (neg V) τ = -gramAt D V τ := by ext i j; simp [gramAt, neg_gram]
      have e' : Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) = -Formalism.REAL.Jm (A.ε τ) := by
        ext a b
        by_cases h : a = b
        · subst h; cases h' : A.ε τ a <;> simp [Formalism.REAL.Jm, h']
        · simp [Formalism.REAL.Jm, h]
      show (A.fr τ)ᴴ * Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) * A.fr τ = gramAt D (neg V) τ
      rw [e, e', ← A.fr_gram τ, Matrix.mul_neg, Matrix.neg_mul]

def frSum {V V₁ : HSp D} (A : Fr V) (B : Fr V₁) : Fr (hsum V V₁) where
  ε τ := Fin.append (A.ε τ) (B.ε τ)
  fr τ := blkMat finSumFinEquiv (A.fr τ) (B.fr τ)
  fr_unit τ := by
    rw [Matrix.isUnit_iff_isUnit_det, det_blkMat]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)).mul ((Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ))
  fr_gram τ := by
    have e : gramAt D (hsum V V₁) τ = blkMat finSumFinEquiv (gramAt D V τ) (gramAt D V₁ τ) := by
      unfold gramAt
      rw [gram_hsum]; exact blkMat_map _ _ (map_zero _) _ _
    have e' : Formalism.REAL.Jm (Fin.append (A.ε τ) (B.ε τ)) =
        blkMat finSumFinEquiv (Formalism.REAL.Jm (A.ε τ)) (Formalism.REAL.Jm (B.ε τ)) := by
      refine submatrix_inj finSumFinEquiv ?_
      rw [submatrix_blkMat]
      ext (a | a) (b | b) <;> simp [Formalism.REAL.Jm, Matrix.diagonal_apply, Fin.ext_iff] <;> omega
    have e'' : (blkMat finSumFinEquiv (A.fr τ) (B.fr τ))ᴴ = blkMat finSumFinEquiv (A.fr τ)ᴴ (B.fr τ)ᴴ := by
      simp [GlobalTheory.Doubling.blkMat, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]
    rw [e, e', e'', blkMat_mul, blkMat_mul, A.fr_gram, B.fr_gram]

section Vec

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X)

def IsFinF (f : WO M X → ℂ) : Prop := IsVacF ψ θ (frSgn ε A) B f

def fockF (f : WO M X → ℂ) : PolF D X.rank M.rank →ₗ[ℂ] (WO M X → ℂ) :=
  pureTensorO ψ θ (sgn ε M) X (frSgn ε A).cart B.cart A.onb B.onb f

def algF : Submodule ℂ (WO M X → ℂ) := Submodule.span ℂ {Φ | ∃ f P, IsFinF ψ θ ε A B f ∧ Φ = fockF ψ θ ε A B f P}

end Vec

def IsHaarFD (M : HSp D) (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) : Prop :=
  ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ M) 𝓕 ν

def thetaInt {M X : HSp D} (ω : WRep M X) (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) (Φ : WO M X → ℂ) (h : GA D X) : ℂ :=
  ∫ g in 𝓕, thetaKO ω g h Φ ∂ν

def ModInt (θ : InfFam D) {M X : HSp D} (ω : WRep M X) (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) (Φ : WO M X → ℂ) : Prop :=
  ∃ (N : ℕ) (C : ℝ), ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν ∧
    ∫ g in 𝓕, ‖thetaKO ω g h Φ‖ ∂ν ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N

def finRel {M X : HSp D} (ω : WRep M X) (S : Submodule ℂ (WO M X → ℂ)) : Submodule ℂ (WO M X → ℂ) :=
  Submodule.span ℂ {Φ | ∃ u ∈ GfC M, ∃ Ψ ∈ S, Φ = ω (u, 1) Ψ - Ψ}

structure IsTriple (W W₁ X : HSp D) (α β : (AE D)ˣ →* Circle) : Prop where

  hecA : IsHeckeChar D α

  hecB : IsHeckeChar D β

  resA : ResEta D α W₁.rank

  resB : ResEta D β W.rank

  rank : X.rank = W.rank + W₁.rank

  even : Even X.rank

  sig : ∃ p q : ℕ, (∀ τ, Formalism.UG.HasSignature (gramAt D W τ) (W.rank - p) p ∧ Formalism.UG.HasSignature (gramAt D W₁ τ) (W₁.rank - q) q ∧
      Formalism.UG.HasSignature (gramAt D X τ) (X.rank - (p + q)) (p + q)) ∧
    W₁.rank + 2 * (2 * (p + q) + 1) < W.rank ∧ 2 * (p + q) + 1 < W₁.rank

  gap : ∀ τ, ∃ a b : ℚ, HasInfExp D α τ a ∧ HasInfExp D β τ b ∧ 2 * (a - b) < -(X.rank : ℚ)

  ram : ∀ v e, IsPlaceIdem D v e → (GlobalTheory.WeilParts.UnramAt e α ∧ GlobalTheory.WeilParts.UnramAt e β) ∨
    (¬ GlobalTheory.WeilParts.NonSplitAt D v e ∧ ¬ GlobalTheory.WeilParts.UnramAt e (α / β) ∧
      ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F))

structure IsMatch (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle) (ωA : WRep W X) (ωB : WRep W₁ X) (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi)
    (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO W X → ℂ) →ₗ[ℂ] Pi) (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi) : Prop where

  weilA : IsWeil ψ true W X β (β / α) ωA

  weilB : IsWeil ψ false W₁ X α (α / β) ωB

  irred : IsIrred X Pi rf rl

  mapA : IsCoinvMap θ ωA (algF ψ θ true A B) Pi rf rl p

  mapB : IsCoinvMap θ ωB (algF ψ θ false A₁ B) Pi rf rl p'

end GlobalTheory.SquareComm

end
