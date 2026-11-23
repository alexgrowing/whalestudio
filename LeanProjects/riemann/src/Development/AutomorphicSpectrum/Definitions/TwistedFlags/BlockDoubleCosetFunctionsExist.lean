import Mathlib
import Development.AutomorphicSpectrum.Definitions.TwistedFlags.OneMemOffK
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl)
open GlobalTheory.LFun (KGL IsSatVecGL heckeVec eulerFac seg)
open Formalism.UG (qV IsUnifV dosetInd)

namespace GlobalTheory.CompanionTheory.Ipf.Val

section Local

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev Cv : Type := v.adicCompletion K

def absV (x : Cv v) : ℝ := (WithZeroMulInt.toNNReal (NumberField.RingOfIntegers.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ)

def IsPar (r c : ℕ) (J : Subgroup (GL (Fin (r + c)) (Cv v))) : Prop :=
  ∀ k, k ∈ J ↔ k ∈ KGL v (r + c) ∧ ∀ i j, Valued.v (bDA (k : Matrix (Fin (r + c)) (Fin (r + c)) (Cv v)) i j) < 1

def IsTame (δ : (Cv v)ˣ →* ℂˣ) : Prop :=
  (∀ x, ‖((δ x : ℂˣ) : ℂ)‖ = 1) ∧ ∀ x : (Cv v)ˣ, Valued.v ((x : Cv v) - 1) < 1 → δ x = 1

def IsRam (δ : (Cv v)ˣ →* ℂˣ) : Prop := ∃ x : (Cv v)ˣ, Valued.v (x : Cv v) = 1 ∧ δ x ≠ 1

def lamD {r c : ℕ} (δ : (Cv v)ˣ →* ℂˣ) (k : GL (Fin (r + c)) (Cv v)) : ℂ :=
  chi0 δ (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) (Cv v))).det

def blk (r : ℕ) {c : ℕ} (m : GL (Fin c) (Cv v)) : GL (Fin (r + c)) (Cv v) := pEl (1 : GL (Fin r) (Cv v)) 0 m

def IsDiag {c : ℕ} (ϖ : Cv v) (d : Fin c → ℤ) (m : GL (Fin c) (Cv v)) : Prop := m.1 = Matrix.diagonal fun i => ϖ ^ d i

def len {c : ℕ} (d : Fin c → ℤ) : ℕ := ∑ i, (d i).natAbs

def IsBlockDoubleCosetFunction {r c : ℕ} (J : Subgroup (GL (Fin (r + c)) (Cv v))) (δ : (Cv v)ˣ →* ℂˣ) (m : GL (Fin c) (Cv v))
    (h : GL (Fin (r + c)) (Cv v) → ℂ) : Prop :=
  (∀ k₁ ∈ J, ∀ k₂ ∈ J, h (k₁ * blk v r m * k₂) = (lamD v δ k₁ * lamD v δ (blk v r m) * lamD v δ k₂)⁻¹) ∧
    ∀ g, g ∉ DoubleCoset.doubleCoset (blk v r m) (J : Set _) J → h g = 0

def IsSphEig {c : ℕ} (B : Multiset ℂˣ) (m : GL (Fin c) (Cv v)) (lam : ℂ) : Prop :=
  ∃ (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module ℂ V₀) (ρ₀ : Representation ℂ (GL (Fin c) (Cv v)) V₀) (x₀ : V₀),
    IsSatVecGL v ρ₀ x₀ B ∧ heckeVec ρ₀ (KGL v c) (dosetInd ℂ (KGL v c) m) x₀ = lam • x₀

def IsBlockVector {r c : ℕ} (J : Subgroup (GL (Fin (r + c)) (Cv v))) (δ : (Cv v)ˣ →* ℂˣ) {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (GL (Fin (r + c)) (Cv v)) X) (x : X) (B : Multiset ℂˣ) : Prop :=
  B.card = c ∧ (∀ k ∈ J, ρ k x = lamD v δ k • x) ∧
    ∀ ϖ, IsUnifV K v ϖ → ∀ (d : Fin c → ℤ) (m : GL (Fin c) (Cv v)), IsDiag v ϖ d m → ∀ lam, IsSphEig v B m lam →
      ∀ h, IsBlockDoubleCosetFunction v J δ m h → heckeVec ρ J h x = ((qV K v : ℂ) ^ ((r : ℂ) / 2 * len d) * lam) • x

def IsBlockKernel {r c : ℕ} (J : Subgroup (GL (Fin (r + c)) (Cv v))) (δ : (Cv v)ˣ →* ℂˣ) (X : ℂ)
    (κ : GL (Fin (r + c)) (Cv v) → ℂ) : Prop :=
  (∀ ϖ, IsUnifV K v ϖ → ∀ (d : Fin c → ℤ) (m : GL (Fin c) (Cv v)), IsDiag v ϖ d m → ∀ k₁ ∈ J, ∀ k₂ ∈ J,
    κ (k₁ * blk v r m * k₂) = (lamD v δ k₁ * lamD v δ (blk v r m) * lamD v δ k₂)⁻¹ * X ^ len d) ∧
    ∀ g, (∀ m : GL (Fin c) (Cv v), g ∉ DoubleCoset.doubleCoset (blk v r m) (J : Set _) J) → κ g = 0

def HasSph (c : ℕ) (B : Multiset ℂˣ) : Prop :=
  (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV K v : ℝ) ^ (((c : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV K v : ℝ) ^ (((c : ℝ) - 1) / 2)) ∧
  ∃ (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module ℂ V₀) (ρ₀ : Representation ℂ (GL (Fin c) (Cv v)) V₀) (x₀ : V₀)
    (ℓ : V₀ →ₗ[ℂ] ℂ), IsSatVecGL v ρ₀ x₀ B ∧ ℓ x₀ ≠ 0 ∧ (∃ C : ℝ, ∀ g, ‖ℓ (ρ₀ g x₀)‖ ≤ C) ∧
      ∀ m, ∃ lam : ℂ, heckeVec ρ₀ (KGL v c) (dosetInd ℂ (KGL v c) m) x₀ = lam • x₀

def phiB (δ : (Cv v)ˣ →* ℂˣ) (r d c : ℕ) (x : Matrix (Fin (r + d)) (Fin (r + c)) (Cv v)) : ℂ :=
  open Classical in
  if (∀ i j, Valued.v (x i j) ≤ 1) ∧ Valued.v (bAA x).det = 1 ∧ ∀ i j, Valued.v (bDA x i j) < 1 then chi0 δ (bAA x).det else 0

def linAct {a b : ℕ} (δS δT : (Cv v)ˣ →* ℂˣ) (g : GL (Fin a) (Cv v)) (h : GL (Fin b) (Cv v))
    (Φ : Matrix (Fin b) (Fin a) (Cv v) → ℂ) : Matrix (Fin b) (Fin a) (Cv v) → ℂ :=
  fun y => (((δT (Matrix.GeneralLinearGroup.det g))⁻¹ * δS (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
    ((absV v g.1.det ^ ((b : ℝ) / 2) * absV v h.1.det ^ (-(a : ℝ) / 2) : ℝ) : ℂ) * Φ ((h⁻¹).1 * y * g.1)

end Local

def lFac (q : ℕ) (B : Multiset ℂˣ) (s : ℂ) : ℂ :=
  eulerFac B ((q : ℂ) ^ (-(s + 1 / 2))) * eulerFac (B.map (·⁻¹)) ((q : ℂ) ^ (-(s + 1 / 2)))

def qFac (q c : ℕ) (B : Multiset ℂˣ) (s : ℂ) : ℂ :=
  lFac q B s * ∏ i ∈ Finset.range c, (1 - (q : ℂ) ^ (-(2 * s + c - i)))

def BlockDoubleCosetFunctionsExist : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (r c : ℕ),
    (∃ J, IsPar v r c J) ∧ ∀ J, IsPar v r c J → ∀ δ, IsTame v δ → ∀ m, ∃ h, IsBlockDoubleCosetFunction v J δ m h

def SphEigUnique : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (c : ℕ) (B : Multiset ℂˣ), B.card = c →
    ∀ m : GL (Fin c) (Cv v), ∃! lam, IsSphEig v B m lam

def SphStrings : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (k t : ℕ) (x : ℕ → ℂˣ), (∀ i, ‖(x i : ℂ)‖ = 1) →
    HasSph v (k * t) (∑ i ∈ Finset.range k, seg v (x i) t)

def QSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (r c : ℕ) (J : Subgroup (GL (Fin (r + c)) (Cv v))),
    IsPar v r c J → ∀ δ, IsTame v δ → ∀ (s : ℂ) (κ : GL (Fin (r + c)) (Cv v) → ℂ), (c : ℝ) / 2 < s.re →
    IsBlockKernel v J δ ((qV K v : ℂ) ^ (-(((r : ℂ) + c) / 2 + s))) κ →
    ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (Fin (r + c)) (Cv v)) X) (x : X) (B : Multiset ℂˣ),
      IsBlockVector v J δ ρ x B → HasSph v c B → ∀ ℓ : X →ₗ[ℂ] ℂ,
      Summable (fun y : GL (Fin (r + c)) (Cv v) ⧸ J => κ y.out * ℓ (ρ y.out x)) →
        HasSum (fun y : GL (Fin (r + c)) (Cv v) ⧸ J => κ y.out * ℓ (ρ y.out x)) (qFac (qV K v) c B s * ℓ x)

def EquivSupp : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (r d c : ℕ) (J : Subgroup (GL (Fin (r + c)) (Cv v)))
    (J' : Subgroup (GL (Fin (r + d)) (Cv v))), IsPar v r c J → IsPar v r d J' → ∀ δ, IsTame v δ → IsRam v δ →
    ∀ Φ : Matrix (Fin (r + d)) (Fin (r + c)) (Cv v) → ℂ,
      (∀ k ∈ J, ∀ k' ∈ J', ∀ y, Φ (k'.1 * y * k.1) = chi0 δ (bAA k'.1).det * chi0 δ (bAA k.1).det * Φ y) →
      ∀ y, Φ y ≠ 0 → ∃ k ∈ J, ∃ k' ∈ J', bAD (k'.1 * y * k.1) = 0 ∧ bDA (k'.1 * y * k.1) = 0 ∧ (bAA (k'.1 * y * k.1)).det ≠ 0

def SphMatchAll : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (c t : ℕ) (ϖ : Cv v), IsUnifV K v ϖ →
    ∀ m' : GL (Fin (c + t)) (Cv v), ∃ (I : Finset (Fin c → ℤ)) (a : (Fin c → ℤ) → ℂ) (m : (Fin c → ℤ) → GL (Fin c) (Cv v)),
      (∀ e, IsDiag v ϖ e (m e)) ∧
      (∀ y, (∑ᶠ z : GL (Fin (c + t)) (Cv v) ⧸ KGL v (c + t), dosetInd ℂ (KGL v (c + t)) m' z.out *
          linAct v 1 1 (1 : GL (Fin c) (Cv v)) z.out (Set.indicator {x | ∀ i j, Valued.v (x i j) ≤ 1} 1) y) =
        ∑ e ∈ I, a e * ∑ᶠ z : GL (Fin c) (Cv v) ⧸ KGL v c, dosetInd ℂ (KGL v c) (m e) z.out *
          linAct v 1 1 z.out (1 : GL (Fin (c + t)) (Cv v)) (Set.indicator {x | ∀ i j, Valued.v (x i j) ≤ 1} 1) y) ∧
      ∀ (B : Multiset ℂˣ) (lam : (Fin c → ℤ) → ℂ), (∀ e, IsSphEig v B (m e)⁻¹ (lam e)) →
        IsSphEig v (B + seg v 1 t) m' (∑ e ∈ I, a e * lam e)

def BlockVectorLocalLift : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (r c t : ℕ) (J : Subgroup (GL (Fin (r + c)) (Cv v)))
    (J' : Subgroup (GL (Fin (r + (c + t))) (Cv v))), IsPar v r c J → IsPar v r (c + t) J' →
    ∀ δS δT, IsTame v δS → IsTame v δT → IsRam v δT → (∀ x : (Cv v)ˣ, Valued.v (x : Cv v) = 1 → δS x = δT x) →
    ∀ (Z X Y : Type) [AddCommGroup Z] [Module ℂ Z] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
      (j : Z →ₗ[ℂ] (Matrix (Fin (r + (c + t))) (Fin (r + c)) (Cv v) → ℂ)), Function.Injective j →
      ∀ ω : Representation ℂ (GL (Fin (r + c)) (Cv v) × GL (Fin (r + (c + t))) (Cv v)) Z,
      (∀ g h z, j (ω (g, h) z) = linAct v δS δT g h (j z)) → ∀ z₀, j z₀ = phiB v δT r (c + t) c →
      ∀ (ρ : Representation ℂ (GL (Fin (r + c)) (Cv v)) X) (x : X) (B : Multiset ℂˣ), IsBlockVector v J δT ρ x B →
      ∀ p : Z →ₗ[ℂ] X →ₗ[ℂ] Y, (∀ g z x', p (ω (g, 1) z) (ρ g x') = p z x') →
        IsBlockVector v J' δS (GlobalTheory.PRep.rightReg ℂ (GL (Fin (r + (c + t))) (Cv v)) Y) (fun h => p (ω (1, h) z₀) x) (B + seg v 1 t)

def BlockUnramifiedTwist : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (r c : ℕ) (J : Subgroup (GL (Fin (r + c)) (Cv v))),
    IsPar v r c J → ∀ δ ν : (Cv v)ˣ →* ℂˣ, IsTame v δ → IsTame v ν → ¬ IsRam v ν → ∀ z : ℂˣ,
    (∀ ϖ : (Cv v)ˣ, IsUnifV K v (ϖ : Cv v) → ν ϖ = z) →
    ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (Fin (r + c)) (Cv v)) X) (x : X) (B : Multiset ℂˣ),
      IsBlockVector v J δ ρ x B → IsBlockVector v J (δ * ν) ρ x (B.map (z⁻¹ * ·))

def KerLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (r d c : ℕ) (J : Subgroup (GL (Fin (r + c)) (Cv v))),
    IsPar v r c J → ∀ δS δT, IsTame v δT →
    ∀ [MeasurableSpace (Matrix (Fin (r + d)) (Fin (r + c)) (Cv v))] [BorelSpace (Matrix (Fin (r + d)) (Fin (r + c)) (Cv v))]
      (ν : Measure (Matrix (Fin (r + d)) (Fin (r + c)) (Cv v))), ν.IsAddLeftInvariant → ν {x | ∀ i j, Valued.v (x i j) ≤ 1} = 1 →
      (∫ y, ‖phiB v δT r d c y‖ ^ 2 ∂ν = (qV K v : ℝ) ^ (-((r * d : ℕ) : ℤ)) * GlobalTheory.CompanionTheory.QL.qE (qV K v) 1 r) ∧
      (IsRam v δT → IsBlockKernel v J δT ((qV K v : ℂ) ^ (-(((r : ℂ) + d) / 2))) fun g =>
        (∫ y, linAct v δS δT g 1 (phiB v δT r d c) y * star (phiB v δT r d c y) ∂ν) / ((∫ y, ‖phiB v δT r d c y‖ ^ 2 ∂ν : ℝ) : ℂ))

section Adelic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FinZeta (projV embV Kv Gv)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsIdemOf IsProjAt rdA grpCo frCo)
open GlobalTheory.CompanionTheory.Ipf.Loc (FPl)

variable {D : D7}

def IsQChart {v : FPl D} (φ : SplitProj D v) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r c : ℕ)
    (e : Gv V v ≃* GL (Fin (r + c)) (Cv v)) : Prop :=
  ∃ h : r + c = V.rank, ∀ g, (e g).1 = (grpCo φ V (frCo φ β) (embV V v g)).1.submatrix (Fin.cast h) (Fin.cast h)

def IsLocCh {v : FPl D} (φ : SplitProj D v) (χ : (AE D)ˣ →* Circle) (δ : (Cv v)ˣ →* ℂˣ) : Prop :=
  ∀ e, IsIdemOf φ e → ∀ x : (AE D)ˣ, (1 - e) * (x : AE D) = 1 - e → ∀ y : (Cv v)ˣ, (y : Cv v) = rdA φ (x : AE D) →
    ((δ y : ℂˣ) : ℂ) = (χ x : ℂ)

def IsBlockVectorAtSplitPrime (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r : ℕ) (PP : Formalism.L2.DIV.Pl D.host.E) (χ : (AE D)ˣ →* Circle)
    (F : GA D V → ℂ) (B : Multiset ℂˣ) : Prop :=
  ∀ (v : FPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (c : ℕ) (e : Gv V v ≃* GL (Fin (r + c)) (Cv v)), IsQChart φ V β r c e →
    ∀ δ, IsLocCh φ χ δ → ∀ J, IsPar v r c J →
      IsBlockVector v J δ ((GlobalTheory.PRep.rightReg ℂ (GA D V) ℂ).comp ((embV V v).comp e.symm.toMonoidHom)) F B

def IsKerAt (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r N : ℕ) (PP : Formalism.L2.DIV.Pl D.host.E) (χ : (AE D)ˣ →* Circle)
    (c₀ : GA D V → ℂ) : Prop :=
  ∀ (v : FPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (c : ℕ) (e : Gv V v ≃* GL (Fin (r + c)) (Cv v)), IsQChart φ V β r c e →
    ∀ δ, IsLocCh φ χ δ → ∀ J, IsPar v r c J → ∃ κ, IsBlockKernel v J δ ((qV D.host.F v : ℂ) ^ (-((N : ℂ) / 2))) κ ∧
      ∀ g, projV V v g = 1 → ∀ x : Gv V v, c₀ (g * embV V v x) = κ (e x) * c₀ g

def IsQPlace (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r : ℕ) (PP : Formalism.L2.DIV.Pl D.host.E) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∃ (φ : SplitProj D (PP.under (𝓞 D.host.F))) (c : ℕ) (e : Gv V (PP.under (𝓞 D.host.F)) ≃* GL (Fin (r + c)) (Cv (PP.under (𝓞 D.host.F))))
    (δ : (Cv (PP.under (𝓞 D.host.F)))ˣ →* ℂˣ), IsProjAt φ PP ∧ (∃ i, IsIdemOf φ i) ∧ IsQChart φ V β r c e ∧
      (∀ g, g ∈ Kv V _ ↔ e g ∈ KGL _ (r + c)) ∧ IsLocCh φ χ δ ∧ IsTame _ δ ∧ IsRam _ δ

end Adelic

end GlobalTheory.CompanionTheory.Ipf.Val

end
