import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.TiedAInvOfTheta
import GroundTheory.PAdicHodge.BCrisEigen
import GroundTheory.PAdicHodge.BCrisRegularSenTate
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.MaximalIdealEqSpanT

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.CompanionTheory.LTPer

section Abs

variable {B : Type} [CommRing B]

def ltIter (ϖ : B) (q n : ℕ) : B → B := (fun x => ϖ * x + x ^ q)^[n]

def Near (S : Subring B) (ϖ : B) (J : Ideal B) (m : ℕ) (x : B) : Prop :=
  ∃ s ∈ S, x - ϖ ^ m * s ∈ J

structure PerEnv (S : Subring B) (F : ℕ → Ideal B) (ϖ : B) : Prop where
  top : F 0 = ⊤
  anti : ∀ k, F (k + 1) ≤ F k
  mul_le : ∀ a b, F a * F b ≤ F (a + b)
  sep : ∀ x, (∀ k, x ∈ F k) → x = 0
  complete : ∀ x : ℕ → B, (∀ k, x (k + 1) - x k ∈ F k) → ∃ t, ∀ k, t - x k ∈ F k
  unit : IsUnit ϖ
  mem : ϖ ∈ S
  sumS : ∀ s : ℕ → B, (∀ n, s n ∈ S) → ∃ r ∈ S, ∀ N, ∃ a ∈ S,
    r - ∑ n ∈ Finset.range N, ϖ ^ n * s n = ϖ ^ N * a
  closed : ∀ k, ∀ x ∈ S, (∀ m, Near S ϖ (F k) m x) → x ∈ F k

def Tends (S : Subring B) (F : ℕ → Ideal B) (ϖ : B) (x : ℕ → B) (t : B) : Prop :=
  ∀ k, ∃ c : ℕ, ∀ m, ∃ N, ∀ n ≥ N, Near S ϖ (F k) m (ϖ ^ c * (x n - t))

def EvalMod {R : Type} [CommRing R] (S : Subring B) (F : ℕ → Ideal B) (ϖ : B) (h : R →+* B)
    (φ : PowerSeries R) (y r : B) (m : ℕ) : Prop :=
  ∀ k, ∃ D, ∀ D' ≥ D, Near S ϖ (F k) m
    ((∑ i ∈ Finset.range D', h (PowerSeries.coeff i φ) * y ^ i) - r)

end Abs

section Conc

variable (l : ℕ) [Fact l.Prime]

open scoped Formalism.Per6

abbrev Tl : Type := PreTilt ↥(GroundTheory.PAdicHodge.normInteger ℂ_[l]) l

abbrev Wl : Type := WittVector l (Tl l)

def wB : Wl l →+* Formalism.Per6.BdRp l :=
  GroundTheory.PAdicHodge.wittToBDeRhamPlus ↥(GroundTheory.PAdicHodge.normInteger ℂ_[l]) l

def tch (x : Tl l) : Formalism.Per6.BdRp l := wB l (WittVector.teichmuller l x)

def rB : Om l →+* Formalism.Per6.BdRp l := (GroundTheory.PAdicHodge.algClToBdR l).toRingHom

def thB : Formalism.Per6.BdRp l →+* ℂ_[l] := (GroundTheory.PAdicHodge.thetaAlgHom l).toRingHom

def FB (k : ℕ) : Ideal (Formalism.Per6.BdRp l) := RingHom.ker (thB l) ^ k

variable {l}

def actB (g : GQ l) : Formalism.Per6.BdRp l →+* Formalism.Per6.BdRp l := MulSemiringAction.toRingHom _ _ (Formalism.Per6.toBot g)

def actT (g : GQ l) : Tl l →+* Tl l :=
  GroundTheory.PAdicHodge.preTiltMap l (GroundTheory.PAdicHodge.galCp (Formalism.Per6.toBot g) : ℂ_[l] →+* ℂ_[l])
    (GroundTheory.PAdicHodge.AInf.norm_galCp_toRingHom (Formalism.Per6.toBot g))

abbrev qOf {K : FinExt l} (π : ↥(OL K)) : ℕ := Nat.card (↥(OL K) ⧸ Ideal.span {π})

def oB (K : FinExt l) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) : ↥(OL K) →+* Formalism.Per6.BdRp l :=
  (rB l).comp ((μ : ↥K.1 →+* Om l).comp (algebraMap ↥(OL K) ↥K.1))

def LTData (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l) : Prop :=
  Irreducible π ∧ z 0 = 0 ∧ z 1 ≠ 0 ∧
    (∀ n, z (n + 1) ^ Nat.card (↥(OL K) ⧸ Ideal.span {π}) +
      (((π : ↥K.1) : Om l)) * z (n + 1) = z n) ∧
    ∀ (g : ↥(GK K)) (φ : PowerSeries ↥(OL K)), PowerSeries.constantCoeff φ = 0 →
      ((PowerSeries.coeff 1 φ : ↥(OL K)) : ↥K.1) = ((χ g : (↥K.1)ˣ) : ↥K.1) →
      PowerSeries.subst φ (GlobalTheory.CompanionTheory.LTHodge.ltSeries π) = PowerSeries.subst (GlobalTheory.CompanionTheory.LTHodge.ltSeries π) φ →
      ∀ n, HasSum (fun k : ℕ => (((PowerSeries.coeff k φ : ↥(OL K)) : ↥K.1) : Om l) * z n ^ k)
        ((g : GQ l) (z n))

def PrePer (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (t : Formalism.Per6.BdRp l) : Prop :=
  t ≠ 0 ∧ (∀ (g : GQ l) (hg : g ∈ GK K), (∀ x : ↥K.1, g (μ x) = μ x) →
      actB g t = rB l (μ ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1)) * t) ∧
    (μ = K.1.val → thB l t = 0)

end Conc

end GlobalTheory.CompanionTheory.LTPer
