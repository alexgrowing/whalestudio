import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MulMemRiemannRochSpaceAdd

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU GlobalTheory.TruncKer GlobalTheory.Orb
open scoped ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chamber

example {k : ℕ} (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) :
    (volume : Measure (aMQ 𝔞 Q)) = (stdOrthonormalBasis ℝ (aMQ 𝔞 Q)).toBasis.addHaar := rfl

def ExpFamilyIntegral : Prop :=
  ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ X, IsOrth 𝔞 X → IsGMFam 𝔞 (expFam X) ∧ ∀ Q ∈ parF 𝔞 ∅,
    (Integrable (fun H : aMQ 𝔞 Q => gamM 𝔞 Q X H) ∧
      ∀ l, cM 𝔞 Q (expFam X) l = eL l (X Q) * ∫ H : aMQ 𝔞 Q, eL l H * gamM 𝔞 Q X H) ∧
    (Integrable (fun H : aMQ (aP Q) ∅ => gamP Q ∅ (X Q) H) ∧
      ∀ l, cP Q ∅ (expFam X) l = ∫ H : aMQ (aP Q) ∅, eL l H * gamP Q ∅ (X Q) H)

def FamilySmooth : Prop :=
  ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ c, IsGMFam 𝔞 c → ∀ Q ∈ parF 𝔞 ∅,
    (ContDiff ℝ ∞ (cM 𝔞 Q c) ∧ Set.EqOn (cM 𝔞 Q c) (sumM 𝔞 Q c) (generic k)) ∧
    ∀ R ⊆ Q, ContDiff ℝ ∞ (cP Q R c) ∧ Set.EqOn (cP Q R c) (sumP Q R c) (generic k)

def FamilyProduct : Prop :=
  ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ c d, IsGMFam 𝔞 c → IsGMFam 𝔞 d → ∀ R ∈ parF 𝔞 ∅, ∀ l,
    cM 𝔞 R (c * d) l = ∑ Q ∈ parF 𝔞 R, cM 𝔞 Q c l * cP Q R d l

end GlobalTheory.Chamber

namespace GlobalTheory.TruncKer

variable {D : D7} {V : HSp D} (Φ : WittFrame V) (K : Subgroup (GA D V)) (μ : Measure (GA D V))

def OrthogonalY : Prop :=
  ∀ x T, IsOrth ⊤ (Yfam Φ K x T) ∧
    ∀ π ε w, Φ.IsWeylRep D.sp.cm π ε w → Yfam Φ K x T (weylPar π ε) = Ys Φ K π ε w x T

def KernelConvergence : Prop :=
  ∀ f ∈ CcGA V, ∃ c : ℝ, ∀ T, Regular c T →
    (∀ 𝔬, IsSSClass 𝔬 → Integrable (descend (GQ V) (kT Φ K 𝔬 f T)) (autMeasure V μ)) ∧
    {𝔬 | IsSSClass 𝔬 ∧ ∫ q, ‖descend (GQ V) (kT Φ K 𝔬 f T) q‖ ∂autMeasure V μ ≠ 0}.Finite

def WeightedOrbital : Prop :=
  ∀ f ∈ CcGA V, ∀ γ : GF V, IsRegSS γ.1.1 → ∀ P, IsMinLevi Φ γ P →
    ∀ (dt : Measure (cent (rat V γ))) [dt.IsHaarMeasure], ∃ c : ℝ, ∀ T, Regular c T →
      Integrable (descend (cent (rat V γ)) fun x => (weight Φ K (aP P) T x : ℂ) * conjFn (rat V γ) f x)
        (quotMeas (cent (rat V γ)) dt μ) ∧
      ∫ q, descend (GQ V) (kT Φ K {δ | IsConj γ δ} f T) q ∂autMeasure V μ =
        volA Φ K (aP P) (cent (rat V γ)) dt *
          wOrbInt (cent (rat V γ)) dt μ (rat V γ) (fun x => weight Φ K (aP P) T x) f

end GlobalTheory.TruncKer

namespace GlobalTheory.Published

def LabesseWaldspurger : Prop :=
  (ExpFamilyIntegral ∧ FamilySmooth ∧ FamilyProduct) ∧
  ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a →
    OrthogonalY Φ (levelAll D.sp.cm.sig V.gram L a) ∧
    ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure],
      KernelConvergence Φ (levelAll D.sp.cm.sig V.gram L a) μ ∧ WeightedOrbital Φ (levelAll D.sp.cm.sig V.gram L a) μ

example (D : D7) : wittIndex (CuspDecay.Model.plane D) = 1 ∧
    ∃ (Φ : WittFrame (CuspDecay.Model.plane D)) (L : _) (a : _), Φ.IsGood D.sp.cm L a :=
  ⟨wittIndex_plane D, exists_isGood _⟩

end GlobalTheory.Published

end
