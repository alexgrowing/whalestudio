import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
import Formalism.LocalToGlobal.KernelLattices.KerStd

noncomputable section

namespace GlobalTheory.AtG

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open scoped ComplexConjugate

def JetSplitAmb : Prop :=
  ∀ {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ),
    s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ →
    ∀ (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E a)) (N' : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E b))
      (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), Even a → Even b → Formalism.L2.Col.IsSdLat N → Formalism.L2.Col.IsSdLat N' →
      s.StdAtP p N → s.StdAtP p N' → ¬ (p : ℤ) ∣ NumberField.discr X.E → (∀ τ, ‖ι (cD τ)‖ ≤ 1) → 5 ≤ p →
      ¬ p ∣ D.host.d → (ambOf s B χ cD : Amb X).LaHyp a b S →
      ∀ (π : ℂ) (pE : 𝓞 X.E), Formalism.L2.AlgTh.IsQInt D.host.d π → π * conj π = (p : ℂ) → Formalism.L2.AlgTh.SplitS (ambOf s B χ cD) S p π pE →
      ∀ (c' : ℕ) (x : Formalism.L2.Col.HomE X.E a b), 0 < c' → ¬ p ∣ c' → x ∈ Formalism.L2.Col.divLat c' (Formalism.L2.Col.homAt S N N') → ∀ m : DVar X.Tau a b →₀ ℕ,
        ‖ι ((ambOf s B χ cD : Amb X).σ₀ ((ambOf s B χ cD : Amb X).jetK S N N' (p * c') x m))‖ * ‖ι (conj π)‖ ^ m.degree *
          ‖(p : ℂ_[p])‖ ^ (Fintype.card X.Tau * b * a) ≤ 1

open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound in

def TiesAt (D : D7) (EX : ErrX D) (Dx : DivX D) (μ : D.what₂.Tup) : Prop :=
  ∃ (Ch : Chars (recFields D) (recPrimes EX) D.R.m) (mu0 : _) (eta : _) (sel : _) (δ : ℂ) (B : Base D D.host.ccK δ) (χ : _) (cD : _),
    HostTie EX ∧ CharTie Ch mu0 eta sel ∧ AnTie D δ χ cD ∧ ∀ u, ChainTie Ch sel Dx mu0 (ambOf (recSeam D) B χ cD) u μ

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.KerRat in

def RowPin {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : (I.rec7 l Z).what₂.Tup) : Prop :=
  ∀ u : B.Word, ∃ e : (I.per l u a).Mt ≃ₗ[ℂ] (I.rec7 l Z).what₂.Amb a,
    (a = (I.rec7 l Z).what₂.mu0 → HEq e ((I.rec7 l Z).eMt u)) ∧ (a ≠ (I.rec7 l Z).what₂.mu0 → e = (I.rec7 l Z).eMtTw u a) ∧
    (∀ v ∈ ((I.rec7 l Z).what₂.Mtilde a).gen, ∃ z, e (rowForm I l h u a z) = v) ∧
    ∀ z, z ∈ Formalism.L2.Col.MtildeL (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps ↔ ∃ c : (I.rec7 l Z).what₂.Amb a → 𝓞 (I.rec7 l Z).what₂.LL,
      e (rowForm I l h u a z) = ∑ v ∈ ((I.rec7 l Z).what₂.Mtilde a).gen, (I.rec7 l Z).what₂.embLL ((c v : 𝓞 (I.rec7 l Z).what₂.LL) : (I.rec7 l Z).what₂.LL) • v

end GlobalTheory.AtG

end
