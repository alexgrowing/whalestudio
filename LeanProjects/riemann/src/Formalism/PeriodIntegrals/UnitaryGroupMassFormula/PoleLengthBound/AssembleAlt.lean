import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.GradedCoef

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def yPow (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} (w : Fin N → B.Cusp j wL)
    (α : Fin (WeightFamilies.dimY D j) → ℕ) : ↥(Frac0 X la w) :=
  ∏ i, sfr X la w i.succ ^ α i

def colIdx (D : D7) (j : ℕ) {N : ℕ} (col : Fin N) (α : Fin (WeightFamilies.dimY D j) → ℕ) : Idx D j N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => if p.2 = col then Fin.cases (motive := fun _ => ℕ) 0 α p.1 else 0

def rD (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (β : Idx D j G.N →₀ ℕ) (x : ↥(HK X la G.w wF)) :
    SectionSheafQuotient X la G.w wF := by
  classical
  exact if h : hasse X la G.w β (x : Lw X la G.w) ∈ HK X la G.w wF then toA0K X la G.w wF ⟨_, h⟩ else 0

def uSpec (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (u : Fin G.N → OsK X la G.w) : Prop :=
  ∀ col, ∃ f : ↥(Frac0 X la G.w),
    (f : Lw X la G.w) = algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wL (G.w col))) * w0inv X la G.w ∧
    toOsK X la G.w f = u col

def HKPres (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (β : Idx D j G.N →₀ ℕ) (x : Lw X la G.w), x ∈ HK X la G.w wF → hasse X la G.w β x ∈ HK X la G.w wF

def Vanish (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (k : ℕ) (β : Idx D j G.N →₀ ℕ) (x : ↥(HK X la G.w wF)),
    x ∈ Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) →
    (β.sum fun _ n => n) < k → rD G la β x = 0

def UnitCols (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∃ u : Fin G.N → OsK X la G.w, uSpec G la u ∧
    (∑ col, algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N ((0 : Fin (WeightFamilies.dimY D j + 1)), col)) * u col = 1) ∧
    ∀ (ζ : PtsG G la) (col : Fin G.N), 0 ≤ ord (unifO X la G.N) ζ (u col)

def Taylor (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (k : ℕ) (x : ↥(HK X la G.w wF)),
    x ∈ Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) →
    ∃ (cf : Mon (WeightFamilies.dimY D j) k → ↥(HK X la G.w wF)) (r : ↥(HK X la G.w wF)),
      r ∈ Jid X la G.w ^ (k + 1) • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) ∧
      x = ∑ α, yPow X la G.w α.1 • cf α + r

def ColDeriv (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ u : Fin G.N → OsK X la G.w, uSpec G la u →
    ∀ (k : ℕ) (α α' : Mon (WeightFamilies.dimY D j) k) (col : Fin G.N) (cf : ↥(HK X la G.w wF)),
      rD G la (colIdx D j col α'.1) (yPow X la G.w α.1 • cf) =
        if α = α' then u col ^ k • toA0K X la G.w wF cf else 0

def LinOp (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (k : ℕ) (β : Idx D j G.N →₀ ℕ) (r : Op X la G.N) (x : ↥(HK X la G.w wF)),
    x ∈ Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) →
    (β.sum fun _ n => n) ≤ k → rD G la β (algebraMap (Op X la G.N) (Kp X la G.N) r • x) = r • rD G la β x

def LiftMul (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (T : ℕ) : Prop :=
  ∀ (x : ↥(HK X la G.w wF)) (α : Fin (WeightFamilies.dimY D j) → ℕ),
    toWK X la G.w wF (a0 D j T) x ∈ Q.AA T → toWK X la G.w wF (a0 D j T) (yPow X la G.w α • x) ∈ Q.AA T

def Assemble : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T e : ℕ) (c : ℝ),
    Q.Ok S CRm T c → (∀ k, G.w k ∈ X.WWc S.sW wL) → Q.InLift T →
    HKPres G la → Vanish G la → UnitCols G la → Taylor G la → ColDeriv G la → LinOp G la → LiftMul G la Q T →
    GradedCoef G la Q T (Q.mm S T e)

end PI.PoleLengthCount
