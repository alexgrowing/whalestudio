import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.MonoCount

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def wfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (k : Fin G.N) : ↥(Frac0 X la G.w) :=
  fr0 X la G.w 1 ⟨emb X la G.N (X.inc wL (G.w k)), by rw [add_zero_weight_one_eq]; exact emb_mem_Vw X la G.N wL (G.w k)⟩

def uC (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (jj : Fin G.N) (α : Fin (WeightFamilies.dimY D j) → ℕ) :
    OsK X la G.w :=
  ∏ i, toOsK X la G.w (wfr G la jj) ^ α i

def ym (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (α : Fin (WeightFamilies.dimY D j) → ℕ) : ↥(Frac0 X la G.w) :=
  ∏ i, sfr X la G.w i.succ ^ α i

def bcol {N : ℕ} (jj : Fin N) (α : Fin (WeightFamilies.dimY D j) → ℕ) : Idx D j N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => if p.2 = jj then Fin.cases (motive := fun _ => ℕ) 0 α p.1 else 0

def TaylorRep : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (k : ℕ) (x : ↥(HK X la G.w wF)),
    x ∈ (Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF))) → ∃ cf : (Fin (WeightFamilies.dimY D j) → ℕ) → ↥(HK X la G.w wF),
      x - ∑ α ∈ mon D j k, ym G la α • cf α ∈ (Jid X la G.w ^ (k + 1) • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)))

def TaylorHasse : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (k : ℕ) (x : ↥(HK X la G.w wF)) (cf : (Fin (WeightFamilies.dimY D j) → ℕ) → ↥(HK X la G.w wF)),
    x - ∑ α ∈ mon D j k, ym G la α • cf α ∈ (Jid X la G.w ^ (k + 1) • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF))) →
    ∀ (jj : Fin G.N) (α : Fin (WeightFamilies.dimY D j) → ℕ), α ∈ mon D j k →
      ∀ h : hasse X la G.w (bcol jj α) (x : Lw X la G.w) ∈ HK X la G.w wF,
        toA0K X la G.w wF ⟨_, h⟩ = uC G la jj α • toA0K X la G.w wF (cf α)

def HasseSmul : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (k : ℕ) (o : Op X la G.N) (x : ↥(HK X la G.w wF)), x ∈ (Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF))) →
    ∀ β : Idx D j G.N →₀ ℕ, (β.sum fun _ n => n) = k →
      ∀ (h : hasse X la G.w β ((o • x : ↥(HK X la G.w wF)) : Lw X la G.w) ∈ HK X la G.w wF)
        (h' : hasse X la G.w β (x : Lw X la G.w) ∈ HK X la G.w wF),
        toA0K X la G.w wF ⟨_, h⟩ = o • toA0K X la G.w wF ⟨_, h'⟩

def HasseVan : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (a : ℕ) (x : ↥(HK X la G.w wF)), x ∈ (Jid X la G.w ^ a • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF))) →
    ∀ β : Idx D j G.N →₀ ℕ, (β.sum fun _ n => n) < a →
      ∀ h : hasse X la G.w β (x : Lw X la G.w) ∈ HK X la G.w wF, toA0K X la G.w wF ⟨_, h⟩ = 0

def Column : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ),
    Q.Ok S CRm T c → (∀ k, G.w k ∈ X.WWc S.sW wL) →
    ∀ ζ : PtsG G la, (∀ jj, 0 ≤ ord (unifO X la G.N) ζ (toOsK X la G.w (wfr G la jj))) ∧
      ∃ jj, ord (unifO X la G.N) ζ (toOsK X la G.w (wfr G la jj)) = 0

def UInj : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ),
    Q.Ok S CRm T c → (∀ k, G.w k ∈ X.WWc S.sW wL) →
    ∀ (α : Fin (WeightFamilies.dimY D j) → ℕ) (b : SectionSheafQuotient X la G.w wF), (∀ jj, uC G la jj α • b = 0) → b = 0

def UBall : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ),
    Q.Ok S CRm T c → (∀ k, G.w k ∈ X.WWc S.sW wL) →
    ∀ (α : Fin (WeightFamilies.dimY D j) → ℕ) (b : SectionSheafQuotient X la G.w wF), (∀ jj, uC G la jj α • b ∈ Q.A0) → b ∈ Q.A0

def AARep : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ),
    Q.Ok S CRm T c → (∀ k, G.w k ∈ X.WWc S.sW wL) →
    ∀ x ∈ Q.AA T, ∃ x' : ↥(HK X la G.w wF), toWK X la G.w wF (a0 D j T) x' = x ∧
      ∀ β : Idx D j G.N →₀ ℕ, (β.sum fun _ n => n) ≤ a0 D j T - 1 →
        ∀ h : hasse X la G.w β (x' : Lw X la G.w) ∈ HK X la G.w wF, toA0K X la G.w wF ⟨_, h⟩ ∈ Q.A0

def TaylorSpanGenerators : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (T k : ℕ), k < a0 D j T → ∀ α ∈ mon D j k, ∀ i : Fin G.del,
    ∃ (x : ↥(HK X la G.w wF)) (cf : ↥(HK X la G.w wF)),
      toWK X la G.w wF (a0 D j T) x ∈ firstLength_le_prime_bound G la T ∧ x = ym G la α • cf ∧ toA0K X la G.w wF cf = tL G la i

def TaylorSpanLeBound : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ),
    Q.Ok S CRm T c → (∀ k, G.w k ∈ X.WWc S.sW wL) →
    (∀ i, G.th' i ∈ B.Mlat j wF) → firstLength_le_prime_bound G la T ≤ Q.AA T

end PoleLengthBounds
