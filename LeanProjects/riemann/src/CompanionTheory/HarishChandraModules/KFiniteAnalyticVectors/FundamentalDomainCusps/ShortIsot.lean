import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.CompactIntegralBoundedByQuotientNorm
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.NilpAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef

open Matrix MeasureTheory NumberField Topology
open scoped ENNReal

noncomputable section

namespace CompanionTheory.D.gk.RF

open Formalism.MainNotions.S Formalism.L2.SG.ProjRows

def NWset {n : ℕ} (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) : Set (Formalism.REAL.UJ ε) :=
  {g | Lowers (Formalism.REAL.Jm ε) W (uMat g - 1)}

def NWSub : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)), Isot (Formalism.REAL.Jm ε) W →
    IsClosed (NWset ε W) ∧ ∃ N : Subgroup (Formalism.REAL.UJ ε), (N : Set (Formalism.REAL.UJ ε)) = NWset ε W

def RealPar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)), W ≠ ⊥ → Isot (Formalism.REAL.Jm ε) W →
    ∀ N : Subgroup (Formalism.REAL.UJ ε), (N : Set (Formalism.REAL.UJ ε)) = NWset ε W → ∃ a Ht, ParData N a Ht

def ParPi : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)] (i₀ : ι) (N : Subgroup (G i₀)) (a : ℝ → G i₀) (Ht : G i₀ → ℝ), ParData N a Ht →
    ParData (N.map (MonoidHom.mulSingle G i₀)) (fun t => Pi.mulSingle i₀ (a t)) (fun g => Ht (g i₀))

variable (I : AutInst)

def IntV : Set (Fin I.n → I.E) := {u | ∀ i, IsIntegral ℤ (u i)}

def atV (v : InfinitePlace I.F) (u : Fin I.n → I.E) : Fin I.n → ℂ := (I.P v)⁻¹ *ᵥ fun i => I.φ v (u i)

def atM (v : InfinitePlace I.F) (A : Matrix (Fin I.n) (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) ℂ :=
  (I.P v)⁻¹ * A.map (I.φ v) * I.P v

def vecAt (y : I.Ginf) (u : Fin I.n → I.E) : InfinitePlace I.F → Fin I.n → ℂ :=
  fun v => uMat (y v)⁻¹ *ᵥ atV I v u

def Wv (W : Submodule I.E (Fin I.n → I.E)) (v : InfinitePlace I.F) : Submodule ℂ (Fin I.n → ℂ) :=
  Submodule.span ℂ (atV I v '' (W : Set (Fin I.n → I.E)))

def Covers (y : I.Ginf) (W : Submodule I.E (Fin I.n → I.E)) (ρ : ℝ) : Prop :=
  ∀ b : InfinitePlace I.F → Fin I.n → ℂ, (∀ v, b v ∈ Wv I W v) →
    ∃ u ∈ IntV I, u ∈ W ∧ ‖(fun v => uMat (y v)⁻¹ *ᵥ b v) - vecAt I y u‖ ≤ ρ

def Cong (M : ℕ) (A : Matrix (Fin I.n) (Fin I.n) I.E) : Prop :=
  ∀ i j, ∃ a : I.E, IsIntegral ℤ a ∧ (A - 1) i j = (M : I.E) * a

def IsGam (M : ℕ) (γ : GL (Fin I.n) I.E) : Prop :=
  γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧ Cong I M (γ : Matrix (Fin I.n) (Fin I.n) I.E) ∧
    Cong I M ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E)

def GamSet (M : ℕ) : Set I.Ginf :=
  {g | ∃ γ : GL (Fin I.n) I.E, IsGam I M γ ∧ ∀ v, uMat (g v) = atM I v (γ : Matrix (Fin I.n) (Fin I.n) I.E)}

def NInf (W : Submodule I.E (Fin I.n → I.E)) : Set I.Ginf := {g | ∀ v, g v ∈ NWset (I.ε v) (Wv I W v)}

def Transp : Prop :=
  ∀ I : AutInst, I.Jᴴ = I.J ∧ (∀ v (a : I.E), I.φ v (star a) = star (I.φ v a)) ∧
    (∀ v u u', hf (Formalism.REAL.Jm (I.ε v)) (atV I v u) (atV I v u') = I.φ v (hf I.J u u')) ∧
    (∀ v (W : Submodule I.E (Fin I.n → I.E)), Wv I (perp I.J W) v = perp (Formalism.REAL.Jm (I.ε v)) (Wv I W v)) ∧
    (∀ v (W : Submodule I.E (Fin I.n → I.E)), W ≠ ⊥ → Wv I W v ≠ ⊥) ∧
    (∀ v (A : Matrix (Fin I.n) (Fin I.n) I.E) u, atM I v A *ᵥ atV I v u = atV I v (A *ᵥ u)) ∧
    (∀ v w b, atM I v (xw I.J w b) = xw (Formalism.REAL.Jm (I.ε v)) (atV I v w) (atV I v b)) ∧
    (∀ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J →
      ∃ g : I.Ginf, ∀ v, uMat (g v) = atM I v (γ : Matrix (Fin I.n) (Fin I.n) I.E))

def GamSub : Prop :=
  ∀ (I : AutInst) (M : ℕ), ∃ Γ : Subgroup I.Ginf, (Γ : Set I.Ginf) = GamSet I M ∧ Disc Γ

def ShortIsot : Prop :=
  ∀ I : AutInst, ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ (y : I.Ginf), ∀ u ∈ IntV I, ∀ u' ∈ IntV I,
    ‖vecAt I y u‖ ≤ s₀ → ‖vecAt I y u'‖ ≤ s₀ → hf I.J u u' = 0

def CovSpan : Prop :=
  ∀ I : AutInst, ∃ C : ℝ, 0 < C ∧ ∀ (y : I.Ginf) (d : ℕ) (w : Fin d → Fin I.n → I.E) (s : ℝ), d ≤ I.n → 0 ≤ s →
    (∀ i, w i ∈ IntV I ∧ ‖vecAt I y (w i)‖ ≤ s) → Covers I y (Submodule.span I.E (Set.range w)) (C * s)

def CovPerp : Prop :=
  ∀ I : AutInst, ∃ C : ℝ, 0 < C ∧ ∀ (y : I.Ginf) (W : Submodule I.E (Fin I.n → I.E)) (ρ t : ℝ), 0 < t → 2 * ρ ≤ t →
    Covers I y W ρ → (∀ u ∈ IntV I, u ∉ W → t ≤ ‖vecAt I y u‖) → Covers I y (perp I.J W) (C / t)

def Mahler : Prop :=
  ∀ (I : AutInst) (M : ℕ), 1 ≤ M → ∀ R : ℝ, ∃ C : Set I.Ginf, IsCompact C ∧
    ∀ y : I.Ginf, Covers I y ⊤ R → ∃ γ ∈ GamSet I M, γ * y ∈ C

def NCover : Prop :=
  ∀ (I : AutInst) (M : ℕ), 1 ≤ M → ∃ C : ℝ, 0 < C ∧ ∀ (y : I.Ginf) (d : ℕ) (w : Fin d → Fin I.n → I.E) (s ρ : ℝ),
    d ≤ I.n → 0 ≤ s → 0 ≤ ρ → s * ρ ≤ 1 → (∀ i, w i ∈ IntV I ∧ ‖vecAt I y (w i)‖ ≤ s) →
    Isot I.J (Submodule.span I.E (Set.range w)) → Covers I y (Submodule.span I.E (Set.range w)) ρ →
    Covers I y (perp I.J (Submodule.span I.E (Set.range w))) ρ →
    ∀ m ∈ NInf I (Submodule.span I.E (Set.range w)), ∃ γ ∈ GamSet I M,
      γ ∈ NInf I (Submodule.span I.E (Set.range w)) ∧
      ∀ v i j, ‖(uMat ((y⁻¹ * (γ * m) * y) v) - 1) i j‖ ≤ C * (s * ρ)

def GeoInf : Prop :=
  ∀ (I : AutInst) (M : ℕ), 1 ≤ M → ∀ U ∈ 𝓝 (1 : I.Ginf), ∃ C : Set I.Ginf, IsCompact C ∧ ∀ y : I.Ginf,
    (∃ γ ∈ GamSet I M, γ * y ∈ C) ∨ ∃ W : Submodule I.E (Fin I.n → I.E), W ≠ ⊥ ∧ Isot I.J W ∧
      ∀ m ∈ NInf I W, ∃ γ ∈ GamSet I M, γ ∈ NInf I W ∧ y⁻¹ * (γ * m) * y ∈ U

def CuspInf : Prop :=
  ∀ (I : AutInst) (M : ℕ), 1 ≤ M → ∀ ph : I.Ginf → ℂ, Integrable ph (muInf I) →
    (∀ w, ∫ y, ph y * ph (y⁻¹ * w) ∂(muInf I) = ph w) →
    ∀ U ∈ 𝓝 (1 : I.Ginf), ∃ C : Set I.Ginf, IsCompact C ∧ ∀ y : I.Ginf,
      (∃ γ ∈ GamSet I M, γ * y ∈ C) ∨ ∃ ν : Measure I.Ginf, IsProbabilityMeasure ν ∧ (∀ᵐ m ∂ν, y⁻¹ * m * y ∈ U) ∧
        ∀ u : I.Ginf → ℂ, BC u → (∀ γ ∈ GamSet I M, ∀ x, u (γ * x) = u x) →
          (∀ x, u x = ∫ z, ph z * u (x * z) ∂(muInf I)) → ∀ x, ∫ m, u (m * x) ∂ν = 0

def CongK : Prop :=
  ∀ (I : AutInst), ∀ U ∈ 𝓝 (1 : I.Gf), ∃ M : ℕ, 1 ≤ M ∧ ∀ g ∈ GamSet I M, ∃ x ∈ U, (g, x) ∈ I.GFset

def GFDisc : Prop := ∀ (I : AutInst) (C : Set I.GA), IsCompact C → (C ∩ I.GFset).Finite

def phK (μf : Measure I.Gf) (ph : I.Ginf → ℂ) (Kp : Subgroup I.Gf) : I.GA → ℂ :=
  fun g => ph g.1 * (Kp : Set I.Gf).indicator (fun _ => (((μf Kp).toReal⁻¹ : ℝ) : ℂ)) g.2

def CuspAdel : Prop :=
  ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (Γ : Subgroup I.GA),
    (Γ : Set I.GA) = I.GFset → ∀ Kp : Subgroup I.Gf, IsOpen (Kp : Set I.Gf) → IsCompact (Kp : Set I.Gf) →
    ∀ ph : I.Ginf → ℂ, Integrable ph (muInf I) → (∀ w, ∫ y, ph y * ph (y⁻¹ * w) ∂(muInf I) = ph w) →
    ∀ U ∈ 𝓝 (1 : I.GA), ∃ C : Set I.GA, IsCompact C ∧ ∀ x, (∃ γ ∈ Γ, γ * x ∈ C) ∨
      CuspAt (I.muA μf) (phK I μf ph Kp) Γ {g | g.2 ∈ Kp} U x

def LevelOf : Prop :=
  ∀ (I : AutInst) (e : I.Gf → ℂ), IsLocallyConstant e → (∀ x, e x ≠ 0 → x ∈ I.Kset) →
    ∃ Kp : Subgroup I.Gf, IsOpen (Kp : Set I.Gf) ∧ IsCompact (Kp : Set I.Gf) ∧ ∀ k ∈ Kp, ∀ x, e (k * x) = e x

def ConvRep : Prop :=
  ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA),
    I.IsFundDom (I.muA μf) fund →
    ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R →
    ∀ (φ₀ : I.GA → ℂ) (T : I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRConv μf fund R φ₀ T →
    ∀ Fv : I.L2 μf fund, (∃ M : ℝ, ∀ᵐ x ∂((I.muA μf).restrict fund), ‖(Fv : I.GA → ℂ) x‖ ≤ M) →
      ∃ s : I.GA → ℂ, Measurable s ∧ (∃ M : ℝ, ∀ x, ‖s x‖ ≤ M) ∧
        (∀ γ ∈ I.GFset, ∀ᵐ x ∂(I.muA μf), s (γ * x) = s x) ∧
        ((T Fv : I.L2 μf fund) : I.GA → ℂ) =ᵐ[(I.muA μf).restrict fund] fun x => ∫ y, φ₀ y * s (x * y) ∂(I.muA μf)

def RepOfConv : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (Γ : Subgroup G) (φ φ₀ s : G → ℂ), Integrable φ μ → Integrable φ₀ μ →
    (∀ w, ∫ y, φ y * φ₀ (y⁻¹ * w) ∂μ = φ₀ w) → Measurable s → (∃ M : ℝ, ∀ x, ‖s x‖ ≤ M) →
    (∀ γ ∈ Γ, ∀ᵐ x ∂μ, s (γ * x) = s x) → IsRep μ φ Γ fun x => ∫ y, φ₀ y * s (x * y) ∂μ

end CompanionTheory.D.gk.RF
