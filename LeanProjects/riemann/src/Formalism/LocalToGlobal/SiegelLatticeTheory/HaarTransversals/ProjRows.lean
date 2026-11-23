import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

noncomputable section

open MeasureTheory NumberField
open scoped InnerProductSpace

namespace Formalism.L2.SG.ProjRows

section Defs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsURep (ρ : G → (H →L[ℂ] H)) : Prop :=
  ρ 1 = 1 ∧ (∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) ∧ (∀ g v, ‖ρ g v‖ = ‖v‖) ∧
    ∀ v, Continuous fun g => ρ g v

def IsFdegG (μ : Measure G) (σ : G → (H →L[ℂ] H)) (d : ℝ) : Prop :=
  0 < d ∧ ∀ v w v' w' : H,
    Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧
    ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

def coefM (σ : G → (H →L[ℂ] H)) (w : H) : G → ℂ := fun g => ⟪w, σ g w⟫_ℂ

def phOf (σ : G → (H →L[ℂ] H)) (w : H) (d : ℝ) : G → ℂ := fun g => (d : ℂ) * star (coefM σ w g)

def IsOpInt {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (μ : Measure G)
    (π : G → (K →L[ℂ] K)) (ph : G → ℂ) (T : K →L[ℂ] K) : Prop :=
  ∀ x y : K, ⟪x, T y⟫_ℂ = ∫ g, ph g * ⟪x, π g y⟫_ℂ ∂μ

def IsRowProj {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (π : G → (K →L[ℂ] K)) (m : G → ℂ) (T : K →L[ℂ] K) : Prop :=
  (∀ x y : K, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) ∧ T.comp T = T ∧ ∀ a, T.comp ((π a).comp T) = m a • T

def PhConv (μ : Measure G) (ph m : G → ℂ) : Prop :=
  m 1 = 1 ∧ (∀ g, ph g⁻¹ = star (ph g)) ∧
    ∀ x y : G, Integrable (fun g => ph g * ph (x⁻¹ * g⁻¹ * y)) μ ∧
      ∫ g, ph g * ph (x⁻¹ * g⁻¹ * y) ∂μ = m x * ph y

end Defs

def SchurConv : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (Hσ : Type) [NormedAddCommGroup Hσ] [InnerProductSpace ℂ Hσ]
    (σ : G → (Hσ →L[ℂ] Hσ)) (d : ℝ) (w : Hσ),
    IsURep σ → IsFdegG μ σ d → ‖w‖ = 1 →
      PhConv μ (phOf σ w d) (coefM σ w) ∧
      ∀ u u' : Hσ, Integrable (fun g => phOf σ w d g * ⟪u', σ g u⟫_ℂ) μ ∧
        ∫ g, phOf σ w d g * ⟪u', σ g u⟫_ℂ ∂μ = ⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ

def ConvProj : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (ph m : G → ℂ), Integrable ph μ → PhConv μ ph m →
    ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (π : G → (K →L[ℂ] K)) (T : K →L[ℂ] K),
      IsURep π → IsOpInt μ π ph T → IsRowProj π m T

set_option linter.dupNamespace false in

def ProjRows : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (Hσ : Type) [NormedAddCommGroup Hσ] [InnerProductSpace ℂ Hσ]
    (σ : G → (Hσ →L[ℂ] Hσ)) (d : ℝ) (w : Hσ),
    IsURep σ → IsFdegG μ σ d → ‖w‖ = 1 → Integrable (phOf σ w d) μ →
    ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (π : G → (K →L[ℂ] K)) (T : K →L[ℂ] K),
      IsURep π → IsOpInt μ π (phOf σ w d) T → IsRowProj π (coefM σ w) T

theorem projRows_of (hS : SchurConv) (hC : ConvProj) : ProjRows := by
  intro G _ _ _ _ _ _ μ _ _ _ Hσ _ _ σ d w hU hF hw hL K _ _ π T hπ hT
  exact hC G μ (phOf σ w d) (coefM σ w) hL (hS G μ Hσ σ d w hU hF hw).1 K π T hπ hT

def HomBij : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (Hσ : Type) [NormedAddCommGroup Hσ] [InnerProductSpace ℂ Hσ] [CompleteSpace Hσ]
    (σ : G → (Hσ →L[ℂ] Hσ)) (d : ℝ) (w : Hσ),
    IsURep σ → IsFdegG μ σ d → ‖w‖ = 1 → Integrable (phOf σ w d) μ →
    (∀ S : Submodule ℂ Hσ, IsClosed (S : Set Hσ) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤) →
    ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (π : G → (K →L[ℂ] K)) (T : K →L[ℂ] K),
      IsURep π → IsOpInt μ π (phOf σ w d) T →
      (∀ A : Hσ →L[ℂ] K, (∀ g, A.comp (σ g) = (π g).comp A) → T (A w) = A w) ∧
      (∀ A B : Hσ →L[ℂ] K, (∀ g, A.comp (σ g) = (π g).comp A) → (∀ g, B.comp (σ g) = (π g).comp B) →
        A w = B w → A = B) ∧
      (∀ v : K, T v = v → ∃ A : Hσ →L[ℂ] K, (∀ g, A.comp (σ g) = (π g).comp A) ∧ A w = v)

def ProdConv : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
    [∀ i, SecondCountableTopology (G i)] (μ : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, (μ i).IsMulLeftInvariant] [∀ i, (μ i).IsInvInvariant] (ph m : ∀ i, G i → ℂ),
    (∀ i, Integrable (ph i) (μ i)) → (∀ i, PhConv (μ i) (ph i) (m i)) →
      Integrable (fun g : ∀ i, G i => ∏ i, ph i (g i)) (Measure.pi μ) ∧
      PhConv (Measure.pi μ) (fun g => ∏ i, ph i (g i)) (fun g => ∏ i, m i (g i))

section Inst

open Formalism.MainNotions.S

abbrev muInf (I : AutInst) : Measure I.Ginf := Measure.pi fun v => Formalism.REAL.muG (I.ε v)

def phLoc {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H) (d : ℝ) : Formalism.REAL.UJ ε → ℂ :=
  fun g => (d : ℂ) * star ⟪w, σ (umat g) w⟫_ℂ

def mInf (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    (w : ∀ v, H v) : I.Ginf → ℂ :=
  fun g => ∏ v, ⟪w v, σ v (umat (g v)) (w v)⟫_ℂ

def phInf (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    (w : ∀ v, H v) (dv : InfinitePlace I.F → ℝ) : I.Ginf → ℂ :=
  fun g => ((∏ v, dv v : ℝ) : ℂ) * star (mInf I σ w g)

def RegUnitary : Prop :=
  ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA),
    I.IsFundDom (I.muA μf) fund →
    ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R →
      IsURep (fun g : I.Ginf => R (g, 1))

def ProjRowsR : Prop :=
  ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA),
    I.IsFundDom (I.muA μf) fund →
    ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R →
    ∀ (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
      (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (dv : InfinitePlace I.F → ℝ) (w : ∀ v, H v),
      (∀ v, IsURepOn (UJset (I.ε v)) (σ v)) → (∀ v, IsFdeg (Formalism.REAL.muG (I.ε v)) (σ v) (dv v)) →
      (∀ v, ‖w v‖ = 1) → (∀ v, Integrable (phLoc (ε := I.ε v) (σ v) (w v) (dv v)) (Formalism.REAL.muG (I.ε v))) →
      ∀ T : I.L2 μf fund →L[ℂ] I.L2 μf fund,
        IsOpInt (muInf I) (fun g => R (g, 1)) (phInf I σ w dv) T →
        IsRowProj (fun g => R (g, 1)) (mInf I σ w) T

theorem isURep_of_on {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hU : IsURepOn (UJset ε) σ) :
    IsURep (fun g : Formalism.REAL.UJ ε => σ (umat g)) :=
  ⟨hU.1.1, fun a b => hU.1.2 _ (Formalism.MainNotions.BridgeCSchur.umat_mem a) _ (Formalism.MainNotions.BridgeCSchur.umat_mem b),
    fun g v => hU.2.1 _ (Formalism.MainNotions.BridgeCSchur.umat_mem g) v,
    fun v => (hU.2.2 v).comp_continuous Formalism.MainNotions.BridgeCSchur.continuous_umat Formalism.MainNotions.BridgeCSchur.umat_mem⟩

theorem phInf_eq (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    (w : ∀ v, H v) (dv : InfinitePlace I.F → ℝ) :
    phInf I σ w dv = fun g => ∏ v, phLoc (ε := I.ε v) (σ v) (w v) (dv v) (g v) := by
  funext g
  simp only [phInf, mInf, phLoc, Complex.ofReal_prod, Finset.prod_mul_distrib]
  congr 1
  exact map_prod (starRingEnd ℂ) _ _

theorem projRowsR_of (hS : SchurConv) (hC : ConvProj) (hP : ProdConv) (hR : RegUnitary) : ProjRowsR := by
  classical
  intro I μf _ _ fund hfund R hRR H _ _ σ dv w hU hF hw hL T hT
  have hloc : ∀ v, PhConv (Formalism.REAL.muG (I.ε v)) (phLoc (ε := I.ε v) (σ v) (w v) (dv v))
      (coefM (fun g : Formalism.REAL.UJ (I.ε v) => σ v (umat g)) (w v)) := fun v =>
    (hS (Formalism.REAL.UJ (I.ε v)) (Formalism.REAL.muG (I.ε v)) (H v) (fun g => σ v (umat g)) (dv v) (w v)
      (isURep_of_on (hU v)) (hF v) (hw v)).1
  obtain ⟨hint, hconv⟩ := hP (InfinitePlace I.F) (fun v => Formalism.REAL.UJ (I.ε v)) (fun v => Formalism.REAL.muG (I.ε v))
    (fun v => phLoc (ε := I.ε v) (σ v) (w v) (dv v))
    (fun v => coefM (fun g : Formalism.REAL.UJ (I.ε v) => σ v (umat g)) (w v)) hL hloc
  rw [← phInf_eq] at hint hconv
  rw [phInf_eq] at hT
  have hT' : IsOpInt (muInf I) (fun g => R (g, 1)) (phInf I σ w dv) T := by rw [phInf_eq]; exact hT
  exact hC I.Ginf (muInf I) (phInf I σ w dv) (mInf I σ w) hint hconv (I.L2 μf fund) (fun g => R (g, 1)) T
    (hR I μf fund hfund R hRR) hT'

end Inst

end Formalism.L2.SG.ProjRows
