import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.FlagUnipotentLattices.HalfDeltaL1Bound

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData

theorem one_mem_rational_points (I : AutInst) : (1 : I.GA) ∈ I.GFset := by
  refine ⟨1, one_mem _, fun v => ?_, ?_⟩
  · have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
    simp [uMat, Matrix.nonsing_inv_mul _ hP]
  · simp [AutInst.fmat]

theorem one_le_discriminant_root (I : AutInst) : 1 ≤ I.rd := by
  unfold AutInst.rd
  apply Real.one_le_rpow
  · have h : (1 : ℤ) ≤ |discr I.E| := Int.one_le_abs (NumberField.discr_ne_zero I.E)
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|discr I.E| : ℤ) : ℝ) := by exact_mod_cast h
    simpa using h2
  · positivity

theorem one_le_autInst_f (I : AutInst) : 1 ≤ I.f := Module.finrank_pos

structure CData : Type 1 where
  I : AutInst
  b : ℝ
  lam : InfinitePlace I.F → Fin I.n → ℝ
  g : ℕ
  g₀ : ℕ
  e : I.Gf → ℂ
  H : InfinitePlace I.F → Type
  [hN : ∀ v, NormedAddCommGroup (H v)]
  [hI : ∀ v, InnerProductSpace ℂ (H v)]
  [hC : ∀ v, CompleteSpace (H v)]
  σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)
  w : ∀ v, H v
  Hs : Type
  [sN : NormedAddCommGroup Hs]
  [sI : InnerProductSpace ℂ Hs]
  [sC : CompleteSpace Hs]
  σs : I.Ginf → (Hs →L[ℂ] Hs)
  tens : (∀ v, H v) → Hs
  μf : Measure I.Gf
  [sf : SigmaFinite μf]
  fund : Set I.GA
  R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)
  Re : I.L2 μf fund →L[ℂ] I.L2 μf fund
  h : ℝ

attribute [instance] CData.hN CData.hI CData.hC CData.sN CData.sI CData.sC CData.sf

namespace CData

variable (X : CData)

abbrev L2 : Type := X.I.L2 X.μf X.fund

abbrev rg (T : X.L2 →L[ℂ] X.L2) : Submodule ℂ X.L2 := LinearMap.range (T : X.L2 →ₗ[ℂ] X.L2)

def φ : X.I.GA → ℂ := phe X.I (phOf X.I X.σ X.w) X.e

def μ : Measure X.I.GA := (X.I.muA X.μf).restrict X.fund

def Dc : ℝ := (X.I.Dcount X.σs X.μf X.fund X.R X.Re : ℝ)

def Ds : ℝ := X.I.Dstar (fdegAll X.I X.σ X.w) X.μf X.fund X.e

def one' : X.I.GFset := ⟨1, one_mem_rational_points X.I⟩

def kerD (x : X.I.GA) : ℂ := ∑' γ : X.I.GFset, X.φ (x⁻¹ * (γ : X.I.GA) * x)

open Classical in

def kerR (x : X.I.GA) : ℂ := ∑' γ : X.I.GFset, if γ = X.one' then 0 else X.φ (x⁻¹ * (γ : X.I.GA) * x)

def IsOp (T : X.L2 →L[ℂ] X.L2) : Prop := X.I.IsRConv X.μf X.fund X.R X.φ T

def HypB (n₀ : ℕ) (A : ℝ) : Prop :=
  HidaSetting X.I n₀ A X.b X.lam X.μf X.g X.g₀ X.e ∧
    CountData X.I X.lam X.σ X.w X.σs X.tens X.μf X.fund X.R X.e X.Re ∧
    ∀ v, Formalism.QuantumDeterminants.GapAtLeast (X.I.ε v) (X.lam v) X.h

def GapAboveThreeHalvesPower : Prop := ∀ v, 120 * (X.I.n : ℝ) * (q0At X.I v : ℝ) ^ ((3 : ℝ) / 2) ≤ X.h

def GapAboveSquareRootThreshold (C : ℝ) : Prop := ∀ v, C * (X.I.n : ℝ) ^ 2 * Real.sqrt (q0At X.I v : ℝ) ≤ X.h

def HypC (n₀ : ℕ) (A C cb : ℝ) : Prop :=
  X.HypB n₀ A ∧ C * (X.I.n : ℝ) ^ 19 * (X.I.f : ℝ) ^ 5 * Real.log (X.b * X.I.rd) ≤ X.h ∧
    Real.log (X.I.f : ℝ) ≤ Real.sqrt (X.I.n : ℝ) ∧
    Real.log (Real.log X.b) ≤ cb * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ)

def ConB (C : ℝ) : Prop :=
  ConclB X.I X.σ X.w X.σs X.μf X.fund X.R X.e X.Re X.GapAboveThreeHalvesPower (X.GapAboveThreeHalvesPower ∧ X.GapAboveSquareRootThreshold C)

def ConC (c : ℝ) : Prop :=
  |X.Dc - X.Ds| ≤ Real.exp (-c * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ)) * X.Ds

end CData

theorem second_part_iff_bundles (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C : ℝ) :
    Conclusion2 D n₀ A C ↔ ∀ X : CData, X.HypB n₀ A → X.ConB C := by
  constructor
  · intro h X hX
    exact h X.I X.b X.lam X.g X.g₀ X.e X.H X.σ X.w X.Hs X.σs X.tens X.μf X.fund X.R X.Re X.h hX.1 hX.2.1 hX.2.2
  · intro h I b lam g g₀ e H _ _ _ σ w Hs _ _ _ σs tens μf _ fund R Re hh hS hC hG
    exact h { I := I, b := b, lam := lam, g := g, g₀ := g₀, e := e, H := H, σ := σ, w := w, Hs := Hs, σs := σs,
              tens := tens, μf := μf, fund := fund, R := R, Re := Re, h := hh } ⟨hS, hC, hG⟩

theorem third_part_iff_bundles (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C c cb : ℝ) :
    PointsLemma D n₀ A C c cb ↔ ∀ X : CData, X.HypC n₀ A C cb → X.ConC c := by
  constructor
  · intro h X hX
    exact h X.I X.b X.lam X.g X.g₀ X.e X.H X.σ X.w X.Hs X.σs X.tens X.μf X.fund X.R X.Re X.h hX.1.1 hX.1.2.1 hX.1.2.2
      hX.2.1 hX.2.2.1 hX.2.2.2
  · intro h I b lam g g₀ e H _ _ _ σ w Hs _ _ _ σs tens μf _ fund R Re hh hS hC hG h1 h2 h3
    exact h { I := I, b := b, lam := lam, g := g, g₀ := g₀, e := e, H := H, σ := σ, w := w, Hs := Hs, σs := σs,
              tens := tens, μf := μf, fund := fund, R := R, Re := Re, h := hh } ⟨⟨hS, hC, hG⟩, h1, h2, h3⟩

namespace CData

variable (X : CData)

def ProjStep : Prop := ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T

def CountedStep : Prop := ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T →
  ∃ κ : X.I.eHom X.σs X.μf X.fund X.R X.Re ≃ₗ[ℂ] X.rg T,
    ∀ Φ, ((κ Φ : X.rg T) : X.L2) = (Φ : X.Hs →L[ℂ] X.L2) (X.tens X.w)

def CuspStep : Prop := ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T →
  ∀ Fv ∈ X.rg T, X.I.IsCuspFn (X.I.muA X.μf) (X.I.ext Fv)

theorem phOf_eq_prod (g : X.I.Ginf) :
    phOf X.I X.σ X.w g = ∏ v, phLoc (X.I.ε v) (X.σ v) (X.w v) (g v) := by
  unfold phOf phLoc fdegAll
  rw [Finset.prod_mul_distrib]
  congr 1
  · push_cast; rfl
  · exact map_prod (starRingEnd ℂ) _ _

theorem phOf_integrable
    (hloc : ∀ v, Integrable (phLoc (X.I.ε v) (X.σ v) (X.w v)) (Formalism.REAL.muG (X.I.ε v))) :
    Integrable (phOf X.I X.σ X.w) (Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)) := by
  have h := Integrable.fintype_prod_dep (μ := fun v => Formalism.REAL.muG (X.I.ε v))
    (f := fun v => phLoc (X.I.ε v) (X.σ v) (X.w v)) hloc
  exact h.congr (Filter.Eventually.of_forall fun g => (X.phOf_eq_prod g).symm)

end CData

def StepsB (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ X : CData, X.HypB n₀ A → X.GapAboveThreeHalvesPower → X.GapAboveSquareRootThreshold C → X.ProjStep ∧ X.CountedStep ∧ X.CuspStep

theorem spherical_function_integrable_of_local (D : Formalism.BasicNotions.D7) (hL : MatrixCoefficientIntegrable D) (n₀ : ℕ) (A : ℝ) (X : CData) (hX : X.HypB n₀ A)
    (h1 : X.GapAboveThreeHalvesPower) : Integrable (phOf X.I X.σ X.w) (Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)) := by
  apply X.phOf_integrable
  intro v
  exact hL X.I.n (X.I.ε v) (X.lam v) (hX.1.2.2.2.2.1 v) (X.H v) (X.σ v) (hX.2.1.1 v) (X.w v) (hX.2.1.2.1 v) X.h
    (hX.2.2 v) (h1 v)

theorem hodgeTateFromSandwich_of_admissibility_implication (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A Cb : ℝ)
    (hS : (adm1 D ∧ adm6 D ∧ adm8 D) → DiscreteSeriesDecayBound D → LocalProjectorRealPlace D → StepsB n₀ A Cb) : HodgeTateFromSandwich D n₀ A Cb := by
  intro hadm hdec hloc
  rw [second_part_iff_bundles]
  intro X hX
  refine ⟨fun h1 => ?_, fun hP T hT => ?_⟩
  · apply X.phOf_integrable
    intro v
    exact (hloc X.I.n (X.I.ε v) (X.lam v) (hX.1.2.2.2.2.1 v) (X.H v) (X.σ v) (hX.2.1.1 v) (X.w v) (hX.2.1.2.1 v) X.h
      (hX.2.2 v) (h1 v)).1
  · obtain ⟨s1, s2, s3⟩ := hS hadm hdec hloc X hX hP.1 hP.2
    have hp := s1 T hT
    obtain ⟨κ, -⟩ := s2 T hT hp
    have hfd : FiniteDimensional ℂ (X.I.eHom X.σs X.μf X.fund X.R X.Re) :=
      hadm.2.2 X.I n₀ A X.b X.lam X.g X.g₀ X.e X.H X.σ X.w X.Hs X.σs X.tens X.μf X.fund X.R X.Re hX.1 hX.2.1
    exact ⟨hp, Module.Finite.equiv κ, κ.finrank_eq.symm, s3 T hT hp⟩

theorem closed_second_part_of_estimates
    (hS : ∀ A : ℝ, 1 ≤ A → ∃ (n₀ : ℕ) (C₀ : ℝ), ∀ Cb ≥ C₀, ∀ D : Formalism.BasicNotions.D7,
      (adm1 D ∧ adm6 D ∧ adm8 D) → DiscreteSeriesDecayBound D → LocalProjectorRealPlace D → StepsB n₀ A Cb) : ClosedFormProjectorBound := by
  intro A hA
  obtain ⟨n₀, C₀, h⟩ := hS A hA
  exact ⟨n₀, C₀, fun Cb hCb D => hodgeTateFromSandwich_of_admissibility_implication D n₀ A Cb (h Cb hCb D)⟩

namespace CData

variable (X : CData)

def OpExists : Prop := ∃ T : X.L2 →L[ℂ] X.L2, X.IsOp T

def KernelDiag : Prop := ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T →
  ∀ (N : ℕ) (F : OrthonormalBasis (Fin N) ℂ (X.rg T)), ∀ᵐ x ∂X.μ,
    Summable (fun γ : X.I.GFset => X.φ (x⁻¹ * (γ : X.I.GA) * x)) ∧
      X.kerD x = ((∑ w, ‖(((F w : X.rg T) : X.L2) : X.I.GA → ℂ) x‖ ^ 2 : ℝ) : ℂ)

def FinVol : Prop := (X.I.muA X.μf) X.fund ≠ ⊤

def ProbMod (c₁ : ℝ) (Mod : Set X.I.GA) : Prop :=
  (1 - Real.exp (-(c₁ * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ)))) * X.I.vol X.μf X.fund ≤ X.μ.real Mod

def ModerateSum (c₁ A₁ : ℝ) (Mod : Set X.I.GA) : Prop :=
  |∫ x in Mod, (X.kerR x).re ∂X.μ| ≤
    A₁ * Real.exp (-(c₁ * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) * X.Ds

def DeepInt (A₁ : ℝ) (Mod : Set X.I.GA) : Prop :=
  |∫ x in Modᶜ, (X.kerD x).re ∂X.μ| ≤ A₁ * Real.exp (-((X.I.n : ℝ) ^ 2 * (X.I.f : ℝ))) * X.Dc

def Regions (c₁ A₁ : ℝ) : Prop :=
  ∃ Mod : Set X.I.GA, MeasurableSet Mod ∧ X.ProbMod c₁ Mod ∧ X.ModerateSum c₁ A₁ Mod ∧ X.DeepInt A₁ Mod

theorem φ_one (hDS : ∀ v, IsDS (X.I.ε v) (X.lam v) (X.σ v)) (hw : ∀ v, ‖X.w v‖ = 1) :
    X.φ 1 = ((fdegAll X.I X.σ X.w : ℝ) : ℂ) * X.e 1 := by
  unfold φ phe phOf
  have h1 : ∀ v, coefOn (X.σ v) (X.w v) (X.w v) ((1 : X.I.GA).1 v) = 1 := by
    intro v
    have hσ : X.σ v 1 = 1 := (hDS v).2.2.1.1.1
    have hu : umat ((1 : X.I.GA).1 v) = 1 := rfl
    unfold coefOn
    rw [hu, hσ, one_apply_eq_self, inner_self_eq_norm_sq_to_K, hw v]
    simp
  simp only [h1, Finset.prod_const_one, star_one, mul_one]
  rfl

theorem fdegAll_nonneg : 0 ≤ fdegAll X.I X.σ X.w := by
  unfold fdegAll
  refine Finset.prod_nonneg fun v _ => ?_
  unfold fdegOf
  exact div_nonneg (by positivity) (integral_nonneg fun g => by positivity)

theorem e_one_nonneg (hp : X.I.IsPosType X.e) : 0 ≤ (X.e 1).re := by
  have h := hp 1 (fun _ => 1) (fun _ => 1)
  simp at h
  exact (Complex.le_def.1 h).1

theorem Ds_nonneg (hp : X.I.IsPosType X.e) : 0 ≤ X.Ds := by
  unfold Ds AutInst.Dstar AutInst.vol
  exact mul_nonneg (mul_nonneg X.fdegAll_nonneg ENNReal.toReal_nonneg) (X.e_one_nonneg hp)

theorem vol_eq : X.I.vol X.μf X.fund = X.μ.real Set.univ := by
  unfold AutInst.vol μ Measure.real
  rw [Measure.restrict_apply_univ]

open Classical in

theorem count_of_steps {c₁ A₁ c' : ℝ} {n₁ : ℕ}
    (hFS : ∀ (n f : ℕ) (D Ds pr E₁ E₂ : ℝ), n₁ ≤ n → 1 ≤ f → 0 ≤ D → 0 ≤ Ds → pr ≤ 1 →
      1 - Real.exp (-(c₁ * n * f * Real.log n)) ≤ pr →
      |E₁| ≤ A₁ * Real.exp (-(c₁ * n * f * Real.log n)) * Ds →
      |E₂| ≤ A₁ * Real.exp (-((n : ℝ) ^ 2 * f)) * D →
      D = Ds * pr + E₁ + E₂ → |D - Ds| ≤ Real.exp (-(c' * n * f * Real.log n)) * Ds)
    (hn : n₁ ≤ X.I.n) (hDS : ∀ v, IsDS (X.I.ε v) (X.lam v) (X.σ v)) (hw : ∀ v, ‖X.w v‖ = 1)
    (hp : X.I.IsPosType X.e)
    (hproj : ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T ∧ FiniteDimensional ℂ (X.rg T) ∧
      Module.finrank ℂ (X.rg T) = X.I.Dcount X.σs X.μf X.fund X.R X.Re)
    (hT : X.OpExists) (hK : X.KernelDiag) (hV : X.FinVol) (hR : X.Regions c₁ A₁) : X.ConC c' := by
  obtain ⟨T, hT⟩ := hT
  obtain ⟨hP, hfd, hrk⟩ := hproj T hT
  have := hfd
  set F := stdOrthonormalBasis ℂ (X.rg T) with hF
  have hae := hK T hT hP _ F
  set Fn : Fin (Module.finrank ℂ (X.rg T)) → X.I.GA → ℂ := fun w => (((F w : X.rg T) : X.L2) : X.I.GA → ℂ) with hFn
  have horth : ∀ w w', (∫ x, star (Fn w x) * Fn w' x ∂X.μ) = if w = w' then 1 else 0 := by
    intro w w'
    have h1 := orthonormal_iff_ite.1 F.orthonormal w w'
    rw [Submodule.coe_inner, MeasureTheory.L2.inner_def] at h1
    rw [← h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hFn, RCLike.inner_apply]
    rw [mul_comm]
    rfl
  have htr := Formalism.HermitianLatticeCounting.Final.S7.traceDiag X.I.GA _ X.μ Fn horth
  set S : X.I.GA → ℝ := fun x => ∑ w, ‖Fn w x‖ ^ 2 with hS
  have hSint : Integrable S X.μ := by
    refine integrable_finsetSum _ fun w _ => ?_
    exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 (Lp.memLp _)
  set k0 : ℝ := fdegAll X.I X.σ X.w * (X.e 1).re with hk0
  set K : X.I.GA → ℝ := fun x => k0 + (X.kerR x).re with hKdef
  have hsplit1 : ∀ᵐ x ∂X.μ, (X.kerD x).re = K x ∧ K x = S x := by
    filter_upwards [hae] with x hx
    have h2 : X.kerD x = X.φ (x⁻¹ * ((X.one' : X.I.GFset) : X.I.GA) * x) + X.kerR x :=
      hx.1.tsum_eq_add_tsum_ite X.one'
    have h3 : x⁻¹ * ((X.one' : X.I.GFset) : X.I.GA) * x = 1 := by
      show x⁻¹ * 1 * x = 1
      group
    rw [h3, X.φ_one hDS hw] at h2
    have h4 : (X.kerD x).re = K x := by
      rw [h2, Complex.add_re, Complex.re_ofReal_mul]
    refine ⟨h4, ?_⟩
    rw [← h4, hx.2, Complex.ofReal_re]
  have hKint : Integrable K X.μ := hSint.congr (hsplit1.mono fun x hx => hx.2.symm)
  have hKtot : ∫ x, K x ∂X.μ = X.Dc := by
    rw [integral_congr_ae (hsplit1.mono fun x hx => hx.2), htr, Fintype.card_fin, hrk]
    rfl
  obtain ⟨Mod, hM, hprob, hmod, hdeep⟩ := hR
  have : IsFiniteMeasure X.μ := ⟨by
    unfold μ
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hV⟩
  have hsp := Formalism.HermitianLatticeCounting.Final.S7.diagSplit X.I.GA X.μ K (fun x => (X.kerR x).re) Mod k0 hM hKint (fun x _ => rfl)
  have hE2 : ∫ x in Modᶜ, K x ∂X.μ = ∫ x in Modᶜ, (X.kerD x).re ∂X.μ :=
    integral_congr_ae (ae_restrict_of_ae (hsplit1.mono fun x hx => hx.1.symm))
  rw [hKtot, hE2] at hsp
  have hvol := X.vol_eq
  have hDs : X.Ds = k0 * X.μ.real Set.univ := by
    unfold Ds AutInst.Dstar
    rw [hvol, hk0]
    ring
  have hle : X.μ.real Mod ≤ X.μ.real Set.univ := measureReal_mono (Set.subset_univ _)
  have h0 : 0 ≤ X.μ.real Mod := measureReal_nonneg
  have hconv : ∀ c : ℝ, Real.exp (-c * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ)) =
      Real.exp (-(c * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) := fun c => by
    congr 1; ring
  unfold ConC
  rw [hconv]
  unfold ProbMod at hprob
  rw [hvol] at hprob
  by_cases hv0 : X.μ.real Set.univ = 0
  · refine hFS X.I.n X.I.f X.Dc X.Ds 1 _ _ hn (one_le_autInst_f X.I) (Nat.cast_nonneg _) (X.Ds_nonneg hp) le_rfl ?_ hmod hdeep ?_
    · have := Real.exp_pos (-(c₁ * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ)))
      linarith
    · have hm0 : X.μ.real Mod = 0 := le_antisymm (hv0 ▸ hle) h0
      rw [hsp, hDs, hv0, hm0]
      ring
  · have hvpos : 0 < X.μ.real Set.univ := lt_of_le_of_ne measureReal_nonneg (Ne.symm hv0)
    refine hFS X.I.n X.I.f X.Dc X.Ds (X.μ.real Mod / X.μ.real Set.univ) _ _ hn (one_le_autInst_f X.I) (Nat.cast_nonneg _)
      (X.Ds_nonneg hp) ((div_le_one hvpos).2 hle) ?_ hmod hdeep ?_
    · rw [le_div_iff₀ hvpos]
      exact hprob
    · rw [hsp, hDs]
      field_simp

end CData

def StepsC (n₀ : ℕ) (A C cb c₁ A₁ : ℝ) : Prop :=
  ∀ X : CData, X.HypC n₀ A C cb → X.OpExists ∧ X.KernelDiag ∧ X.FinVol ∧ X.Regions c₁ A₁

theorem gap_thresholds_of_height_bound {Cb Ch : ℝ}
    (hH : ∀ (n q f : ℕ) (b rd h : ℝ), 1 ≤ n → 1 ≤ f → q ^ 2 ≤ n → 2 ≤ b → 1 ≤ rd →
      Ch * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * Real.log (b * rd) ≤ h →
      120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ h ∧ Cb * (n : ℝ) ^ 2 * Real.sqrt q ≤ h ∧ 32 * (n : ℝ) * q < h)
    (X : CData) {n₀ : ℕ} {A C cb : ℝ} (h1 : 1 ≤ n₀) (hC : Ch ≤ C) (hX : X.HypC n₀ A C cb) :
    X.GapAboveThreeHalvesPower ∧ X.GapAboveSquareRootThreshold Cb := by
  obtain ⟨⟨⟨hn, ⟨p, q, hpq, hq⟩, hb, -⟩, -, -⟩, hh, -, -⟩ := hX
  have hrd := one_le_discriminant_root X.I
  have hlog : 0 ≤ Real.log (X.b * X.I.rd) := Real.log_nonneg (by nlinarith)
  have hle : Ch * (X.I.n : ℝ) ^ 19 * (X.I.f : ℝ) ^ 5 * Real.log (X.b * X.I.rd) ≤ X.h := by
    refine le_trans ?_ hh
    have : 0 ≤ (X.I.n : ℝ) ^ 19 * (X.I.f : ℝ) ^ 5 * Real.log (X.b * X.I.rd) := by positivity
    nlinarith
  have key : ∀ v, 120 * (X.I.n : ℝ) * (q0At X.I v : ℝ) ^ ((3 : ℝ) / 2) ≤ X.h ∧
      Cb * (X.I.n : ℝ) ^ 2 * Real.sqrt (q0At X.I v : ℝ) ≤ X.h := by
    intro v
    have hq0 : q0At X.I v ≤ q := by
      unfold q0At
      rw [(hpq v).2]
      exact min_le_right _ _
    have := hH X.I.n (q0At X.I v) X.I.f X.b X.I.rd X.h (le_trans h1 hn) (one_le_autInst_f X.I)
      (le_trans (Nat.pow_le_pow_left hq0 2) hq) hb hrd hle
    exact ⟨this.1, this.2.1⟩
  exact ⟨fun v => (key v).1, fun v => (key v).2⟩

theorem third_part_of_estimates (c₁ A₁ : ℝ) (hc₁ : 0 < c₁) (hA₁ : 0 ≤ A₁) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ n₁ : ℕ, ∀ Cb : ℝ, ∃ C₁ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C cb : ℝ),
      n₁ ≤ n₀ → C₁ ≤ C → Conclusion2 D n₀ A Cb → StepsC n₀ A C cb c₁ A₁ → PointsLemma D n₀ A C c' cb := by
  obtain ⟨c', hc', n₁, hFS⟩ := Formalism.HermitianLatticeCounting.Final.S7.finalSum c₁ A₁ hc₁ hA₁
  refine ⟨c', hc', max n₁ 1, fun Cb => ?_⟩
  obtain ⟨Ch, -, hH⟩ := Formalism.HermitianLatticeCounting.Final.S7.threshHead Cb
  refine ⟨Ch, fun D n₀ A C cb hn hC hb hS => ?_⟩
  rw [third_part_iff_bundles]
  intro X hX
  obtain ⟨s1, s2, s3, s4⟩ := hS X hX
  have hthr := gap_thresholds_of_height_bound hH X (le_trans (le_max_right _ _) hn) hC hX
  have hB := ((second_part_iff_bundles D n₀ A Cb).1 hb X hX.1).2 hthr
  refine X.count_of_steps hFS (le_trans (le_trans (le_max_left _ _) hn) hX.1.1.1) hX.1.2.1.1
    (fun v => (hX.1.2.1.2.1 v).1) hX.1.1.2.2.2.2.2.2.1.2.2.2.1 (fun T hT => ?_) s1 s2 s3 s4
  obtain ⟨a, b, c, -⟩ := hB T hT
  exact ⟨a, b, c⟩

theorem third_bound_of_estimates (c₁ A₁ : ℝ) (hc₁ : 0 < c₁) (hA₁ : 0 ≤ A₁) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ n₁ : ℕ, ∀ Cb : ℝ, ∃ C₁ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (Cres : ℝ) (n₀ : ℕ) (A C cb : ℝ),
      n₁ ≤ n₀ → C₁ ≤ C →
      ((ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D Cres ∧ adm8 D) → DiscreteSeriesDecayBound D → Conclusion2 D n₀ A Cb →
        StepsC n₀ A C cb c₁ A₁) →
      TowerRallisLemma D Cres n₀ A Cb C c' cb := by
  obtain ⟨c', hc', n₁, h⟩ := third_part_of_estimates c₁ A₁ hc₁ hA₁
  refine ⟨c', hc', n₁, fun Cb => ?_⟩
  obtain ⟨C₁, h⟩ := h Cb
  exact ⟨C₁, fun D Cres n₀ A C cb hn hC hS hadm hdec hb => h D n₀ A C cb hn hC hb (hS hadm hdec hb)⟩

def ClosedThirdTermEstimates : Prop :=
  ∃ c₁ cb A₁ : ℝ, 0 < c₁ ∧ 0 < cb ∧ 0 ≤ A₁ ∧ ∀ Cres A Cb : ℝ, 1 ≤ A → ∃ (n₀ : ℕ) (C₀ : ℝ),
    ∀ n₀' ≥ n₀, ∀ C ≥ C₀, ∀ D : Formalism.BasicNotions.D7,
      (ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D Cres ∧ adm8 D) → DiscreteSeriesDecayBound D → Conclusion2 D n₀' A Cb →
        StepsC n₀' A C cb c₁ A₁

theorem closed_third_part_of_estimates (hS : ClosedThirdTermEstimates) : ClosedFormWordCount := by
  obtain ⟨c₁, cb, A₁, hc₁, hcb, hA₁, hS⟩ := hS
  obtain ⟨c', hc', n₁, h⟩ := third_bound_of_estimates c₁ A₁ hc₁ hA₁
  refine ⟨c', cb, hc', hcb, fun Cres A Cb hA => ?_⟩
  obtain ⟨C₁, h⟩ := h Cb
  obtain ⟨n₀, C₀, hS⟩ := hS Cres A Cb hA
  refine ⟨max n₀ n₁, max C₀ C₁, fun C hC D => ?_⟩
  exact h D Cres _ A C cb (le_max_right _ _) (le_trans (le_max_right _ _) hC)
    (hS _ (le_max_left _ _) C (le_trans (le_max_left _ _) hC) D)

def cartanDistance {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) : ℝ :=
  sInf {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
    umat g = k * NormedSpace.exp X ∧ t = Real.sqrt (Formalism.REAL.hs X)}

namespace CData

variable (X : CData)

def dist (x : X.I.GA) (γ : X.I.GFset) (v : InfinitePlace X.I.F) : ℝ :=
  cartanDistance (X.I.ε v) ((x⁻¹ * (γ : X.I.GA) * x).1 v)

open Classical in

def nearS (εN : ℝ) (x : X.I.GA) : ℝ≥0∞ :=
  ∑' γ : X.I.GFset, if γ ≠ X.one' ∧ ∀ v, X.dist x γ v ≤ εN then ‖X.φ (x⁻¹ * (γ : X.I.GA) * x)‖ₑ else 0

open Classical in

def farS (εN : ℝ) (x : X.I.GA) : ℝ≥0∞ :=
  ∑' γ : X.I.GFset, if γ ≠ X.one' ∧ ¬ ∀ v, X.dist x γ v ≤ εN then ‖X.φ (x⁻¹ * (γ : X.I.GA) * x)‖ₑ else 0

def NearStep (εN c₁ A₂ : ℝ) (Mod : Set X.I.GA) : Prop :=
  ∫⁻ x in Mod, X.nearS εN x ∂X.μ ≤
    ENNReal.ofReal (A₂ * Real.exp (-(c₁ * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) * X.Ds)

def FarPoint (εN δ : ℝ) (Mod : Set X.I.GA) : Prop :=
  ∀ x ∈ Mod, X.farS εN x ≤ ENNReal.ofReal (fdegAll X.I X.σ X.w * (X.e 1).re * δ)

open Classical in
theorem enorm_kerR_le (εN : ℝ) (x : X.I.GA) : ‖X.kerR x‖ₑ ≤ X.nearS εN x + X.farS εN x := by
  unfold kerR nearS farS
  refine le_trans enorm_tsum_le_tsum_enorm ?_
  rw [← ENNReal.tsum_add]
  refine le_of_eq (tsum_congr fun γ => ?_)
  by_cases h1 : γ = X.one' <;> by_cases h2 : (∀ v, X.dist x γ v ≤ εN) <;> simp [h1, h2]

theorem moderate_of_near_far {εN c₁ A₂ δ : ℝ} {Mod : Set X.I.GA} (hM : MeasurableSet Mod) (hV : X.FinVol)
    (hp : X.I.IsPosType X.e) (hA₂ : 0 ≤ A₂) (h0δ : 0 ≤ δ)
    (hδ : δ ≤ Real.exp (-(c₁ * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))))
    (hN : X.NearStep εN c₁ A₂ Mod) (hF : X.FarPoint εN δ Mod) : X.ModerateSum c₁ (A₂ + 1) Mod := by
  have : IsFiniteMeasure X.μ := ⟨by
    unfold μ
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hV⟩
  set Ex := Real.exp (-(c₁ * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) with hEx
  set k0 : ℝ := fdegAll X.I X.σ X.w * (X.e 1).re with hk0
  have hk0n : 0 ≤ k0 := mul_nonneg X.fdegAll_nonneg (X.e_one_nonneg hp)
  have hDs : X.Ds = k0 * X.μ.real Set.univ := by
    unfold Ds AutInst.Dstar
    rw [X.vol_eq, hk0]
    ring
  have hDsn := X.Ds_nonneg hp
  have hle : X.μ.real Mod ≤ X.μ.real Set.univ := measureReal_mono (Set.subset_univ _)
  have h0 : 0 ≤ X.μ.real Mod := measureReal_nonneg
  have hExp : 0 < Ex := Real.exp_pos _
  unfold ModerateSum
  rw [← Real.norm_eq_abs]
  refine le_trans (norm_integral_le_lintegral_norm _) ?_
  have hb : ∫⁻ x in Mod, ENNReal.ofReal ‖(X.kerR x).re‖ ∂X.μ ≤
      ENNReal.ofReal (A₂ * Ex * X.Ds + k0 * δ * X.μ.real Mod) := by
    calc ∫⁻ x in Mod, ENNReal.ofReal ‖(X.kerR x).re‖ ∂X.μ
        ≤ ∫⁻ x in Mod, (X.nearS εN x + ENNReal.ofReal (k0 * δ)) ∂X.μ := by
          refine setLIntegral_mono' hM fun x hx => ?_
          have h1 : ENNReal.ofReal ‖(X.kerR x).re‖ ≤ ‖X.kerR x‖ₑ := by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)
          exact le_trans h1 (le_trans (X.enorm_kerR_le εN x) (by gcongr; exact hF x hx))
      _ = ∫⁻ x in Mod, X.nearS εN x ∂X.μ + ENNReal.ofReal (k0 * δ) * X.μ Mod := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ENNReal.ofReal (A₂ * Ex * X.Ds) + ENNReal.ofReal (k0 * δ * X.μ.real Mod) := by
          gcongr
          · exact hN
          · rw [ENNReal.ofReal_mul (show 0 ≤ k0 * δ by positivity) (q := X.μ.real Mod), Measure.real,
              ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ = ENNReal.ofReal (A₂ * Ex * X.Ds + k0 * δ * X.μ.real Mod) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb) ?_
  rw [ENNReal.toReal_ofReal (by positivity)]
  have h3 : k0 * δ * X.μ.real Mod ≤ Ex * X.Ds := by
    rw [hDs]
    calc k0 * δ * X.μ.real Mod = δ * (k0 * X.μ.real Mod) := by ring
      _ ≤ Ex * (k0 * X.μ.real Set.univ) := by gcongr
  linarith

end CData

theorem cartan_distance_nonneg {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) : 0 ≤ cartanDistance ε g := by
  apply Real.sInf_nonneg
  rintro t ⟨k, Y, -, -, -, rfl⟩
  exact Real.sqrt_nonneg _

theorem hilbert_schmidt_nonneg {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs Y := by
  unfold Formalism.REAL.hs
  positivity

theorem decay_bound_notation_eq {n : ℕ} (q : ℕ) (h : ℝ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    decBound q h Y = Real.exp (-(Formalism.HermitianLatticeCounting.S7.decExp h q (Real.sqrt (Formalism.REAL.hs Y)))) := by
  unfold decBound Formalism.HermitianLatticeCounting.S7.decExp
  rw [Real.sq_sqrt (hilbert_schmidt_nonneg Y)]
  congr 1
  ring

theorem decay_exponent_monotone {h : ℝ} (hh : 0 ≤ h) (q : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Formalism.HermitianLatticeCounting.S7.decExp h q s ≤ Formalism.HermitianLatticeCounting.S7.decExp h q t := by
  unfold Formalism.HermitianLatticeCounting.S7.decExp
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply min_le_min
  · exact pow_le_pow_left₀ hs hst 2
  · exact div_le_div_of_nonneg_right hst (Real.sqrt_nonneg _)

theorem coefficient_le_decay_bound (D : Formalism.BasicNotions.D7) (hdec : DiscreteSeriesDecayBound D) {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ}
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hDS : IsDS ε lam σ) {E : H →L[ℂ] H}
    (hE : IsOrthProjOnto E (lowKSub ε lam σ)) {w : H} (hw : IsLowUnit ε lam σ w) {h : ℝ}
    (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h)
    (hthr : 120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) (g : Formalism.REAL.UJ ε) :
    ‖coefOn σ w w g‖ ≤ Real.exp (-(Formalism.HermitianLatticeCounting.S7.decExp h (min (pOf ε) (qOf ε)) (cartanDistance ε g))) := by
  have hh : 0 ≤ h := le_trans (by positivity) hthr
  by_cases hne : {t | ∃ k Y : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε Y ∧
      umat g = k * NormedSpace.exp Y ∧ t = Real.sqrt (Formalism.REAL.hs Y)}.Nonempty
  · obtain ⟨t, k, Y, hk, hY, hg, rfl⟩ := hne
    have hEw : E w = w := by
      have hwr : w ∈ LinearMap.range (E : H →ₗ[ℂ] H) := by rw [hE.2.2]; exact hw.2
      obtain ⟨u, hu⟩ := hwr
      have hu' : E u = w := hu
      rw [← hu']
      exact congrArg (fun T : H →L[ℂ] H => T u) hE.1
    have h1 : coefOn σ w w g = ⟪w, (E.comp ((σ (k * NormedSpace.exp Y)).comp E)) w⟫_ℂ := by
      unfold coefOn
      rw [hg]
      simp only [ContinuousLinearMap.comp_apply]
      rw [← hE.2.1, hEw]
    have h2 : ‖coefOn σ w w g‖ ≤ decBound (min (pOf ε) (qOf ε)) h Y := by
      rw [h1]
      refine le_trans (norm_inner_le_norm _ _) ?_
      refine le_trans (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)) ?_
      rw [hw.1, one_mul, mul_one]
      exact hdec n ε lam hlam H σ hDS E hE h hgap hthr k Y hk hY
    rw [decay_bound_notation_eq] at h2
    refine le_trans h2 (Real.exp_le_exp.2 (neg_le_neg ?_))
    refine decay_exponent_monotone hh _ (cartan_distance_nonneg ε g) ?_
    refine csInf_le ⟨0, ?_⟩ ⟨k, Y, hk, hY, hg, rfl⟩
    rintro t ⟨_, Y', -, -, -, rfl⟩
    exact Real.sqrt_nonneg _
  · have h0 : cartanDistance ε g = 0 := by
      unfold cartanDistance
      rw [Set.not_nonempty_iff_eq_empty.1 hne, Real.sInf_empty]
    have h1 : Formalism.HermitianLatticeCounting.S7.decExp h (min (pOf ε) (qOf ε)) 0 = 0 := by
      unfold Formalism.HermitianLatticeCounting.S7.decExp
      simp
    rw [h0, h1, neg_zero, Real.exp_zero]
    unfold coefOn
    refine le_trans (norm_inner_le_norm _ _) ?_
    rw [hDS.2.2.1.2.1 _ g.2 w, hw.1, one_mul]

theorem positive_type_notation_eq (I : AutInst) {e : I.Gf → ℂ} (hp : I.IsPosType e) : Formalism.HermitianLatticeCounting.S7.IsPosType e := by
  intro s c
  have h := hp s.card (fun i => ((s.equivFin.symm i : s) : I.Gf)) (fun i => c ((s.equivFin.symm i : s) : I.Gf))
  have e1 : ∀ F : I.Gf → ℂ, ∑ i : Fin s.card, F ((s.equivFin.symm i : s) : I.Gf) = ∑ x ∈ s, F x := by
    intro F
    rw [Equiv.sum_comp s.equivFin.symm (fun x : s => F (x : I.Gf))]
    exact Finset.sum_coe_sort s F
  rw [e1 (fun x => ∑ j : Fin s.card, star (c x) * c ((s.equivFin.symm j : s) : I.Gf) *
    e (x⁻¹ * ((s.equivFin.symm j : s) : I.Gf)))] at h
  refine le_of_le_of_eq h (Finset.sum_congr rfl fun x _ => ?_)
  exact e1 (fun y => star (c x) * c y * e (x⁻¹ * y))

namespace CData

variable (X : CData)

def LowProj : Prop :=
  ∀ v, ∃ E : X.H v →L[ℂ] X.H v, IsOrthProjOnto E (lowKSub (X.I.ε v) (X.lam v) (X.σ v))

theorem norm_φ_le (D : Formalism.BasicNotions.D7) (hdec : DiscreteSeriesDecayBound D) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (h1 : X.GapAboveThreeHalvesPower)
    (hE : X.LowProj) {q₀ : ℕ} (hq : ∀ v, q0At X.I v = q₀) (y : X.I.GA) :
    ‖X.φ y‖ ≤ fdegAll X.I X.σ X.w * (X.e 1).re *
      ∏ v, Real.exp (-(Formalism.HermitianLatticeCounting.S7.decExp X.h q₀ (cartanDistance (X.I.ε v) (y.1 v)))) := by
  have hp : X.I.IsPosType X.e := hX.1.2.2.2.2.2.2.1.2.2.2.1
  have he : ‖X.e y.2‖ ≤ (X.e 1).re := Formalism.HermitianLatticeCounting.Final.S7.posTypeBound X.I.Gf X.e (positive_type_notation_eq X.I hp) y.2
  have hm : ∀ v, ‖coefOn (X.σ v) (X.w v) (X.w v) (y.1 v)‖ ≤
      Real.exp (-(Formalism.HermitianLatticeCounting.S7.decExp X.h q₀ (cartanDistance (X.I.ε v) (y.1 v)))) := by
    intro v
    obtain ⟨E, hEv⟩ := hE v
    have := coefficient_le_decay_bound D hdec (hX.1.2.2.2.2.1 v) (hX.2.1.1 v) hEv (hX.2.1.2.1 v) (hX.2.2 v) (h1 v) (y.1 v)
    rw [← hq v]
    exact this
  unfold φ phe phOf
  rw [norm_mul, norm_mul, norm_star, norm_prod, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg X.fdegAll_nonneg]
  calc fdegAll X.I X.σ X.w * (∏ v, ‖coefOn (X.σ v) (X.w v) (X.w v) (y.1 v)‖) * ‖X.e y.2‖
      ≤ fdegAll X.I X.σ X.w * (∏ v, Real.exp (-(Formalism.HermitianLatticeCounting.S7.decExp X.h q₀ (cartanDistance (X.I.ε v) (y.1 v))))) *
          (X.e 1).re := by
        have := X.fdegAll_nonneg
        gcongr with v _
        exact hm v
    _ = fdegAll X.I X.σ X.w * (X.e 1).re *
        ∏ v, Real.exp (-(Formalism.HermitianLatticeCounting.S7.decExp X.h q₀ (cartanDistance (X.I.ε v) (y.1 v)))) := by ring

end CData

namespace CData

variable (X : CData)

def FarCount (Ac B : ℝ) (Mod : Set X.I.GA) : Prop :=
  ∀ x ∈ Mod, ∀ r : InfinitePlace X.I.F → ℝ, (∀ v, 0 ≤ r v) → ∀ S : Finset X.I.GFset,
    (∀ γ ∈ S, X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0 ∧ ∀ v, X.dist x γ v ≤ r v) →
    (S.card : ℝ) ≤ Ac * Real.exp (B * ∑ v, r v)

open Classical in

theorem farPoint_of_count (D : Formalism.BasicNotions.D7) (hdec : DiscreteSeriesDecayBound D) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (h1 : X.GapAboveThreeHalvesPower)
    (hE : X.LowProj) {q₀ : ℕ} (hq : ∀ v, q0At X.I v = q₀) (hq1 : 1 ≤ q₀) {Ac B εN : ℝ} {Mod : Set X.I.GA}
    (hAc : 0 ≤ Ac) (hB : 0 ≤ B) (hε : 0 < εN) (hεq : εN * Real.sqrt (2 * (q₀ : ℝ)) ≤ 1) (hBε : B * εN ≤ 1)
    (h32 : 32 * B ≤ X.h * εN) (h16 : 16 ≤ X.h * εN ^ 2) (hcnt : X.FarCount Ac B Mod) :
    X.FarPoint εN (Ac * 4 ^ Fintype.card (InfinitePlace X.I.F) * (2 * Fintype.card (InfinitePlace X.I.F)) *
      Real.exp (-(X.h * εN ^ 2 / 16))) Mod := by
  intro x hx
  have hp : X.I.IsPosType X.e := hX.1.2.2.2.2.2.2.1.2.2.2.1
  set k0 : ℝ := fdegAll X.I X.σ X.w * (X.e 1).re with hk0
  have hk0n : 0 ≤ k0 := mul_nonneg X.fdegAll_nonneg (X.e_one_nonneg hp)
  set bd : X.I.GFset → ℝ := fun γ => ∏ v, Real.exp (-(Formalism.HermitianLatticeCounting.S7.decExp X.h q₀ (X.dist x γ v))) with hbd
  have hbdn : ∀ γ, 0 ≤ bd γ := fun γ => Finset.prod_nonneg fun v _ => (Real.exp_pos _).le
  unfold farS
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  set S := s.filter (fun γ => (γ ≠ X.one' ∧ ¬ ∀ v, X.dist x γ v ≤ εN) ∧ X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0) with hS
  have hterm : ∀ γ ∈ s, (if γ ≠ X.one' ∧ ¬ ∀ v, X.dist x γ v ≤ εN then ‖X.φ (x⁻¹ * (γ : X.I.GA) * x)‖ₑ else 0) ≤
      (if (γ ≠ X.one' ∧ ¬ ∀ v, X.dist x γ v ≤ εN) ∧ X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0 then
        ENNReal.ofReal (k0 * bd γ) else 0) := by
    intro γ _
    by_cases hP : γ ≠ X.one' ∧ ¬ ∀ v, X.dist x γ v ≤ εN
    · by_cases h0 : X.φ (x⁻¹ * (γ : X.I.GA) * x) = 0
      · simp [h0]
      · rw [if_pos hP, if_pos ⟨hP, h0⟩, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (X.norm_φ_le D hdec hX h1 hE hq _)
    · rw [if_neg hP]
      exact zero_le
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_filter, ← ENNReal.ofReal_sum_of_nonneg (fun γ _ => mul_nonneg hk0n (hbdn γ)), ← Finset.mul_sum]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hk0n)
  refine Formalism.HermitianLatticeCounting.Final.S7.farSum (InfinitePlace X.I.F) X.I.GFset S (X.dist x) Ac B X.h εN q₀ hq1 hAc hB hε hεq hBε
    h32 h16 (fun γ _ v => cartan_distance_nonneg _ _) (fun γ hγ => ?_) (fun r hr => ?_)
  · have h2 := (Finset.mem_filter.1 hγ).2.1.2
    obtain ⟨v, hv⟩ := not_forall.1 h2
    exact ⟨v, not_le.1 hv⟩
  · refine hcnt x hx r hr _ fun γ hγ => ?_
    have h3 := Finset.mem_filter.1 hγ
    exact ⟨(Finset.mem_filter.1 h3.1).2.2, h3.2⟩

end CData

section Numbers

open Formalism.HermitianLatticeCounting.S7 (Ydat epsN)

theorem two_mul_le_height_parameter {n f : ℕ} {rd g b : ℝ} (hn : 1 ≤ n) (hf : 1 ≤ f) (hrd : 1 ≤ rd) (hg : 1 ≤ g) (hb : 2 ≤ b) :
    2 * (n : ℝ) ≤ Ydat n f rd g b := by
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  unfold Ydat
  calc 2 * (n : ℝ) = (n : ℝ) * 1 * 1 * 1 * 2 := by ring
    _ ≤ (n : ℝ) * f * rd * g * b := by gcongr

theorem epsilon_small_bounds {cε : ℝ} (hcε : 0 < cε) (hcε2 : cε ≤ 1 / 2) {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) :
    0 < epsN cε n f ∧ 2 * (n : ℝ) ^ 2 * epsN cε n f ≤ 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le one_pos hnR
  have hf0 : (0 : ℝ) < f := lt_of_lt_of_le one_pos hfR
  unfold epsN
  refine ⟨by positivity, ?_⟩
  rw [mul_div_assoc', div_le_one (by positivity)]
  calc 2 * (n : ℝ) ^ 2 * cε ≤ 2 * (n : ℝ) ^ 2 * (1 / 2) := by gcongr
    _ = (n : ℝ) ^ 2 * 1 := by ring
    _ ≤ (n : ℝ) ^ 8 * (f : ℝ) ^ 2 := by
        exact mul_le_mul (pow_le_pow_right₀ hnR (by norm_num)) (one_le_pow₀ hfR) zero_le_one (by positivity)

theorem far_region_inequalities {ε h N : ℝ} (hε : 0 < ε) (h1 : 2 * N * ε ≤ 1) (hN : 1 ≤ N) (hb : 64 * N ≤ h * ε ^ 2) :
    32 * (2 * N) ≤ h * ε ∧ 16 ≤ h * ε ^ 2 := by
  have hε1 : ε ≤ 1 := by nlinarith
  have hh : 0 ≤ h := by
    by_contra hneg
    have : h * ε ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hneg) (by positivity)
    linarith
  have h2 : ε ^ 2 ≤ ε := by nlinarith
  have h3 : h * ε ^ 2 ≤ h * ε := mul_le_mul_of_nonneg_left h2 hh
  constructor <;> linarith

theorem sqrt_two_mul_le_two_sq {n q : ℕ} (hn : 1 ≤ n) (hq2 : q ^ 2 ≤ n) : Real.sqrt (2 * (q : ℝ)) ≤ 2 * (n : ℝ) ^ 2 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : (q : ℝ) ≤ n := by
    have : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hq2
    exact_mod_cast this
  have h2 : (n : ℝ) ≤ (n : ℝ) ^ 4 := by
    calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ hnR (by norm_num)
  calc 2 * (q : ℝ) ≤ 2 * (n : ℝ) ^ 4 := by linarith
    _ ≤ (2 * (n : ℝ) ^ 2) ^ 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
        nlinarith

theorem pow_neg_pos_and_mul_le_one {n q : ℕ} {Y C₁ : ℝ} (hq : 1 ≤ q) (hC₁ : 1 ≤ C₁) (hn : 1 ≤ n) (hY : 2 * (n : ℝ) ≤ Y) :
    0 < Y ^ (-(C₁ * q)) ∧ (n : ℝ) * Y ^ (-(C₁ * q)) ≤ 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hYpos : 0 < Y := by linarith
  refine ⟨Real.rpow_pos_of_pos hYpos _, ?_⟩
  have h0 : (1 : ℝ) ≤ C₁ * q := by nlinarith
  have h1 : Y ^ (-(C₁ * q)) ≤ Y ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  rw [Real.rpow_neg_one] at h1
  calc (n : ℝ) * Y ^ (-(C₁ * q)) ≤ (n : ℝ) * Y⁻¹ := by gcongr
    _ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hYpos]
        linarith

theorem sixty_four_sq_le_of_threshold {n q f : ℕ} {K L x : ℝ} (hn : 1 ≤ n) (hq : 1 ≤ q) (hf : 1 ≤ f) (hK : 128 ≤ K) (hL : 1 / 2 ≤ L)
    (hx : K * (n : ℝ) ^ 2 * q * f * L ≤ x) : 64 * (n : ℝ) ^ 2 ≤ x := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  refine le_trans ?_ hx
  calc 64 * (n : ℝ) ^ 2 = 128 * (n : ℝ) ^ 2 * 1 * 1 * (1 / 2) := by ring
    _ ≤ K * (n : ℝ) ^ 2 * q * f * L := by gcongr

theorem far_region_numerics (cε C₁ c₁ A : ℝ) (hcε : 0 < cε) (hcε2 : cε ≤ 1 / 2) (hC₁ : 1 ≤ C₁) (hc₁ : 0 < c₁) (hA : 1 ≤ A) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (n q f np : ℕ) (rd g b h : ℝ), 1 ≤ n → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ f → np ≤ f →
      Real.log f ≤ Real.sqrt n → 2 ≤ b → 1 ≤ rd → 1 ≤ g → g ≤ b ^ A →
      C₀ * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * Real.log (b * rd) ≤ h →
      0 < epsN cε n f ∧ epsN cε n f * Real.sqrt (2 * (q : ℝ)) ≤ 1 ∧ 2 * (n : ℝ) ^ 2 * epsN cε n f ≤ 1 ∧
        32 * (2 * (n : ℝ) ^ 2) ≤ h * epsN cε n f ∧ 16 ≤ h * epsN cε n f ^ 2 ∧
        (3 * Real.sqrt n / (Ydat n f rd g b ^ (-(C₁ * q))) ^ 2) ^ (2 * n ^ 2 * f) * 4 ^ np * (2 * np) *
            Real.exp (-(h * epsN cε n f ^ 2 / 16)) ≤
          Real.exp (-(c₁ * n * f * Real.log n)) := by
  obtain ⟨C', hC', hneg⟩ := Formalism.HermitianLatticeCounting.Final.S7.farNegligible 3 C₁ c₁ 5 (by norm_num) hC₁ hc₁
  obtain ⟨C₀, hC₀, hthr⟩ := Formalism.HermitianLatticeCounting.Final.S7.threshFar (max C' 128) cε A (lt_of_lt_of_le hC' (le_max_left _ _)) hcε hA
  refine ⟨C₀, hC₀, fun n q f np rd g b h hn hq hq2 hf hnp hlf hb hrd hg hgb hh => ?_⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx := hthr n q f rd g b h hn hf hq2 hlf hb hrd hg hgb hh
  obtain ⟨hεpos, hε2n⟩ := epsilon_small_bounds hcε hcε2 hn hf
  have hYn := two_mul_le_height_parameter (rd := rd) (g := g) (b := b) hn hf hrd hg hb
  have hlogY : 1 / 2 ≤ Real.log (Ydat n f rd g b) := by
    have h1 : Real.log 2 ≤ Real.log (Ydat n f rd g b) := Real.log_le_log (by norm_num) (by linarith)
    have h2 := Real.log_two_gt_d9
    linarith
  have hbig := sixty_four_sq_le_of_threshold hn hq hf (le_max_right C' 128) hlogY hx
  obtain ⟨h32, h16⟩ := far_region_inequalities hεpos hε2n (one_le_pow₀ hnR) hbig
  refine ⟨hεpos, ?_, hε2n, h32, h16, ?_⟩
  · calc epsN cε n f * Real.sqrt (2 * (q : ℝ)) ≤ epsN cε n f * (2 * (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (sqrt_two_mul_le_two_sq hn hq2) hεpos.le
      _ = 2 * (n : ℝ) ^ 2 * epsN cε n f := by ring
      _ ≤ 1 := hε2n
  · obtain ⟨hτpos, hnτ⟩ := pow_neg_pos_and_mul_le_one hq hC₁ hn hYn
    have hpre := Formalism.HermitianLatticeCounting.Final.S7.farPrefactor n f _ hn hf hτpos hnτ
    have hx' : C' * (n : ℝ) ^ 2 * q * f * Real.log (Ydat n f rd g b) ≤ h * epsN cε n f ^ 2 := by
      refine le_trans ?_ hx
      have hl : 0 ≤ Real.log (Ydat n f rd g b) := by linarith
      gcongr
      exact le_max_left _ _
    have hfin := hneg n q f rd g b (h * epsN cε n f ^ 2) hn hq hf hrd hg hb hx'
    have hnpR : (np : ℝ) ≤ f := by exact_mod_cast hnp
    have h4 : (4 : ℝ) ^ np ≤ 4 ^ f := pow_le_pow_right₀ (by norm_num) hnp
    refine le_trans ?_ hfin
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have hA0 : 0 ≤ (3 * Real.sqrt n / (Ydat n f rd g b ^ (-(C₁ * q))) ^ 2) ^ (2 * n ^ 2 * f) := by positivity
    calc (3 * Real.sqrt n / (Ydat n f rd g b ^ (-(C₁ * q))) ^ 2) ^ (2 * n ^ 2 * f) * 4 ^ np * (2 * np)
        ≤ (3 * Real.sqrt n / (Ydat n f rd g b ^ (-(C₁ * q))) ^ 2) ^ (2 * n ^ 2 * f) * 4 ^ f * (2 * f) := by
          gcongr
      _ ≤ (3 / Ydat n f rd g b ^ (-(C₁ * q))) ^ (5 * n ^ 2 * f) * (2 * f) :=
          mul_le_mul_of_nonneg_right hpre (by positivity)

end Numbers

theorem cartan_distance_eq_zero_of_definite {n : ℕ} {ε : Fin n → Bool} (h0 : min (pOf ε) (qOf ε) = 0) (g : Formalism.REAL.UJ ε) : cartanDistance ε g = 0 := by
  have hsame : ∃ s : ℂ, s ≠ 0 ∧ ∀ a, (if ε a then (1 : ℂ) else -1) = s := by
    rcases Nat.min_eq_zero_iff.1 h0 with h | h
    · refine ⟨-1, by norm_num, fun a => ?_⟩
      have : a ∉ univ.filter fun a => ε a = true := by
        rw [Finset.card_eq_zero.1 h]; exact Finset.notMem_empty a
      have h2 : ε a ≠ true := fun hh => this (Finset.mem_filter.2 ⟨Finset.mem_univ a, hh⟩)
      simp [h2]
    · refine ⟨1, one_ne_zero, fun a => ?_⟩
      have : a ∉ univ.filter fun a => ε a = false := by
        rw [Finset.card_eq_zero.1 h]; exact Finset.notMem_empty a
      have h2 : ε a ≠ false := fun hh => this (Finset.mem_filter.2 ⟨Finset.mem_univ a, hh⟩)
      simp [h2]
  obtain ⟨s, hs, hall⟩ := hsame
  have hJ : Formalism.REAL.Jm ε = Matrix.diagonal fun _ => s := by
    unfold Formalism.REAL.Jm
    congr 1
    funext a
    exact hall a
  have hY0 : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inP ε Y → Y = 0 := by
    intro Y hY
    have h1 := hY.2
    rw [hJ] at h1
    ext i j
    have h2 := congrFun (congrFun h1 i) j
    rw [Matrix.mul_diagonal, Matrix.neg_apply, Matrix.diagonal_mul] at h2
    have h3 : (2 * s) * Y i j = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd h4 (mul_ne_zero two_ne_zero hs)
    · simpa using h4
  apply le_antisymm _ (cartan_distance_nonneg ε g)
  unfold cartanDistance
  by_cases hne : {t | ∃ k Y : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε Y ∧
      umat g = k * NormedSpace.exp Y ∧ t = Real.sqrt (Formalism.REAL.hs Y)}.Nonempty
  · obtain ⟨t, k, Y, hk, hY, hg, rfl⟩ := hne
    refine le_trans (csInf_le ⟨0, ?_⟩ ⟨k, Y, hk, hY, hg, rfl⟩) ?_
    · rintro t ⟨_, Y', -, -, -, rfl⟩
      exact Real.sqrt_nonneg _
    · rw [hY0 Y hY]
      simp [Formalism.REAL.hs]
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, Real.sInf_empty]

theorem card_infinite_places_le_degree (I : AutInst) : Fintype.card (InfinitePlace I.F) ≤ I.f := by
  have h1 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces I.F
  have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.F
  unfold AutInst.f
  omega

namespace CData

variable (X : CData)

def qq : ℕ := Finset.univ.sup fun v => q0At X.I v

def Acnt (C₁ : ℝ) : ℝ :=
  (3 * Real.sqrt (X.I.n : ℝ) /
    (Formalism.HermitianLatticeCounting.S7.Ydat X.I.n X.I.f X.I.rd (X.g : ℝ) X.b ^ (-(C₁ * (X.qq : ℝ)))) ^ 2) ^ (2 * X.I.n ^ 2 * X.I.f)

theorem qq_spec {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) : (∀ v, q0At X.I v = X.qq) ∧ X.qq ^ 2 ≤ X.I.n := by
  obtain ⟨p, q, hpq, hq⟩ := hX.1.2.1
  have h1 : ∀ v, q0At X.I v = min p q := fun v => by
    unfold q0At; rw [(hpq v).1, (hpq v).2]
  have h2 : X.qq = min p q := by
    unfold qq
    rw [show (fun v => q0At X.I v) = fun _ => min p q from funext h1]
    exact Finset.sup_const Finset.univ_nonempty _
  refine ⟨fun v => by rw [h1 v, h2], ?_⟩
  rw [h2]
  exact le_trans (Nat.pow_le_pow_left (min_le_right _ _) 2) hq

end CData

def StepsC' (n₀ : ℕ) (A C cb c₁ A₂ cε C₁ : ℝ) : Prop :=
  ∀ X : CData, X.HypC n₀ A C cb → X.OpExists ∧ X.KernelDiag ∧ X.FinVol ∧ X.LowProj ∧
    ∃ Mod : Set X.I.GA, MeasurableSet Mod ∧ X.ProbMod c₁ Mod ∧
      X.NearStep (Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f) c₁ A₂ Mod ∧
      X.FarCount (X.Acnt C₁) (2 * (X.I.n : ℝ) ^ 2) Mod ∧ X.DeepInt (A₂ + 1) Mod

open Classical in

theorem StepsC_of_refined (cε C₁ c₁ A A₂ : ℝ) (hcε : 0 < cε) (hcε2 : cε ≤ 1 / 2) (hC₁ : 1 ≤ C₁) (hc₁ : 0 < c₁)
    (hA : 1 ≤ A) (hA₂ : 0 ≤ A₂) :
    ∃ C₀ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (C cb : ℝ), 1 ≤ n₀ → C₀ ≤ C → DiscreteSeriesDecayBound D →
      StepsC' n₀ A C cb c₁ A₂ cε C₁ → StepsC n₀ A C cb c₁ (A₂ + 1) := by
  obtain ⟨Cf, -, hnum⟩ := far_region_numerics cε C₁ c₁ A hcε hcε2 hC₁ hc₁ hA
  obtain ⟨Ch, -, hH⟩ := Formalism.HermitianLatticeCounting.Final.S7.threshHead 0
  refine ⟨max Cf Ch, fun D n₀ C cb hn₀ hC hdec hS X hX => ?_⟩
  obtain ⟨s1, s2, s3, s4, Mod, hM, hpr, hnear, hcnt, hdeep⟩ := hS X hX
  refine ⟨s1, s2, s3, Mod, hM, hpr, ?_, hdeep⟩
  have hthr := (gap_thresholds_of_height_bound hH X hn₀ (le_trans (le_max_right _ _) hC) hX).1
  have hp : X.I.IsPosType X.e := hX.1.1.2.2.2.2.2.2.1.2.2.2.1
  obtain ⟨hq, hq2⟩ := X.qq_spec hX.1
  have hn1 : 1 ≤ X.I.n := le_trans hn₀ hX.1.1.1
  by_cases hq0 : X.qq = 0
  ·
    refine X.moderate_of_near_far hM s3 hp hA₂ le_rfl (Real.exp_pos _).le hnear fun x _ => ?_
    have hε := (epsilon_small_bounds hcε hcε2 hn1 (one_le_autInst_f X.I)).1
    have : X.farS (Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f) x = 0 := by
      unfold CData.farS
      refine ENNReal.tsum_eq_zero.2 fun γ => if_neg fun hh => hh.2 fun v => ?_
      unfold CData.dist
      rw [cartan_distance_eq_zero_of_definite (by have := hq v; unfold q0At AutInst.pAt AutInst.qAt at this; rw [hq0] at this; exact this)]
      exact hε.le
    rw [this]
    exact zero_le
  · have hq1 : 1 ≤ X.qq := Nat.one_le_iff_ne_zero.2 hq0
    have hrd := one_le_discriminant_root X.I
    have hb : 2 ≤ X.b := hX.1.1.2.2.1
    have hlog : 0 ≤ Real.log (X.b * X.I.rd) := Real.log_nonneg (by nlinarith)
    have hle : Cf * (X.I.n : ℝ) ^ 19 * (X.I.f : ℝ) ^ 5 * Real.log (X.b * X.I.rd) ≤ X.h := by
      refine le_trans ?_ hX.2.1
      gcongr
      exact le_trans (le_max_left _ _) hC
    have hg1 : (1 : ℝ) ≤ (X.g : ℝ) := by exact_mod_cast hX.1.1.2.2.2.2.2.2.2.1
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hnum X.I.n X.qq X.I.f (Fintype.card (InfinitePlace X.I.F)) X.I.rd X.g X.b X.h hn1
      hq1 hq2 (one_le_autInst_f X.I) (card_infinite_places_le_degree X.I) hX.2.2.1 hb hrd hg1 hX.1.1.2.2.2.2.2.2.2.2.1 hle
    have hAc : 0 ≤ X.Acnt C₁ := by unfold CData.Acnt; positivity
    have hfar := X.farPoint_of_count D hdec hX.1 hthr s4 hq hq1 hAc (by positivity) n1 n2 n3 n4 n5 hcnt
    exact X.moderate_of_near_far hM s3 hp hA₂ (by positivity) n6 hnear hfar

theorem third_bound_of_refined_estimates (cε C₁ c₁ A A₂ : ℝ) (hcε : 0 < cε) (hcε2 : cε ≤ 1 / 2) (hC₁ : 1 ≤ C₁) (hc₁ : 0 < c₁)
    (hA : 1 ≤ A) (hA₂ : 0 ≤ A₂) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ n₁ : ℕ, ∀ Cb : ℝ, ∃ C₂ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (Cres : ℝ) (n₀ : ℕ) (C cb : ℝ),
      n₁ ≤ n₀ → C₂ ≤ C →
      ((ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D Cres ∧ adm8 D) → DiscreteSeriesDecayBound D → Conclusion2 D n₀ A Cb →
        StepsC' n₀ A C cb c₁ A₂ cε C₁) →
      TowerRallisLemma D Cres n₀ A Cb C c' cb := by
  obtain ⟨c', hc', n₁, h⟩ := third_bound_of_estimates c₁ (A₂ + 1) hc₁ (by linarith)
  obtain ⟨C₀, hR⟩ := StepsC_of_refined cε C₁ c₁ A A₂ hcε hcε2 hC₁ hc₁ hA hA₂
  refine ⟨c', hc', max n₁ 1, fun Cb => ?_⟩
  obtain ⟨C₁', h⟩ := h Cb
  refine ⟨max C₁' C₀, fun D Cres n₀ C cb hn hC hS => ?_⟩
  exact h D Cres n₀ A C cb (le_trans (le_max_left _ _) hn) (le_trans (le_max_left _ _) hC)
    fun hadm hdec hb => hR D n₀ C cb (le_trans (le_max_right _ _) hn) (le_trans (le_max_right _ _) hC) hdec
      (hS hadm hdec hb)

theorem lowest_K_type_projector_exists (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) :
    X.LowProj := by
  intro v
  have hfd : FiniteDimensional ℂ (lowKSub (X.I.ε v) (X.lam v) (X.σ v)) :=
    (h2 X.I.n (X.I.ε v) (X.lam v) (hX.1.2.2.2.2.1 v) (X.H v) (X.σ v) (hX.2.1.1 v)).1.1
  refine ⟨(lowKSub (X.I.ε v) (X.lam v) (X.σ v)).starProjection, ?_, ?_, ?_⟩
  · exact (lowKSub (X.I.ε v) (X.lam v) (X.σ v)).isIdempotentElem_starProjection
  · intro x y
    exact Submodule.inner_starProjection_left_eq_right _ x y
  · exact Submodule.range_starProjection _

theorem φ_integrable (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    (hph : Integrable (phOf X.I X.σ X.w) (Measure.pi fun v => Formalism.REAL.muG (X.I.ε v))) :
    Integrable X.φ (X.I.muA X.μf) := by
  have he : Integrable X.e X.μf := hX.2.1.2.2.2.2.2.2.1
  exact hph.mul_prod he

def StepsU3' : Prop :=
  ∃ c₁ cb A₂ cε : ℝ, 0 < c₁ ∧ 0 < cb ∧ 0 ≤ A₂ ∧ 0 < cε ∧ cε ≤ 1 / 2 ∧ ∀ Cres A Cb : ℝ, 1 ≤ A →
    ∃ (C₁ : ℝ) (n₀ : ℕ) (C₀ : ℝ), 1 ≤ C₁ ∧ ∀ n₀' ≥ n₀, ∀ C ≥ C₀, ∀ D : Formalism.BasicNotions.D7,
      (ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D Cres ∧ adm8 D) → DiscreteSeriesDecayBound D → Conclusion2 D n₀' A Cb →
        StepsC' n₀' A C cb c₁ A₂ cε C₁

theorem closed_third_part_of_refined (hS : StepsU3') : ClosedFormWordCount := by
  obtain ⟨c₁, cb, A₂, cε, hc₁, hcb, hA₂, hcε, hcε2, hS⟩ := hS
  refine closed_third_part_of_estimates ⟨c₁, cb, A₂ + 1, hc₁, hcb, by linarith, fun Cres A Cb hA => ?_⟩
  obtain ⟨C₁, n₀, C₀, hC₁, hS⟩ := hS Cres A Cb hA
  obtain ⟨C₂, hR⟩ := StepsC_of_refined cε C₁ c₁ A A₂ hcε hcε2 hC₁ hc₁ hA hA₂
  refine ⟨max n₀ 1, max C₀ C₂, fun n₀' hn C hC D hadm hdec hb => ?_⟩
  exact hR D n₀' C cb (le_trans (le_max_right _ _) hn) (le_trans (le_max_right _ _) hC) hdec
    (hS n₀' (le_trans (le_max_left _ _) hn) C (le_trans (le_max_left _ _) hC) D hadm hdec hb)

theorem third_part_of_refined_estimates (cε C₁ c₁ A A₂ : ℝ) (hcε : 0 < cε) (hcε2 : cε ≤ 1 / 2) (hC₁ : 1 ≤ C₁) (hc₁ : 0 < c₁)
    (hA : 1 ≤ A) (hA₂ : 0 ≤ A₂) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ n₁ : ℕ, ∀ Cb : ℝ, ∃ C₂ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (C cb : ℝ),
      n₁ ≤ n₀ → C₂ ≤ C → DiscreteSeriesDecayBound D → Conclusion2 D n₀ A Cb → StepsC' n₀ A C cb c₁ A₂ cε C₁ → PointsLemma D n₀ A C c' cb := by
  obtain ⟨c', hc', n₁, h⟩ := third_part_of_estimates c₁ (A₂ + 1) hc₁ (by linarith)
  obtain ⟨C₀, hR⟩ := StepsC_of_refined cε C₁ c₁ A A₂ hcε hcε2 hC₁ hc₁ hA hA₂
  refine ⟨c', hc', max n₁ 1, fun Cb => ?_⟩
  obtain ⟨C₁', h⟩ := h Cb
  refine ⟨max C₁' C₀, fun D n₀ C cb hn hC hdec hb hS => ?_⟩
  exact h D n₀ A C cb (le_trans (le_max_left _ _) hn) (le_trans (le_max_left _ _) hC) hb
    (hR D n₀ C cb (le_trans (le_max_right _ _) hn) (le_trans (le_max_right _ _) hC) hdec hS)

theorem full_statement_of_parts (D : Formalism.BasicNotions.D7) (Cres : ℝ) (n₀ : ℕ) (A Cb C c cb : ℝ) (i0 : HarishChandraFormulaStatement D) (i1 : IntegralityFromMetric D)
    (i2 : IntegrabilityFromDecay D) (i3 : AbstractGroupProjectorForDatum D) (i4 : LocalProjectorFromSchur D) (i5 : HodgeTateFromSandwich D n₀ A Cb)
    (i6 : TowerRallisLemma D Cres n₀ A Cb C c cb) : Stmt D Cres n₀ A Cb C c cb := by
  rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
  have p0 := i0 ⟨a2, a3⟩
  have p1 := i1 p0
  have p2 := i2 p1
  have p4 := i4 a1 p2 i3
  have p5 := i5 ⟨a1, a6, a8⟩ p1 p4
  exact ⟨p0, p1, p2, i3, p4, p5, i6 ⟨a4, a5, a6, a7, a8⟩ p1 p5⟩

theorem family_full_statement_of_parts {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cres : ℝ) (n₀ : ℕ) (A Cb C c cb : ℝ)
    (i0 : FamilyFormulaStatement Fm) (i1 : PeriodFamilyStatement Fm) (i2 : FamilyIntegrabilityOfDecay Fm) (i3 : FamilyAbstractProjector Fm) (i4 : FamilyLocalProjectorOfAbstractProjector Fm)
    (i5 : DeterminantValueFamily Fm n₀ A Cb) (i6 : FlatLineDegreeFamilyStatement Fm Cres n₀ A Cb C c cb) : KudlaFamilyStatement Fm Cres n₀ A Cb C c cb := by
  intro hA
  have a1 : admF1 Fm := fun x i => (hA x i).1
  have a2 : admF2 Fm := fun x i => (hA x i).2.1
  have a3 : admF3 Fm := fun x i => (hA x i).2.2.1
  have a4 : admF4 Fm := fun x i => (hA x i).2.2.2.1
  have a5 : admF5 Fm := fun x i => (hA x i).2.2.2.2.1
  have a6 : admF6 Fm := fun x i => (hA x i).2.2.2.2.2.1
  have a7 : admF7 Fm Cres := fun x i => (hA x i).2.2.2.2.2.2.1
  have a8 : admF8 Fm := fun x i => (hA x i).2.2.2.2.2.2.2
  have p0 := i0 ⟨a2, a3⟩
  have p1 := i1 p0
  have p2 := i2 p1
  have p4 := i4 a1 p2 i3
  have p5 := i5 ⟨a1, a6, a8⟩ p1 p4
  exact ⟨p0, p1, p2, i3, p4, p5, i6 ⟨a4, a5, a6, a7, a8⟩ p1 p5⟩

theorem family_second_part_of_local {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (n₀ : ℕ) (A Cb : ℝ)
    (h : ∀ x (i : Fm.Ix x), HodgeTateFromSandwich (Fm.D x i) n₀ A Cb) : DeterminantValueFamily Fm n₀ A Cb :=
  fun ha h1 h2 x i => h x i ⟨ha.1 x i, ha.2.1 x i, ha.2.2 x i⟩ (h1 x i) (h2 x i)

theorem family_third_part_of_local {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cres : ℝ) (n₀ : ℕ) (A Cb C c cb : ℝ) (hc : 0 < c)
    (hcb : 0 < cb) (h : ∀ x (i : Fm.Ix x), TowerRallisLemma (Fm.D x i) Cres n₀ A Cb C c cb) :
    FlatLineDegreeFamilyStatement Fm Cres n₀ A Cb C c cb :=
  fun ha h1 h2 => ⟨hc, hcb, fun x i =>
    h x i ⟨ha.1 x i, ha.2.1 x i, ha.2.2.1 x i, ha.2.2.2.1 x i, ha.2.2.2.2 x i⟩ (h1 x i) (h2 x i)⟩

namespace CData

variable (X : CData)

def RegRep : Prop :=
  (∀ g (F : X.L2), ‖X.R g F‖ = ‖F‖) ∧
    ∀ x y : X.L2, AEStronglyMeasurable (fun g => ⟪x, X.R g y⟫_ℂ) (X.I.muA X.μf)

theorem opExists_of_regRep (hR : X.RegRep) (hφ : Integrable X.φ (X.I.muA X.μf)) : X.OpExists := by
  have hbd : ∀ (x y : X.L2) g, ‖⟪x, X.R g y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := fun x y g => by
    refine le_trans (norm_inner_le_norm _ _) ?_
    rw [hR.1]
  have hint : ∀ x y : X.L2, Integrable (fun g => X.φ g * ⟪x, X.R g y⟫_ℂ) (X.I.muA X.μf) := fun x y =>
    hφ.mul_bdd (c := ‖x‖ * ‖y‖) (hR.2 x y) (Filter.Eventually.of_forall (hbd x y))
  let f : X.L2 →ₗ⋆[ℂ] X.L2 →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ∫ g, X.φ g * ⟪x, X.R g y⟫_ℂ ∂(X.I.muA X.μf))
      (fun x x' y => by
        simp only [inner_add_left, mul_add]
        exact integral_add (hint x y) (hint x' y))
      (fun c x y => by
        simp only [inner_smul_left, smul_eq_mul]
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun g => by ring))
      (fun x y y' => by
        simp only [map_add, inner_add_right, mul_add]
        exact integral_add (hint x y) (hint x y'))
      (fun c x y => by
        simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun g => by ring))
  have hf : ∀ x y, f x y = ∫ g, X.φ g * ⟪x, X.R g y⟫_ℂ ∂(X.I.muA X.μf) := fun x y => rfl
  have hbound : ∀ x y, ‖f x y‖ ≤ (∫ g, ‖X.φ g‖ ∂(X.I.muA X.μf)) * ‖x‖ * ‖y‖ := by
    intro x y
    rw [hf, mul_assoc, ← integral_mul_const]
    refine norm_integral_le_of_norm_le (hφ.norm.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbd x y g) (norm_nonneg _)
  let B : X.L2 →L⋆[ℂ] X.L2 →L[ℂ] ℂ := f.mkContinuous₂ _ hbound
  refine ⟨ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin B), hφ, fun x y => ?_⟩
  rw [ContinuousLinearMap.adjoint_inner_right, InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

end CData

def StepsC'' (n₀ : ℕ) (A C cb c₁ A₂ cε C₁ : ℝ) : Prop :=
  ∀ X : CData, X.HypC n₀ A C cb → X.RegRep ∧ X.KernelDiag ∧ X.FinVol ∧
    ∃ Mod : Set X.I.GA, MeasurableSet Mod ∧ X.ProbMod c₁ Mod ∧
      X.NearStep (Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f) c₁ A₂ Mod ∧
      X.FarCount (X.Acnt C₁) (2 * (X.I.n : ℝ) ^ 2) Mod ∧ X.DeepInt (A₂ + 1) Mod

theorem StepsC'_of_last : ∃ C₃ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A Cb C cb c₁ A₂ cε C₁ : ℝ), 1 ≤ n₀ → C₃ ≤ C →
    adm2 D → Conclusion2 D n₀ A Cb → StepsC'' n₀ A C cb c₁ A₂ cε C₁ → StepsC' n₀ A C cb c₁ A₂ cε C₁ := by
  obtain ⟨Ch, -, hH⟩ := Formalism.HermitianLatticeCounting.Final.S7.threshHead 0
  refine ⟨Ch, fun D n₀ A Cb C cb c₁ A₂ cε C₁ hn hC h2 hb hS X hX => ?_⟩
  obtain ⟨s1, s2, s3, s4⟩ := hS X hX
  have hthr := (gap_thresholds_of_height_bound hH X hn hC hX).1
  have hph := ((second_part_iff_bundles D n₀ A Cb).1 hb X hX.1).1 hthr
  exact ⟨X.opExists_of_regRep s1 (φ_integrable X hX.1 hph), s2, s3, lowest_K_type_projector_exists D h2 X hX.1, s4⟩

theorem third_part_of_final_estimates (cε C₁ c₁ A A₂ : ℝ) (hcε : 0 < cε) (hcε2 : cε ≤ 1 / 2) (hC₁ : 1 ≤ C₁) (hc₁ : 0 < c₁)
    (hA : 1 ≤ A) (hA₂ : 0 ≤ A₂) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ n₁ : ℕ, ∀ Cb : ℝ, ∃ C₂ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (C cb : ℝ),
      n₁ ≤ n₀ → C₂ ≤ C → adm2 D → DiscreteSeriesDecayBound D → Conclusion2 D n₀ A Cb → StepsC'' n₀ A C cb c₁ A₂ cε C₁ →
      PointsLemma D n₀ A C c' cb := by
  obtain ⟨c', hc', n₁, h⟩ := third_part_of_refined_estimates cε C₁ c₁ A A₂ hcε hcε2 hC₁ hc₁ hA hA₂
  obtain ⟨C₃, h3⟩ := StepsC'_of_last
  refine ⟨c', hc', max n₁ 1, fun Cb => ?_⟩
  obtain ⟨C₂, h⟩ := h Cb
  refine ⟨max C₂ C₃, fun D n₀ C cb hn hC h2 hdec hb hS => ?_⟩
  exact h D n₀ C cb (le_trans (le_max_left _ _) hn) (le_trans (le_max_left _ _) hC) hdec hb
    (h3 D n₀ A Cb C cb c₁ A₂ cε C₁ (le_trans (le_max_right _ _) hn) (le_trans (le_max_right _ _) hC) h2 hb hS)

end Formalism.MainNotions.BridgeLemma

end
