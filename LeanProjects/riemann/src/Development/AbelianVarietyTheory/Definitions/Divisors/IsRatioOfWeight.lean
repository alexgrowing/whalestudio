import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatrixIsForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiPosFubiniStudyPowerAddSmoothFn

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ChartGlue GlobalTheory.ArInt GlobalTheory.VolBr

namespace GlobalTheory.HSAmp

section Gram

variable {S : Type} {Y : S → Type} [∀ σ, MeasurableSpace (Y σ)] {ι : Type}

def gram (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => ∑ᶠ σ, ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ

def cmb [Fintype ι] (v : ∀ σ, Y σ → ι → ℂ) (c : ι → ℂ) (σ : S) (y : Y σ) : ℝ := ‖∑ i, c i * v σ y i‖ ^ 2

def l2 [Fintype ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ) (c : ι → ℂ) : ℝ :=
  ∑ᶠ σ, ∫ y, cmb v c σ y ∂μ σ

def bergmanDensity [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ) (σ : S) (y : Y σ) : ℝ :=
  (∑ i, ∑ j, (gram μ v)⁻¹ j i * (v σ y i * (starRingEnd ℂ) (v σ y j))).re

structure IsFam (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ) : Prop where

  finite : Finite S

  integrable : ∀ σ i j, Integrable (fun y => v σ y i * (starRingEnd ℂ) (v σ y j)) (μ σ)

end Gram

def ellCount {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (R : ℝ) : ℕ :=
  {z : ι → ℤ | ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R ^ 2}.ncard

variable {k : Type} [CommRing k] {X : Scheme.{0}}

structure VolDens (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) where

  dens : AlgChart p σ D → CxPts p σ → ℝ

  cont : ∀ c, ContinuousOn (dens c) c.e.source

  pos : ∀ c, ∀ y ∈ c.e.source, 0 < dens c y

  trans : ∀ c c', ∀ y ∈ c.e.source, y ∈ c'.e.source → dens c y = ‖transDet c.e c'.e y‖ ^ 2 * dens c' y

def VolDens.meas {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} (ω : VolDens p σ D) : Measure (CxPts p σ) :=
  glueMeas (fun c : AlgChart p σ D => c.e) fun c y => ENNReal.ofReal (ω.dens c y)

def VolDens.IsRatio {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} (ω : VolDens p σ D) {B : LB X} (φ : Weight p σ B)
    (ρ : CxPts p σ → ℝ) : Prop :=
  Continuous ρ ∧ ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, c.chernDens φ y = ρ y * ω.dens c y

structure SmFn (p : X ⟶ Sp k) where

  u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ

  cInf : ∀ σ y, CInfAt (u σ) y

  conj : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))

def SmFn.smul {p : X ⟶ Sp k} (t : ℝ) (u : SmFn p) : SmFn p where
  u σ y := t * u.u σ y
  cInf σ y := (u.cInf σ y).const_mul t
  conj σ σ' i y y' h hy := congrArg (t * ·) (u.conj σ σ' i y y' h hy)

def SmFn.pull {p : X ⟶ Sp k} (u : SmFn p) {Y : Scheme.{0}} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) : SmFn q where
  u σ y := u.u σ (Points.PtsOver.map π hπ _ y)
  cInf σ _ := CInfAt.pull π hπ (u.cInf σ _)
  conj σ σ' _ _ _ h _ := u.conj σ σ' PUnit.unit _ _ ((congrArg (· ≫ π) h).trans (Category.assoc _ _ _)) mem_ptsIn_top

abbrev up {p : X ⟶ Sp k} (L : HermLB p) (u : SmFn p) : HermLB p := L.raise u.u u.cInf u.conj

variable [IsIntegral X] {p : X ⟶ Sp k}

def upperParabolic (P : Pair p) (u : SmFn p) : Pair p := ⟨up P.L u, P.A, P.r, P.r', P.hr, P.hr'⟩

def val (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : ℂ :=
  ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y *
    (Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2) : ℝ)

theorem norm_val (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    ‖val P a b σ y f‖ = P.nu a b σ y f := by
  rw [val, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rfl

def vals (P : Pair p) (a b : ℤ) {ι : Type} (f : ι → X.functionField) (σ : k →+* ℂ) (y : CxPts p σ) (i : ι) : ℂ :=
  val P a b σ y (f i)

def NV (P : Pair p) (a b : ℤ) (f : X.functionField) : Set X :=
  {x | ∀ i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → UnitAt x (P.loc a b f i j)}

def ballIn (P : Pair p) (Λ : AddSubgroup X.functionField) (a b : ℤ) (R : ℝ) : Set X.functionField :=
  {f | f ∈ Λ ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y f ≤ R}

theorem ballIn_H (P : Pair p) (a b : ℤ) (R : ℝ) : ballIn P (P.H a b) a b R = P.Bl a b R := rfl

structure GoodFam (P : Pair p) (D : ℕ) (g : ℝ) (Λ : ℕ → AddSubgroup X.functionField) : Prop where

  le : ∀ m : ℕ, Λ m ≤ P.H m 1

  fg : ∀ m, (Λ m).FG

  small : ∃ C : ℝ, 1 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → Λ m ≤ AddSubgroup.closure (ballIn P (Λ m) m 1 (C ^ m))

  rank : Tendsto (fun m : ℕ => (Module.finrank ℤ (Λ m) : ℝ) / (m : ℝ) ^ D) atTop (𝓝 g)

structure Gens (P : Pair p) (D e : ℕ) (x : Fin (D + 1) → X.functionField) : Prop where

  pos : 0 < e

  mem : ∀ l, x l ∈ P.H e 0

  cover : ∀ z : X, ∃ l, z ∈ NV P e 0 (x l)

def IsCan (P : Pair p) {D : ℕ} (e n : ℕ) (x : Fin (D + 1) → X.functionField) (u : SmFn p) : Prop :=
  ∀ σ y, u.u σ y = ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n))

def ratF {K : Type} [Field K] {D : ℕ} (x : Fin (D + 1) → K) : Subfield K :=
  Subfield.closure (Set.range fun j : Fin D => x j.succ / x 0)

def ratR {K : Type} [Field K] {D : ℕ} (x : Fin (D + 1) → K) (l : Fin (D + 1)) : Subring K :=
  Subring.closure (Set.range fun j => x j / x l)

omit [IsIntegral X] in

def fib (X : Scheme.{0}) (ℓ : ℕ) : Set X := {x | ringChar (X.residueField x) = ℓ}

theorem gens_int : Gens IntExample.pair 0 1 fun _ => 1 where
  pos := Nat.one_pos
  mem _ x i j _ _ := by
    rw [IntExample.loc_eq]
    exact (unitAt_one x).regAt
  cover z := ⟨0, fun i j _ _ => by rw [IntExample.loc_eq]; exact unitAt_one z⟩

theorem gram_point : IsFam (S := Unit) (Y := fun _ => Unit) (ι := Unit) (fun _ => Measure.dirac ()) (fun _ _ _ => 1) ∧
    gram (S := Unit) (Y := fun _ => Unit) (ι := Unit) (fun _ => Measure.dirac ()) (fun _ _ _ => 1) = 1 := by
  refine ⟨⟨inferInstance, fun _ _ _ => integrable_const _⟩, ?_⟩
  ext i j
  simp [gram, finsum_unique]

private theorem fderiv_half_comb_fderiv {n : ℕ} {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} {y : ReciprocityTheory.L2DbarEstimates.V n} (hD : DifferentiableAt ℝ (fderiv ℝ g) y)
    (c : ℂ) (u u' v : ReciprocityTheory.L2DbarEstimates.V n) :
    fderiv ℝ (fun w => (fderiv ℝ g w u + c * fderiv ℝ g w u') / 2) y v =
      (fderiv ℝ (fderiv ℝ g) y v u + c * fderiv ℝ (fderiv ℝ g) y v u') / 2 := by
  have h1 : ∀ u, HasFDerivAt (fun w => fderiv ℝ g w u) ((fderiv ℝ (fderiv ℝ g) y).flip u) y := fun u => by
    simpa using hD.hasFDerivAt.clm_apply (hasFDerivAt_const u y)
  have h3 : HasFDerivAt (fun w => fderiv ℝ g w u + c * fderiv ℝ g w u')
      ((fderiv ℝ (fderiv ℝ g) y).flip u + c • (fderiv ℝ (fderiv ℝ g) y).flip u') y :=
    HasFDerivAt.add (h1 u) (HasFDerivAt.const_mul (h1 u') c)
  rw [(show HasFDerivAt (fun w => (fderiv ℝ g w u + c * fderiv ℝ g w u') / 2)
      ((2 : ℂ)⁻¹ • ((fderiv ℝ (fderiv ℝ g) y).flip u + c • (fderiv ℝ (fderiv ℝ g) y).flip u')) y by
    simpa only [div_eq_mul_inv] using HasFDerivAt.mul_const h3 (2 : ℂ)⁻¹).fderiv]
  simp <;> ring

private theorem wd_eq_half_fderiv_sub_I {n : ℕ} (j : Fin n) (g : ReciprocityTheory.L2DbarEstimates.V n → ℂ) :
    ReciprocityTheory.L2DbarEstimates.wd n j g = fun w => (fderiv ℝ g w (ReciprocityTheory.L2DbarEstimates.bas n j) +
      (-Complex.I) * fderiv ℝ g w (Complex.I • ReciprocityTheory.L2DbarEstimates.bas n j)) / 2 := by
  funext w
  simp [ReciprocityTheory.L2DbarEstimates.wd, sub_eq_add_neg]

private theorem wdb_eq_half_fderiv_add_I {n : ℕ} (j : Fin n) (g : ReciprocityTheory.L2DbarEstimates.V n → ℂ) :
    ReciprocityTheory.L2DbarEstimates.wdb n j g = fun w => (fderiv ℝ g w (ReciprocityTheory.L2DbarEstimates.bas n j) +
      Complex.I * fderiv ℝ g w (Complex.I • ReciprocityTheory.L2DbarEstimates.bas n j)) / 2 := rfl

private theorem star_cHess_swap_of_contDiffAt {n : ℕ} {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n} (hf : ContDiffAt ℝ 2 f x) (i j : Fin n) :
    star (ReciprocityTheory.L2DbarEstimates.cHess n (fun v => ((f v : ℝ) : ℂ)) x j i) = ReciprocityTheory.L2DbarEstimates.cHess n (fun v => ((f v : ℝ) : ℂ)) x i j := by
  have hg2 : ContDiffAt ℝ 2 (fun v => ((f v : ℝ) : ℂ)) x := Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  have hD : DifferentiableAt ℝ (fderiv ℝ (fun v => ((f v : ℝ) : ℂ))) x :=
    (hg2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsymm := hg2.isSymmSndFDerivAt (by simp)
  have hreal : (fun w => (starRingEnd ℂ) ((fun v => ((f v : ℝ) : ℂ)) w)) = fun v => ((f v : ℝ) : ℂ) :=
    funext fun w => Complex.conj_ofReal _
  have hc : (fun w => (starRingEnd ℂ) (ReciprocityTheory.L2DbarEstimates.wdb n i (fun v => ((f v : ℝ) : ℂ)) w)) =
      ReciprocityTheory.L2DbarEstimates.wd n i (fun v => ((f v : ℝ) : ℂ)) := by
    funext w
    rw [← ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wd_conj', hreal]
  simp only [ReciprocityTheory.L2DbarEstimates.cHess, Matrix.of_apply, Complex.star_def]
  rw [← ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wdb_conj', hc]
  simp only [wd_eq_half_fderiv_sub_I, wdb_eq_half_fderiv_add_I]
  rw [fderiv_half_comb_fderiv hD, fderiv_half_comb_fderiv hD, fderiv_half_comb_fderiv hD, fderiv_half_comb_fderiv hD]
  rw [hsymm (ReciprocityTheory.L2DbarEstimates.bas n i) (ReciprocityTheory.L2DbarEstimates.bas n j),
    hsymm (ReciprocityTheory.L2DbarEstimates.bas n i) (Complex.I • ReciprocityTheory.L2DbarEstimates.bas n j),
    hsymm (Complex.I • ReciprocityTheory.L2DbarEstimates.bas n i) (ReciprocityTheory.L2DbarEstimates.bas n j),
    hsymm (Complex.I • ReciprocityTheory.L2DbarEstimates.bas n i) (Complex.I • ReciprocityTheory.L2DbarEstimates.bas n j)]
  ring

section Inhabitants

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ComplexOrder

omit [IsIntegral X]

open scoped ComplexConjugate in

theorem det_cHess_pos {n : ℕ} {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hL : ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun v => ((f v : ℝ) : ℂ)) x ξ).re) :
    0 < (cHess n (fun v => ((f v : ℝ) : ℂ)) x).det.re := by
  have hH := star_cHess_swap_of_contDiffAt hf
  have hP : (cHess n (fun v => ((f v : ℝ) : ℂ)) x).PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨Matrix.IsHermitian.ext hH, fun z hz => ?_⟩
    have hz' : (fun i => (starRingEnd ℂ) (z i)) ≠ 0 := fun h => hz (funext fun i => by
      simpa using congrFun h i)
    have hre := hL _ hz'
    have heq : leviV n (fun v => ((f v : ℝ) : ℂ)) x (fun i => (starRingEnd ℂ) (z i)) =
        dotProduct (star z) (Matrix.mulVec (cHess n (fun v => ((f v : ℝ) : ℂ)) x) z) := by
      simp only [ReciprocityTheory.L2DbarEstimates.leviV, ReciprocityTheory.L2DbarEstimates.cHess, dotProduct, Matrix.mulVec, Matrix.of_apply,
        Finset.mul_sum, Pi.star_apply, Complex.star_def, Complex.conj_conj]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have hself : (starRingEnd ℂ) (dotProduct (star z) (Matrix.mulVec (cHess n (fun v => ((f v : ℝ) : ℂ)) x) z)) =
        dotProduct (star z) (Matrix.mulVec (cHess n (fun v => ((f v : ℝ) : ℂ)) x) z) := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Complex.star_def, map_sum, map_mul,
        Complex.conj_conj, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      have := hH j k
      rw [Complex.star_def] at this
      rw [this]
      ring
    rw [heq] at hre
    exact Complex.pos_iff.2 ⟨hre, (Complex.conj_eq_iff_im.1 hself).symm⟩
  exact (Complex.pos_iff.1 hP.det_pos).1

def VolDens.ofWeight {σ : k →+* ℂ} {D : ℕ} {B : LB X} (φ : Weight p σ B) (h : φ.IsCInf)
    (hp : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, 0 < c.chernDens φ y) : VolDens p σ D where
  dens c := c.chernDens φ
  cont c := by
    have hcont : ContinuousOn (fun v => c.chernDens φ (c.e.symm v)) c.e.target :=
      continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
        ((Continuous.matrix_det continuous_id).comp_continuousOn
          ((GlobalTheory.MixDens.chernMat_isForm k X p σ D _ φ h).2.1 c)))
    exact (hcont.comp c.e.continuousOn c.e.mapsTo).congr fun y hy => by
      simp only [Function.comp_apply, c.e.left_inv hy]
  pos := hp
  trans c c' _ hy hy' := c.chernDens_trans c' h hy hy'

theorem VolDens.isRatio_ofWeight {σ : k →+* ℂ} {D : ℕ} {B : LB X} (φ : Weight p σ B) (h : φ.IsCInf)
    (hp : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, 0 < c.chernDens φ y) :
    (VolDens.ofWeight φ h hp).IsRatio φ fun _ => 1 :=
  ⟨continuous_const, fun _ _ _ => (one_mul _).symm⟩

def volFS (k : Type) [CommRing k] (σ : k →+* ℂ) (N : ℕ) : VolDens (PSpace.str k N) σ N :=
  .ofWeight ((ProjSpace.hermitianTwistingSheaf k N).φ σ) ((ProjSpace.hermitianTwistingSheaf k N).cInf σ) fun c y hy =>
    mul_pos (by positivity) (det_cHess_pos (((ProjSpace.hermitianTwistingSheaf k N).cInf σ).contDiffAt c hy (mem_pick _ y))
      fun ξ hξ => WeightShift.strictPos_fsO1 N (AnRead.all _ σ N) _ c y ⟨hy, mem_pick _ y⟩ ξ hξ)

theorem volFS_meas (k : Type) [CommRing k] (σ : k →+* ℂ) (N : ℕ) :
    (volFS k σ N).meas = ((ProjSpace.hermitianTwistingSheaf k N).φ σ).chernPart N 1 := by
  simp only [VolDens.meas, volFS, VolDens.ofWeight, Weight.chernPart, Units.val_one, Int.cast_one, one_mul]

def SmFn.const (p : X ⟶ Sp k) (t : ℝ) : SmFn p := ⟨fun _ _ => t, fun _ y => cInfAt_const t y, fun _ _ _ _ _ _ _ => rfl⟩

def SmFn.ofSec (L : HermLB p) (s : L.B.Sec) : SmFn p where
  u σ := (L.φ σ).nsq (secVal p σ s)
  cInf σ y := by
    have hi := mem_pick L.isLB y
    have h₁ : CInfAt (fun z => ‖ev p σ _ (s.f (pick L.isLB y)) z‖ ^ 2) y :=
      ⟨_, Unit, inferInstance, fun _ => s.f _, fun v => ‖v ()‖ ^ 2, Set.univ, hi, isOpen_univ, trivial,
        ((contDiff_apply ℝ ℂ ()).norm_sq ℂ).contDiffOn, EventuallyEq.rfl⟩
    exact (h₁.comp₂ (L.cInf σ _ y hi) (G := fun x => x.1 * Real.exp (-x.2))
      (contDiff_fst.mul contDiff_snd.neg.exp)).congr
      (eventually_of_mem ((isOpen_ptsIn _).mem_nhds hi) fun z hz => (L.φ σ).nsq_eq (secVal_mem s) hz)
  conj σ σ' _ y y' h _ := by
    have hi := mem_pick L.isLB y
    have hi' : y' ∈ ptsIn p σ' (L.B.U (pick L.isLB y)) := by
      have := mem_ptsIn.1 hi
      refine mem_ptsIn.2 ?_
      rw [h]
      have e : spMap (starRingEnd ℂ) (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint ℂ :=
        Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      exact (congrArg (fun z => y.1 z ∈ L.B.U (pick L.isLB y)) e).mpr this
    change (L.φ σ').nsq _ y' = (L.φ σ).nsq _ y
    rw [(L.φ σ).nsq_eq (secVal_mem s) hi, (L.φ σ').nsq_eq (secVal_mem s) hi', L.conj σ σ' _ y y' h hi, secVal_apply,
      secVal_apply, CxPts.ev_conj h hi, RCLike.norm_conj]

theorem goodFam_int : GoodFam IntExample.pair 0 1 fun _ => AddSubgroup.zmultiples ((2 : ℕ) : (Sp ℤ).functionField) where
  le m := AddSubgroup.zmultiples_le.2 fun x i j _ _ => by
    rw [IntExample.loc_eq]
    exact IntExample.regAt_nat x 2
  fg _ := ⟨{((2 : ℕ) : (Sp ℤ).functionField)}, by simp [AddSubgroup.zmultiples_eq_closure]⟩
  small := by
    refine ⟨1, le_rfl, fun m _ => AddSubgroup.zmultiples_le.2 (AddSubgroup.subset_closure ?_)⟩
    refine ⟨AddSubgroup.mem_zmultiples _, fun σ y => ?_⟩
    rw [IntExample.nu_nat, one_pow, Int.cast_one, one_mul, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rank := by
    have h2 : ((2 : ℕ) : (Sp ℤ).functionField) ≠ 0 := by
      haveI := IntExample.charZero_functionField
      exact Nat.cast_ne_zero.mpr two_ne_zero
    have e : ℤ ≃+ AddSubgroup.zmultiples ((2 : ℕ) : (Sp ℤ).functionField) :=
      AddEquiv.ofBijective (zmultiplesHom _ ⟨_, AddSubgroup.mem_zmultiples _⟩) ⟨fun a b hab => by
        haveI := IntExample.charZero_functionField
        have := congrArg Subtype.val hab
        simp only [zmultiplesHom_apply, AddSubgroup.coe_zsmul, zsmul_eq_mul] at this
        exact_mod_cast mul_right_cancel₀ h2 this, fun ⟨z, hz⟩ => by
        obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hz
        exact ⟨n, rfl⟩⟩
    have hr : Module.finrank ℤ (AddSubgroup.zmultiples ((2 : ℕ) : (Sp ℤ).functionField)) = 1 := by
      rw [← e.toIntLinearEquiv.finrank_eq, Module.finrank_self]
    simp only [hr, pow_zero, div_one, Nat.cast_one]
    exact tendsto_const_nhds

theorem gens_int' : Gens IntExample.pair 1 1 ![((2 : ℕ) : (Sp ℤ).functionField), ((3 : ℕ) : (Sp ℤ).functionField)] where
  pos := Nat.one_pos
  mem l x i j _ _ := by
    rw [IntExample.loc_eq]
    fin_cases l
    · exact IntExample.regAt_nat x 2
    · exact IntExample.regAt_nat x 3
  cover z := by
    by_cases h : UnitAt z ((2 : ℕ) : (Sp ℤ).functionField)
    · exact ⟨0, fun i j _ _ => by rw [IntExample.loc_eq]; exact h⟩
    · refine ⟨1, fun i j _ _ => ?_⟩
      rw [IntExample.loc_eq]
      obtain ⟨a, ha, ha'⟩ := zeroAt_iff.2 ⟨IntExample.regAt_nat z 2, h⟩
      refine ⟨1 + a, ?_, ?_⟩
      · by_contra hu
        have h1 : (1 + a) - a ∈ IsLocalRing.maximalIdeal _ :=
          Ideal.sub_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hu) ha
        simp at h1
      · simp [ha']
        norm_num

theorem isCan_int : IsCan IntExample.pair (D := 1) 1 1 ![((2 : ℕ) : (Sp ℤ).functionField), ((3 : ℕ) : (Sp ℤ).functionField)] (SmFn.const _ (Real.log 13)) := by
  intro σ y
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [IntExample.nu_nat, IntExample.nu_nat]
  simp only [SmFn.const]
  norm_num

end Inhabitants

end GlobalTheory.HSAmp
