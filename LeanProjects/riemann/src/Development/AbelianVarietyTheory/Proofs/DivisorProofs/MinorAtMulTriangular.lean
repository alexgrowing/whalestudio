import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionExtendsRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicPointSpecializing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtPointsOverPrimeBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFiniteIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelFunctionFieldCompatibility
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MvPolynomial Formalism.BasicNotions.DV
open GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag
open GlobalTheory.Cartier GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.WholeFlag
open IsDedekindDomain GlobalTheory.WholeFlag.Glue
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WholeFlag.GlueProof

theorem minorAt_mul_triangular {K : Type} [CommRing K] {n g : ℕ} (R : Matrix (Fin n) (Fin g) K) (T : Matrix (Fin g) (Fin g) K)
    (hT : T.BlockTriangular id) (k : ℕ) (hk : k ≤ g) (σ : Fin k → Fin n) :
    minorAt (R * T) k hk σ = minorAt R k hk σ * ∏ i : Fin k, T (Fin.castLE hk i) (Fin.castLE hk i) := by
  unfold minorAt
  have e : (Matrix.of fun r l : Fin k => (R * T) (σ r) (Fin.castLE hk l)) =
      (Matrix.of fun r l : Fin k => R (σ r) (Fin.castLE hk l)) *
        (Matrix.of fun a l : Fin k => T (Fin.castLE hk a) (Fin.castLE hk l)) := by
    ext r l
    simp only [Matrix.of_apply, Matrix.mul_apply]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb hk))) ?_, Finset.sum_map]
    · rfl
    intro j _ hj
    have hjk : k ≤ (j : ℕ) := by
      by_contra h
      exact hj (Finset.mem_map.2 ⟨⟨j, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    have hlt : id (Fin.castLE hk l) < id j := by
      change (l : ℕ) < j
      omega
    rw [hT hlt, mul_zero]
  have ht : (Matrix.of fun a l : Fin k => T (Fin.castLE hk a) (Fin.castLE hk l)).BlockTriangular id := by
    intro a l h
    exact hT (show (Fin.castLE hk l : ℕ) < Fin.castLE hk a from h)
  rw [e, Matrix.det_mul, Matrix.det_of_upperTriangular ht]
  rfl

end GlobalTheory.WholeFlag.GlueProof

namespace GlobalTheory.WholeFlag.GlueProof

open GlobalTheory.TrueGeo.SmallSec

theorem minor_eq_mul_inv {K : Type} [Field K] {n g : ℕ} (H : Matrix (Fin n) (Fin g) K) (T : Matrix (Fin g) (Fin g) K)
    (hT : T.BlockTriangular id) (hd : ∀ i, T i i ≠ 0) (k : ℕ) (hk : k ≤ g) (σ : Fin k → Fin n) :
    minorAt H k hk σ = minorAt (H * T⁻¹) k hk σ * ∏ i : Fin k, T (Fin.castLE hk i) (Fin.castLE hk i) := by
  have hdet : IsUnit T.det := by
    rw [Matrix.det_of_upperTriangular hT]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
  have h := minorAt_mul_triangular (H * T⁻¹) T hT k hk σ
  rwa [Matrix.mul_assoc, Matrix.nonsing_inv_mul T hdet, Matrix.mul_one] at h

theorem prod_ratio (ν : ℕ → ℝ) (m : ℕ) : ∀ k : ℕ, (∀ j, j ≤ k → 0 < ν j) →
    ∏ i : Fin k, (ν i / ν ((i : ℕ) + 1)) ^ m = (ν 0 / ν k) ^ m := by
  intro k
  induction k with
  | zero => intro hν; simp [div_self (hν 0 le_rfl).ne']
  | succ k ih =>
    intro hν
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih (fun j hj => hν j (hj.trans (Nat.le_succ k))), ← mul_pow]
    congr 1
    have h1 := hν k (Nat.le_succ k)
    have h2 := hν (k + 1) le_rfl
    field_simp

section Lift

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem exists_lift {x : Z} {m n : Type} (M : Matrix m n Z.functionField) (h : ∀ i j, RegAt x (M i j)) :
    ∃ S : Matrix m n (Z.presheaf.stalk x), S.map (algebraMap _ Z.functionField) = M := by
  choose S hS using h
  exact ⟨Matrix.of S, Matrix.ext fun i j => hS i j⟩

theorem map_valAt_lift {K : Type} [Field K] (y : Sp K ⟶ Z) {m n : Type} (S : Matrix m n (Z.presheaf.stalk (below y))) :
    (S.map (algebraMap _ Z.functionField)).map (valAt y) = S.map (Scheme.stalkClosedPointTo y).hom := by
  ext i j
  simp only [Matrix.map_apply]
  exact Res.valAt_algebraMap y _

theorem regAt_prod {x : Z} {ι : Type} [Fintype ι] (f : ι → Z.functionField) (h : ∀ i, RegAt x (f i)) :
    RegAt x (∏ i, f i) := by
  choose s hs using h
  exact ⟨∏ i, s i, by rw [map_prod]; exact Finset.prod_congr rfl fun i _ => hs i⟩

theorem unitAt_prod {x : Z} {ι : Type} [Fintype ι] (f : ι → Z.functionField) (h : ∀ i, UnitAt x (f i)) :
    UnitAt x (∏ i, f i) := by
  choose s hs hs' using h
  exact ⟨∏ i, s i, Finset.prod_induction s IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun i _ => hs i, by
    rw [map_prod]; exact Finset.prod_congr rfl fun i _ => hs' i⟩

theorem valAt_prod {K : Type} [Field K] (y : Sp K ⟶ Z) {ι : Type} [Fintype ι] (f : ι → Z.functionField)
    (h : ∀ i, RegAt (below y) (f i)) : valAt y (∏ i, f i) = ∏ i, valAt y (f i) := by
  choose s hs using h
  have e : ∏ i, f i = algebraMap _ Z.functionField (∏ i, s i) := by
    rw [map_prod]; exact Finset.prod_congr rfl fun i _ => (hs i).symm
  rw [e, Res.valAt_algebraMap, map_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [← hs i, Res.valAt_algebraMap]

theorem unitAt_of_pow_of_regAt {x : Z} {f : Z.functionField} {m : ℕ} (hm : 0 < m) (hf : RegAt x f)
    (h : UnitAt x (f ^ m)) : UnitAt x f := by
  obtain ⟨s, rfl⟩ := hf
  obtain ⟨a, ha, e⟩ := h
  rw [← map_pow] at e
  obtain rfl := IsFractionRing.injective (Z.presheaf.stalk x) Z.functionField e
  exact ⟨s, (isUnit_pow_iff hm.ne').1 ha, rfl⟩

theorem minor_valAt {K : Type} [Field K] (y : Sp K ⟶ Z) {n g : ℕ} (H : Matrix (Fin n) (Fin g) Z.functionField)
    (hH : ∀ r l, RegAt (below y) (H r l)) (k : ℕ) (hk : k ≤ g) (σ : Fin k → Fin n) :
    RegAt (below y) (minorAt H k hk σ) ∧ valAt y (minorAt H k hk σ) = minorAt (H.map (valAt y)) k hk σ := by
  obtain ⟨S, rfl⟩ := exists_lift H hH
  have e : minorAt (S.map (algebraMap _ Z.functionField)) k hk σ = algebraMap _ Z.functionField (minorAt S k hk σ) := by
    unfold minorAt
    rw [RingHom.map_det]
    rfl
  refine ⟨⟨_, e.symm⟩, ?_⟩
  rw [e, Res.valAt_algebraMap, map_valAt_lift]
  unfold minorAt
  rw [RingHom.map_det]
  rfl

end Lift

end GlobalTheory.WholeFlag.GlueProof

namespace GlobalTheory.WholeFlag.GlueProof

open GlobalTheory.TrueGeo.SmallSec

section More

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem unitAt_pow {x : Z} {f : Z.functionField} (h : UnitAt x f) (n : ℕ) : UnitAt x (f ^ n) := by
  induction n with
  | zero => simpa using unitAt_one x
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem regAt_minor {x : Z} {n g : ℕ} (H : Matrix (Fin n) (Fin g) Z.functionField) (hH : ∀ r l, RegAt x (H r l))
    (k : ℕ) (hk : k ≤ g) (σ : Fin k → Fin n) : RegAt x (minorAt H k hk σ) := by
  obtain ⟨S, rfl⟩ := exists_lift H hH
  refine ⟨minorAt S k hk σ, ?_⟩
  unfold minorAt
  rw [RingHom.map_det]
  rfl

theorem valAt_inv {K : Type} [Field K] (y : Sp K ⟶ Z) {f : Z.functionField} (h : UnitAt (below y) f) :
    valAt y f⁻¹ = (valAt y f)⁻¹ := by
  have e := Res.valAt_mul h.regAt h.inv.regAt
  rw [mul_inv_cancel₀ h.ne_zero, Res.valAt_one] at e
  exact eq_inv_of_mul_eq_one_right e.symm

end More

section Transport

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)

def toG : V.X.functionField ≃+* V.G.functionField :=
  haveI := GlobalTheory.Mean4O.RootLine.isPreimmersion_j V
  RingEquiv.ofBijective (fnMap V.j (GlobalTheory.Mean4O.RootLine.j_gen_specializes V))
    ⟨(fnMap V.j _).injective, fnMap_surjective V.j _⟩

theorem regAt_symm {z : V.G} {f : V.G.functionField} : RegAt (V.j z) ((toG V).symm f) ↔ RegAt z f := by
  haveI := GlobalTheory.Mean4O.RootLine.isPreimmersion_j V
  conv_rhs => rw [← (toG V).apply_symm_apply f]
  exact (regAt_fnMap_iff V.j _).symm

theorem unitAt_symm {z : V.G} {f : V.G.functionField} : UnitAt (V.j z) ((toG V).symm f) ↔ UnitAt z f := by
  haveI := GlobalTheory.Mean4O.RootLine.isPreimmersion_j V
  conv_rhs => rw [← (toG V).apply_symm_apply f]
  exact ⟨fun h => GlobalTheory.Mean4O.RootLine.unitAt_fnMap V.j _ h, fun h => GlobalTheory.Mean4O.RootLine.unitAt_of_fnMap V.j _ h⟩

theorem valAt_symm {K : Type} [Field K] (z : Sp K ⟶ V.G) (f : V.G.functionField) :
    valAt (z ≫ V.j) ((toG V).symm f) = valAt z f := by
  haveI := GlobalTheory.Mean4O.RootLine.isPreimmersion_j V
  rw [ModelFn.valAt_comp V.j (GlobalTheory.Mean4O.RootLine.j_gen_specializes V) z]
  exact congrArg _ ((toG V).apply_symm_apply f)

end Transport

section Chart

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) {g : ℕ}

def nmin (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField) (rl : Fin g → V.G.functionFieldˣ) (m k : ℕ) (hk : k ≤ g)
    (σ : Fin k → Fin (g + g)) : V.G.functionField :=
  minorAt H k hk σ ^ m / ∏ i : Fin k, (rl (Fin.castLE hk i) : V.G.functionField)

theorem blockTriangular_map {Tz : Matrix (Fin g) (Fin g) Y.Fn} (hT : Tz.BlockTriangular id) :
    (Tz.map V.φ).BlockTriangular id := fun i j h => by rw [Matrix.map_apply, hT h, map_zero]

theorem nmin_eq (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField) (rl : Fin g → V.G.functionFieldˣ) (m k : ℕ)
    (hk : k ≤ g) (σ : Fin k → Fin (g + g)) (Tz : Matrix (Fin g) (Fin g) Y.Fn) (dz : Fin g → Y.Fnˣ) (G : Fin g → Y.Fn)
    (hT : Tz.BlockTriangular id) (hTd : ∀ i, Tz i i = dz i) (hG : ∀ i, G i ≠ 0) :
    nmin V H rl m k hk σ = minorAt (H * (Tz.map V.φ)⁻¹) k hk σ ^ m *
      ∏ i : Fin k, (V.φ (G (Fin.castLE hk i) * dz (Fin.castLE hk i)) ^ m *
        (V.φ (G (Fin.castLE hk i) ^ m) * rl (Fin.castLE hk i))⁻¹) := by
  have hd : ∀ i, (Tz.map V.φ) i i ≠ 0 := fun i => by
    rw [Matrix.map_apply, hTd, map_ne_zero]; exact Units.ne_zero _
  unfold nmin
  rw [minor_eq_mul_inv H _ (blockTriangular_map V hT) hd k hk σ]
  have e : ∀ i : Fin k, V.φ (G (Fin.castLE hk i) * dz (Fin.castLE hk i)) ^ m *
      (V.φ (G (Fin.castLE hk i) ^ m) * rl (Fin.castLE hk i))⁻¹ =
      (Tz.map V.φ) (Fin.castLE hk i) (Fin.castLE hk i) ^ m * ((rl (Fin.castLE hk i) : V.G.functionField))⁻¹ := by
    intro i
    have h1 : V.φ (G (Fin.castLE hk i)) ≠ 0 := (map_ne_zero _).2 (hG _)
    rw [Matrix.map_apply, hTd, map_mul, map_pow, mul_pow, mul_inv]
    field_simp
  rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib, mul_pow,
    div_eq_mul_inv, mul_assoc]

theorem unitAt_minor_of_nmin {z : V.G} (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField)
    (rl : Fin g → V.G.functionFieldˣ) (m : ℕ) (hm : 0 < m) (k : ℕ) (hk : k ≤ g) (σ : Fin k → Fin (g + g))
    (Tz : Matrix (Fin g) (Fin g) Y.Fn) (dz : Fin g → Y.Fnˣ) (G : Fin g → Y.Fn) (hT : Tz.BlockTriangular id)
    (hTd : ∀ i, Tz i i = dz i) (hHz : ∀ r l, RegAt z ((H * (Tz.map V.φ)⁻¹) r l))
    (hGd : ∀ i, UnitAt z (V.φ (G i * dz i))) (hrl : ∀ i, UnitAt z (V.φ (G i ^ m) * rl i)) :
    RegAt z (nmin V H rl m k hk σ) ∧
      (UnitAt z (nmin V H rl m k hk σ) → UnitAt z (minorAt (H * (Tz.map V.φ)⁻¹) k hk σ)) := by
  have hG : ∀ i, G i ≠ 0 := fun i h => (hGd i).ne_zero (by rw [h, zero_mul, map_zero])
  have hQ := unitAt_prod _ fun i : Fin k => (unitAt_pow (hGd (Fin.castLE hk i)) m).mul (hrl (Fin.castLE hk i)).inv
  have hM := regAt_minor _ hHz k hk σ
  rw [nmin_eq V H rl m k hk σ Tz dz G hT hTd hG]
  refine ⟨(regAt_pow hM m).mul hQ.regAt, fun h => unitAt_of_pow_of_regAt hm hM ?_⟩
  have e := h.mul hQ.inv
  rwa [mul_assoc, mul_inv_cancel₀ hQ.ne_zero, mul_one] at e

theorem w_nmin {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G)
    (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField) (rl : Fin g → V.G.functionFieldˣ) (m k : ℕ) (hk : k ≤ g)
    (σ : Fin k → Fin (g + g)) (Tz : Matrix (Fin g) (Fin g) Y.Fn) (dz : Fin g → Y.Fnˣ) (G : Fin g → Y.Fn)
    (hT : Tz.BlockTriangular id) (hTd : ∀ i, Tz i i = dz i) (hHz : ∀ r l, RegAt (below z) ((H * (Tz.map V.φ)⁻¹) r l))
    (hGd : ∀ i, UnitAt (V.π (below z)) (G i * dz i)) (hrl : ∀ i, UnitAt (below z) (V.φ (G i ^ m) * rl i))
    (ν : ℕ → ℝ) (hν : ∀ j, j ≤ g → 0 < ν j) (hν0 : ν 0 = 1) (lg : Fin g → ℝ)
    (hnorm : ∀ i, (m : ℝ) * lg i = Real.log (e.w (valAt z (V.φ (G i ^ m) * rl i))))
    (hlg : ∀ i, lg i = Real.log (e.w (valAt (z ≫ V.π) (G i * dz i))) + Real.log (ν ((i : ℕ) + 1)) - Real.log (ν i)) :
    e.w (valAt z (nmin V H rl m k hk σ)) =
      e.w (minorAt ((H * (Tz.map V.φ)⁻¹).map (valAt z)) k hk σ) ^ m / ν k ^ m := by
  have hG : ∀ i, G i ≠ 0 := fun i h => (hGd i).ne_zero (by rw [h, zero_mul])
  have hGd' : ∀ i, UnitAt (below z) (V.φ (G i * dz i)) := fun i => V.unitAt_φ (hGd i)
  have hterm : ∀ i : Fin g, e.w (valAt z (V.φ (G i * dz i) ^ m * (V.φ (G i ^ m) * rl i)⁻¹)) =
      (ν i / ν ((i : ℕ) + 1)) ^ m := by
    intro i
    have hu := (hrl i)
    rw [Res.valAt_mul (regAt_pow (hGd' i).regAt m) hu.inv.regAt, Res.valAt_pow (hGd' i).regAt, valAt_inv z hu,
      map_mul, map_pow, map_inv₀, V.valAt_φ z (hGd i).regAt]
    have hpos : 0 < e.w (valAt z (V.φ (G i ^ m) * rl i)) := e.w.pos (Res.valAt_ne_zero hu)
    have hpos' : 0 < e.w (valAt (z ≫ V.π) (G i * dz i)) := by
      rw [← V.valAt_φ z (hGd i).regAt]; exact e.w.pos (Res.valAt_ne_zero (hGd' i))
    have h1 := hnorm i
    rw [hlg i] at h1
    have hb := hν _ (Nat.succ_le_of_lt i.2)
    have hc := hν _ i.2.le
    have hq : 0 < e.w (valAt (z ≫ V.π) (G i * dz i)) * ν ((i : ℕ) + 1) / ν i := div_pos (mul_pos hpos' hb) hc
    have h2 : e.w (valAt z (V.φ (G i ^ m) * rl i)) =
        (e.w (valAt (z ≫ V.π) (G i * dz i)) * ν ((i : ℕ) + 1) / ν i) ^ m := by
      rw [← Real.exp_log hpos, ← Real.exp_log (pow_pos hq m), ← h1, Real.log_pow, Real.log_div (mul_pos hpos' hb).ne' hc.ne',
        Real.log_mul hpos'.ne' hb.ne']
    rw [h2, div_pow, mul_pow, div_pow]
    field_simp
  have hQ : ∀ i : Fin k, RegAt (below z) (V.φ (G (Fin.castLE hk i) * dz (Fin.castLE hk i)) ^ m *
      (V.φ (G (Fin.castLE hk i) ^ m) * rl (Fin.castLE hk i))⁻¹) :=
    fun i => (regAt_pow (hGd' _).regAt m).mul (hrl _).inv.regAt
  have hM := minor_valAt z _ hHz k hk σ
  rw [nmin_eq V H rl m k hk σ Tz dz G hT hTd hG, Res.valAt_mul (regAt_pow hM.1 m) (regAt_prod _ hQ),
    Res.valAt_pow hM.1, hM.2, valAt_prod z _ hQ, map_mul, map_pow, map_prod]
  have hprod : ∏ i : Fin k, e.w (valAt z (V.φ (G (Fin.castLE hk i) * dz (Fin.castLE hk i)) ^ m *
      (V.φ (G (Fin.castLE hk i) ^ m) * rl (Fin.castLE hk i))⁻¹)) = 1 / ν k ^ m := by
    rw [Finset.prod_congr rfl fun i _ => hterm (Fin.castLE hk i)]
    have hr := prod_ratio ν m k fun j hj => hν j (hj.trans hk)
    simp only [Fin.coe_castLE]
    rw [hr, hν0, div_pow, one_pow]
  rw [hprod, mul_one_div]

end Chart

end GlobalTheory.WholeFlag.GlueProof

namespace GlobalTheory.WholeFlag.GlueProof

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def Hyp {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ) (V : Cover Y) (W : Y.X.Opens) {ι : Type}
    (U : ι → V.X.Opens) (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField)
    (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn)
    (L : Fin g → LB V.X) (m : ℕ) (r : ∀ i, ((L i).pull V.j).ι → V.G.functionFieldˣ) : Prop :=
  p.Prime ∧ 0 < g ∧ IsUnit J.det ∧ genericPoint Y.X ∈ W ∧ 0 < m ∧
    (∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ a, x ∈ U a) ∧
    (∀ i (x : V.X), ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ c, x ∈ (L i).U c) ∧
    (∀ y, (T y).BlockTriangular id ∧ ∀ i, T y i i = (d y i : Y.Fn)) ∧
    (∀ i y, UnitAt y (genAt (A i).D y * d y i)) ∧
    (∀ i c, ∀ x ∈ ((L i).pull V.j).U c, UnitAt x (V.φ (genAt (A i).D (V.π x) ^ m) * r i c)) ∧
    (∀ i (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G)
      (yt : Sp e.O ⟶ V.X) (c : ((L i).pull V.j).ι), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ⊤ ≤ yt ⁻¹ᵁ (L i).U (c PUnit.unit) →
      (m : ℝ) * (A i).lg v e y =
        Real.log (e.w (valAt z (V.φ (genAt (A i).D (below y.1) ^ m) * (r i c : V.G.functionField))))) ∧
    (∀ a (z : V.G), V.j z ∈ U a → ∀ k l, RegAt z ((H a * ((T (V.π z)).map V.φ)⁻¹) k l)) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W →
      ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ∃ ν : ℕ → ℝ, (∀ k, k ≤ g → 0 < ν k) ∧
        (∀ i : Fin g, (A i).lg v e y = Real.log (e.w (valAt y.1 (genAt (A i).D (below y.1) * d (below y.1) i))) +
          Real.log (ν ((i : ℕ) + 1)) - Real.log (ν (i : ℕ))) ∧
        ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a →
          (∀ (k : ℕ) (hk : k ≤ g) (σ : Fin k → Fin (g + g)), e.w (minorAt (valMat V (H a) (T (below y.1)) z) k hk σ) ≤ ν k) ∧
          (∀ (k : ℕ) (hk : k ≤ g), ∃ σ : Fin k → Fin (g + g), e.w (minorAt (valMat V (H a) (T (below y.1)) z) k hk σ) = ν k) ∧
          (∀ u u' : Fin g → AlgebraicClosure F, (∀ r, e.w ((Matrix.mulVec (valMat V (H a) (T (below y.1)) z) u) r) ≤ 1) →
            (∀ r, e.w ((Matrix.mulVec (valMat V (H a) (T (below y.1)) z) u') r) ≤ 1) →
            e.w (dotProduct (Matrix.mulVec (valMat V (H a) (T (below y.1)) z) u)
              (Matrix.mulVec (J.map (Int.castRingHom (AlgebraicClosure F))) (Matrix.mulVec (valMat V (H a) (T (below y.1)) z) u'))) < 1) ∧
          ∀ b, ⊤ ≤ yt ⁻¹ᵁ U b → ∀ u : Fin g → AlgebraicClosure F,
            (∀ r, e.w ((Matrix.mulVec (valMat V (H a) (T (below y.1)) z) u) r) ≤ 1) →
            ∀ r, e.w ((Matrix.mulVec (valMat V (H b) (T (below y.1)) z) u) r - (Matrix.mulVec (valMat V (H a) (T (below y.1)) z) u) r) < 1

abbrev Idx {V : Cover Y} (ι : Type) {g : ℕ} (L : Fin g → LB V.X) : Type :=
  ι × (∀ k : ℕ, Fin k → Fin (g + g)) × (∀ i, (L i).ι)

def frames {V : Cover Y} {g : ℕ} {L : Fin g → LB V.X} (r : ∀ i, ((L i).pull V.j).ι → V.G.functionFieldˣ)
    (jj : ∀ i, (L i).ι) : Fin g → V.G.functionFieldˣ :=
  fun i => r i (fun _ => jj i)

def chartSet (V : Cover Y) {ι : Type} {g : ℕ} (U : ι → V.X.Opens) (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField)
    (L : Fin g → LB V.X) (m : ℕ) (r : ∀ i, ((L i).pull V.j).ι → V.G.functionFieldˣ) (q : Idx ι L) : Set V.X :=
  {x | x ∈ U q.1 ∧ (∀ i, x ∈ (L i).U (q.2.2 i)) ∧
    ∀ (k : ℕ) (hk : k ≤ g), UnitAt x ((toG V).symm (nmin V (H q.1) (frames r q.2.2) m k hk (q.2.1 k)))}

theorem isOpen_chartSet (V : Cover Y) {ι : Type} {g : ℕ} (U : ι → V.X.Opens)
    (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField) (L : Fin g → LB V.X) (m : ℕ)
    (r : ∀ i, ((L i).pull V.j).ι → V.G.functionFieldˣ) (q : Idx ι L) : IsOpen (chartSet V U H L m r q) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨h1, h2, h3⟩ := hx
  choose N hN hN' using fun k : Fin (g + 1) => (h3 k (Nat.lt_succ_iff.1 k.2)).exists_nhds
  refine ⟨(U q.1 : Set V.X) ∩ (⋂ i, ((L i).U (q.2.2 i) : Set V.X)) ∩ ⋂ k, (N k : Set V.X), ?_, ?_, ?_⟩
  · rintro y ⟨⟨hy1, hy2⟩, hy3⟩
    refine ⟨hy1, fun i => Set.mem_iInter.1 hy2 i, fun k hk => ?_⟩
    exact hN' ⟨k, Nat.lt_succ_of_le hk⟩ y (Set.mem_iInter.1 hy3 _)
  · exact ((U q.1).isOpen.inter (isOpen_iInter_of_finite fun i => ((L i).U _).isOpen)).inter
      (isOpen_iInter_of_finite fun k => (N k).isOpen)
  · exact ⟨⟨h1, Set.mem_iInter.2 h2⟩, Set.mem_iInter.2 fun k => hN k⟩

def chartOpen (V : Cover Y) {ι : Type} {g : ℕ} (U : ι → V.X.Opens) (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField)
    (L : Fin g → LB V.X) (m : ℕ) (r : ∀ i, ((L i).pull V.j).ι → V.G.functionFieldˣ) (q : Idx ι L) : V.X.Opens :=
  ⟨chartSet V U H L m r q, isOpen_chartSet V U H L m r q⟩

def chartU (V : Cover Y) {ι : Type} {g : ℕ} (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField)
    {L : Fin g → LB V.X} (q : Idx ι L) : Matrix (Fin (g + g)) (Fin g) V.X.functionField :=
  (cramerCol (H q.1) q.2.1).map (toG V).symm

def chartM (V : Cover Y) {ι : Type} {g : ℕ} (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField)
    (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) {L : Fin g → LB V.X} (q : Idx ι L) :
    Matrix (Fin (g + g)) (Fin (g + g)) V.X.functionField :=
  fullFrame (chartU V H q) (J.map (Int.castRingHom _)) (leftInv (chartU V H q) (q.2.1 g))

def chartC (V : Cover Y) {ι : Type} {g : ℕ} (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField)
    {L : Fin g → LB V.X} (q : Idx ι L) (k : Fin g) : V.G.functionFieldˣ :=
  if h : minorAt (H q.1) ((k : ℕ) + 1) k.2 (q.2.1 ((k : ℕ) + 1)) / minorAt (H q.1) k k.2.le (q.2.1 k) ≠ 0 then
    Units.mk0 _ h else 1

end GlobalTheory.WholeFlag.GlueProof
