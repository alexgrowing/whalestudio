import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Matrix ComplexOrder ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section HidaSetting

def hermG {κ : Type} [Fintype κ] (G : Matrix κ κ ℂ) (u w : κ → ℂ) : ℂ :=
  star u ⬝ᵥ (G *ᵥ w)

def sinSqG {κ : Type} [Fintype κ] (G : Matrix κ κ ℂ) (u w : κ → ℂ) : ℝ :=
  1 - ‖hermG G u w‖ ^ 2 / ((hermG G u u).re * (hermG G w w).re)

variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]

def IsEEMetric (G : ((Σ k, T.yyIdx ι ν κ k) → ℂ) → Matrix κ κ ℂ) : Prop :=
  (∀ z, (G z).PosDef) ∧
  (∀ z z' : (Σ k, T.yyIdx ι ν κ k) → ℂ, (∀ i : ι, z ⟨.base, i⟩ = z' ⟨.base, i⟩) →
      (∀ l : ν, z ⟨.det, l⟩ = z' ⟨.det, l⟩) → G z = G z') ∧
  (∀ (c : T.YBlk → ℂ) (z : (Σ k, T.yyIdx ι ν κ k) → ℂ), (∀ k, c k ≠ 0) →
      G (fun p => c p.1 * z p) = G z) ∧
  ∀ m n : κ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => G z m n) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}

def IsFromBase (A : HermLine (T.yyIdx ι ν κ)) : Prop :=
  A.a .line = 0 ∧
    ∀ z z' : (Σ k, T.yyIdx ι ν κ k) → ℂ, (∀ i : ι, z ⟨.base, i⟩ = z' ⟨.base, i⟩) →
      (∀ l : ν, z ⟨.det, l⟩ = z' ⟨.det, l⟩) → A.h z = A.h z'

end HidaSetting

structure ProjectiveLineBundle (D : ℕ) where

  Ω : Type
  [fieldΩ : Field Ω]

  ι : Type

  ν : Type

  κ : Type
  [finι : Fintype ι]
  [finν : Fintype ν]
  [finκ : Fintype κ]

  E : Type
  [acgE : AddCommGroup E]
  [modE : Module Ω E]

  Φ : Type
  [fieldΦ : Field Φ]
  [algΦ : Algebra Ω Φ]
  x : ι → Ω
  B : ChartBundle ℤ x 2 E
  e : Module.Basis (Fin 2) Ω E
  φ : κ → E →ₗ[Ω] Ω
  δ : ν → Ω
  a : Fin 2 → Φ
  dualSec : T.IsTwistedDualSec B φ
  dualGen : T.IsTwistedDualGen B φ
  detGen : T.IsTwistedDetGen B e δ
  chart : ∃ i, x i ≠ 0
  indep : AlgebraicIndependent Ω a
  arithYY : IsArithVar (T.yyIdeal x δ e φ (a 0)) (D + 1)
  arithWW : IsArithVar (T.wwIdeal x δ e φ (a 0) (a 1)) (D + 2)

  G : ((Σ k, T.yyIdx ι ν κ k) → ℂ) → Matrix κ κ ℂ
  metric : IsEEMetric G
  n : ℕ

  g : MRing (T.wwIdx ι ν κ)

  h : MRing (T.wwIdx ι ν κ)
  g_deg : IsMultiHomog g (T.wwDeg n 1)
  h_deg : IsMultiHomog h (T.wwDeg (n + 3) 0)
  h_nmem : h ∉ T.wwIdeal x δ e φ (a 0) (a 1)
  quot : aeval (T.wwCoord x δ e φ (a 0) (a 1)) g =
    T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) h

attribute [instance] ProjectiveLineBundle.fieldΩ ProjectiveLineBundle.finι ProjectiveLineBundle.finν ProjectiveLineBundle.finκ ProjectiveLineBundle.acgE ProjectiveLineBundle.modE
  ProjectiveLineBundle.fieldΦ ProjectiveLineBundle.algΦ

namespace ProjectiveLineBundle

variable {D : ℕ} (S : ProjectiveLineBundle D)

abbrev YIdx : T.YBlk → Type := T.yyIdx S.ι S.ν S.κ

abbrev WIdx : T.WBlk → Type := T.wwIdx S.ι S.ν S.κ

abbrev YY : Ideal (MRing S.YIdx) := T.yyIdeal S.x S.δ S.e S.φ (S.a 0)

abbrev WW : Ideal (MRing S.WIdx) := T.wwIdeal S.x S.δ S.e S.φ (S.a 0) (S.a 1)

def IsXi (X : HermLine S.YIdx) : Prop :=
  X.a = T.twoXiDegY ∧ IsSmoothHerm X ∧
    ∀ z ∈ mcPts S.WW,
      ‖eval z (map (Int.castRingHom ℂ) S.g)‖ ^ 2 * X.h (fun p => z (T.yyEmb 0 p)) *
          X.h (fun p => z (T.yyEmb 1 p)) =
        ‖eval z (map (Int.castRingHom ℂ) S.h)‖ ^ 2 *
          sinSqG (S.G fun p => z (T.yyEmb 0 p)) (fun k => z ⟨.line0, k⟩) (fun k => z ⟨.line1, k⟩)

end ProjectiveLineBundle

section Diag

variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]

def diagLogNorm (g h : MRing (T.wwIdx ι ν κ)) (X₀ X₁ : HermLine (T.wwIdx ι ν κ))
    (z : (Σ k, T.wwIdx ι ν κ k) → ℂ) : ℝ :=
  Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / ‖eval z (map (Int.castRingHom ℂ) h)‖) +
    (Real.log (X₀.h z) + Real.log (X₁.h z)) / 2

def diagInt (P : Ideal (MRing (T.wwIdx ι ν κ))) (g h : MRing (T.wwIdx ι ν κ))
    (X₀ X₁ : HermLine (T.wwIdx ι ν κ)) {D : ℕ} (L : Fin D → HermLine (T.wwIdx ι ν κ)) : ℝ :=
  ptsIntegral P
    (Fin.cons (α := fun _ => ((Σ k, T.wwIdx ι ν κ k) → ℂ) → ℝ)
      (fun z => Real.log (X₀.h z) - Real.log (X₁.h z)) (pot L))
    (diagLogNorm g h X₀ X₁)

end Diag

section Powers

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def hermZpow (A : HermLine ι) (m : ℤ) : HermLine ι where
  a := m • A.a
  h z := A.h z ^ m
  pos z hz := zpow_pos (A.pos z hz) m
  smul c z hc := by
    rw [A.smul c z hc, mul_zpow, ← Finset.prod_zpow]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, ← _root_.zpow_mul, mul_comm]

def lamLine (A X : HermLine ι) (c : ℤ) : HermLine ι :=
  (A.tensor A).tensor (hermZpow X (-c))

end Powers

section Statements

open ReciprocityTheory.ChartRestriction.G.AI

def XiMetric.Statement : Prop :=
  ∀ (D : ℕ) (S : ProjectiveLineBundle D), ∃ X : HermLine S.YIdx, S.IsXi X

def ProjectivePointSetting.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ (D : ℕ) (S : ProjectiveLineBundle D) (A : HermLine S.YIdx),
    IsSmoothHerm A → IsFromBase A → I T.YBlk S.YIdx S.YY (D + 1) (fun _ => A) = 0

def DiagR.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ (D : ℕ) (S : ProjectiveLineBundle D) (X : HermLine S.YIdx) (X₀ X₁ : HermLine S.WIdx)
    (L : Fin D → HermLine S.WIdx),
    X.a = T.twoXiDegY → IsSmoothHerm X → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) X X₀ →
    IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) X X₁ → (∀ j, IsSmoothHerm (L j)) →
    I T.WBlk S.WIdx S.WW (D + 2) (Fin.append L ![X₀, X₀]) -
        I T.WBlk S.WIdx S.WW (D + 2) (Fin.append L ![X₁, X₁]) =
      2 * diagInt S.WW S.g S.h X₀ X₁ L

def FibreInt.Statement : Prop :=
  ∀ (D : ℕ) (S : ProjectiveLineBundle D) (X A : HermLine S.YIdx) (X₀ X₁ A₀ : HermLine S.WIdx),
    S.IsXi X → IsSmoothHerm A → IsFromBase A → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) X X₀ →
    IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) X X₁ → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) A A₀ →
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 →
      ∑ i ∈ Finset.range k, diagInt S.WW S.g S.h X₀ X₁ (word D k i X₀ X₁ A₀) =
        2 * kappa k * ptsIntegral S.YY (pot (mix (2 * k - 1) X A : Fin D → HermLine S.YIdx)) (fun _ => 1)

def ToFibreSquare.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ (D : ℕ) (S : ProjectiveLineBundle D) (X A : HermLine S.YIdx) (X₀ X₁ A₀ : HermLine S.WIdx),
    S.IsXi X → IsSmoothHerm A → IsFromBase A → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) X X₀ →
    IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) X X₁ → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) A A₀ →
    ∃ F : FibreSquare.{0} D,
      (∀ j : ℕ, j ≤ D + 1 →
        F.I (mix j F.ξ F.A) = (1 / 2 : ℝ) ^ j * I T.YBlk S.YIdx S.YY (D + 1) (mix j X A)) ∧
      ∀ k i : ℕ, 1 ≤ k → 2 * k ≤ D + 1 → i < k →
        F.Φ (word D k i (F.p₁ F.ξ) (F.p₂ F.ξ) (F.p₁ F.A)) =
          (1 / 2 : ℝ) ^ (2 * k) * diagInt S.WW S.g S.h X₀ X₁ (word D k i X₀ X₁ A₀)

def PropAPrime.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ (D : ℕ) (S : ProjectiveLineBundle D) (X A : HermLine S.YIdx),
    S.IsXi X → IsSmoothHerm A → IsFromBase A →
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 →
      I T.YBlk S.YIdx S.YY (D + 1) (mix (2 * k) X A) =
        -(2 * kappa k * ptsIntegral S.YY (pot (mix (2 * k - 1) X A : Fin D → HermLine S.YIdx)) (fun _ => 1))

def TheoremA.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ (D : ℕ) (S : ProjectiveLineBundle D) (X A : HermLine S.YIdx),
    S.IsXi X → IsSmoothHerm A → IsFromBase A → ∀ c : ℤ,
      I T.YBlk S.YIdx S.YY (D + 1) (fun _ => lamLine A X c) +
          I T.YBlk S.YIdx S.YY (D + 1) (fun _ => lamLine A X (-c)) =
        2 ^ (D + 1) * (tsgPoly D kappa (volPoly D fun j =>
          (1 / 2 : ℝ) ^ j * ptsIntegral S.YY (pot (mix j X A : Fin D → HermLine S.YIdx)) (fun _ => 1))).eval (c : ℝ)

end Statements

section Inhabit

abbrev exX : Unit → ℚ := fun _ => 1

theorem mem_chartRing_exX (q : ℚ) : q ∈ chartRing ℤ exX () ↔ ∃ n : ℤ, (n : ℚ) = q := by
  constructor
  · intro hq
    have hle : chartRing ℤ exX () ≤ ⊥ := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨j, rfl⟩
      simp only [exX, div_one]
      exact Subalgebra.one_mem _
    obtain ⟨n, hn⟩ := Algebra.mem_bot.1 (hle hq)
    exact ⟨n, by simpa using hn⟩
  · rintro ⟨n, rfl⟩
    exact Subalgebra.intCast_mem _ n

def intLat : AddSubgroup (Fin 2 → ℚ) where
  carrier := {v | ∀ q, ∃ n : ℤ, (n : ℚ) = v q}
  add_mem' {v w} hv hw q := by
    obtain ⟨n, hn⟩ := hv q
    obtain ⟨m, hm⟩ := hw q
    exact ⟨n + m, by simp [hn, hm]⟩
  zero_mem' q := ⟨0, by simp⟩
  neg_mem' {v} hv q := by
    obtain ⟨n, hn⟩ := hv q
    exact ⟨-n, by simp [hn]⟩

theorem mem_intLat (v : Fin 2 → ℚ) : v ∈ intLat ↔ ∀ q, ∃ n : ℤ, (n : ℚ) = v q := Iff.rfl

theorem single_mem_intLat (q : Fin 2) : (Pi.single q 1 : Fin 2 → ℚ) ∈ intLat := by
  intro r
  by_cases h : r = q
  · subst h
    exact ⟨1, by simp⟩
  · exact ⟨0, by simp [h]⟩

def exBundle : ChartBundle ℤ exX 2 (Fin 2 → ℚ) where
  lat _ := intLat
  stable i a ha v hv q := by
    obtain ⟨m, hm⟩ := (mem_chartRing_exX a).1 ha
    obtain ⟨n, hn⟩ := hv q
    exact ⟨m * n, by simp [← hm, ← hn]⟩
  frame i _ := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => Subalgebra.one_mem _, fun _ => Subalgebra.one_mem _, by simp,
      fun _ => ⟨Pi.basisFun ℚ (Fin 2), (Pi.basisFun ℚ (Fin 2)).linearIndependent,
        (Pi.basisFun ℚ (Fin 2)).span_eq, fun v => ?_⟩⟩
    simp only [one_pow, one_smul, exists_const, one_mul]
    constructor
    · intro hv
      refine ⟨v, fun q => (mem_chartRing_exX _).2 (hv q), ?_⟩
      exact ((Pi.basisFun ℚ (Fin 2)).sum_repr v).symm.trans (by simp)
    · rintro ⟨c, hc, rfl⟩ q
      obtain ⟨n, hn⟩ := (mem_chartRing_exX _).1 (hc q)
      exact ⟨n, by simp [Finset.sum_apply, Pi.single_apply, hn]⟩
  overlap i j _ _ v hv := ⟨0, by simpa using hv⟩

def exφ : Unit ⊕ Unit → (Fin 2 → ℚ) →ₗ[ℚ] ℚ :=
  Sum.elim (fun _ => LinearMap.proj 0) (fun _ => LinearMap.proj 1)

theorem ex_dualSec : T.IsTwistedDualSec exBundle exφ := by
  intro i _ k v hv
  rw [mem_lineLat]
  rcases k with _ | _
  · obtain ⟨n, hn⟩ := hv 0
    exact ⟨v 0, (mem_chartRing_exX _).2 ⟨n, hn⟩, by simp [exφ, exX]⟩
  · obtain ⟨n, hn⟩ := hv 1
    exact ⟨v 1, (mem_chartRing_exX _).2 ⟨n, hn⟩, by simp [exφ, exX]⟩

theorem ex_dualGen : T.IsTwistedDualGen exBundle exφ := by
  intro i _ ψ hψ
  refine ⟨Sum.elim (fun _ => ψ (Pi.single 0 1)) (fun _ => ψ (Pi.single 1 1)), ?_, ?_⟩
  · rintro (_ | _)
    · exact hψ _ (single_mem_intLat 0)
    · exact hψ _ (single_mem_intLat 1)
  · refine (Pi.basisFun ℚ (Fin 2)).ext fun q => ?_
    fin_cases q <;> simp [exφ, exX, Fintype.sum_sum_type]

theorem ex_detGen : T.IsTwistedDetGen (ν := Unit) exBundle (Pi.basisFun ℚ (Fin 2)) (fun _ => 1) := by
  intro i _
  refine ⟨fun _ => Submodule.subset_span ⟨Pi.single 0 1, single_mem_intLat 0, Pi.single 1 1, single_mem_intLat 1,
    by simp [T.detE, exX]⟩, fun u hu w hw => ?_⟩
  obtain ⟨a, ha⟩ := hu 0
  obtain ⟨b, hb⟩ := hu 1
  obtain ⟨c, hc⟩ := hw 0
  obtain ⟨d, hd⟩ := hw 1
  have hmem : ((a * d - b * c : ℤ) : ℚ) ∈ chartRing ℤ exX i := (mem_chartRing_exX _).2 ⟨_, rfl⟩
  have h1 : (1 : ℚ) ∈ Submodule.span (chartRing ℤ exX i) (Set.range fun _ : Unit => (exX i)⁻¹ * 1) :=
    Submodule.subset_span ⟨(), by simp [exX]⟩
  have := Submodule.smul_mem _ (⟨_, hmem⟩ : chartRing ℤ exX i) h1
  convert this using 1
  simp [T.detE, ← ha, ← hb, ← hc, ← hd, Subalgebra.smul_def]

abbrev ExΦ := FractionRing (MvPolynomial (Fin 2) ℚ)

def exA : Fin 2 → ExΦ := fun j => algebraMap (MvPolynomial (Fin 2) ℚ) ExΦ (X j)

def exιR : MvPolynomial (Fin 2) ℤ →+* ExΦ :=
  (algebraMap (MvPolynomial (Fin 2) ℚ) ExΦ).comp (MvPolynomial.map (Int.castRingHom ℚ))

theorem exιR_injective : Function.Injective exιR :=
  (IsFractionRing.injective (MvPolynomial (Fin 2) ℚ) ExΦ).comp
    (MvPolynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℚ)))

theorem exιR_X (j : Fin 2) : exιR (X j) = exA j := by
  simp [exιR, exA]

theorem ex_indep : AlgebraicIndependent ℚ exA := by
  rw [algebraicIndependent_iff_injective_aeval]
  have h : (MvPolynomial.aeval exA : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] ExΦ).toRingHom =
      algebraMap (MvPolynomial (Fin 2) ℚ) ExΦ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    · simp [exA]
  intro p q hpq
  apply IsFractionRing.injective (MvPolynomial (Fin 2) ℚ) ExΦ
  have hp := RingHom.congr_fun h p
  have hq := RingHom.congr_fun h q
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hp hq
  rw [← hp, ← hq]
  exact hpq

abbrev ExY := T.yyIdx Unit Unit (Unit ⊕ Unit)

abbrev ExW := T.wwIdx Unit Unit (Unit ⊕ Unit)

def exCW : (Σ k, ExW k) → MvPolynomial (Fin 2) ℤ
  | ⟨.line0, Sum.inr _⟩ => X 0
  | ⟨.line1, Sum.inr _⟩ => X 1
  | _ => 1

def exCY : (Σ k, ExY k) → MvPolynomial (Fin 2) ℤ
  | ⟨.line, Sum.inr _⟩ => X 0
  | _ => 1

theorem ex_wwCoord (p : Σ k, ExW k) :
    T.wwCoord exX (fun _ : Unit => (1 : ℚ)) (Pi.basisFun ℚ (Fin 2)) exφ (exA 0) (exA 1) p = exιR (exCW p) := by
  rcases p with ⟨_ | _ | _ | _, i⟩
  · simp [T.wwCoord, exCW, exX]
  · simp [T.wwCoord, exCW]
  · rcases i with _ | _ <;> simp [T.wwCoord, exCW, T.lineVal, exφ, exιR_X]
  · rcases i with _ | _ <;> simp [T.wwCoord, exCW, T.lineVal, exφ, exιR_X]

theorem ex_yyCoord (p : Σ k, ExY k) :
    T.yyCoord exX (fun _ : Unit => (1 : ℚ)) (Pi.basisFun ℚ (Fin 2)) exφ (exA 0) p = exιR (exCY p) := by
  rcases p with ⟨_ | _ | _, i⟩
  · simp [T.yyCoord, exCY, exX]
  · simp [T.yyCoord, exCY]
  · rcases i with _ | _ <;> simp [T.yyCoord, exCY, T.lineVal, exφ, exιR_X]

def exZW : MRing ExW →+* MvPolynomial T.WBlk (MvPolynomial (Fin 2) ℤ) :=
  eval₂Hom (Int.castRingHom _) fun p => C (exCW p) * X p.1

def exZY : MRing ExY →+* MvPolynomial T.YBlk (MvPolynomial (Fin 2) ℤ) :=
  eval₂Hom (Int.castRingHom _) fun p => C (exCY p) * X p.1

theorem ex_multiConeMap_ww :
    T.multiConeMap (T.wwCoord exX (fun _ : Unit => (1 : ℚ)) (Pi.basisFun ℚ (Fin 2)) exφ (exA 0) (exA 1)) =
      (MvPolynomial.map exιR).comp exZW := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
  · simp [T.multiConeMap, exZW]
  · simp [T.multiConeMap, exZW, ex_wwCoord]

theorem ex_multiConeMap_yy :
    T.multiConeMap (T.yyCoord exX (fun _ : Unit => (1 : ℚ)) (Pi.basisFun ℚ (Fin 2)) exφ (exA 0)) =
      (MvPolynomial.map exιR).comp exZY := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
  · simp [T.multiConeMap, exZY]
  · simp [T.multiConeMap, exZY, ex_yyCoord]

abbrev ExLW := FractionRing (MRing ExW)

abbrev ExLY := FractionRing (MRing ExY)

theorem exLW_X_ne_zero (p : Σ k, ExW k) : algebraMap (MRing ExW) ExLW (X p) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ ExLW)).2 (X_ne_zero _)

theorem exLY_X_ne_zero (p : Σ k, ExY k) : algebraMap (MRing ExY) ExLY (X p) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ ExLY)).2 (X_ne_zero _)

def exθW : MvPolynomial T.WBlk (MvPolynomial (Fin 2) ℤ) →+* ExLW :=
  eval₂Hom (eval₂Hom (Int.castRingHom ExLW)
      ![algebraMap (MRing ExW) ExLW (X ⟨.line0, Sum.inr ()⟩) / algebraMap (MRing ExW) ExLW (X ⟨.line0, Sum.inl ()⟩),
        algebraMap (MRing ExW) ExLW (X ⟨.line1, Sum.inr ()⟩) / algebraMap (MRing ExW) ExLW (X ⟨.line1, Sum.inl ()⟩)])
    fun
    | .base => algebraMap (MRing ExW) ExLW (X ⟨.base, ()⟩)
    | .det => algebraMap (MRing ExW) ExLW (X ⟨.det, ()⟩)
    | .line0 => algebraMap (MRing ExW) ExLW (X ⟨.line0, Sum.inl ()⟩)
    | .line1 => algebraMap (MRing ExW) ExLW (X ⟨.line1, Sum.inl ()⟩)

def exθY : MvPolynomial T.YBlk (MvPolynomial (Fin 2) ℤ) →+* ExLY :=
  eval₂Hom (eval₂Hom (Int.castRingHom ExLY)
      ![algebraMap (MRing ExY) ExLY (X ⟨.line, Sum.inr ()⟩) / algebraMap (MRing ExY) ExLY (X ⟨.line, Sum.inl ()⟩), 0])
    fun
    | .base => algebraMap (MRing ExY) ExLY (X ⟨.base, ()⟩)
    | .det => algebraMap (MRing ExY) ExLY (X ⟨.det, ()⟩)
    | .line => algebraMap (MRing ExY) ExLY (X ⟨.line, Sum.inl ()⟩)

theorem exθW_comp : exθW.comp exZW = algebraMap (MRing ExW) ExLW := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
  · simp [exθW, exZW]
  · rcases p with ⟨_ | _ | _ | _, i⟩
    · simp [exθW, exZW, exCW]; rfl
    · simp [exθW, exZW, exCW]; rfl
    · rcases i with _ | _
      · simp [exθW, exZW, exCW]
      · simp [exθW, exZW, exCW, div_mul_cancel₀ _ (exLW_X_ne_zero _)]
    · rcases i with _ | _
      · simp [exθW, exZW, exCW]
      · simp [exθW, exZW, exCW, div_mul_cancel₀ _ (exLW_X_ne_zero _)]

theorem exθY_comp : exθY.comp exZY = algebraMap (MRing ExY) ExLY := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
  · simp [exθY, exZY]
  · rcases p with ⟨_ | _ | _, i⟩
    · simp [exθY, exZY, exCY]; rfl
    · simp [exθY, exZY, exCY]; rfl
    · rcases i with _ | _
      · simp [exθY, exZY, exCY]
      · simp [exθY, exZY, exCY, div_mul_cancel₀ _ (exLY_X_ne_zero _)]

theorem ex_wwIdeal :
    T.wwIdeal exX (fun _ : Unit => (1 : ℚ)) (Pi.basisFun ℚ (Fin 2)) exφ (exA 0) (exA 1) = ⊥ := by
  rw [eq_bot_iff]
  intro P hP
  rw [T.wwIdeal, RingHom.mem_ker, ex_multiConeMap_ww, RingHom.comp_apply] at hP
  have h1 : exZW P = 0 :=
    MvPolynomial.map_injective _ exιR_injective (hP.trans (map_zero _).symm)
  have h2 : algebraMap (MRing ExW) ExLW P = 0 := by
    rw [← exθW_comp, RingHom.comp_apply, h1, map_zero]
  exact (Ideal.mem_bot).2 (IsFractionRing.injective _ ExLW (h2.trans (map_zero _).symm))

theorem ex_yyIdeal :
    T.yyIdeal exX (fun _ : Unit => (1 : ℚ)) (Pi.basisFun ℚ (Fin 2)) exφ (exA 0) = ⊥ := by
  rw [eq_bot_iff]
  intro P hP
  rw [T.yyIdeal, RingHom.mem_ker, ex_multiConeMap_yy, RingHom.comp_apply] at hP
  have h1 : exZY P = 0 :=
    MvPolynomial.map_injective _ exιR_injective (hP.trans (map_zero _).symm)
  have h2 : algebraMap (MRing ExY) ExLY P = 0 := by
    rw [← exθY_comp, RingHom.comp_apply, h1, map_zero]
  exact (Ideal.mem_bot).2 (IsFractionRing.injective _ ExLY (h2.trans (map_zero _).symm))

theorem card_blocks_projLine_example : Fintype.card T.WBlk = 4 := rfl

theorem ex_card_Y : Fintype.card T.YBlk = 3 := rfl

theorem natCard_sigma_blocks_example : Nat.card (Σ k, ExW k) = 6 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem ex_natCard_Y : Nat.card (Σ k, ExY k) = 4 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem ex_arithWW :
    IsArithVar (T.wwIdeal exX (fun _ : Unit => (1 : ℚ)) (Pi.basisFun ℚ (Fin 2)) exφ (exA 0) (exA 1)) (1 + 2) := by
  rw [ex_wwIdeal]
  refine ⟨⟨.base⟩, ⟨Ideal.isPrime_bot,
    ⟨∅, fun f hf => absurd hf (Set.notMem_empty f), Ideal.span_empty.symm⟩, fun k => ?_⟩, ?_, ?_⟩
  · rcases k with _ | _ | _ | _
    · exact ⟨(), by rw [Submodule.mem_bot]; exact X_ne_zero _⟩
    · exact ⟨(), by rw [Submodule.mem_bot]; exact X_ne_zero _⟩
    · exact ⟨Sum.inl (), by rw [Submodule.mem_bot]; exact X_ne_zero _⟩
    · exact ⟨Sum.inl (), by rw [Submodule.mem_bot]; exact X_ne_zero _⟩
  · ext a
    simp [Ideal.mem_comap]
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField, natCard_sigma_blocks_example, card_blocks_projLine_example]
    rfl

theorem ex_arithYY :
    IsArithVar (T.yyIdeal exX (fun _ : Unit => (1 : ℚ)) (Pi.basisFun ℚ (Fin 2)) exφ (exA 0)) (1 + 1) := by
  rw [ex_yyIdeal]
  refine ⟨⟨.base⟩, ⟨Ideal.isPrime_bot,
    ⟨∅, fun f hf => absurd hf (Set.notMem_empty f), Ideal.span_empty.symm⟩, fun k => ?_⟩, ?_, ?_⟩
  · rcases k with _ | _ | _
    · exact ⟨(), by rw [Submodule.mem_bot]; exact X_ne_zero _⟩
    · exact ⟨(), by rw [Submodule.mem_bot]; exact X_ne_zero _⟩
    · exact ⟨Sum.inl (), by rw [Submodule.mem_bot]; exact X_ne_zero _⟩
  · ext a
    simp [Ideal.mem_comap]
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField, ex_natCard_Y, ex_card_Y]
    rfl

section Homog

variable {K : Type*} [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem exHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem exHomog_X (k : K) (i : ι k) : IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [h]

theorem exHomog_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  classical
  intro m hm k
  rw [sub_eq_add_neg] at hm
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · rw [MvPolynomial.support_neg] at h
    exact hg m h k

theorem exHomog_pow {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  classical
  induction n with
  | zero =>
    intro m hm k
    rw [pow_zero, MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact exHomog_mul ih hf

end Homog

def exg : MRing ExW :=
  X ⟨.det, ()⟩ * (X ⟨.line0, Sum.inl ()⟩ * X ⟨.line1, Sum.inr ()⟩ - X ⟨.line0, Sum.inr ()⟩ * X ⟨.line1, Sum.inl ()⟩)

def exh : MRing ExW := X ⟨.base, ()⟩ ^ 3

theorem ex_g_deg : IsMultiHomog exg (T.wwDeg 0 1) := by
  simp only [exg]
  have h1 := exHomog_mul (exHomog_X (ι := ExW) T.WBlk.line0 (Sum.inl ()))
    (exHomog_X (ι := ExW) T.WBlk.line1 (Sum.inr ()))
  have h2 := exHomog_mul (exHomog_X (ι := ExW) T.WBlk.line0 (Sum.inr ()))
    (exHomog_X (ι := ExW) T.WBlk.line1 (Sum.inl ()))
  have h3 := exHomog_mul (exHomog_X (ι := ExW) T.WBlk.det ()) (exHomog_sub h1 (by rwa [add_comm] at h2 ⊢))
  convert h3 using 1
  funext k
  cases k <;> simp [T.wwDeg]

theorem ex_h_deg : IsMultiHomog exh (T.wwDeg (0 + 3) 0) := by
  simp only [exh]
  have h := exHomog_pow (exHomog_X (ι := ExW) T.WBlk.base ()) 3
  convert h using 1
  funext k
  cases k <;> simp [T.wwDeg]

theorem ex_h_nmem :
    exh ∉ T.wwIdeal exX (fun _ : Unit => (1 : ℚ)) (Pi.basisFun ℚ (Fin 2)) exφ (exA 0) (exA 1) := by
  rw [ex_wwIdeal, Submodule.mem_bot]
  exact pow_ne_zero _ (X_ne_zero _)

theorem ex_metric : IsEEMetric (ι := Unit) (ν := Unit) (κ := Unit ⊕ Unit) fun _ => 1 :=
  ⟨fun _ => Matrix.PosDef.one, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => contDiffOn_const⟩

section FS

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem ofMetrics_fs_h (a : K → ℤ) (z : (Σ k, ι k) → ℂ) :
    (HermLine.ofMetrics (fun k => fsMetric (ι k)) a).h z =
      ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ a k := by
  simp only [HermLine.ofMetrics, fsMetric, EuclideanSpace.norm_eq]

theorem isSmoothHerm_ofMetrics_fs (a : K → ℤ) : IsSmoothHerm (HermLine.ofMetrics (fun k => fsMetric (ι k)) a) := by
  have hfun : (HermLine.ofMetrics (fun k => fsMetric (ι k)) a).h =
      fun z => ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ a k := funext (ofMetrics_fs_h a)
  unfold IsSmoothHerm
  rw [hfun]
  refine contDiffOn_prod fun k _ => ?_
  have hpos : ∀ z ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
    intro z hz
    obtain ⟨i, hi⟩ := hz k
    exact Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
  have hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2))
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    ContDiffOn.sqrt (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k))).contDiffOn fun z hz => (hpos z hz).ne'
  have hf0 : ∀ z ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ≠ 0 :=
    fun z hz => (Real.sqrt_pos.2 (hpos z hz)).ne'
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg (a k)
  · simp only [hm, zpow_natCast]
    exact hf.pow m
  · simp only [hm, _root_.zpow_neg, zpow_natCast]
    exact (hf.pow m).inv fun z hz => pow_ne_zero _ (hf0 z hz)

end FS

theorem sumY_base (f : ExY .base → ℝ) : ∑ i, f i = f () := by
  have h : ∀ g : Unit → ℝ, ∑ i, g i = g () := fun g => by simp
  exact h f

theorem sumY_det (f : ExY .det → ℝ) : ∑ i, f i = f () := by
  have h : ∀ g : Unit → ℝ, ∑ i, g i = g () := fun g => by simp
  exact h f

theorem sumY_line (f : ExY .line → ℝ) : ∑ i, f i = f (Sum.inl ()) + f (Sum.inr ()) := by
  have h : ∀ g : Unit ⊕ Unit → ℝ, ∑ i, g i = g (Sum.inl ()) + g (Sum.inr ()) := fun g => by
    simp [Fintype.sum_sum_type]
  exact h f

theorem sumW_base (f : ExW .base → ℝ) : ∑ i, f i = f () := by
  have h : ∀ g : Unit → ℝ, ∑ i, g i = g () := fun g => by simp
  exact h f

theorem sumW_det (f : ExW .det → ℝ) : ∑ i, f i = f () := by
  have h : ∀ g : Unit → ℝ, ∑ i, g i = g () := fun g => by simp
  exact h f

theorem sumW_line0 (f : ExW .line0 → ℝ) : ∑ i, f i = f (Sum.inl ()) + f (Sum.inr ()) := by
  have h : ∀ g : Unit ⊕ Unit → ℝ, ∑ i, g i = g (Sum.inl ()) + g (Sum.inr ()) := fun g => by
    simp [Fintype.sum_sum_type]
  exact h f

theorem sumW_line1 (f : ExW .line1 → ℝ) : ∑ i, f i = f (Sum.inl ()) + f (Sum.inr ()) := by
  have h : ∀ g : Unit ⊕ Unit → ℝ, ∑ i, g i = g (Sum.inl ()) + g (Sum.inr ()) := fun g => by
    simp [Fintype.sum_sum_type]
  exact h f

theorem prod_YBlk (f : T.YBlk → ℝ) : ∏ k, f k = f .base * (f .det * f .line) := by
  rw [show (Finset.univ : Finset T.YBlk) = {.base, .det, .line} from rfl]
  simp

theorem prod_WBlk (f : T.WBlk → ℝ) : ∏ k, f k = f .base * (f .det * (f .line0 * f .line1)) := by
  rw [show (Finset.univ : Finset T.WBlk) = {.base, .det, .line0, .line1} from rfl]
  simp

def exXi : HermLine ExY := HermLine.ofMetrics (fun k => fsMetric (ExY k)) T.twoXiDegY

def exAL : HermLine ExY := HermLine.ofMetrics (fun k => fsMetric (ExY k)) (Pi.single T.YBlk.base 1)

theorem exXi_h (w : (Σ k, ExY k) → ℂ) :
    exXi.h w = ‖w ⟨.base, ()⟩‖ ^ 3 * ‖w ⟨.det, ()⟩‖⁻¹ *
      (‖w ⟨.line, Sum.inl ()⟩‖ ^ 2 + ‖w ⟨.line, Sum.inr ()⟩‖ ^ 2)⁻¹ := by
  rw [exXi, ofMetrics_fs_h, prod_YBlk, sumY_base, sumY_det, sumY_line]
  simp only [T.twoXiDegY]
  have h1 : Real.sqrt (‖w ⟨.base, ()⟩‖ ^ 2) = ‖w ⟨.base, ()⟩‖ := Real.sqrt_sq (norm_nonneg _)
  have h2 : Real.sqrt (‖w ⟨.det, ()⟩‖ ^ 2) = ‖w ⟨.det, ()⟩‖ := Real.sqrt_sq (norm_nonneg _)
  have h3 : Real.sqrt (‖w ⟨.line, Sum.inl ()⟩‖ ^ 2 + ‖w ⟨.line, Sum.inr ()⟩‖ ^ 2) ^ (-2 : ℤ) =
      (‖w ⟨.line, Sum.inl ()⟩‖ ^ 2 + ‖w ⟨.line, Sum.inr ()⟩‖ ^ 2)⁻¹ := by
    rw [_root_.zpow_neg, zpow_two, Real.mul_self_sqrt (by positivity)]
  rw [h1, h2, h3]
  simp [_root_.zpow_neg, mul_assoc]

theorem lagrange_identity_complex_two (u0 u1 w0 w1 : ℂ) :
    ‖u0 * w1 - u1 * w0‖ ^ 2 + ‖star u0 * w0 + star u1 * w1‖ ^ 2 =
      (‖u0‖ ^ 2 + ‖u1‖ ^ 2) * (‖w0‖ ^ 2 + ‖w1‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem hermG_one (u w : Unit ⊕ Unit → ℂ) :
    hermG 1 u w = star (u (Sum.inl ())) * w (Sum.inl ()) + star (u (Sum.inr ())) * w (Sum.inr ()) := by
  simp [hermG, dotProduct, Fintype.sum_sum_type, Matrix.one_mulVec]

theorem hermG_one_re (u : Unit ⊕ Unit → ℂ) :
    (hermG 1 u u).re = ‖u (Sum.inl ())‖ ^ 2 + ‖u (Sum.inr ())‖ ^ 2 := by
  rw [hermG_one]
  simp only [Complex.add_re, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

def projLineBundleExample : ProjectiveLineBundle 1 where
  Ω := ℚ
  ι := Unit
  ν := Unit
  κ := Unit ⊕ Unit
  E := Fin 2 → ℚ
  Φ := ExΦ
  x := exX
  B := exBundle
  e := Pi.basisFun ℚ (Fin 2)
  φ := exφ
  δ := fun _ => 1
  a := exA
  dualSec := ex_dualSec
  dualGen := ex_dualGen
  detGen := ex_detGen
  chart := ⟨(), one_ne_zero⟩
  indep := ex_indep
  arithYY := ex_arithYY
  arithWW := ex_arithWW
  G := fun _ => 1
  metric := ex_metric
  n := 0
  g := exg
  h := exh
  g_deg := ex_g_deg
  h_deg := ex_h_deg
  h_nmem := ex_h_nmem
  quot := by
    simp only [exg, exh, map_mul, map_sub, map_pow, aeval_X, ex_wwCoord, exCW, exιR_X, map_one, T.diagSec]
    ring

theorem eval_exg (z : (Σ k, ExW k) → ℂ) :
    eval z (map (Int.castRingHom ℂ) exg) = z ⟨.det, ()⟩ *
      (z ⟨.line0, Sum.inl ()⟩ * z ⟨.line1, Sum.inr ()⟩ - z ⟨.line0, Sum.inr ()⟩ * z ⟨.line1, Sum.inl ()⟩) := by
  simp [exg]

theorem eval_exh (z : (Σ k, ExW k) → ℂ) : eval z (map (Int.castRingHom ℂ) exh) = z ⟨.base, ()⟩ ^ 3 := by
  simp [exh]

theorem norm_sq_heights_eq_sine_sq_example (z : (Σ k, ExW k) → ℂ) (hblk : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ‖eval z (map (Int.castRingHom ℂ) exg)‖ ^ 2 * exXi.h (fun p => z (T.yyEmb 0 p)) *
        exXi.h (fun p => z (T.yyEmb 1 p)) =
      ‖eval z (map (Int.castRingHom ℂ) exh)‖ ^ 2 *
        sinSqG (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) (fun k : Unit ⊕ Unit => z ⟨.line0, k⟩)
          (fun k : Unit ⊕ Unit => z ⟨.line1, k⟩) := by
  have hd : z ⟨.det, ()⟩ ≠ 0 := by
    obtain ⟨i, hi⟩ := hblk .det
    exact hi
  have hU : 0 < ‖z ⟨.line0, Sum.inl ()⟩‖ ^ 2 + ‖z ⟨.line0, Sum.inr ()⟩‖ ^ 2 := by
    obtain ⟨i, hi⟩ := hblk .line0
    rcases i with ⟨⟩ | ⟨⟩
    · have := pow_pos (norm_pos_iff.2 hi) 2
      positivity
    · have := pow_pos (norm_pos_iff.2 hi) 2
      positivity
  have hW : 0 < ‖z ⟨.line1, Sum.inl ()⟩‖ ^ 2 + ‖z ⟨.line1, Sum.inr ()⟩‖ ^ 2 := by
    obtain ⟨i, hi⟩ := hblk .line1
    rcases i with ⟨⟩ | ⟨⟩
    · have := pow_pos (norm_pos_iff.2 hi) 2
      positivity
    · have := pow_pos (norm_pos_iff.2 hi) 2
      positivity
  have hdn : 0 < ‖z ⟨.det, ()⟩‖ := norm_pos_iff.2 hd
  have hL := lagrange_identity_complex_two (z ⟨.line0, Sum.inl ()⟩) (z ⟨.line0, Sum.inr ()⟩) (z ⟨.line1, Sum.inl ()⟩)
    (z ⟨.line1, Sum.inr ()⟩)
  have key : ‖z ⟨.line0, Sum.inl ()⟩ * z ⟨.line1, Sum.inr ()⟩ - z ⟨.line0, Sum.inr ()⟩ * z ⟨.line1, Sum.inl ()⟩‖ ^ 2 =
      (‖z ⟨.line0, Sum.inl ()⟩‖ ^ 2 + ‖z ⟨.line0, Sum.inr ()⟩‖ ^ 2) *
        (‖z ⟨.line1, Sum.inl ()⟩‖ ^ 2 + ‖z ⟨.line1, Sum.inr ()⟩‖ ^ 2) -
      ‖star (z ⟨.line0, Sum.inl ()⟩) * z ⟨.line1, Sum.inl ()⟩ +
        star (z ⟨.line0, Sum.inr ()⟩) * z ⟨.line1, Sum.inr ()⟩‖ ^ 2 := by
    linarith
  rw [eval_exg, eval_exh, exXi_h, exXi_h, sinSqG, hermG_one, hermG_one_re, hermG_one_re]
  simp only [T.yyEmb, if_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false]
  rw [norm_mul, mul_pow, key, norm_pow]
  field_simp

theorem ex_isXi : projLineBundleExample.IsXi exXi :=
  ⟨rfl, isSmoothHerm_ofMetrics_fs _, fun z hz => norm_sq_heights_eq_sine_sq_example z hz.1⟩

theorem ex_fromBase : IsFromBase exAL := by
  refine ⟨by simp [exAL, HermLine.ofMetrics], fun z z' hb hd => ?_⟩
  rw [exAL, ofMetrics_fs_h, ofMetrics_fs_h, prod_YBlk, prod_YBlk, sumY_base, sumY_base]
  simp [hb ()]

theorem segreBlockEmbedding_injective (j : Fin 2) : Function.Injective (diagonalBlockIndex j) := by
  intro a b h
  fin_cases j <;> cases a <;> cases b <;> simp_all [diagonalBlockIndex]

theorem pullDeg_segreBlockEmbedding (j : Fin 2) (c : T.YBlk → ℤ) (k : T.YBlk) :
    I1.pullDeg (diagonalBlockIndex j) c (diagonalBlockIndex j k) = c k :=
  (segreBlockEmbedding_injective j).extend_apply c 0 k

theorem pullDeg_otherLine (j : Fin 2) (c : T.YBlk → ℤ) : I1.pullDeg (diagonalBlockIndex j) c (otherLine j) = 0 := by
  refine Function.extend_apply' _ _ _ ?_
  rintro ⟨k, hk⟩
  fin_cases j <;> cases k <;> simp [diagonalBlockIndex, otherLine] at hk

def exPull (j : Fin 2) (c : T.YBlk → ℤ) : HermLine ExW :=
  HermLine.ofMetrics (fun k => fsMetric (ExW k)) (I1.pullDeg (diagonalBlockIndex j) c)

theorem ex_isPull0 (c : T.YBlk → ℤ) :
    IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) (HermLine.ofMetrics (fun k => fsMetric (ExY k)) c) (exPull 0 c) := by
  refine ⟨rfl, fun z => ?_⟩
  have e1 : I1.pullDeg (diagonalBlockIndex 0) c .base = c .base := pullDeg_segreBlockEmbedding 0 c .base
  have e2 : I1.pullDeg (diagonalBlockIndex 0) c .det = c .det := pullDeg_segreBlockEmbedding 0 c .det
  have e3 : I1.pullDeg (diagonalBlockIndex 0) c .line0 = c .line := pullDeg_segreBlockEmbedding 0 c .line
  have e4 : I1.pullDeg (diagonalBlockIndex 0) c .line1 = 0 := pullDeg_otherLine 0 c
  rw [exPull, ofMetrics_fs_h, ofMetrics_fs_h, prod_WBlk, prod_YBlk, sumW_base, sumW_det, sumW_line0, sumW_line1,
    sumY_base, sumY_det, sumY_line, e1, e2, e3, e4]
  simp [T.yyEmb]

theorem ex_isPull1 (c : T.YBlk → ℤ) :
    IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) (HermLine.ofMetrics (fun k => fsMetric (ExY k)) c) (exPull 1 c) := by
  refine ⟨rfl, fun z => ?_⟩
  have e1 : I1.pullDeg (diagonalBlockIndex 1) c .base = c .base := pullDeg_segreBlockEmbedding 1 c .base
  have e2 : I1.pullDeg (diagonalBlockIndex 1) c .det = c .det := pullDeg_segreBlockEmbedding 1 c .det
  have e3 : I1.pullDeg (diagonalBlockIndex 1) c .line1 = c .line := pullDeg_segreBlockEmbedding 1 c .line
  have e4 : I1.pullDeg (diagonalBlockIndex 1) c .line0 = 0 := pullDeg_otherLine 1 c
  rw [exPull, ofMetrics_fs_h, ofMetrics_fs_h, prod_WBlk, prod_YBlk, sumW_base, sumW_det, sumW_line0, sumW_line1,
    sumY_base, sumY_det, sumY_line, e1, e2, e3, e4]
  simp [T.yyEmb]

theorem setting_inhabited :
    ∃ (S : ProjectiveLineBundle 1) (X A : HermLine S.YIdx) (X₀ X₁ A₀ : HermLine S.WIdx),
      S.IsXi X ∧ IsSmoothHerm A ∧ IsFromBase A ∧
      IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) X X₀ ∧ IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) X X₁ ∧
      IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) A A₀ ∧
      IsSmoothHerm X₀ ∧ IsSmoothHerm X₁ ∧ IsSmoothHerm A₀ :=
  ⟨projLineBundleExample, exXi, exAL, exPull 0 T.twoXiDegY, exPull 1 T.twoXiDegY, exPull 0 (Pi.single T.YBlk.base 1),
    ex_isXi, isSmoothHerm_ofMetrics_fs _, ex_fromBase, ex_isPull0 _, ex_isPull1 _, ex_isPull0 _,
    isSmoothHerm_ofMetrics_fs _, isSmoothHerm_ofMetrics_fs _, isSmoothHerm_ofMetrics_fs _⟩

end Inhabit

end

end GroundTheory.Heights₂.Heights.Inter
