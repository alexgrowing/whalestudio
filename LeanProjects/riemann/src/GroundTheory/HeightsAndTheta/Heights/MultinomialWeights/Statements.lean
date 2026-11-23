import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagBasic
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

structure IndexData where
  f : ℕ
  N : ℕ
  j : ℕ
  two_le_N : 2 ≤ N
  one_le_j : 1 ≤ j
  j_lt_N : j < N

namespace IndexData

variable (d : IndexData)

def D : ℕ := RestTerms.topDegree d.f d.N

def n0 : ℕ := d.f * d.N

def TextRange : Prop := 2 < d.f * (d.N - 1)

def jIdx : Fin d.N := ⟨d.j - 1, by have := d.j_lt_N; omega⟩

def jSucc : Fin d.N := ⟨d.j, d.j_lt_N⟩

end IndexData

variable (d : IndexData)

abbrev Idx := Fin d.f × Fin d.N

abbrev Weight := Idx d → ℝ

abbrev LamPoly := MvPolynomial (Idx d) ℝ

abbrev XPoly := RestTerms.RootRing d.f d.N

def lamDotX (u : Idx d → ℚ) : XPoly d := ∑ p : Idx d, C (u p) * X p

def lineClass (u : Idx d → ℚ) : XPoly d := -lamDotX d u

def permWeight {R : Type*} (w : Fin d.f → Equiv.Perm (Fin d.N)) (u : Idx d → R) : Idx d → R :=
  fun p => u (p.1, w p.1 p.2)

abbrev weylL : Subgroup (Equiv.Perm (Idx d)) := antisymWeyl (Fin d.f) d.N d.j

def permAct (σ : Equiv.Perm (Idx d)) (lam : Weight d) : Weight d := fun p => lam (σ.symm p)

def gap (τ : Fin d.f) (lam : Weight d) : ℝ := lam (τ, d.jIdx) - lam (τ, d.jSucc)

def IsCompactStep (a b : Fin d.N) : Prop := b.val = a.val + 1 ∧ b.val ≠ d.j

def IsDominant (lam : Weight d) : Prop :=
  ∀ (τ : Fin d.f) (a b : Fin d.N), b.val = a.val + 1 → 0 ≤ lam (τ, a) - lam (τ, b)

def IsRegular (lam : Weight d) : Prop :=
  ∀ (τ : Fin d.f) (a b : Fin d.N), b.val = a.val + 1 → 0 < lam (τ, a) - lam (τ, b)

def varpi (τ : Fin d.f) : Weight d := fun p => if p.1 = τ ∧ p.2.val < d.j then 1 else 0

def lowerPowerSum (k : ℕ) (τ : Fin d.f) : XPoly d :=
  ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), X (τ, i) ^ k

def upperPowerSum (k : ℕ) (τ : Fin d.f) : XPoly d :=
  ∑ i ∈ univ.filter (fun i : Fin d.N => d.j ≤ i.val), X (τ, i) ^ k

def flagIntegralLin (f N : ℕ) : RestTerms.RootRing f N →ₗ[ℚ] ℚ where
  toFun := RestTerms.flagIntegral f N
  map_add' := RestTerms.Flag.flagIntegral_add f N
  map_smul' c Φ := by
    rw [← C_mul', RestTerms.Flag.flagIntegral_C_mul, RingHom.id_apply, smul_eq_mul]

def flagNormalisation (f N : ℕ) : ℚ :=
  (-1) ^ RestTerms.topDegree f N / (∏ i : Fin N, ((i : ℕ).factorial : ℚ)) ^ f

def intFl : XPoly d →ₗ[ℚ] ℚ := flagNormalisation d.f d.N • flagIntegralLin d.f d.N

def degAt (u : Idx d → ℚ) : ℚ := intFl d (lineClass d u ^ d.D)

def outerDot (σ R : Type*) [CommRing R] [Fintype σ] : MvPolynomial σ (MvPolynomial σ R) :=
  ∑ v : σ, X v * C (X v)

def polarPoly {σ R : Type*} [CommRing R] [Fintype σ] (Φ : MvPolynomial σ R →ₗ[R] R) (n : ℕ) :
    MvPolynomial σ R :=
  ∑ m ∈ ((-outerDot σ R) ^ n).support, monomial m (Φ (coeff m ((-outerDot σ R) ^ n)))

def degPoly : MvPolynomial (Idx d) ℚ := polarPoly (intFl d) d.D

def shiftFl (τ : Fin d.f) (F : XPoly d) : ℚ :=
  intFl d (∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), pderiv (τ, i) F)

def totalFl (τ : Fin d.f) (F : XPoly d) : ℚ :=
  intFl d (∑ i : Fin d.N, pderiv (τ, i) F)

abbrev vSpace : Submodule ℝ (LamPoly d) := antisymSpace (Fin d.f) d.N d.j

def lowerSum (τ : Fin d.f) : LamPoly d :=
  ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), X (τ, i)

def upperSum (τ : Fin d.f) : LamPoly d :=
  ∑ i ∈ univ.filter (fun i : Fin d.N => d.j ≤ i.val), X (τ, i)

def invForms : Submodule ℝ (LamPoly d) :=
  Submodule.span ℝ (Set.range (lowerSum d) ∪ Set.range (upperSum d))

def uSpace : Submodule ℝ (LamPoly d) :=
  (invForms d).map (LinearMap.mulLeft ℝ (antisymDelta (Fin d.f) d.N))

abbrev rootHyperplane (τ : Fin d.f) (a b : Fin d.N) : Set (Weight d) :=
  diagHyperplane (Fin d.f) d.N τ a b

def IsCross (a b : Fin d.N) : Prop := a.val < d.j ∧ d.j ≤ b.val

def HasRelInteriorIn (S H : Set (Weight d)) : Prop :=
  ∃ O : Set (Weight d), IsOpen O ∧ (O ∩ H).Nonempty ∧ O ∩ H ⊆ S

def KSet (τ0 : Fin d.f) (c0 : ℝ) : Set (Weight d) :=
  {lam | ‖lam‖ ≤ 1 / 2 ∧ gap d τ0 lam = 0 ∧ (∀ τ, τ ≠ τ0 → c0 ≤ gap d τ lam) ∧
    ∀ (τ : Fin d.f) (a b : Fin d.N), IsCompactStep d a b → c0 ≤ lam (τ, a) - lam (τ, b)}

def quarterInverseN : ℝ := 1 / (4 * (d.N : ℝ))

def supOn (S : Set (Weight d)) (P : LamPoly d) : ℝ := sSup ((fun x => |eval x P|) '' S)

def IsWallFamily (Om : Fin d.f → Fin d.N → Fin d.N → Set (Weight d)) : Prop :=
  ∀ (τ : Fin d.f) (a b : Fin d.N), IsCross d a b →
    IsCompact (Om τ a b) ∧ Om τ a b ⊆ rootHyperplane d τ a b ∧
      HasRelInteriorIn d (Om τ a b) (rootHyperplane d τ a b)

def wallUnion (Om : Fin d.f → Fin d.N → Fin d.N → Set (Weight d)) : Set (Weight d) :=
  {x | ∃ (τ : Fin d.f) (a b : Fin d.N), IsCross d a b ∧ x ∈ Om τ a b}

def DegVanishesOnWall.Statement : Prop :=
  ∀ (d : IndexData) (u : Idx d → ℚ) (τ : Fin d.f) (a b : Fin d.N), b.val = a.val + 1 →
    u (τ, a) = u (τ, b) → degAt d u = 0

def DegAntisym.Statement : Prop :=
  ∀ (d : IndexData) (w : Fin d.f → Equiv.Perm (Fin d.N)) (u : Idx d → ℚ),
    degAt d (permWeight d w u) = RestTerms.blockSign d.f d.N w * degAt d u

def DegPolyEval.Statement : Prop :=
  ∀ (d : IndexData) (u : Idx d → ℚ), eval u (degPoly d) = degAt d u

def DelDividesDeg.Statement : Prop :=
  ∀ d : IndexData, RestTerms.blockVandermonde d.f d.N ∣ degPoly d

def DegEqConstDel.Statement : Prop :=
  ∀ d : IndexData, ∃ c : ℚ, degPoly d = C c * RestTerms.blockVandermonde d.f d.N

def CFlPos.Statement : Prop :=
  ∀ d : IndexData, ∃ c : ℚ, 0 < c ∧ degPoly d = C c * RestTerms.blockVandermonde d.f d.N

def ShFormula.Statement : Prop :=
  ∀ (d : IndexData) (τ : Fin d.f) (F : XPoly d) (Q : ℕ → Fin d.f → XPoly d),
    F.IsHomogeneous (d.D + 1) →
    (∀ k ∈ Icc 1 d.N, ∀ τ' : Fin d.f, (Q k τ').IsHomogeneous (d.D + 1 - k)) →
    RestTerms.IsPowerSumDecomposition d.f d.N F Q →
    shiftFl d τ F = ∑ k ∈ Icc 1 d.N, (k : ℚ) * intFl d (lowerPowerSum d (k - 1) τ * Q k τ)

def TotFormula.Statement : Prop :=
  ∀ (d : IndexData) (τ : Fin d.f) (F : XPoly d) (Q : ℕ → Fin d.f → XPoly d),
    F.IsHomogeneous (d.D + 1) →
    (∀ k ∈ Icc 1 d.N, ∀ τ' : Fin d.f, (Q k τ').IsHomogeneous (d.D + 1 - k)) →
    RestTerms.IsPowerSumDecomposition d.f d.N F Q →
    totalFl d τ F = (d.N : ℚ) * intFl d (Q 1 τ)

def ShOfPower.Statement : Prop :=
  ∀ (d : IndexData) (τ : Fin d.f) (u : Idx d → ℚ),
    shiftFl d τ (lineClass d u ^ (d.D + 1)) =
      -((d.D + 1 : ℕ) : ℚ) * degAt d u * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), u (τ, i)

def TotOfPower.Statement : Prop :=
  ∀ (d : IndexData) (τ : Fin d.f) (u : Idx d → ℚ),
    totalFl d τ (lineClass d u ^ (d.D + 1)) = -((d.D + 1 : ℕ) : ℚ) * degAt d u * ∑ i : Fin d.N, u (τ, i)

def PolarisationCoeff.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Φ : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (n : ℕ) (m : σ →₀ ℕ),
    (m.sum fun _ e => e) = n →
    Φ (monomial m 1) =
      (-1) ^ n * ((m.prod fun _ e => (e.factorial : ℝ)) / (n.factorial : ℝ)) * coeff m (polarPoly Φ n)

def PolarisationBound.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (n : ℕ),
    (∀ Φ Ψ : MvPolynomial σ ℝ →ₗ[ℝ] ℝ, polarPoly Φ n = polarPoly Ψ n →
      ∀ F : MvPolynomial σ ℝ, F.IsHomogeneous n → Φ F = Ψ F) ∧
    ∀ (Φ : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (m : σ →₀ ℕ) (M : ℝ), (m.sum fun _ e => e) = n →
      (∀ m' : σ →₀ ℕ, |coeff m' (polarPoly Φ n)| ≤ M) → |Φ (monomial m 1)| ≤ M

def ULiesInV.Statement : Prop :=
  ∀ d : IndexData, uSpace d ≤ vSpace d

def PolyVanishesOnHyperplane.Statement : Prop :=
  ∀ (d : IndexData) (P : LamPoly d) (τ : Fin d.f) (a b : Fin d.N), a ≠ b →
    (∃ O : Set (Weight d), IsOpen O ∧ (O ∩ rootHyperplane d τ a b).Nonempty ∧
      ∀ x ∈ O ∩ rootHyperplane d τ a b, eval x P = 0) →
    ∀ x ∈ rootHyperplane d τ a b, eval x P = 0

def DivisibleByRootForm.Statement : Prop :=
  ∀ (d : IndexData) (P : LamPoly d) (τ : Fin d.f) (a b : Fin d.N), a ≠ b →
    (∀ x ∈ rootHyperplane d τ a b, eval x P = 0) → (X (τ, a) - X (τ, b) : LamPoly d) ∣ P

def CompactRootVanishes.Statement : Prop :=
  ∀ (d : IndexData) (P : LamPoly d), P ∈ vSpace d →
    ∀ (τ : Fin d.f) (a b : Fin d.N), a < b → (a.val < d.j ↔ b.val < d.j) →
      ∀ x ∈ rootHyperplane d τ a b, eval x P = 0

def DelDividesV.Statement : Prop :=
  ∀ (d : IndexData) (P : LamPoly d),
    (∀ (τ : Fin d.f) (a b : Fin d.N), a < b → (X (τ, a) - X (τ, b) : LamPoly d) ∣ P) →
    antisymDelta (Fin d.f) d.N ∣ P

def QuotientLinear.Statement : Prop :=
  ∀ (d : IndexData) (P l : LamPoly d), P ∈ vSpace d → P = antisymDelta (Fin d.f) d.N * l →
    l ∈ antisymInv (Fin d.f) d.N d.j

def InvariantLinearForm.Statement : Prop :=
  ∀ d : IndexData, antisymInv (Fin d.f) d.N d.j = invForms d

def VInUOfVanish.Statement : Prop :=
  ∀ (d : IndexData) (P : LamPoly d), P ∈ vSpace d →
    (∀ (τ : Fin d.f) (a b : Fin d.N), IsCross d a b →
      ∃ O : Set (Weight d), IsOpen O ∧ (O ∩ rootHyperplane d τ a b).Nonempty ∧
        ∀ x ∈ O ∩ rootHyperplane d τ a b, eval x P = 0) →
    P ∈ uSpace d

def SeminormOnV.Statement : Prop :=
  ∀ (d : IndexData) (Om : Fin d.f → Fin d.N → Fin d.N → Set (Weight d)), IsWallFamily d Om →
    ∃ s : Seminorm ℝ (vSpace d), ∀ P : vSpace d, s P = supOn d (wallUnion d Om) (P : LamPoly d)

def SeminormKernel.Statement : Prop :=
  ∀ (d : IndexData) (Om : Fin d.f → Fin d.N → Fin d.N → Set (Weight d)), IsWallFamily d Om →
    ∀ P ∈ vSpace d, (supOn d (wallUnion d Om) P = 0 ↔ P ∈ uSpace d)

def NormEquivalence.Statement : Prop :=
  ∀ (d : IndexData) (Om : Fin d.f → Fin d.N → Fin d.N → Set (Weight d)), IsWallFamily d Om →
    ∀ V' : Submodule ℝ (LamPoly d), V' ≤ vSpace d → Disjoint (uSpace d) V' →
      ∃ C : ℝ, ∀ P ∈ V', ∀ m, |coeff m P| ≤ C * supOn d (wallUnion d Om) P

def DecompositionBound.Statement : Prop :=
  ∀ (d : IndexData) (Om : Fin d.f → Fin d.N → Fin d.N → Set (Weight d)), IsWallFamily d Om →
    ∀ V' : Submodule ℝ (LamPoly d), V' ≤ vSpace d → Disjoint (uSpace d) V' →
      uSpace d ⊔ V' = vSpace d →
      ∃ C : ℝ, ∀ P ∈ vSpace d, ∃ l ∈ invForms d, ∃ P' ∈ V',
        P = antisymDelta (Fin d.f) d.N * l + P' ∧
          ∀ m, |coeff m P'| ≤ C * supOn d (wallUnion d Om) P

def KNonemptyInterior.Statement : Prop :=
  ∀ (d : IndexData) (τ0 : Fin d.f),
    HasRelInteriorIn d (KSet d τ0 (quarterInverseN d)) (rootHyperplane d τ0 d.jIdx d.jSucc)

def KRationalDense.Statement : Prop :=
  ∀ (d : IndexData) (τ0 : Fin d.f) (c0 : ℚ), 0 < c0 → c0 ≤ 1 →
    KSet d τ0 c0 ⊆ closure (KSet d τ0 c0 ∩ {lam | ∀ p, ∃ q : ℚ, lam p = q})

def KTransport.Statement : Prop :=
  ∀ (d : IndexData) (τ : Fin d.f) (a b : Fin d.N), IsCross d a b →
    ∃ σ ∈ weylL d, σ (τ, d.jIdx) = (τ, a) ∧ σ (τ, d.jSucc) = (τ, b) ∧
      IsCompact (permAct d σ '' KSet d τ (quarterInverseN d)) ∧
      permAct d σ '' KSet d τ (quarterInverseN d) ⊆ rootHyperplane d τ a b ∧
      HasRelInteriorIn d (permAct d σ '' KSet d τ (quarterInverseN d)) (rootHyperplane d τ a b) ∧
      ∀ R ∈ vSpace d, ∀ lam : Weight d, |eval (permAct d σ lam) R| = |eval lam R|

abbrev d1 : IndexData := ⟨1, 2, 1, le_rfl, le_rfl, by norm_num⟩

abbrev d2 : IndexData := ⟨1, 3, 2, by norm_num, by norm_num, by norm_num⟩

theorem textRange_inhabited : (⟨3, 2, 1, le_rfl, le_rfl, by norm_num⟩ : IndexData).TextRange := by
  show 2 < 3 * (2 - 1)
  norm_num

theorem rankTwo_D : d1.D = 1 := rfl

theorem DegVanishesOnWall.hypotheses_inhabited :
    ∃ (u : Idx d1 → ℚ) (a b : Fin d1.N), b.val = a.val + 1 ∧ u (0, a) = u (0, b) :=
  ⟨fun _ => 1, ⟨0, by norm_num⟩, ⟨1, by norm_num⟩, rfl, rfl⟩

def sampleQ : ℕ → Fin d1.f → XPoly d1 := fun k τ => if k = 1 then X (τ, ⟨0, by norm_num⟩) else 0

def sampleF : XPoly d1 := ∑ k ∈ Icc 1 d1.N, ∑ τ : Fin d1.f, RestTerms.blockPowerSum d1.f d1.N k τ * sampleQ k τ

theorem blockPowerSum_isHomogeneous (f N k : ℕ) (τ : Fin f) :
    (RestTerms.blockPowerSum f N k τ).IsHomogeneous k := by
  unfold RestTerms.blockPowerSum
  exact IsHomogeneous.sum _ _ _ (fun i _ => by simpa using (isHomogeneous_X ℚ (τ, i)).pow k)

theorem ShFormula.hypotheses_inhabited :
    sampleF ≠ 0 ∧ sampleF.IsHomogeneous (d1.D + 1) ∧
      (∀ k ∈ Icc 1 d1.N, ∀ τ' : Fin d1.f, (sampleQ k τ').IsHomogeneous (d1.D + 1 - k)) ∧
      RestTerms.IsPowerSumDecomposition d1.f d1.N sampleF sampleQ := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · intro h
    have h1 := congrArg (eval (fun _ => (1 : ℚ))) h
    have hI : Icc 1 d1.N = {1, 2} := by decide
    simp [sampleF, sampleQ, hI, RestTerms.blockPowerSum] at h1
  · apply IsHomogeneous.sum
    intro k _
    apply IsHomogeneous.sum
    intro τ _
    by_cases hk : k = 1
    · subst hk
      simp only [sampleQ, if_true]
      exact (blockPowerSum_isHomogeneous _ _ 1 τ).mul (isHomogeneous_X ℚ _)
    · simp only [sampleQ, if_neg hk, mul_zero]
      exact isHomogeneous_zero _ _ _
  · intro k _ τ
    by_cases hk : k = 1
    · subst hk
      simp only [sampleQ, if_true]
      exact isHomogeneous_X ℚ _
    · simp only [sampleQ, if_neg hk]
      exact isHomogeneous_zero _ _ _

theorem exists_coeff_bound {σ : Type*} (P : MvPolynomial σ ℝ) : ∃ M : ℝ, ∀ m, |coeff m P| ≤ M := by
  refine ⟨∑ m ∈ P.support, |coeff m P|, fun m => ?_⟩
  by_cases hm : m ∈ P.support
  · exact Finset.single_le_sum (f := fun m => |coeff m P|) (fun _ _ => abs_nonneg _) hm
  · rw [notMem_support_iff.1 hm, abs_zero]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem PolarisationBound.hypotheses_inhabited (Φ : MvPolynomial (Fin 1) ℝ →ₗ[ℝ] ℝ) :
    ((Finsupp.single (0 : Fin 1) 1).sum fun _ e => e) = 1 ∧
      ∃ M : ℝ, ∀ m', |coeff m' (polarPoly Φ 1)| ≤ M :=
  ⟨Finsupp.sum_single_index rfl, exists_coeff_bound _⟩

theorem PolyVanishesOnHyperplane.hypotheses_inhabited :
    let a : Fin d1.N := ⟨0, by norm_num⟩
    let b : Fin d1.N := ⟨1, by norm_num⟩
    a ≠ b ∧
      (∃ O : Set (Weight d1), IsOpen O ∧ (O ∩ rootHyperplane d1 0 a b).Nonempty ∧
        ∀ x ∈ O ∩ rootHyperplane d1 0 a b, eval x (X (0, a) - X (0, b) : LamPoly d1) = 0) ∧
      ∀ x ∈ rootHyperplane d1 0 a b, eval x (X (0, a) - X (0, b) : LamPoly d1) = 0 := by
  intro a b
  have hv : ∀ x ∈ rootHyperplane d1 0 a b, eval x (X (0, a) - X (0, b) : LamPoly d1) = 0 := by
    intro x hx
    have hx' : x (0, a) = x (0, b) := hx
    simp [hx']
  refine ⟨by decide, ⟨Set.univ, isOpen_univ, ⟨0, Set.mem_univ _, ?_⟩, fun x hx => hv x hx.2⟩, hv⟩
  show (0 : Weight d1) (0, a) = (0 : Weight d1) (0, b)
  rfl

theorem DelDividesV.hypotheses_inhabited (d : IndexData) :
    ∀ (τ : Fin d.f) (a b : Fin d.N), a < b →
      (X (τ, a) - X (τ, b) : LamPoly d) ∣ antisymDelta (Fin d.f) d.N := by
  intro τ a b hab
  unfold antisymDelta
  exact ((Finset.dvd_prod_of_mem (fun b => (X (τ, a) - X (τ, b) : LamPoly d))
    (Finset.mem_Ioi.2 hab)).trans (Finset.dvd_prod_of_mem
      (fun a => ∏ b ∈ Finset.Ioi a, (X (τ, a) - X (τ, b) : LamPoly d)) (Finset.mem_univ a))).trans
    (Finset.dvd_prod_of_mem
      (fun τ => ∏ a : Fin d.N, ∏ b ∈ Finset.Ioi a, (X (τ, a) - X (τ, b) : LamPoly d))
      (Finset.mem_univ τ))

theorem CompactRootVanishes.hypotheses_inhabited :
    antisymSample ∈ vSpace d2 ∧ antisymSample ≠ 0 ∧
      ((⟨0, by norm_num⟩ : Fin d2.N) < ⟨1, by norm_num⟩ ∧ (0 < d2.j ↔ 1 < d2.j)) ∧
      antisymSample = antisymDelta (Fin d2.f) d2.N * ∑ p : Idx d2, X p ∧
      ∀ (τ : Fin d2.f) (a b : Fin d2.N), IsCross d2 a b →
        ∃ O : Set (Weight d2), IsOpen O ∧ (O ∩ rootHyperplane d2 τ a b).Nonempty ∧
          ∀ x ∈ O ∩ rootHyperplane d2 τ a b, eval x (antisymSample : LamPoly d2) = 0 := by
  refine ⟨antisymSample_mem.1, antisymSample_mem.2, ⟨by decide, by decide⟩, rfl, ?_⟩
  intro τ a b hab
  exact antisymDelta_mul_vanishes (Fin 1) 3 2 _ τ a b hab.1 hab.2

theorem isClosed_rootHyperplane (τ : Fin d.f) (a b : Fin d.N) : IsClosed (rootHyperplane d τ a b) :=
  isClosed_eq (continuous_apply _) (continuous_apply _)

def unitWallFamily : Fin d.f → Fin d.N → Fin d.N → Set (Weight d) :=
  fun τ a b => Metric.closedBall 0 1 ∩ rootHyperplane d τ a b

theorem unitWallFamily_isWallFamily : IsWallFamily d (unitWallFamily d) := by
  intro τ a b _
  refine ⟨(isCompact_closedBall 0 1).inter_right (isClosed_rootHyperplane d τ a b),
    Set.inter_subset_right, Metric.ball 0 1, Metric.isOpen_ball,
    ⟨0, Metric.mem_ball_self one_pos, ?_⟩, ?_⟩
  · show (0 : Weight d) (τ, a) = (0 : Weight d) (τ, b)
    rfl
  · exact Set.inter_subset_inter_left _ Metric.ball_subset_closedBall

theorem exists_complement_of_le {M : Type*} [AddCommGroup M] [Module ℝ M] {U V : Submodule ℝ M}
    (h : U ≤ V) : ∃ V' : Submodule ℝ M, V' ≤ V ∧ Disjoint U V' ∧ U ⊔ V' = V := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (U.comap V.subtype)
  refine ⟨q.map V.subtype, Submodule.map_subtype_le _ _, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxU hxV'
    obtain ⟨y, hyq, rfl⟩ := Submodule.mem_map.1 hxV'
    have hyp : y ∈ U.comap V.subtype := Submodule.mem_comap.2 hxU
    have hy0 : y = 0 := (Submodule.disjoint_def.1 hq.disjoint) y hyp hyq
    simp [hy0]
  · refine le_antisymm (sup_le h (Submodule.map_subtype_le _ _)) ?_
    intro x hx
    have htop : (⟨x, hx⟩ : V) ∈ U.comap V.subtype ⊔ q := by
      rw [hq.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 htop
    have e : (y : M) + (z : M) = x := by simpa using congrArg Subtype.val hyz
    rw [← e]
    exact Submodule.add_mem_sup (Submodule.mem_comap.1 hy) (Submodule.mem_map_of_mem hz)

theorem antisymDelta_rankTwo : antisymDelta (Fin d1.f) d1.N = (X (0, 0) - X (0, 1) : LamPoly d1) := by
  have h0 : Finset.Ioi (0 : Fin 2) = {1} := by decide
  have h1 : Finset.Ioi (1 : Fin 2) = ∅ := by decide
  simp [antisymDelta, Fin.prod_univ_two, h0, h1]

theorem invForms_le_homogeneous : invForms d ≤ homogeneousSubmodule (Idx d) ℝ 1 := by
  rw [invForms, Submodule.span_le]
  rintro P (⟨τ, rfl⟩ | ⟨τ, rfl⟩)
  · exact (mem_homogeneousSubmodule _ _).2
      (IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_X ℝ _))
  · exact (mem_homogeneousSubmodule _ _).2
      (IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_X ℝ _))

theorem uSpace_le_vSpace_rankTwo : uSpace d1 ≤ vSpace d1 := by
  intro P hP
  obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.1 hP
  have hl1 : l.IsHomogeneous 1 := (mem_homogeneousSubmodule _ _).1 (invForms_le_homogeneous d1 hl)
  refine ⟨?_, ?_⟩
  · rw [mem_homogeneousSubmodule]
    have hdeg : antisymDegree (Fin d1.f) d1.N + 1 = 1 + 1 := by decide
    rw [hdeg, LinearMap.mulLeft_apply, antisymDelta_rankTwo]
    exact ((isHomogeneous_X ℝ _).sub (isHomogeneous_X ℝ _)).mul hl1
  · rintro σ ⟨τ, a, b, hab, hblk, -⟩
    exfalso
    have ha : a.val < 2 := a.isLt
    have hb : b.val < 2 := b.isLt
    have hblk' : b.val < 1 ∨ 1 ≤ a.val := hblk
    omega

theorem DecompositionBound.hypotheses_inhabited :
    IsWallFamily d1 (unitWallFamily d1) ∧
      ∃ V' : Submodule ℝ (LamPoly d1), V' ≤ vSpace d1 ∧ Disjoint (uSpace d1) V' ∧
        uSpace d1 ⊔ V' = vSpace d1 :=
  ⟨unitWallFamily_isWallFamily d1, exists_complement_of_le uSpace_le_vSpace_rankTwo⟩

theorem zero_mem_KSet_rankTwo : (0 : Weight d1) ∈ KSet d1 0 (quarterInverseN d1) := by
  refine ⟨by rw [norm_zero]; norm_num, by simp [gap], ?_, ?_⟩
  · intro τ hτ
    exact absurd (Subsingleton.elim τ 0) hτ
  · rintro τ a b ⟨hab, hbj⟩
    exfalso
    have hb : b.val < 2 := b.isLt
    have hbj' : b.val ≠ 1 := hbj
    omega

theorem KRationalDense.hypotheses_inhabited : (0 : ℚ) < 1 / 2 ∧ (1 / 2 : ℚ) ≤ 1 := by norm_num

end GroundTheory.Heights₂.Heights.TheoremB
