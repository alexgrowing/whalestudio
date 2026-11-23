import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.AdmM
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.SchwartzR2
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Global.AdicLiesOver
open Ad3.R (G2 Jd md KA LInv pri dia2 pt)
open scoped NumberField.AdeleRing ValuativeRel ComplexConjugate

namespace Ad3.K.QuadraticBaseChangeGL3.Th

variable {K : Type} [Field K] [NumberField K]

def GENSL : Prop := ∀ P : GL (Fin 2) ℚ → Prop, P 1 → (∀ (b : ℚ) γ, P γ → P (uni2 b * γ)) →
  (∀ γ' γ : GL (Fin 2) ℚ, γ'.val = !![0, 1; -1, 0] → P γ → P (γ' * γ)) → ∀ γ : GL (Fin 2) ℚ, (γ.val).det = 1 → P γ

variable (K) in

def THN : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (DK : DatK K) c n t S, AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M → ∀ (b : ℚ), ∀ g ∈ Gp M, thP n t M (dia2 (uni2 b) * g) = thP n t M g

variable (K) in

def THW : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (DK : DatK K) c n t S, AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M → ∀ γ' : GL (Fin 2) ℚ, γ'.val = !![0, 1; -1, 0] →
    ∀ g ∈ Gp M, thP n t M (dia2 γ' * g) = thP n t M g

variable (K) in

def THSOF : Prop := GENSL → THN K → THW K → THS K

def LPIF : Prop := GL2LocalData.WRep → GL2LocalData.ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (c : Eˣ →* ℂˣ), ∀ Φ ∈ GL2LocalData.SBc F E c,
  ∀ γ g : GL (Fin 2) F, (γ.val).det = 1 → GL2LocalData.piE E χ σ η c (γ * g) Φ = GL2LocalData.rWE E χ σ η γ.val (GL2LocalData.piE E χ σ η c g Φ)

def LPIS : Prop := GL2LocalData.SRep → GL2LocalData.ForES fun F _ _ _ _ _ _ _ χ => ∀ (c₁ : Fˣ →* ℂˣ), ∀ Φ ∈ GL2LocalData.SBE (F × F),
  ∀ γ g : GL (Fin 2) F, (γ.val).det = 1 → GL2LocalData.piS χ c₁ (γ * g) Φ = GL2LocalData.rWS χ γ.val (GL2LocalData.piS χ c₁ g Φ)

def LPIR : Prop := RWRREP → ∀ (cf : ℂˣ → ℂ), ∀ Φ ∈ SchC, ∀ γ g : GL (Fin 2) ℝ, (γ.val).det = 1 →
  piRc cf (γ * g) Φ = rWRm γ.val (piRc cf g Φ)

def IntB (β : Module.Basis (Fin 2) ℚ K) : Prop := ∀ x : K, IsIntegral ℤ x ↔ ∀ i, ∃ m : ℤ, β.repr x i = m

def gramQ (β : Module.Basis (Fin 2) ℚ K) : Matrix (Fin 2) (Fin 2) ℚ :=
  fun i j => Algebra.trace ℚ K (β i) * Algebra.trace ℚ K (β j) - Algebra.trace ℚ K (β i * β j)

def crd (R : Type) [Field R] [Algebra ℚ R] (β : Module.Basis (Fin 2) ℚ K) (ξ : K) : Fin 2 → R :=
  fun i => algebraMap ℚ R (β.repr ξ i)

def FTbR (M : Matrix (Fin 2) (Fin 2) ℝ) (Φ : (Fin 2 → ℝ) → ℂ) (y : Fin 2 → ℝ) : ℂ :=
  ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((bMR M y x : ℝ) : ℂ)) ∂muMR M

def IntAt (v : Pl) (x : Fin 2 → ℚ) : Prop := ∀ i, algebraMap ℚ (Qv v) (x i) ∈ 𝒪[Qv v]

open Classical in

def CPOIS : Prop := ∀ (M : Matrix (Fin 2) (Fin 2) ℚ), M.IsSymm → M.det ≠ 0 → ∀ S : Finset Pl,
  (∀ v ∉ S, (∀ i j, algebraMap ℚ (Qv v) (M i j) ∈ 𝒪[Qv v]) ∧ (modulus (algebraMap ℚ (Qv v) M.det) : ℝ) = 1) →
  ∀ Fi ∈ schwartzR2, ∀ Fv : ∀ v : S, (Fin 2 → Qv v.1) → ℂ, (∀ v, Fv v ∈ (SBC : Set ((Fin 2 → Qv v.1) → ℂ))) →
    (∑' x : Fin 2 → ℚ, Fi (fun i => (x i : ℝ)) * (∏ v : S, Fv v (fun i => algebraMap ℚ (Qv v.1) (x i))) *
        (if ∀ v ∉ S, IntAt v x then 1 else 0)) =
      ∑' x : Fin 2 → ℚ, FTbR (M.map (algebraMap ℚ ℝ)) Fi (fun i => (x i : ℝ)) *
        (∏ v : S, FTb (GP.psiF v.1)⁻¹ (M.map (algebraMap ℚ (Qv v.1))) (Fv v) (fun i => algebraMap ℚ (Qv v.1) (x i))) *
        (if ∀ v ∉ S, IntAt v x then 1 else 0)

namespace LM
variable {c : HeckeCharacter K} {v : Pl}

def lam : LM c v → ℂ
  | sp .. => 1
  | ns w _ η _ => GL2LocalData.lamE (Kv K w) (GP.psiF v)⁻¹ η

end LM

variable (K) in

def LAMP : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v), AdmM M →
  ∏ᶠ v, (M v).lam = -Complex.I

variable (K) in

def JEX : Prop := Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (d : LM c v), d.ok →
  ∀ β : Module.Basis (Fin 2) ℚ K, IntB β →
  match d with
  | @LM.sp _ _ _ _ _ w₁ w₂ _ _ _ => ∃ j : (Fin 2 → Qv v) ≃ₗ[Qv v] (Qv v × Qv v), Continuous j ∧ Continuous j.symm ∧
      (∀ x, (j x).1 * (j x).2 = nM ((gramQ β).map (algebraMap ℚ (Qv v))) x) ∧
      (∀ x y, Algebra.trace (Qv v) (Qv v × Qv v) (GL2LocalData.swapE (j x) * j y) = bM ((gramQ β).map (algebraMap ℚ (Qv v))) x y) ∧
      Measure.map j (muM (GP.psiF v)⁻¹ ((gramQ β).map (algebraMap ℚ (Qv v)))) = GL2LocalData.muS (GP.psiF v)⁻¹ ∧
      (∀ ξ : K, j (crd (Qv v) β ξ) = (dg1 v w₁ ξ, dg1 v w₂ ξ)) ∧
      ∀ x, (j x).1 ∈ 𝒪[Qv v] ∧ (j x).2 ∈ 𝒪[Qv v] ↔ ∀ i, x i ∈ 𝒪[Qv v]
  | @LM.ns _ _ _ _ _ w _ σ _ _ => ∃ j : (Fin 2 → Qv v) ≃ₗ[Qv v] Kv K w, Continuous j ∧ Continuous j.symm ∧
      (∀ x, Algebra.norm (Qv v) (j x) = nM ((gramQ β).map (algebraMap ℚ (Qv v))) x) ∧
      (∀ x y, Algebra.trace (Qv v) (Kv K w) (σ (j x) * j y) = bM ((gramQ β).map (algebraMap ℚ (Qv v))) x y) ∧
      Measure.map j (muM (GP.psiF v)⁻¹ ((gramQ β).map (algebraMap ℚ (Qv v)))) =
        selfDualMeasure (GL2LocalData.chE (Kv K w) (GP.psiF v)⁻¹) ∧
      (∀ ξ : K, j (crd (Qv v) β ξ) = algebraMap K (Kv K w) ξ) ∧
      ∀ x, j x ∈ 𝒪[Kv K w] ↔ ∀ i, x i ∈ 𝒪[Qv v]

variable (K) in

def JEXR : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ β : Module.Basis (Fin 2) ℚ K,
  ∃ j : (Fin 2 → ℝ) ≃ₗ[ℝ] ℂ, (∀ x, Complex.normSq (j x) = nMR ((gramQ β).map (algebraMap ℚ ℝ)) x) ∧
    (∀ x y, 2 * (conj (j x) * j y).re = bMR ((gramQ β).map (algebraMap ℚ ℝ)) x y) ∧
    Measure.map j (muMR ((gramQ β).map (algebraMap ℚ ℝ))) = volC ∧ ∀ ξ : K, j (crd ℝ β ξ) = embC K ξ

variable (K) in

def IBEX : Prop := Module.finrank ℚ K = 2 → ∃ β : Module.Basis (Fin 2) ℚ K, IntB β

variable (K) in

def THWOF : Prop := LPIF → LPIS → LPIR → GL2LocalData.WRep → GL2LocalData.SRep → RWRREP → GL2LocalData.WSB → TRANS → REPC → RCWF → TRANSR → REPCR →
  CPOIS → LAMP K → JEX K → JEXR K → IBEX K → THW K

end Ad3.K.QuadraticBaseChangeGL3.Th
