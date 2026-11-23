import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CMCurveCharacterAction
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmEllipticCurveIntegersWithPeriod
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmActionPolarisedCurveAdjointConj
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersSqrtNegThreeModFour
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingSmul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolUnifReparam
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeLineBundleAdjointIffHermFormAdjoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointEndomorphismsCubeLBOfDenseFibres
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj UpperHalfPlane
open GlobalTheory.IndefiniteRowSideFullHecke.LegendreCharacterCMCurves

namespace GlobalTheory.CMCurveCompare

section Fibre

variable {R R' : Type} [CommRing R] [CommRing R']

def pullPol (P : Out.PolAV (Sp R)) (hg : P.g = 1) {s : R →+* R'} {A : Over (Sp R')} [GrpObj A]
    {φ : A.left ⟶ P.A.left} (h : IsGrpPullback A P.A (spMap s) φ) : Out.PolAV (Sp R') :=
  have hL := pull_isLB P.isLB φ
  have H := pol_pull _ _ P.A A _ φ P.L _ P.isLB hL P.isAb h (PolBaseChange.lbIso_refl hL)
  { A := A, isAb := H.1, g := 1
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 (hg ▸ P.smoothDim)
    L := P.L.pull φ, isLB := hL, rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym, ample := H.2.1 P.ample, ktriv := H.2.2 P.ktriv }

theorem exists_unif (P : Out.PolAV (Sp R)) (hg : P.g = 1) (s : R →+* ℂ) :
    ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.A.left) (u : HolUnif A (P.L.pull φ) 1)
      (Hm : Matrix (Fin 1) (Fin 1) ℂ) (χ : u.Λ → ℂ), IsGrpPullback A P.A (spMap s) φ ∧ u.IsAH Hm χ := by
  obtain ⟨Q, φ, -, h, -⟩ := exists_isPolFibre polBaseChange_holds s P
  obtain ⟨rig, hr⟩ := (pullPol P hg h).rigid
  obtain ⟨u, Hm, χ, -, hA, -⟩ := thetaUnifAV_all (pullPol P hg h) rig hr
  exact ⟨Q.A, inferInstance, φ, u, Hm, χ, h, hA⟩

theorem isLieComb_one_iff {G : Over (Sp R)} [GrpObj G] (c : R) (v w : epsR R ⟶ G) :
    IsLieComb ![c] ![v] w ↔ w.left = spMap (epsScaleR c) ≫ v.left := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy 0
  · intro h
    exact ⟨![w], fun i => by fin_cases i; exact h, by simp⟩

theorem isLieNormSq_unique {P : Out.PolAV (Sp R)} {v : epsR R ⟶ P.A} (hv : IsTangent v) {s : R →+* ℂ} {x y : ℝ}
    (hx : IsLieNormSq P v s x) (hy : IsLieNormSq P v s y) : y = x := by
  have h1 : IsLieComb ![(1 : R)] ![v] (v ≫ 𝟙 P.A) := by
    rw [isLieComb_one_iff, Category.comp_id]
    have e : epsScaleR (1 : R) = RingHom.id _ := by
      ext a <;> simp [epsScaleR]
    rw [e]
    exact ((congrArg (· ≫ v.left) (Spec.map_id (CommRingCat.of (DualNumber R)))).trans (Category.id_comp _)).symm
  have e := NormHom.lieNormSq_comp thetaUnifAV_all T.abelianScheme_laws_unconditional.1 R P P (𝟙 P.A) (𝟙 P.A) v 1 s x y inferInstance
    inferInstance (PolBaseChange.lbIso_refl (LB.isLB_linComb P.isLB _ _)) hv h1 hx (by rwa [Category.comp_id])
  simpa using e

variable {P : Out.PolAV (Sp R)} {s : R →+* ℂ} {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ P.A.left}

end Fibre

section Line

theorem exists_scaled {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L 1)
    {Hm : Matrix (Fin 1) (Fin 1) ℂ} {χ : u.Λ → ℂ} (hA : u.IsAH Hm χ) {c : ℂ} (hc : c ≠ 0) :
    ∃ (u' : HolUnif A L 1) (Hm' : Matrix (Fin 1) (Fin 1) ℂ) (χ' : u'.Λ → ℂ), u'.IsAH Hm' χ' ∧
      ∀ z, z ∈ u'.Λ ↔ c • z ∈ u.Λ := by
  have e : ∀ z w : Fin 1 → ℂ, z ⬝ᵥ ((c * starRingEnd ℂ c) • Hm).mulVec (star w) =
      (c • z) ⬝ᵥ Hm.mulVec (star (c • w)) := fun z w => by
    simp [Matrix.mulVec, dotProduct]
    ring
  refine ⟨holUnifReparam u (LinearEquiv.smulOfNeZero ℂ _ c hc) 1 (differentiable_const _) fun _ => one_ne_zero,
    (c * starRingEnd ℂ c) • Hm, fun l => χ ⟨c • l.1, l.2⟩, ⟨?_, fun z hz => ?_, fun l => hA.2.2.1 _,
      fun l i z hz => ?_⟩, fun _ => Iff.rfl⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hA.1.eq]
    simp [mul_comm]
  · rw [e]
    exact hA.2.1 _ (smul_ne_zero hc hz)
  · rw [e, e]
    change u.fr i (c • z) / 1 = _ * (u.fr i (c • (z + l.1)) / 1)
    rw [div_one, div_one, smul_add]
    exact hA.2.2.2 ⟨c • l.1, l.2⟩ i _ hz

end Line

theorem zpow_identity {A : Type*} [CommGroup A] (i w : A) (k m n m' n' : ℤ) :
    i ^ (m * m' + (-k) * n * n') * w ^ (m * n' + n * m' + n * n') =
      (i ^ m * w ^ n) ^ m' * (w ^ m * (w * i ^ (-k)) ^ n) ^ n' := by
  simp only [mul_zpow, ← zpow_mul, zpow_add]
  ac_rfl

theorem exists_oAct {O : Type} [CommRing O] {ω : O} {k : ℕ} (hsq : ω ^ 2 + k = ω)
    (hco : ∀ a : O, ∃! p : ℤ × ℤ, a = p.1 + p.2 * ω) {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    {W : G ⟶ G} (hW : IsMonHom W) (hEq : (W ≫ W) * (𝟙 G) ^ k = W) : ∃ a : OAct O G, a.act ω = W := by
  choose c hc hcu using hco
  have hcoord : ∀ m n : ℤ, c ((m : O) + (n : O) * ω) = (m, n) := fun m n => (hcu _ (m, n) rfl).symm
  have hWW : W ≫ W = W * (𝟙 G) ^ (-(k : ℤ)) := by
    rw [zpow_neg, zpow_natCast, eq_mul_inv_iff_mul_eq]
    exact hEq
  let F : O → (G ⟶ G) := fun a => (𝟙 G) ^ (c a).1 * W ^ (c a).2
  have hF : ∀ m n : ℤ, F ((m : O) + (n : O) * ω) = (𝟙 G) ^ m * W ^ n := fun m n => by
    simp only [F, hcoord]
  have hex : ∀ a : O, ∃ m n : ℤ, a = (m : O) + (n : O) * ω := fun a => ⟨_, _, hc a⟩
  refine ⟨⟨F, fun a => ?_, ?_, fun a b => ?_, fun a b => ?_⟩, ?_⟩
  · have h1 := Serre.isMonHom_zpow (𝟙 G) (c a).1
    have h2 := Serre.isMonHom_zpow W (c a).2
    exact Serre.isMonHom_mul _ _
  · simpa using hF 1 0
  · obtain ⟨m, n, rfl⟩ := hex a
    obtain ⟨m', n', rfl⟩ := hex b
    have e : ((m : O) + (n : O) * ω) * ((m' : O) + (n' : O) * ω) =
        ((m * m' + (-(k : ℤ)) * n * n' : ℤ) : O) + ((m * n' + n * m' + n * n' : ℤ) : O) * ω := by
      push_cast
      linear_combination ((n : O) * (n' : O)) * hsq
    rw [e, hF, hF, hF]
    simp only [MonObj.comp_mul, GrpObj.comp_zpow, MonObj.mul_comp, GrpObj.zpow_comp, Category.comp_id,
      Category.id_comp, hWW]
    exact zpow_identity _ _ _ _ _ _ _
  · obtain ⟨m, n, rfl⟩ := hex a
    obtain ⟨m', n', rfl⟩ := hex b
    have e : ((m : O) + (n : O) * ω) + ((m' : O) + (n' : O) * ω) =
        ((m + m' : ℤ) : O) + ((n + n' : ℤ) : O) * ω := by
      push_cast
      ring
    rw [e, hF, hF, hF, zpow_add, zpow_add]
    exact mul_mul_mul_comm _ _ _ _
  · simpa using hF 0 1

section Clauses

def IsEtaMean (K : Type) [Field K] [NumberField K] (x : ℝ) : Prop :=
  ∀ (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ), (∀ C, IsIdealClassPoint σ C (τ C)) →
    (∑ C, Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K = x

def IsEtaCurve (d : ℕ) (K : Type) [Field K] [NumberField K] (M : IntermediateField ℚ ℂ) [NumberField M] (w : M)
    (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) : Prop :=
  (w : ℂ) = (1 + Complex.I * √d) / 2 ∧ P.g = 1 ∧ IsLieBasis ![v] ∧
    (∃ (P₀ : Out.PolAV (Sp M)) (φ : P₀.A.left ⟶ P.A.left) (v₀ : epsR M ⟶ P₀.A) (W : P₀.A ⟶ P₀.A),
      IsPolFibre (algebraMap (𝓞 M) M) P P₀ φ ∧ IsVecOver (algebraMap (𝓞 M) M) φ v v₀ ∧ IsLieBasis ![v₀] ∧
      IsMonHom W ∧ (W ≫ W) * (𝟙 P₀.A) ^ ((1 + d) / 4) = W ∧ IsLieComb ![w] ![v₀] (v₀ ≫ W)) ∧
    (∀ (P' : Out.PolAV (Sp ℂ)) (φ : P'.A.left ⟶ P.A.left),
      IsPolFibre ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) P P' φ → ∀ u : HolUnif P'.A P'.L P'.g,
      ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ u.Λ ↔ ∃ m n : ℤ, z = fun _ => c * (m + n * (w : ℂ))) ∧
    (∀ s : M →+* ℂ, ∃ r : ℝ, 0 < r ∧ ∀ r', IsLieNormSq P v (s.comp (algebraMap (𝓞 M) M)) r' ↔ r' = r) ∧
    ∀ n : (M →+* ℂ) → ℝ, (∀ s, IsLieNormSq P v (s.comp (algebraMap (𝓞 M) M)) (n s)) →
    ∀ (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ), (∀ C, IsIdealClassPoint σ C (τ C)) →
      (∑ s, Real.log (n s)) / Module.finrank ℚ M =
        (∑ C, -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K

def EtaCurve (d : ℕ) (K : Type) [Field K] [NumberField K] : Prop :=
  ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (w : M) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A),
    IsEtaCurve d K M w P v

def ActCurve (d : ℕ) {K : Type} [Field K] (τ : K →+* ℂ) (x : ℝ) : Prop :=
  ∃ (M : Type) (_ : Field M) (_ : NumberField M) (P : Out.PolAV (Sp (𝓞 M))) (act : OAct (𝓞 K) P.A)
    (ρ : 𝓞 K →+* 𝓞 M) (v : epsR (𝓞 M) ⟶ P.A), IsCMCurve d τ x M P act ρ v

end Clauses

section Compare

variable {d : ℕ} {K : Type} [Field K] [NumberField K]

theorem exists_generator (hs : Squarefree d) (h4 : d % 4 = 3) (h2 : Module.finrank ℚ K = 2) {rt : K}
    (hr : rt ^ 2 = -(d : K)) {τ : K →+* ℂ} (hτ : τ rt = Complex.I * (Real.sqrt d : ℝ)) :
    ∃ ω : 𝓞 K, τ (ω : K) = (1 + Complex.I * √d) / 2 ∧ ω ^ 2 + ((1 + d) / 4 : ℕ) = ω ∧
      (∀ a : 𝓞 K, ∃! p : ℤ × ℤ, a = p.1 + p.2 * ω) ∧ ∀ Λ : Submodule ℤ (Fin 1 → ℂ),
        PureType.IsQuadLattice Λ d 1 ↔ ∀ z : Fin 1 → ℂ, z ∈ Λ ↔ ∃ a : 𝓞 K, z 0 = τ (a : K) := by
  obtain ⟨ω, hω, hgen⟩ := exists_integer_generator_of_sq_eq_neg h2 hs h4 hr
  have h1 : τ (ω : K) = (1 + Complex.I * √d) / 2 := by
    have := congrArg τ hω
    rw [map_mul, map_add, map_one, map_ofNat, hτ] at this
    linear_combination this / 2
  have hd' : (0 : ℝ) < √d := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < d))
  have hc : ∀ m n : ℤ, τ (((m : 𝓞 K) + n * ω : 𝓞 K) : K) = m + n * ((1 + Complex.I * √d) / 2) := fun m n => by
    rw [← h1]
    simp
  refine ⟨ω, h1, ?_, fun a => ?_, fun Λ => forall_congr' fun z => iff_congr Iff.rfl ⟨?_, ?_⟩⟩
  · obtain ⟨k, rfl⟩ : ∃ k, d = 4 * k + 3 := ⟨d / 4, by omega⟩
    rw [show (1 + (4 * k + 3)) / 4 = k + 1 by omega]
    refine RingOfIntegers.coe_injective ?_
    simp only [map_add, map_pow, map_natCast]
    change (ω : K) ^ 2 + _ = (ω : K)
    push_cast at hr ⊢
    linear_combination (2 * (ω : K) - 1 + rt) / 4 * hω + hr / 4
  · obtain ⟨m, n, e⟩ := hgen a
    refine ⟨(m, n), e, ?_⟩
    rintro ⟨m', n'⟩ e'
    have e₁ := (hc m' n').symm.trans ((congrArg (fun b : 𝓞 K => τ (b : K)) (e'.symm.trans e)).trans (hc m n))
    have e₂ := congrArg Complex.im e₁
    simp [hd'.ne'] at e₂
    subst e₂
    have e₃ : m' = m := by exact_mod_cast add_right_cancel e₁
    rw [e₃]
  · rintro ⟨m, n, rfl⟩
    exact ⟨_, by rw [hc, _root_.one_mul]⟩
  · rintro ⟨a, ha⟩
    obtain ⟨m, n, rfl⟩ := hgen a
    refine ⟨m, n, funext fun i => ?_⟩
    rw [Subsingleton.elim i 0, ha, hc, _root_.one_mul]

end Compare

def ActCurveAll : Prop :=
  ∀ (d : ℕ) [NeZero d], 7 ≤ d → Squarefree d → d % 4 = 3 → ∀ χ : DirichletCharacter ℂ d, IsKroneckerChar χ →
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ rt : K, rt ^ 2 = -(d : K) →
    ∀ τ : K →+* ℂ, τ rt = Complex.I * (Real.sqrt d : ℝ) → ActCurve d τ (Real.eulerMascheroniConstant +
      Real.log (2 * Real.pi / √d) - (deriv χ.LFunction 1 / χ.LFunction 1).re)

def CMCurvePrime : Prop :=
  ∀ d : ℕ, d.Prime → d % 16 = 7 → ∀ (K : Type) [Field K] [NumberField K],
    Module.finrank ℚ K = 2 → (∃ r : K, r ^ 2 = -(d : K)) → EtaCurve d K

end GlobalTheory.CMCurveCompare
