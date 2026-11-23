import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilEisensteinSiegelConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicStd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryUnnSubgroupEqTopOfLeviUnipotentWeyl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeftMulUnitaryMatrixAddHaar

noncomputable section

open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilSchComm

def lmul {R : Type} [CommRing R] {m : ℕ} (n : ℕ) (A : Matrix (Fin m) (Fin m) R) (z : Fin m → Fin n → R) :
    Fin m → Fin n → R := fun i j => ∑ c, A i c * z c j

theorem lmul_lmul {R : Type} [CommRing R] {m n : ℕ} {A B : Matrix (Fin m) (Fin m) R} (h : A * B = 1)
    (z : Fin m → Fin n → R) : lmul n A (lmul n B z) = z := by
  change (A * (B * Matrix.of z) : Matrix (Fin m) (Fin n) R) = Matrix.of z
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

theorem continuous_lmul {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m : ℕ} (n : ℕ)
    (A : Matrix (Fin m) (Fin m) R) : Continuous (lmul n A) := by
  unfold lmul
  fun_prop

def lmulHomeo {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m : ℕ} (n : ℕ)
    {A B : Matrix (Fin m) (Fin m) R} (h : A * B = 1) : (Fin m → Fin n → R) ≃ₜ (Fin m → Fin n → R) where
  toFun := lmul n A
  invFun := lmul n B
  left_inv := lmul_lmul (mul_eq_one_comm.1 h)
  right_inv := lmul_lmul h
  continuous_toFun := continuous_lmul n A
  continuous_invFun := continuous_lmul n B

def lmulFam {T : Type} {m : ℕ} (n : ℕ) {A B : T → Matrix (Fin m) (Fin m) ℂ} (h : ∀ τ, A τ * B τ = 1) :
    (T → Fin m → Fin n → ℂ) ≃ₗ[ℝ] (T → Fin m → Fin n → ℂ) where
  toFun z τ := lmul n (A τ) (z τ)
  invFun z τ := lmul n (B τ) (z τ)
  map_add' z z' := by
    funext τ i j
    simp [lmul, mul_add, Finset.sum_add_distrib]
  map_smul' c z := by
    funext τ i j
    simp [lmul, Finset.mul_sum, mul_left_comm]
  left_inv z := funext fun τ => lmul_lmul (mul_eq_one_comm.1 (h τ)) (z τ)
  right_inv z := funext fun τ => lmul_lmul (h τ) (z τ)

theorem map_mul_entry {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {m n : ℕ} (M : Matrix (Fin m) (Fin m) R)
    (x : Matrix (Fin m) (Fin n) R) : (fun i j => φ ((M * x) i j)) = lmul n (M.map φ) fun i j => φ (x i j) := by
  funext i j
  simp only [lmul, Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply]

variable {D : D7} {n : ℕ}

theorem map_cancel {R : Type} [CommRing R] (φ : AE D →+* R) (V : HSp D) (g : GA D V) :
    (mt V g).map φ * (mt V g⁻¹).map φ = 1 := by
  have h : mt V g * mt V g⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_inv]
    exact Units.mul_inv _
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem comp_mem (θ : InfFam D) (V : HSp D) (h : GA D V) {Φ : Mx D V.rank n → ℂ} (hΦ : Φ ∈ schwartzA θ V.rank n) :
    (fun x : Mx D V.rank n => Φ (mt V h ⬝ x)) ∈ schwartzA θ V.rank n := by
  induction hΦ using Submodule.span_induction with
  | zero => exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul c Φ _ h1 => exact Submodule.smul_mem _ c h1
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (lmulFam n fun τ => map_cancel ((θ τ).comp (infPart D)) V h).toContinuousLinearEquiv f,
      g ∘ lmulHomeo n (map_cancel (finPart D) V h), ⟨hg.1.comp_continuous (lmulHomeo n _).continuous, hg.2.comp_homeomorph _⟩, funext fun x => ?_⟩
    have e1 := fun τ => map_mul_entry ((θ τ).comp (infPart D)) (mt V h) x
    have e2 := map_mul_entry (finPart D) (mt V h) x
    exact congrArg₂ (· * ·) (congrArg f (funext e1)) (congrArg g e2)

theorem inner_mul (V : HSp D) (h : GA D V) (x y : Mx D V.rank n) :
    StdUnn.inner V (mt V h ⬝ x) (mt V h ⬝ y) = StdUnn.inner V x y := by
  unfold StdUnn.inner
  rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA V), ← Matrix.mul_assoc (adj (mt V h)), mt_unitary]

def subst (θ : InfFam D) (V : HSp D) (n : ℕ) (h : GA D V) : Module.End ℂ (schwartzA θ V.rank n) where
  toFun Φ := ⟨fun x => Φ.1 (mt V h ⬝ x), comp_mem θ V h Φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem subst_mem_and_comm : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D), IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n), StdUnn.IsWeilSch ψ χ θ V μ ω → ∀ h : GA D V, (∀ Φ ∈ schwartzA θ V.rank n, (fun x : Mx D V.rank n => Φ (mt V h ⬝ x)) ∈ schwartzA θ V.rank n) ∧ ∀ (g : StdUnn.G D n) (Φ Ψ : schwartzA θ V.rank n), (∀ x, Ψ.1 x = Φ.1 (mt V h ⬝ x)) → ∀ x, (ω g Ψ).1 x = (ω g Φ).1 (mt V h ⬝ x) := by
  intro D n V ψ χ θ _ μ 𝓕 hμ ω hω h
  refine ⟨fun Φ hΦ => comp_mem θ V h hΦ, fun g Φ Ψ hΨ x => ?_⟩
  let S : Subgroup (StdUnn.G D n) :=
    { carrier := {g | Commute (ω g) (subst θ V n h)}
      one_mem' := by
        change Commute (ω 1) _
        rw [map_one]
        exact Commute.one_left _
      mul_mem' := fun {a b} ha hb => by
        change Commute (ω (a * b)) _
        rw [map_mul]
        exact Commute.mul_left ha hb
      inv_mem' := fun {a} ha => Commute.units_inv_left (u := ω.toHomUnits a) ha }
  have hS : S = ⊤ := by
    refine StdUnn.eq_top_of_levi_unip_weyl D n S (fun g a hg => ?_) (fun g b hg => ?_) (fun g hg => ?_) <;>
      refine LinearMap.ext fun Φ => Subtype.ext (funext fun x => ?_) <;>
      change (ω g (subst θ V n h Φ)).1 x = (ω g Φ).1 (mt V h ⬝ x)
    · rw [hω.levi g a hg, hω.levi g a hg, Matrix.mul_assoc]
      rfl
    · rw [hω.unip g b hg, hω.unip g b hg, inner_mul]
      rfl
    · rw [hω.weyl g hg, hω.weyl g hg, ← GlobalTheory.Twist.LeftHaar.integral_left_unitary D V n h μ hμ.1
        (fun y => Φ.1 y * ψ (StdUnn.trA (Matrix.trace (StdUnn.inner V (mt V h ⬝ x) y))))]
      refine congrArg (integral μ) (funext fun y => ?_)
      exact congrArg (fun t => Φ.1 (mt V h ⬝ y) * ψ (StdUnn.trA (Matrix.trace t))) (inner_mul V h x y).symm
  have hg : g ∈ S := hS ▸ Subgroup.mem_top g
  obtain rfl : Ψ = subst θ V n h Φ := Subtype.ext (funext hΨ)
  exact congrFun (congrArg Subtype.val (LinearMap.congr_fun (show Commute (ω g) (subst θ V n h) from hg).eq Φ)) x

end GlobalTheory.WeilSchComm

end
