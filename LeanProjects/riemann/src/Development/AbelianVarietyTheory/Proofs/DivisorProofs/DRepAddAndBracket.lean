import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSmoothLogNearOneOfIsUnitaryLieExpData
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothInExponentialCoordsIffFirstSecondKind
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieSmoothAndLinear
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieCommutatorEqBracket

noncomputable section

open GlobalTheory.SmoothForms NormedSpace
open scoped ContDiff Topology InnerProductSpace

namespace GlobalTheory.DerivedAction

variable {𝔸 H : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

def dOp (π : 𝔸 → (H →L[ℂ] H)) (X : 𝔸) (v : H) : H := deriv (fun t : ℝ => π (exp (t • X)) v) 0

theorem abstract (σ : 𝔸 →ₗ[ℝ] 𝔸) (anti : ∀ a b, σ (a * b) = σ b * σ a) (one : σ 1 = 1) (invol : ∀ a, σ (σ a) = a)
    (π : 𝔸 → (H →L[ℂ] H)) (π1 : π 1 = 1) (πm : ∀ a b, σ a * a = 1 → σ b * b = 1 → π (a * b) = π a * π b) (v : H)
    (hv : ∀ (k : ℕ) (Xs : Fin k → 𝔸), (∀ i, σ (Xs i) = -Xs i) →
      ContDiff ℝ ∞ fun t : Fin k → ℝ => π ((List.ofFn fun i => exp (t i • Xs i)).prod) v)
    (X : 𝔸) (hX : σ X = -X) (Y : 𝔸) (hY : σ Y = -Y) :
    dOp π (X + Y) v = dOp π X v + dOp π Y v ∧
      dOp π (X * Y - Y * X) v = dOp π X (dOp π Y v) - dOp π Y (dOp π X v) := by
  classical
  let L : Submodule ℝ 𝔸 := LinearMap.ker (σ + LinearMap.id)
  have hL : ∀ Z, Z ∈ L ↔ σ Z = -Z := fun Z => by
    simp only [L, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg]
  have hunit : ∀ a, σ a * a = 1 → IsUnit (π a) := fun a ha => by
    have hr : a * σ a = 1 := by
      have : IsArtinianRing 𝔸 := IsArtinianRing.of_finite ℝ 𝔸
      exact mul_eq_one_comm.1 ha
    have hs : σ (σ a) * σ a = 1 := by rw [invol, hr]
    exact ⟨⟨π a, π (σ a), by rw [← πm _ _ ha hs, hr, π1], by rw [← πm _ _ hs ha, ha, π1]⟩, rfl⟩
  have hmul : ∀ a b, σ a * a = 1 → σ b * b = 1 → σ (a * b) * (a * b) = 1 := fun a b ha hb => by
    rw [anti, mul_assoc, ← mul_assoc (σ a), ha, one_mul, hb]
  let s : 𝔸 → (H →L[ℂ] H)ˣ := fun a => if h : IsUnit (π a) then h.unit else 1
  have hs : ∀ a, σ a * a = 1 → (s a : H →L[ℂ] H) = π a := fun a ha => by
    simp only [s, dif_pos (hunit a ha), IsUnit.unit_spec]
  have hD : IsLieData σ L.subtype s :=
    ⟨anti, one, invol, L.injective_subtype,
      fun Z => ⟨fun h => ⟨⟨Z, (hL Z).2 h⟩, rfl⟩, by rintro ⟨Z, rfl⟩; exact (hL _).1 Z.2⟩,
      fun a b ha hb => Units.ext (by rw [Units.val_mul, hs _ ha, hs _ hb, hs _ (hmul a b ha hb), πm _ _ ha hb])⟩
  have hl := hasLog_of_isLieData _ _ _ _ _ _ hD
  have hu : ∀ Z : L, σ (exp Z.1) * exp Z.1 = 1 := fun Z => SecondKind.exp_unitary hD Z
  have he : ∀ Z : L, ((expMap L.subtype s Z : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) = π (exp Z.1) := fun Z => hs _ (hu Z)
  have hprod : ∀ l : List L, σ (l.map fun Z => exp Z.1).prod * (l.map fun Z => exp Z.1).prod = 1 ∧
      (((l.map (expMap L.subtype s)).prod : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) = π (l.map fun Z => exp Z.1).prod := fun l => by
    induction l with
    | nil => simp [one, π1]
    | cons Z l ih =>
      simp only [List.map_cons, List.prod_cons, Units.val_mul]
      exact ⟨hmul _ _ (hu Z) ih.1, by rw [he, ih.2, πm _ _ (hu Z) ih.1]⟩

  have d1 : ∀ Z : L, DifferentiableAt ℝ (fun t : ℝ => π (exp (t • Z.1)) v) 0 := fun Z => by
    have h := (hv 1 (fun _ => Z.1) fun _ => (hL _).1 Z.2).comp
      (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun (t : ℝ) (_ : Fin 1) => t)
    have := (h.differentiable (by simp)).differentiableAt (x := 0)
    simpa [Function.comp_def] using this
  have hlin : ∀ (A : H →L[ℂ] H) (Z : L) (u : H), DifferentiableAt ℝ (fun t : ℝ => π (exp (t • Z.1)) u) 0 →
      HasDerivAt (fun t : ℝ => A (π (exp (t • Z.1)) u)) (A (dOp π Z.1 u)) 0 := fun A Z u h =>
    (A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h.hasDerivAt
  have d2 : ∀ Z Z' : L, DifferentiableAt ℝ (fun t : ℝ => π (exp (t • Z.1)) (dOp π Z'.1 v)) 0 := fun Z Z' => by
    have h := (hv 2 ![Z.1, Z'.1] (by
      intro i; fin_cases i
      · exact (hL _).1 Z.2
      · exact (hL _).1 Z'.2)).comp
      (contDiff_pi.2 (by
        intro i; fin_cases i
        · exact contDiff_fst
        · exact contDiff_snd) : ContDiff ℝ ∞ fun (p : ℝ × ℝ) => ![p.1, p.2])
    have h' : ContDiff ℝ ∞ (Function.uncurry fun (t r : ℝ) => π (exp (t • Z.1)) (π (exp (r • Z'.1)) v)) := by
      convert h using 1
      funext p
      have := πm _ _ (hu (p.1 • Z)) (hu (p.2 • Z'))
      simp only [Submodule.coe_smul] at this
      simp [Function.uncurry, this]
    have h3 : ContDiff ℝ ∞ fun t : ℝ =>
        fderiv ℝ (fun r : ℝ => π (exp (t • Z.1)) (π (exp (r • Z'.1)) v)) 0 (1 : ℝ) :=
      (ContDiff.fderiv (m := ∞) h' contDiff_const (by simp)).clm_apply contDiff_const
    have h4 := (h3.differentiable (by simp)).differentiableAt (x := 0)
    exact h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (hlin _ Z' v (d1 Z')).deriv.symm)

  let φ : H → H → (H →L[ℂ] H)ˣ → ℂ := fun w u g => ⟪w, (g : H →L[ℂ] H) u⟫_ℂ
  have hder : ∀ (w : H) (Z : L) (u : H), DifferentiableAt ℝ (fun t : ℝ => π (exp (t • Z.1)) u) 0 →
      Der (expMap L.subtype s) Z (φ w u) = φ w (dOp π Z.1 u) := fun w Z u h => by
    funext g
    have h1 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hlin g Z u h)
    refine Eq.trans ?_ h1.deriv
    simp only [Der, φ, Units.val_mul, he]
    rfl
  have hsm : ∀ w, Sm (expMap L.subtype s) (φ w v) := fun w => by
    refine (SecondKind.main _ _ _ _ _ _ hD hl Set.univ Submodule.span_univ _).2 fun k Z _ g => ?_
    have h1 := (((innerSL ℂ w).comp (g : H →L[ℂ] H)).restrictScalars ℝ).contDiff.comp
      (hv k (fun i => (Z i).1) fun i => (hL _).1 (Z i).2)
    convert h1 using 1
    funext t
    have h2 := (hprod (List.ofFn fun i => t i • Z i)).2
    rw [List.map_ofFn, List.map_ofFn] at h2
    simp only [φ, Units.val_mul]
    exact congrArg (fun A : H →L[ℂ] H => ⟪w, (g : H →L[ℂ] H) (A v)⟫_ℂ) h2
  let X' : L := ⟨X, (hL _).2 hX⟩
  let Y' : L := ⟨Y, (hL _).2 hY⟩
  let Z' : L := ⟨X * Y - Y * X, (hL _).2 (by rw [map_sub, anti, anti, hX, hY]; noncomm_ring)⟩
  refine ⟨ext_inner_left ℂ fun w => ?_, ext_inner_left ℂ fun w => ?_⟩
  · have h := (der_smooth_and_linear _ _ _ _ _ _ hD hl _ (hsm w)).2.1 X' Y'
    rw [hder w _ _ (d1 _), hder w _ _ (d1 _), hder w _ _ (d1 _)] at h
    rw [inner_add_right]
    exact congrFun h 1
  · have h := Bracket.der_bracket _ _ _ _ _ _ hD hl _ (hsm w) X' Y' Z' rfl
    rw [hder w _ _ (d1 _), hder w _ _ (d1 _), hder w _ _ (d1 _), hder w _ _ (d2 _ _), hder w _ _ (d2 _ _)] at h
    rw [inner_sub_right]
    exact (congrFun h 1).symm

open Matrix Formalism.MainNotions.S Formalism.L2.Theta

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem dRep_add_and_bracket : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Jᴴ = J → IsUnit J.det → IsURepOn (Formalism.QuantumDeterminants.UH J) π → ∀ v, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π v → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, ∀ Y ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, dRep π (X + Y) v = dRep π X v + dRep π Y v ∧ dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) := by
  intro n H _ _ J π hJ hd hπ v hv X hX Y hY
  let σ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun X => J⁻¹ * Xᴴ * J
      map_add' := fun X Y => by rw [conjTranspose_add, mul_add, add_mul]
      map_smul' := fun c X => by
        rw [conjTranspose_smul, star_trivial, mul_smul_comm, smul_mul_assoc]; rfl }
  have hσ : ∀ Z, σ Z = J⁻¹ * Zᴴ * J := fun _ => rfl
  have hskew : ∀ Z, σ Z = -Z ↔ Zᴴ * J + J * Z = 0 := fun Z => by
    rw [hσ]
    constructor
    · intro h1
      rw [← mul_nonsing_inv_cancel_left _ (Zᴴ * J) hd, ← mul_assoc J⁻¹, h1, mul_neg, neg_add_cancel]
    · intro h1
      rw [mul_assoc, eq_neg_of_add_eq_zero_left h1, mul_neg, nonsing_inv_mul_cancel_left _ _ hd]
  have hun : ∀ u, σ u * u = 1 → u ∈ Formalism.QuantumDeterminants.UH J := fun u h1 => by
    change uᴴ * J * u = J
    have := congrArg (J * ·) h1
    simpa only [hσ, ← mul_assoc, mul_nonsing_inv _ hd, one_mul, mul_one] using this
  refine abstract σ (fun a b => ?_) ?_ (fun a => ?_) π hπ.1.1 (fun a b ha hb => hπ.1.2 _ (hun a ha) _ (hun b hb)) v
    (fun k Xs h => hv k Xs fun i => (hskew _).1 (h i)) X ((hskew _).2 hX) Y ((hskew _).2 hY)
  · simp only [hσ, conjTranspose_mul, mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hd]
  · rw [hσ, conjTranspose_one, mul_one, nonsing_inv_mul _ hd]
  · rw [hσ, hσ, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hJ]
    simp only [mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hd, nonsing_inv_mul _ hd, mul_one]

end GlobalTheory.DerivedAction

end
