import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg
open Matrix

namespace GlobalTheory.AdjDescent

theorem jm_mul_jm (p q : ℕ) : Jm p q * Jm p q = 1 := by
  unfold Jm Formalism.UG.Jpq
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

theorem jm_conjTranspose (p q : ℕ) : (Jm p q)ᴴ = Jm p q := by
  unfold Jm Formalism.UG.Jpq
  simp [Matrix.fromBlocks_conjTranspose]

theorem conjR_conjTranspose_mul {p q : ℕ} (Z : Mat p q) : (conjR Z)ᴴ * Jm p q = -(Jm p q * Z) := by
  unfold conjR adjZ
  rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, jm_conjTranspose, Matrix.neg_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, jm_mul_jm, Matrix.mul_one]

theorem mul_conjR {p q : ℕ} (Z : Mat p q) : Jm p q * conjR Z = -(Zᴴ * Jm p q) := by
  unfold conjR adjZ
  rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, jm_mul_jm, Matrix.one_mul]

theorem re_mem_upq {p q : ℕ} (Z : Mat p q) : Z + conjR Z ∈ upq p q := by
  show (Z + conjR Z)ᴴ * Jm p q + Jm p q * (Z + conjR Z) = 0
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, conjR_conjTranspose_mul, mul_conjR]
  abel

theorem im_mem_upq {p q : ℕ} (Z : Mat p q) : Complex.I • (Z - conjR Z) ∈ upq p q := by
  show (Complex.I • (Z - conjR Z))ᴴ * Jm p q + Jm p q * (Complex.I • (Z - conjR Z)) = 0
  have hI : (star Complex.I : ℂ) = -Complex.I := Complex.conj_I
  rw [Matrix.conjTranspose_smul, hI, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sub_mul, Matrix.mul_sub, conjR_conjTranspose_mul, mul_conjR]
  simp only [neg_smul, sub_neg_eq_add, smul_add]
  abel

theorem decomp {p q : ℕ} (Z : Mat p q) :
    Z = (1 / 2 : ℂ) • (Z + conjR Z) + (-Complex.I / 2) • (Complex.I • (Z - conjR Z)) := by
  have h : (-Complex.I / 2) • (Complex.I • (Z - conjR Z)) = (1 / 2 : ℂ) • (Z - conjR Z) := by
    rw [smul_smul]
    congr 1
    rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I]
    norm_num
  rw [h, ← smul_add, show Z + conjR Z + (Z - conjR Z) = (2 : ℂ) • Z by rw [two_smul]; abel,
    smul_smul]
  norm_num

theorem inner_apply_of_norm {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : G →* (H →L[ℂ] H)) (h : ∀ g x, ‖ρ g x‖ = ‖x‖) (g : G) (x y : H) :
    inner ℂ x (ρ g y) = inner ℂ (ρ g⁻¹ x) y := by
  have e : ρ g * ρ g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hinv : ρ g (ρ g⁻¹ x) = x := by
    calc ρ g (ρ g⁻¹ x) = (ρ g * ρ g⁻¹) x := rfl
      _ = x := by rw [e]; rfl
  let L : H →ₗᵢ[ℂ] H := ⟨(ρ g : H →ₗ[ℂ] H), h g⟩
  calc inner ℂ x (ρ g y) = inner ℂ (L (ρ g⁻¹ x)) (L y) := by
        show inner ℂ x (ρ g y) = inner ℂ (ρ g (ρ g⁻¹ x)) (ρ g y)
        rw [hinv]
    _ = inner ℂ (ρ g⁻¹ x) y := L.inner_map_map _ _

private theorem kFin_map_of_intertwining {p q : ℕ} (T : GrpData p q) {E F : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (πE : T.G → (E →L[ℂ] E)) (πF : T.G → (F →L[ℂ] F)) (L : E →L[ℂ] F)
    (hL : ∀ g x, L (πE g x) = πF g (L x)) (x : E) (hx : KFin T πE x) : KFin T πF (L x) := by
  unfold KFin at hx ⊢
  have key : ∀ (κ : Type) (c : κ → T.G),
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => πE (c k) x)) →
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => πF (c k) (L x))) := by
    intro κ c hc
    have e : (Set.range fun k => πF (c k) (L x)) =
        (L : E →ₗ[ℂ] F) '' Set.range (fun k => πE (c k) x) := by
      rw [← Set.range_comp]
      congr 1
      funext k
      simp [hL]
    rw [e, Submodule.span_image]
    haveI := hc
    infer_instance
  exact key _ _ hx

theorem adjoint_descends : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : T.G →* (H →L[ℂ] H)), (∀ g x, ‖ρ g x‖ = ‖x‖) → ∀ S : D.U.H →L[ℂ] H, (∀ g x, ρ g (S x) = S (D.U.π g x)) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : V →ₗ[ℂ] H) (act : Mat p q →ₗ[ℂ] Module.End ℂ V), (∀ P, KFin T (fun g => ρ g) (ι P)) → (∀ Y ∈ upq p q, ∀ P, HasDerivAt (fun t : ℝ => ρ (T.expt (t • Y)) (ι P)) (ι (act Y P)) 0) → ∃ φ : V →ₗ[ℂ] D.HK.V, (∀ P x, inner ℂ x (D.ι (φ P)) = inner ℂ (S x) (ι P)) ∧ ∀ Z P, φ (act Z P) = D.HK.act Z (φ P) := by
  intro p q T D H _ _ _ ρ hρ S hS V _ _ ι act hK hD

  have hA : ∀ g y, ContinuousLinearMap.adjoint S (ρ g y) =
      D.U.π g (ContinuousLinearMap.adjoint S y) := by
    intro g y
    apply ext_inner_left ℂ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_right, inner_apply_of_norm ρ hρ, hS,
      ← ContinuousLinearMap.adjoint_inner_right S, inner_apply_of_norm D.U.π D.U.isom]

  have hmem : ∀ P, ∃ w, D.ι w = ContinuousLinearMap.adjoint S (ι P) := fun P =>
    (D.ι_range _).2 (kFin_map_of_intertwining T (fun g => ρ g) (fun g => D.U.π g) _ hA (ι P) (hK P))
  choose f hf using hmem
  have hinj := D.ι_inj
  let φ : V →ₗ[ℂ] D.HK.V :=
    { toFun := f
      map_add' := fun P Q => hinj (by simp only [map_add, hf])
      map_smul' := fun c P => hinj (by simp only [RingHom.id_apply, map_smul, hf]) }
  have hφ : ∀ P, D.ι (φ P) = ContinuousLinearMap.adjoint S (ι P) := hf

  have hY : ∀ Y ∈ upq p q, ∀ P, φ (act Y P) = D.HK.act Y (φ P) := by
    intro Y hYm P
    apply hinj
    rw [hφ]
    have h1 : HasDerivAt (fun t : ℝ => D.U.π (T.expt (t • Y)) (D.ι (φ P)))
        (ContinuousLinearMap.adjoint S (ι (act Y P))) 0 := by
      have h0 := ((ContinuousLinearMap.adjoint S).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
        (0 : ℝ) (hD Y hYm P)
      convert h0 using 1
      all_goals first
        | rfl
        | (funext t; simp [hA, hφ])
    exact h1.unique (D.der Y hYm (φ P))
  refine ⟨φ, fun P x => ?_, fun Z P => ?_⟩
  · rw [hφ, ContinuousLinearMap.adjoint_inner_right]
  · have hre := re_mem_upq Z
    have him := im_mem_upq Z
    rw [decomp Z]
    generalize Z + conjR Z = A at hre ⊢
    generalize Complex.I • (Z - conjR Z) = B at him ⊢
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hY A hre, hY B him]

end GlobalTheory.AdjDescent
