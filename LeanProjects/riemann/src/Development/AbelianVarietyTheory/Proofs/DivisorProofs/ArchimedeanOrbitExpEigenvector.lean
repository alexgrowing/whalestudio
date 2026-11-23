import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcGASmoothAndRderMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsSecondKindFormPreservingGroup
open scoped TensorProduct Matrix
open NumberField Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (tensNU tensNU_tmul extH)
open GlobalTheory.AutFunCompare (sgW sgW_mul mat_extH)

noncomputable section

namespace GlobalTheory.StabLine

theorem smul_mat_mulVec {n : ℕ} (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    (c • M) *ᵥ x = c • (M *ᵥ x) := by
  ext p; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem exp_mulVec_of_eigen {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (l : ℂ)
    (h : Z *ᵥ v = l • v) (t : ℝ) :
    NormedSpace.exp (t • Z) *ᵥ v = NormedSpace.exp ((t : ℂ) * l) • v := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have ht : t • Z = (t : ℂ) • Z := by ext i j; simp [Complex.real_smul]
  rw [ht]
  have hpow : ∀ k : ℕ, ((t : ℂ) • Z) ^ k *ᵥ v = ((t : ℂ) * l) ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, smul_mat_mulVec, h, smul_smul,
        smul_smul]
      congr 1; ring
  let f : Matrix (Fin n) (Fin n) ℂ →+ (Fin n → ℂ) :=
    AddMonoidHom.mk' (fun A => A *ᵥ v) (fun A B => Matrix.add_mulVec A B v)
  have hf : Continuous f := continuous_id.matrix_mulVec continuous_const
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((t : ℂ) • Z)).map f hf
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((t : ℂ) * l)).smul_const v
  refine h1.unique ?_
  convert h2 using 1
  funext k
  simp only [Function.comp_apply, f, AddMonoidHom.mk'_apply, smul_mat_mulVec, hpow, smul_smul, smul_eq_mul]

theorem tensNU_mul_one_tmul {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (u : R ⊗[F] E) (e : E) :
    tensNU j hj u * ((1 : R') ⊗ₜ[F] e) = tensNU j hj (u * ((1 : R) ⊗ₜ[F] e)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]
  | tmul a e' => simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem mat_extH_eq {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (g : HA R σ J) (r s : Fin n) :
    (HA.mat R' σ J (extH σ J j hj g)).1 r s =
      (1 : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) r s +
        tensNU j hj ((HA.mat R σ J g).1 r s - (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) r s) := by
  rw [mat_extH]
  by_cases h : r = s
  · subst h; simp [map_sub]; ring
  · simp [Matrix.one_apply, h]

theorem mulVec_embArch_eq_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E), x ≠ 0 → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (Z : Matrix (Fin n) (Fin n) ℂ) (l : ℂ),
      Z *ᵥ (fun i => τ.1 (x i)) = l • (fun i => τ.1 (x i)) → ∀ (t : ℝ) (y : GArch σ J w), GlobalTheory.Orb.archMat σ J τ y = NormedSpace.exp (t • Z) →
      ∃ a : AF F ⊗[F] E, (matHom _ σ J (embArch σ J w y)).1 *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = a • fun i => inclR (F := F) (AF F) (x i) := by
  intro F E _ _ _ _ _ σ hcm n J x _hx w τ Z l hZ t y hy
  classical
  let T1 := tensNU (E := E) (sgW w) (sgW_mul w)
  let T2 := tensNU (E := E) (R' := AF F) (LinearMap.inl F (Ainf F) (Af F)) (fun _ _ => Prod.ext rfl (mul_zero _).symm)
  let Y : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E) := (matHom _ σ J y).1
  let X' : Fin n → w.Completion ⊗[F] E := fun i => (1 : w.Completion) ⊗ₜ[F] x i
  obtain ⟨b, hb⟩ := (infEmb_bijective hcm τ).2 (NormedSpace.exp ((t : ℂ) * l))
  have hτ : ∀ i, infEmb τ (X' i) = τ.1 (x i) := fun i => by simp [X']
  have hYX : ∀ r, (Y *ᵥ X') r = b * X' r := by
    intro r
    apply (infEmb_bijective hcm τ).1
    rw [RingHom.map_mulVec, map_mul, hb, hτ]
    have e1 := congrFun (exp_mulVec_of_eigen Z _ l hZ t) r
    rw [← hy, GlobalTheory.Orb.archMat_apply] at e1
    have e2 : (infEmb τ ∘ X') = fun i => τ.1 (x i) := funext hτ
    rw [e2]
    simpa [Pi.smul_apply, smul_eq_mul] using e1
  have hM : ∀ r s, (matHom _ σ J (embArch σ J w y)).1 r s =
      (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) r s +
        T2 (T1 (Y r s - (1 : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) r s)) := by
    intro r s
    show (HA.mat _ σ J (extH (R' := AF F) σ J (LinearMap.inl F (Ainf F) (Af F)) (fun _ _ => Prod.ext rfl (mul_zero _).symm)
      (extH σ J (sgW w) (sgW_mul w) y))).1 r s = _
    refine (mat_extH_eq (R' := AF F) σ J _ _ _ r s).trans ?_
    rw [mat_extH_eq]
    simp [T1, T2, Y, matHom_apply]
  have hinc : ∀ e : E, inclR (F := F) (AF F) e = (1 : AF F) ⊗ₜ[F] e := fun _ => rfl
  have hkey : ∀ (u : w.Completion ⊗[F] E) (e : E), T2 (T1 u) * inclR (F := F) (AF F) e = T2 (T1 (u * ((1 : w.Completion) ⊗ₜ[F] e))) := by
    intro u e
    rw [hinc]
    exact (tensNU_mul_one_tmul (R' := AF F) _ _ (T1 u) e).trans (congrArg T2 (tensNU_mul_one_tmul _ _ u e))
  refine ⟨1 + T2 (T1 (b - 1)), funext fun r => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, hM, add_mul, Finset.sum_add_distrib, hkey]
  have hs : ∑ s, T2 (T1 ((Y r s - (1 : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) r s) * ((1 : w.Completion) ⊗ₜ[F] x s))) =
      T2 (T1 ((b - 1) * ((1 : w.Completion) ⊗ₜ[F] x r))) := by
    rw [← map_sum, ← map_sum]
    congr 2
    have := hYX r
    simp only [Matrix.mulVec, dotProduct, X'] at this
    simp only [sub_mul, Finset.sum_sub_distrib, this, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hs, ← hkey]
  simp [Matrix.one_apply]

end GlobalTheory.StabLine
