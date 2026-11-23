import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne

set_option autoImplicit false

noncomputable section

open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)

namespace GlobalTheory.LieFilt

theorem BlockUni.support_of_mulVec {κ R : Type} [Fintype κ] [CommRing R] {bl : κ → ℕ} {Q : Matrix κ κ R}
    (hQ : BlockUni bl Q) {y x : κ → R} (h : Q.mulVec y = x) {k : ℕ} (hx : ∀ z, k < bl z → x z = 0) :
    (∀ z, k < bl z → y z = 0) ∧ ∀ z, bl z = k → y z = x z := by
  have key : ∀ z, (∀ z', bl z < bl z' → y z' = 0) → y z = x z := by
    intro z hz
    rw [← h, Matrix.mulVec, dotProduct, Finset.sum_eq_single z]
    · rw [hQ z z (lt_irrefl _), Matrix.one_apply_eq, one_mul]
    · intro z' _ hne
      by_cases hlt : bl z < bl z'
      · rw [hz z' hlt, mul_zero]
      · rw [hQ z z' hlt, Matrix.one_apply_ne (Ne.symm hne), zero_mul]
    · simp
  have h1 : ∀ z, k < bl z → y z = 0 := by
    by_contra hne
    push Not at hne
    obtain ⟨z₀, hz₀, hy₀⟩ := hne
    obtain ⟨z, hz, hmax⟩ := (Finset.univ.filter fun z => y z ≠ 0).exists_max_image bl ⟨z₀, by simpa using hy₀⟩
    have hz' : y z ≠ 0 := by simpa using hz
    refine hz' ((key z fun z' hlt => ?_).trans (hx z (hz₀.trans_le (hmax z₀ (by simpa using hy₀)))))
    by_contra hy
    exact absurd (hmax z' (by simpa using hy)) (not_le.2 hlt)
  exact ⟨h1, fun z hz => key z fun z' hlt => h1 z' (hz ▸ hlt)⟩

section

variable {X : Scheme.{0}} {L : X.Modules} {U V : X.Opens} {κ μ : Type} [Fintype κ] [Fintype μ]
  [DecidableEq κ] [DecidableEq μ]

theorem isFrame_change {ℓ : μ → Γ(L, U)} (hℓ : VB.IsFrame ℓ) (hV : V ≤ U) {C : Matrix μ κ Γ(X, V)}
    {C' : Matrix κ μ Γ(X, V)} (h1 : C * C' = 1) (h2 : C' * C = 1) :
    VB.IsFrame fun z => ∑ b, C b z • resM L hV (ℓ b) := by
  intro V' h
  have e : ⇑(Fintype.linearCombination Γ(X, V') fun z => resM L h (∑ b, C b z • resM L hV (ℓ b))) =
      (Fintype.linearCombination Γ(X, V') fun b => resM L (h.trans hV) (ℓ b)) ∘
        (C.map (resG X h)).mulVec := by
    funext y
    simp only [Fintype.linearCombination_apply, map_sum, resM_smul, resM_resM, Function.comp, Matrix.mulVec,
      dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul, Matrix.map_apply]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [e]
  refine (hℓ V' _).comp (Function.bijective_iff_has_inverse.2 ⟨(C'.map (resG X h)).mulVec, fun y => ?_, fun y => ?_⟩)
  · rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  · rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

theorem repr_change {ℓ : μ → Γ(L, U)} (hℓ : VB.IsFrame ℓ) (hV : V ≤ U) {C : Matrix μ κ Γ(X, V)}
    {C' : Matrix κ μ Γ(X, V)} (h1 : C * C' = 1) (h2 : C' * C = 1) (s : Γ(L, V)) (z : κ) :
    ((isFrame_change hℓ hV h1 h2).basis le_rfl).repr s z = C'.mulVec ((hℓ.basis hV).repr s) z := by
  have e : s = ∑ z, C'.mulVec ((hℓ.basis hV).repr s) z • (isFrame_change hℓ hV h1 h2).basis le_rfl z := by
    have h3 : C.mulVec (C'.mulVec ((hℓ.basis hV).repr s)) = (hℓ.basis hV).repr s := by
      rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    conv_lhs => rw [← (hℓ.basis hV).sum_repr s, ← h3]
    generalize C'.mulVec ((hℓ.basis hV).repr s) = y
    simp only [VB.IsFrame.basis_apply, resM_self, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum,
      smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  conv_lhs => rw [e]
  rw [Module.Basis.repr_sum_self]

omit [DecidableEq μ] in

theorem basis_res {ℓ : μ → Γ(L, U)} (hℓ : VB.IsFrame ℓ) (hV : V ≤ U) :
    (hℓ.res hV).basis le_rfl = hℓ.basis hV := by
  ext b
  simp only [VB.IsFrame.basis_apply, resM_self]

theorem app_resG_eq {W : Scheme.{0}} (j : W ⟶ X) (hV : V ≤ U) (s : Γ(X, U)) :
    j.app V (resG X hV s) = resG W (j.preimage_mono hV) (j.app U s) :=
  ConcreteCategory.congr_hom (j.naturality (homOfLE hV).op) s

end

theorem locAdapted_of_matrix : ∀ {X W : Scheme.{0}} (jB : W ⟶ X) {ι : Type} [Fintype ι] {L : X.Modules} {E E' : ι → X.Modules} {r : ι → ℕ} {g : ℕ}
    (o : ι → ℕ) (T : ∀ a, E a ⟶ L) (u : ∀ a, E a ⟶ E' a) {U V V' : X.Opens} (hV : V ≤ U) (hV' : V' ≤ V)
    (ℓ : Fin g → Γ(L, U)) (hℓ : VB.IsFrame ℓ) (f : ∀ a, Fin (r a) → Γ(E a, V)), (∀ a, VB.IsFrame (f a)) →
    ∀ (f' : ∀ a, Fin (r a) → Γ(E' a, V)) (hf' : ∀ a, VB.IsFrame (f' a))
      (A : Matrix (Fin g) (Σ a, Fin (r a)) Γ(W, jB ⁻¹ᵁ V)),
    (∀ a b i, jB.app V ((hℓ.basis hV).repr ((T a).app V (f a i)) b) =
      ∑ j, A b ⟨a, j⟩ * jB.app V (((hf' a).basis le_rfl).repr ((u a).app V (f a i)) j)) →
    Function.Injective (jB.app V') →
    ∀ (C : Matrix (Fin g) (Σ a, Fin (r a)) Γ(X, V')) (C' : Matrix (Σ a, Fin (r a)) (Fin g) Γ(X, V'))
      (Q : Matrix (Σ a, Fin (r a)) (Σ a, Fin (r a)) Γ(W, jB ⁻¹ᵁ V')), C * C' = 1 → C' * C = 1 →
      BlockUni (fun s : Σ a, Fin (r a) => o s.1) Q → C.map (jB.app V') = A.map (resG W (jB.preimage_mono hV')) * Q →
    LocAdapted r o T u V' := by
  intro X W jB ι _ L E E' r g o T u U V V' hV hV' ℓ hℓ f hf f' hf' A hA hinj C C' Q h1 h2 hQ hC
  refine ⟨fun a i => resM _ hV' (f a i), fun a => (hf a).res hV', fun a i => resM _ hV' (f' a i),
    fun a => (hf' a).res hV', _, isFrame_change hℓ (hV'.trans hV) h1 h2, fun a i => ?_⟩
  set φ : Γ(X, V') →+* Γ(W, jB ⁻¹ᵁ V') := (jB.app V').hom with hφ
  set ρ := resG W (jB.preimage_mono hV') with hρ
  have hC' : C.map φ = A.map ρ * Q := hC
  have hinj' : Function.Injective φ := hinj
  have hQ1 : Q * (C'.map φ * A.map ρ) = 1 := by
    rw [mul_eq_one_comm, Matrix.mul_assoc, ← hC', ← Matrix.map_mul, h2,
      Matrix.map_one _ (map_zero _) (map_one _)]
  let w : Fin (r a) → Γ(X, V') := fun j =>
    (((hf' a).res hV').basis le_rfl).repr ((u a).app V' (resM _ hV' (f a i))) j
  have hw (j) : φ (w j) = ρ (jB.app V (((hf' a).basis le_rfl).repr ((u a).app V (f a i)) j)) := by
    simp only [w]
    rw [basis_res (hf' a), app_resM, (hf' a).repr_resM le_rfl hV']
    exact app_resG_eq jB hV' _
  let x : (Σ a, Fin (r a)) → Γ(W, jB ⁻¹ᵁ V') := fun z => ∑ j, if z = ⟨a, j⟩ then φ (w j) else 0
  let p : Fin g → Γ(X, V') := (hℓ.basis (hV'.trans hV)).repr ((T a).app V' (resM _ hV' (f a i)))
  have hp : φ ∘ p = (A.map ρ).mulVec x := by
    funext b
    have : φ (p b) = ρ (jB.app V ((hℓ.basis hV).repr ((T a).app V (f a i)) b)) := by
      simp only [p]
      rw [app_resM, hℓ.repr_resM hV hV']
      exact app_resG_eq jB hV' _
    rw [Function.comp_apply, this, hA, map_sum]
    simp only [Matrix.mulVec, dotProduct, x, Finset.mul_sum, mul_ite, mul_zero, Matrix.map_apply]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, hw]
  have hy : Q.mulVec (fun z => φ (C'.mulVec p z)) = x := by
    have : (fun z => φ (C'.mulVec p z)) = (C'.map φ).mulVec (φ ∘ p) := funext fun z => RingHom.map_mulVec φ C' p z
    rw [this, hp, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hQ1, Matrix.one_mulVec]
  obtain ⟨h3, h4⟩ := hQ.support_of_mulVec hy (k := o a) fun z hz =>
    Finset.sum_eq_zero fun j _ => if_neg (by rintro rfl; exact lt_irrefl _ hz)
  refine ⟨fun z hz => hinj' ?_, fun j => hinj' ?_⟩
  · rw [repr_change hℓ _ h1 h2, map_zero]
    exact h3 z hz
  · rw [repr_change hℓ _ h1 h2]
    refine (h4 ⟨a, j⟩ rfl).trans ?_
    simp only [x, Sigma.mk.injEq, heq_eq_eq, true_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl

end GlobalTheory.LieFilt

end
