import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueUniformisingVectorVerticalTangentStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFibreCoords
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CauchyRiemannIffDifferentiableOnComplex
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.VertField

theorem differentiableAt_det {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (M : E → Matrix (Fin g) (Fin g) ℂ) (z₀ : E) (h : ∀ i j, DifferentiableAt ℂ (fun z => M z i j) z₀) :
    DifferentiableAt ℂ (fun z => (M z).det) z₀ := by
  simp only [Matrix.det_apply']
  fun_prop

private theorem differentiableAt_adjugate_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (M : E → Matrix (Fin g) (Fin g) ℂ) (z₀ : E) (h : ∀ i j, DifferentiableAt ℂ (fun z => M z i j) z₀)
    (i j : Fin g) : DifferentiableAt ℂ (fun z => (M z).adjugate i j) z₀ := by
  simp only [Matrix.adjugate_apply]
  refine differentiableAt_det (fun z => (M z).updateRow j (Pi.single i 1)) z₀ fun k l => ?_
  by_cases hk : k = j <;> simp [Matrix.updateRow_apply, hk, h k l]

theorem differentiableAt_of_mulVec {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (M : E → Matrix (Fin g) (Fin g) ℂ) (b w : E → Fin g → ℂ) (z₀ : E)
    (h : ∀ i j, DifferentiableAt ℂ (fun z => M z i j) z₀) (hb : ∀ i, DifferentiableAt ℂ (fun z => b z i) z₀)
    (hdet : (M z₀).det ≠ 0) (hw : ∀ᶠ z in nhds z₀, (M z).mulVec (w z) = b z) :
    DifferentiableAt ℂ w z₀ := by
  have hd : DifferentiableAt ℂ (fun z => (M z).det) z₀ := differentiableAt_det M z₀ h
  have hne : ∀ᶠ z in nhds z₀, (M z).det ≠ 0 := hd.continuousAt.eventually_ne hdet
  have heq : w =ᶠ[nhds z₀] fun z => ((M z).det)⁻¹ • ((M z).adjugate.mulVec (b z)) := by
    filter_upwards [hne, hw] with z hz hzw
    rw [← hzw, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      smul_smul, inv_mul_cancel₀ hz, one_smul]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  rw [differentiableAt_pi]
  intro i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  have hadj := differentiableAt_adjugate_apply M z₀ h i
  have hi := hd.inv hdet
  fun_prop

theorem valAt'_comp {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  have hpre : (x ≫ φ) ⁻¹ᵁ U = x ⁻¹ᵁ φ ⁻¹ᵁ U := by simp
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U
  · rw [dif_pos (by rwa [hpre]), dif_pos h]
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · rw [dif_neg (by rwa [hpre]), dif_neg h]

theorem isOpen_dom_and_differentiableOn_fn {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left}
    (u : HolUnif A₀ L₀ g) {X : Scheme.{0}} (m : A₀.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    IsOpen (dom u m W) ∧ DifferentiableOn ℂ (fn u m W f) (dom u m W) := by
  have hcomp : ∀ z, ((u.ex z).left ≫ m) ⁻¹ᵁ W = (u.ex z).left ⁻¹ᵁ m ⁻¹ᵁ W := fun z => by simp
  have hdom : dom u m W = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ m ⁻¹ᵁ W} := by
    ext z
    simp only [dom, Set.mem_ofPred_eq, hcomp]
  have hfn : fn u m W f = fun z => valAt' (u.ex z).left (m ⁻¹ᵁ W) ((m.app W).hom f) := by
    funext z
    exact valAt'_comp _ _ _ _
  rw [hdom, hfn]
  exact u.8 (m ⁻¹ᵁ W) ((m.app W).hom f)

private theorem clm_apply_eq_sum_single_mul {g : ℕ} (L : (Fin g → ℂ) →L[ℂ] ℂ) (v : Fin g → ℂ) :
    L v = ∑ a, L (Pi.single a 1) * v a := by
  have hv : v = ∑ a, v a • (Pi.single a 1 : Fin g → ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem exists_differentiableOn_vertical : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ (n : ℕ) (B : Set (Fin n → ℂ)) (G : (Fin n → ℂ) → (Fin P₀.g → ℂ)) (s : (Fin n → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ), IsOpen B → Differentiable ℂ G → (∀ z ∈ B, PtDer ((u.ex (G z)).left ≫ m) (s z) ∧ ∀ r, s z ⊤ (constFn p ⊤ r) = 0) → (∀ W f, DifferentiableOn ℂ (fun z => s z W f) {z ∈ B | G z ∈ dom u m W}) → ∃ w : (Fin n → ℂ) → (Fin P₀.g → ℂ), DifferentiableOn ℂ w B ∧ ∀ z ∈ B, ∀ W f, G z ∈ dom u m W → s z W f = fderiv ℂ (fn u m W f) (G z) (w z) := by
  intro P₀ u Hm χ hU R _ x₀ X p m hsm hpb n B G s hB hGd hs hhol
  have key : ∀ z ∈ B, ∃ v : Fin P₀.g → ℂ, ∀ W f, G z ∈ dom u m W → s z W f = fderiv ℂ (fn u m W f) (G z) v :=
    fun z hz => (GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hU R x₀ X p m hsm hpb (G z) (s z) (hs z hz).1 (hs z hz).2).exists
  choose! w hw using key
  refine ⟨w, fun z₁ hz₁ => ?_, hw⟩
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨W, t, hW, hdet⟩ := exists_fibre_coords P₀ u Hm χ hU R x₀ X p m hsm hpb (G z₁)
  have hD : IsOpen (dom u m W) := (isOpen_dom_and_differentiableOn_fn u m W 0).1
  have hV : IsOpen {z ∈ B | G z ∈ dom u m W} := hB.inter (hD.preimage hGd.continuous)
  have hz₁V : z₁ ∈ {z ∈ B | G z ∈ dom u m W} := ⟨hz₁, hW⟩
  have hT : Matrix.transpose (Matrix.of fun b a => fderiv ℂ (fn u m W (t b)) (G z₁) (Pi.single a 1)) =
      Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) (G z₁) (Pi.single a 1) := by
    ext a b
    rfl
  refine differentiableAt_of_mulVec (fun z => Matrix.of fun b a => fderiv ℂ (fn u m W (t b)) (G z) (Pi.single a 1))
    (fun z b => s z W (t b)) w z₁ (fun b a => ?_) (fun b => ?_) ?_ ?_
  · have h1 := ((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex P₀.g (dom u m W) (fn u m W (t b)) hD).2
      (isOpen_dom_and_differentiableOn_fn u m W (t b)).2).2 (Pi.single a 1)
    exact (h1.differentiableAt (hD.mem_nhds hW)).comp z₁ (hGd z₁)
  · exact (hhol W (t b)).differentiableAt (hV.mem_nhds hz₁V)
  · rw [← Matrix.det_transpose, hT]
    exact hdet
  · filter_upwards [hV.mem_nhds hz₁V] with z hz
    ext b
    exact ((hw z hz.1 W (t b) hz.2).trans (clm_apply_eq_sum_single_mul _ _)).symm

end GlobalTheory.KS.VertField
