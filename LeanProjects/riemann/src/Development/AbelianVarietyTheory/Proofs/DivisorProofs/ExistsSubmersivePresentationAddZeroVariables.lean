import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchEnl

open MvPolynomial

theorem ker_aeval_zero_eq_span (D κ : Type) [CommRing D] :
    RingHom.ker (aeval (R := D) (fun _ : κ ↦ (0 : D))) = Ideal.span (Set.range X) := by
  apply le_antisymm
  · intro p hp
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra h
    push_neg at h
    have hm0 : m = 0 := by ext i; simpa using h i (Set.mem_univ i)
    subst hm0
    rw [RingHom.mem_ker] at hp
    have : aeval (R := D) (fun _ : κ ↦ (0 : D)) p = coeff 0 p := by
      first
        | (show MvPolynomial.eval (0 : κ → D) p = _
           exact congrFun (congrArg DFunLike.coe (MvPolynomial.eval_zero (R := D) (σ := κ))) p)
        | (rw [MvPolynomial.aeval_def]; simp [MvPolynomial.eval₂_eq, MvPolynomial.coeff_zero_eq_constantCoeff])
    exact (mem_support_iff.mp hm) (this ▸ hp)
  · rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    simp

noncomputable def zeroPre (D κ : Type) [CommRing D] :
    Algebra.PreSubmersivePresentation D D κ κ where
  val _ := 0
  σ' x := C x
  aeval_val_σ' x := by simp
  relation k := X k
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_eq_ker_aeval_val]
    exact (ker_aeval_zero_eq_span D κ).symm
  map := id
  map_inj := Function.injective_id

theorem zeroPre_jacobian (D κ : Type) [CommRing D] [Finite κ] : (zeroPre D κ).jacobian = 1 := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  have h1 : (zeroPre D κ).jacobiMatrix = 1 := by
    ext i j
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    simp [zeroPre, Matrix.one_apply, pderiv_X, Pi.single_apply, eq_comm]
  rw [h1]
  simp

end GlobalTheory.PinchEnl

theorem GlobalTheory.PinchEnl.exists_submersivePresentation_sum_zero : ∀ (R D ν σ κ : Type) [CommRing R] [CommRing D] [Algebra R D] [Finite ν] [Finite σ] [Finite κ] (P : Algebra.SubmersivePresentation R D ν σ), ∃ P' : Algebra.SubmersivePresentation R D (κ ⊕ ν) (κ ⊕ σ), P'.val = Sum.elim (fun _ ↦ 0) P.val := by
  intro R D ν σ κ _ _ _ _ _ _ P
  let Q : Algebra.SubmersivePresentation D D κ κ :=
    { __ := GlobalTheory.PinchEnl.zeroPre D κ
      jacobian_isUnit := by rw [GlobalTheory.PinchEnl.zeroPre_jacobian]; exact isUnit_one }
  refine ⟨Q.comp P, ?_⟩
  ext i
  rcases i with k | j
  · rfl
  · rfl
