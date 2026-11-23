import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData

section Loc

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem umat_mem (g : Formalism.REAL.UJ ε) : umat g ∈ UJset ε := g.2

def homOf (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsURepOn (UJset ε) σ) :
    Formalism.REAL.UJ ε →* (H →L[ℂ] H) where
  toFun g := σ (umat g)
  map_one' := h.1.1
  map_mul' a b := h.1.2 _ (umat_mem a) _ (umat_mem b)

theorem homOf_apply (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsURepOn (UJset ε) σ)
    (g : Formalism.REAL.UJ ε) : homOf σ h g = σ (umat g) := rfl

theorem homOf_norm (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsURepOn (UJset ε) σ)
    (g : Formalism.REAL.UJ ε) (x : H) : ‖homOf σ h g x‖ = ‖x‖ := h.2.1 _ (umat_mem g) x

theorem continuous_umat : Continuous (fun g : Formalism.REAL.UJ ε => umat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem homOf_cont (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsURepOn (UJset ε) σ) (x : H) :
    Continuous fun g => homOf σ h g x :=
  (h.2.2 x).comp_continuous continuous_umat umat_mem

theorem mul_star_eq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  have : star z = (starRingEnd ℂ) z := rfl
  rw [this, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem schur_abs {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (hd : IsFdeg (Formalism.REAL.muG ε) σ d) (x y : H) :
    Integrable (fun g : Formalism.REAL.UJ ε => ‖⟪y, σ (umat g) x⟫_ℂ‖ ^ 2) (Formalism.REAL.muG ε) ∧
      ∫ g : Formalism.REAL.UJ ε, ‖⟪y, σ (umat g) x⟫_ℂ‖ ^ 2 ∂(Formalism.REAL.muG ε) = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d := by
  obtain ⟨hi, he⟩ := hd.2 x y x y
  have hfun : (fun g : Formalism.REAL.UJ ε => coefOn σ x y g * star (coefOn σ x y g)) =
      fun g : Formalism.REAL.UJ ε => ((‖⟪y, σ (umat g) x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    exact mul_star_eq _
  rw [hfun] at hi he
  refine ⟨?_, ?_⟩
  · exact hi.re.congr (Filter.Eventually.of_forall fun g => Complex.ofReal_re _)
  · rw [integral_complex_ofReal] at he
    have h2 : ((∫ g : Formalism.REAL.UJ ε, ‖⟪y, σ (umat g) x⟫_ℂ‖ ^ 2 ∂(Formalism.REAL.muG ε) : ℝ) : ℂ) =
        ((‖x‖ ^ 2 * ‖y‖ ^ 2 / d : ℝ) : ℂ) := by
      rw [he, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    exact_mod_cast h2

theorem fdegOf_eq {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (hd : IsFdeg (Formalism.REAL.muG ε) σ d) {w : H} (hw : ‖w‖ = 1) : fdegOf (Formalism.REAL.muG ε) σ w = d := by
  unfold fdegOf
  have h := (schur_abs hd w w).2
  have h' : ∫ g : Formalism.REAL.UJ ε, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 1 / d := by
    have : (fun g : Formalism.REAL.UJ ε => ‖coefOn σ w w g‖ ^ 2) = fun g : Formalism.REAL.UJ ε => ‖⟪w, σ (umat g) w⟫_ℂ‖ ^ 2 := rfl
    rw [this, h, hw]
    norm_num
  rw [h', hw]
  have := hd.1
  field_simp

end Loc

theorem projector_section_local (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.PlaceDegreeData.LocalProjectorFromSchur D := by
  intro h1 hL1 habs n ε lam hlam H _ _ _ σ hDS w hw h hgap hh
  obtain ⟨d, hd⟩ := h1 n ε lam hlam H σ hDS
  have hU : IsURepOn (UJset ε) σ := hDS.2.2.1
  have hint : Integrable (phLoc ε σ w) (Formalism.REAL.muG ε) := hL1 n ε lam hlam H σ hDS w hw h hgap hh
  have hdeg : fdegOf (Formalism.REAL.muG ε) σ w = d := fdegOf_eq hd hw.1
  have hph : phLoc ε σ w = phA d (homOf σ hU) w := by
    funext g
    unfold phLoc phA
    rw [hdeg]
    rfl
  have : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  have hcoef : Integrable (fun g => ⟪w, homOf σ hU g w⟫_ℂ) (Formalism.REAL.muG ε) := by
    have h2 : Integrable (fun g => ((d : ℂ)⁻¹) * phLoc ε σ w g) (Formalism.REAL.muG ε) := hint.const_mul _
    have h3 := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp h2
    refine h3.congr (Filter.Eventually.of_forall fun g => ?_)
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.1.ne'
    simp only [phLoc, hdeg]
    rw [← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
    simp [coefOn, homOf_apply]
  obtain ⟨c1, c2, c3⟩ := habs (Formalism.REAL.UJ ε) (Formalism.REAL.muG ε) H (homOf σ hU) (homOf_norm σ hU) (homOf_cont σ hU) d hd.1
    (fun x y => schur_abs hd x y) w hw.1 hcoef
  refine ⟨hint, ?_, ?_, ?_⟩
  · intro g
    rw [hph]
    exact c1 g
  · intro x y
    rw [hph]
    exact c2 x y
  · intro Hp _ _ _ π hπ
    rw [hph]
    exact c3 Hp (homOf π hπ) (homOf_norm π hπ) (homOf_cont π hπ)

theorem family_projector_section_local {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Formalism.MainNotions.PlaceDegreeData.FamilyLocalProjectorOfAbstractProjector Fm :=
  fun h1 h2 h3 x i => projector_section_local (Fm.D x i) (h1 x i) (h2 x i) (h3 x i)

end Formalism.MainNotions.BridgeLemma

end
