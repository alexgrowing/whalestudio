import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.InseparableFrobenius
import GroundTheory.GlobalFields.ComplexMultiplication.DualDescent

namespace GroundTheory.Global

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField GroundTheory.Arith.Abelian

universe u

variable {F : Type u} [Field F] {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] (p : ℕ)
  [hp : Fact p.Prime] [CharP F p]

omit [E.IsElliptic] in

theorem exists_frobeniusPoint_eq {L : Type*} [Field L] [Algebra F L] [CharP L p] [PerfectRing L p]
    (P : ((frobeniusTwist E p).baseChange L).toAffine.Point) :
    ∃ R : (E.baseChange L).toAffine.Point, frobeniusPoint E p L R = P := by
  have hroot : ∀ z : L, ∃ w : L, w ^ p = z := fun z =>
    ⟨(frobeniusEquiv L p).symm z, by rw [← frobenius_def, frobenius_apply_frobeniusEquiv_symm]⟩
  rcases P with (_ | ⟨u, v, h⟩)
  · exact ⟨0, rfl⟩
  · obtain ⟨u', rfl⟩ := hroot u
    obtain ⟨v', rfl⟩ := hroot v
    exact ⟨.some u' v' ((nonsingular_pow_iff E p).mp h), rfl⟩

variable [PerfectRing F p]

theorem fieldRange_le_powField_of_not_isSeparable (φ : Isogeny E E') (hφ : ¬ φ.IsSeparable) :
    φ.comap.fieldRange ≤ powField E p := by
  have := φ.finiteDimensional
  apply le_powField_of_finSepDegree_lt E p
  exact lt_of_le_of_ne (Field.finSepDegree_le_finrank _ _)
    fun h => hφ ((Field.finSepDegree_eq_finrank_iff _ _).mp h)

theorem exists_comp_frobeniusIsogeny_eq (φ : Isogeny E E') (hφ : ¬ φ.IsSeparable) :
    ∃ ψ : Isogeny (frobeniusTwist E p) E', ψ.comp (frobeniusIsogeny E p) = φ := by
  classical
  have hle := fieldRange_le_powField_of_not_isSeparable p φ hφ
  rw [← fieldRange_comap_frobeniusIsogeny E p] at hle
  obtain ⟨a, ha⟩ := AlgHom.mem_fieldRange.mp (hle (AlgHom.mem_fieldRange.mpr ⟨genX E', φ.comap_genX⟩))
  obtain ⟨b, hb⟩ := AlgHom.mem_fieldRange.mp (hle (AlgHom.mem_fieldRange.mpr ⟨genY E', φ.comap_genY⟩))
  have hns : (E'.baseChange (frobeniusTwist E p).toAffine.FunctionField).toAffine.Nonsingular a b :=
    (E'.toAffine.baseChange_nonsingular (frobeniusIsogeny E p).comap.toRingHom.injective a b).mp (by
      rw [ha, hb]
      exact φ.nonsingular)
  have ht : Transcendental F a := fun h => φ.transcendental_alt (by rw [← ha]; exact h.algHom (frobeniusIsogeny E p).comap)
  set Q : (E'.baseChange (frobeniusTwist E p).toAffine.FunctionField).toAffine.Point :=
    .some a b hns with hQdef
  have hQ : Point.map (frobeniusIsogeny E p).comap Q = φ.1 := by
    rw [φ.val_eq_some_x_y, hQdef, Point.map_some]
    simp only [Point.some.injEq]
    exact ⟨ha, hb⟩

  have key : ∀ {L : Type u} [Field L] [Algebra F L] [CharP L p] [DecidableEq L]
      (R : (E.baseChange L).toAffine.Point) (hR : IsGenPt E R)
      (h' : IsGenPt (frobeniusTwist E p) (frobeniusPoint E p L R)),
      Point.map (genEval _ (frobeniusPoint E p L R) h') Q = φ.app R hR := by
    intro L _ _ _ _ R hR h'
    rw [genEval_congr _ (frobeniusIsogeny_app E p R hR).symm h'
      ((frobeniusIsogeny E p).isGenPt_app R hR), Isogeny.genEval_app, ← Point.map_map, hQ]
    rfl
  have hresp : RespectsAdd (frobeniusTwist E p) E' Q := by
    rw [respectsAdd_iff]
    intro L _ _ _ P₁ P₂ h₁ h₂ h₃
    have : CharP L p := charP_of_injective_algebraMap (algebraMap F L).injective p
    have : CharP (AlgebraicClosure L) p :=
      charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure L)).injective p
    let σ : L →ₐ[F] AlgebraicClosure L := IsScalarTower.toAlgHom F L (AlgebraicClosure L)
    obtain ⟨R₁, e₁⟩ := exists_frobeniusPoint_eq (E := E) p (Point.map σ P₁)
    obtain ⟨R₂, e₂⟩ := exists_frobeniusPoint_eq (E := E) p (Point.map σ P₂)
    have e₃ : frobeniusPoint E p _ (R₁ + R₂) = Point.map σ (P₁ + P₂) := by
      rw [frobeniusPoint_add, e₁, e₂, map_add]
    have gen : ∀ {R P} (hP : IsGenPt (frobeniusTwist E p) P)
        (e : frobeniusPoint E p (AlgebraicClosure L) R = Point.map σ P), IsGenPt E R :=
      fun hP e => (isGenPt_frobeniusPoint_iff E p _).mp (e ▸ isGenPt_map _ σ hP)
    have step : ∀ (P : ((frobeniusTwist E p).baseChange L).toAffine.Point)
        (hP : IsGenPt (frobeniusTwist E p) P) (R : (E.baseChange (AlgebraicClosure L)).toAffine.Point)
        (e : frobeniusPoint E p _ R = Point.map σ P),
        Point.map σ (Point.map (genEval _ P hP) Q) = φ.app R (gen hP e) := by
      intro P hP R e
      rw [Point.map_map, ← genEval_map, genEval_congr _ e.symm _
        ((isGenPt_frobeniusPoint_iff E p R).mpr (gen hP e))]
      exact key R _ _
    apply Point.map_injective (W' := E') σ
    rw [map_add, step _ h₁ R₁ e₁, step _ h₂ R₂ e₂, step _ h₃ _ e₃]
    exact φ.app_add (gen h₁ e₁) (gen h₂ e₂) (gen h₃ e₃)
  refine ⟨⟨Q, (isIsogeny_iff _).mpr ⟨ht, hresp⟩⟩, Isogeny.ext' ?_⟩
  exact (Isogeny.comp_val _ _).trans hQ

theorem exists_eq_comp_frobeniusIsogeny (φ : Isogeny E E')
    (hφ : isogenyPullback φ (invariantDifferential E') = 0) :
    ∃ ψ : Isogeny (frobeniusTwist E p) E', φ = ψ.comp (frobeniusIsogeny E p) ∧
      φ.degree = ψ.degree * p ∧ ψ.degree = φ.degree / p := by
  obtain ⟨ψ, hψ⟩ := exists_comp_frobeniusIsogeny_eq p φ
    fun h => (isSeparable_iff_isogenyPullback_ne_zero φ).mp h hφ
  have hd : φ.degree = ψ.degree * p := by
    rw [← hψ, Isogeny.degree_comp, degree_frobeniusIsogeny]
  exact ⟨ψ, hψ.symm, hd, by rw [hd, Nat.mul_div_cancel _ hp.out.pos]⟩

omit [E.IsElliptic] [CharP F p] [PerfectRing F p] hp in

theorem Isogeny.comap_bijective_of_degree_eq_one {E₁ E₂ : WeierstrassCurve F} [E₁.IsElliptic]
    [E₂.IsElliptic] (ψ : Isogeny E₁ E₂) (h : ψ.degree = 1) : Function.Bijective ψ.comap := by
  refine ⟨ψ.comap.toRingHom.injective, fun z => ?_⟩
  have htop : (⊤ : IntermediateField F E₁.toAffine.FunctionField) ≤ ψ.comap.fieldRange := by
    rw [← relfinrank_eq_one_iff, relfinrank_top_right]
    exact h
  exact AlgHom.mem_fieldRange.mp (htop trivial)

theorem exists_isomorphism_of_degree_eq (φ : Isogeny E E')
    (hφ : isogenyPullback φ (invariantDifferential E') = 0) (hdeg : φ.degree = p) :
    ∃ ψ : Isogeny (frobeniusTwist E p) E', φ = ψ.comp (frobeniusIsogeny E p) ∧ ψ.degree = 1 ∧
      Function.Bijective ψ.comap ∧
      (dualOver ψ).comp ψ = mulIsogeny (frobeniusTwist E p) 1 one_ne_zero ∧
      ψ.comp (dualOver ψ) = mulIsogeny E' 1 one_ne_zero := by
  obtain ⟨ψ, hψ, hd, -⟩ := exists_eq_comp_frobeniusIsogeny p φ hφ
  have h1 : ψ.degree = 1 := by
    rw [hdeg] at hd
    exact (Nat.mul_eq_right hp.out.ne_zero).mp hd.symm
  refine ⟨ψ, hψ, h1, Isogeny.comap_bijective_of_degree_eq_one ψ h1, ?_, ?_⟩
  · rw [dualOver_comp]
    congr 1
    simp [h1]
  · rw [comp_dualOver]
    congr 1
    simp [h1]

end GroundTheory.Global
