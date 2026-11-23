import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.HilbertClassFieldArtin
import GroundTheory.GlobalFields.ComplexMultiplication.AutCFixed
import GroundTheory.ArithmeticGeometry.AbelianVarieties.Supersingular
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField IsDedekindDomain WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian

section Torsion

variable {F : Type*} [Field F] [Algebra F ℂ] (A : WeierstrassCurve F)

theorem baseChange_map_algEquiv (ρ : ℂ ≃ₐ[F] ℂ) :
    (A.baseChange ℂ).map (ρ : ℂ →+* ℂ) = A.baseChange ℂ := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  congr 1
  ext a
  exact ρ.commutes a

theorem nsmul_some_congr {V₁ V₂ : WeierstrassCurve ℂ} (e : V₁ = V₂) {x y : ℂ}
    (h₁ : V₁.toAffine.Nonsingular x y) (h₂ : V₂.toAffine.Nonsingular x y) {m : ℕ}
    (h : m • (Point.some x y h₁ : V₁.toAffine.Point) = 0) :
    m • (Point.some x y h₂ : V₂.toAffine.Point) = 0 := by
  subst e
  exact h

theorem exists_nsmul_some_algEquiv (ρ : ℂ ≃ₐ[F] ℂ) {m : ℕ} {x y : ℂ}
    (h : (A.baseChange ℂ).toAffine.Nonsingular x y)
    (hP : m • (Point.some x y h : (A.baseChange ℂ).toAffine.Point) = 0) :
    ∃ h' : (A.baseChange ℂ).toAffine.Nonsingular (ρ x) (ρ y),
      m • (Point.some (ρ x) (ρ y) h' : (A.baseChange ℂ).toAffine.Point) = 0 := by
  classical
  obtain ⟨h₁, e⟩ := pointMapRing_some (ρ : ℂ →+* ℂ) (A.baseChange ℂ) h
  have hA := baseChange_map_algEquiv A ρ
  have h₂ : (A.baseChange ℂ).toAffine.Nonsingular (ρ x) (ρ y) := by
    rw [← hA]
    exact h₁
  refine ⟨h₂, nsmul_some_congr hA h₁ h₂ ?_⟩
  have := congrArg (pointMapRing (ρ : ℂ →+* ℂ) (A.baseChange ℂ)) hP
  rwa [map_nsmul, e, map_zero] at this

theorem exists_nsmul_some_of_eq {V : WeierstrassCurve ℂ} {x y x' y' : ℂ} (hx : x = x') (hy : y = y')
    (h : V.toAffine.Nonsingular x y) {m : ℕ} (hm : m • (Point.some x y h : V.toAffine.Point) = 0) :
    ∃ h' : V.toAffine.Nonsingular x' y', m • (Point.some x' y' h' : V.toAffine.Point) = 0 := by
  subst hx
  subst hy
  exact ⟨h, hm⟩

omit [Algebra F ℂ] in
theorem isIntegral_of_isIntegral_add_natCast {B : Type*} [CommRing B] [Algebra F B] {x : B} (n : ℕ)
    (hx : IsIntegral F (x + n)) : IsIntegral F x := by
  have h := hx.sub (isIntegral_algebraMap (R := F) (x := (n : F)))
  rwa [map_natCast, add_sub_cancel_right] at h

variable [A.IsElliptic]

theorem isAlgebraic_of_nsmul_eq_zero {m : ℕ} (hm : m ≠ 0) {x y : ℂ}
    (h : (A.baseChange ℂ).toAffine.Nonsingular x y)
    (hP : m • (Point.some x y h : (A.baseChange ℂ).toAffine.Point) = 0) :
    IsAlgebraic F x ∧ IsAlgebraic F y := by
  classical
  have hfin := finite_torsionBy_natCast (A.baseChange ℂ) hm
  have hmem : ∀ {u v : ℂ} (k : (A.baseChange ℂ).toAffine.Nonsingular u v),
      m • (Point.some u v k : (A.baseChange ℂ).toAffine.Point) = 0 →
        (Point.some u v k : (A.baseChange ℂ).toAffine.Point) ∈
          AddSubgroup.torsionBy (A.baseChange ℂ).toAffine.Point (m : ℤ) := fun k hk ↦
    (mem_torsionBy_natCast_iff _ m _).2 hk
  constructor
  · by_contra hx
    have ht : ∀ n : ℕ, Transcendental F (x + n) := fun n hn ↦
      hx (isIntegral_of_isIntegral_add_natCast n hn.isIntegral).isAlgebraic
    have hρ : ∀ n : ℕ, ∃ ρ : ℂ ≃ₐ[F] ℂ, ρ x = x + n := fun n ↦
      exists_algEquiv_apply_eq_of_transcendental (fun h' ↦ hx h') (ht n)
    choose ρ hρ using hρ
    have hpt : ∀ n : ℕ, ∃ k : (A.baseChange ℂ).toAffine.Nonsingular (x + n) (ρ n y),
        m • (Point.some (x + n) (ρ n y) k : (A.baseChange ℂ).toAffine.Point) = 0 := fun n ↦ by
      obtain ⟨k, hk⟩ := exists_nsmul_some_algEquiv A (ρ n) h hP
      exact exists_nsmul_some_of_eq (hρ n) rfl k hk
    choose k hk using hpt
    have hinj : Function.Injective fun n : ℕ ↦
        (⟨Point.some (x + n) (ρ n y) (k n), hmem (k n) (hk n)⟩ :
          AddSubgroup.torsionBy (A.baseChange ℂ).toAffine.Point (m : ℤ)) := by
      intro a b hab
      have := congrArg Subtype.val hab
      simp only [Point.some.injEq, add_right_inj, Nat.cast_inj] at this
      exact this.1
    have := Finite.of_injective _ hinj
    exact not_finite ℕ
  · by_contra hy
    have ht : ∀ n : ℕ, Transcendental F (y + n) := fun n hn ↦
      hy (isIntegral_of_isIntegral_add_natCast n hn.isIntegral).isAlgebraic
    have hρ : ∀ n : ℕ, ∃ ρ : ℂ ≃ₐ[F] ℂ, ρ y = y + n := fun n ↦
      exists_algEquiv_apply_eq_of_transcendental (fun h' ↦ hy h') (ht n)
    choose ρ hρ using hρ
    have hpt : ∀ n : ℕ, ∃ k : (A.baseChange ℂ).toAffine.Nonsingular (ρ n x) (y + n),
        m • (Point.some (ρ n x) (y + n) k : (A.baseChange ℂ).toAffine.Point) = 0 := fun n ↦ by
      obtain ⟨k, hk⟩ := exists_nsmul_some_algEquiv A (ρ n) h hP
      exact exists_nsmul_some_of_eq rfl (hρ n) k hk
    choose k hk using hpt
    have hinj : Function.Injective fun n : ℕ ↦
        (⟨Point.some (ρ n x) (y + n) (k n), hmem (k n) (hk n)⟩ :
          AddSubgroup.torsionBy (A.baseChange ℂ).toAffine.Point (m : ℤ)) := by
      intro a b hab
      have := congrArg Subtype.val hab
      simp only [Point.some.injEq, add_right_inj, Nat.cast_inj] at this
      exact this.2
    have := Finite.of_injective _ hinj
    exact not_finite ℕ

end Torsion

section TorsionField

variable {K : Type*} [Field K] [Algebra K ℂ]

theorem exists_le_forall_torsion_mem (L₀ : IntermediateField K ℂ) [FiniteDimensional K L₀]
    (A : WeierstrassCurve L₀) [A.IsElliptic] {m : ℕ} (hm : m ≠ 0) :
    ∃ M : IntermediateField K ℂ, FiniteDimensional K M ∧ L₀ ≤ M ∧
      ∀ (x y : ℂ) (h : (A.baseChange ℂ).toAffine.Nonsingular x y),
        m • (Point.some x y h : (A.baseChange ℂ).toAffine.Point) = 0 → x ∈ M ∧ y ∈ M := by
  classical
  set T := AddSubgroup.torsionBy (A.baseChange ℂ).toAffine.Point (m : ℤ)
  have : Finite T := finite_torsionBy_natCast (A.baseChange ℂ) hm
  let c : (A.baseChange ℂ).toAffine.Point → Set ℂ := fun P ↦
    match P with
    | .zero => ∅
    | .some x y _ => {x, y}
  have hc : ∀ P, (c P).Finite := fun P ↦ by
    rcases P with _ | ⟨x, y, h⟩
    · exact Set.finite_empty
    · exact (Set.finite_singleton y).insert x
  set S : Set ℂ := ⋃ P : T, c P.1
  have hSfin : S.Finite := Set.finite_iUnion fun P ↦ hc P.1
  have hcoord : ∀ z ∈ S, IsIntegral K z := by
    intro z hz
    obtain ⟨⟨P, hP⟩, hzP⟩ := Set.mem_iUnion.1 hz
    have hP' : m • P = 0 := (mem_torsionBy_natCast_iff _ m P).1 hP
    rcases P with _ | ⟨x, y, h⟩
    · exact absurd hzP (Set.notMem_empty z)
    · obtain ⟨hx, hy⟩ := isAlgebraic_of_nsmul_eq_zero A hm h hP'
      have hz' : z = x ∨ z = y := hzP
      rcases hz' with rfl | rfl
      · exact isIntegral_trans (R := K) (A := L₀) _ hx.isIntegral
      · exact isIntegral_trans (R := K) (A := L₀) _ hy.isIntegral
  have : Finite S := hSfin.to_subtype
  have : FiniteDimensional K (IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin hcoord
  refine ⟨L₀ ⊔ IntermediateField.adjoin K S, inferInstance, le_sup_left, fun x y h hP ↦ ?_⟩
  have hPT : (Point.some x y h : (A.baseChange ℂ).toAffine.Point) ∈ T :=
    (mem_torsionBy_natCast_iff _ m _).2 hP
  have hx : x ∈ S := Set.mem_iUnion.2 ⟨⟨_, hPT⟩, Set.mem_insert x _⟩
  have hy : y ∈ S := Set.mem_iUnion.2 ⟨⟨_, hPT⟩, Set.mem_insert_of_mem x rfl⟩
  exact ⟨le_sup_right (a := L₀) (IntermediateField.subset_adjoin K S hx),
    le_sup_right (a := L₀) (IntermediateField.subset_adjoin K S hy)⟩

end TorsionField

section Frobenius

open scoped Pointwise

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

theorem exists_isArithFrobAt (L : IntermediateField K ℂ) [FiniteDimensional K L] [IsGalois K L]
    (τ : L ≃ₐ[K] L) {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ v ∈ degreeOnePrimes ℚ K ∧
      ∃ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal ∧
        w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ IsArithFrobAt (𝓞 K) τ w.asIdeal := by
  classical
  have : NumberField L := NumberField.of_module_finite K L
  set C : Set (L ≃ₐ[K] L) := {ρ | IsConj τ ρ}
  have hC : ∀ σ ∈ C, ∀ ρ : L ≃ₐ[K] L, ρ * σ * ρ⁻¹ ∈ C := fun σ hσ ρ ↦
    IsConj.trans hσ (isConj_iff.2 ⟨ρ, rfl⟩)
  have hdens := hasDirichletDensity_setOf_arithFrobAt_mem C hC
  rw [← hasDirichletDensity_inter_degreeOnePrimes_iff ℚ] at hdens
  have : Nonempty C := ⟨⟨τ, IsConj.refl τ⟩⟩
  have hpos : (0 : ℝ) < Nat.card C / Nat.card (L ≃ₐ[K] L) :=
    div_pos (Nat.cast_pos.2 Nat.card_pos) (Nat.cast_pos.2 Nat.card_pos)
  obtain ⟨v, ⟨hvA, hv1⟩, hvS⟩ :
      (({v : HeightOneSpectrum (𝓞 K) | ∀ w : HeightOneSpectrum (𝓞 L),
        w.asIdeal.LiesOver v.asIdeal → w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧
          arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal ∈ C} ∩ degreeOnePrimes ℚ K) \ S).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hne
    have h0 := hasDirichletDensity_zero_of_finite (hS.subset hne)
    have := hdens.dirichletDensity_eq.symm.trans h0.dirichletDensity_eq
    linarith
  obtain ⟨⟨w, hw⟩⟩ := nonempty_placesOver L v
  obtain ⟨c, hc⟩ := isConj_iff.1 (hvA w hw).2
  have hfrob : IsArithFrobAt (𝓞 K) (c * τ * c⁻¹) w.asIdeal := by
    rw [hc]
    exact IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal
  set w' : HeightOneSpectrum (𝓞 L) := ⟨c⁻¹ • w.asIdeal, Ideal.IsPrime.smul c⁻¹, fun h ↦ w.ne_bot (by
    rw [← smul_inv_smul c w.asIdeal, h, Ideal.smul_bot])⟩
  have hw' : w'.asIdeal.LiesOver v.asIdeal :=
    ⟨(hw.over).trans (Ideal.under_smul (𝓞 K) w.asIdeal c⁻¹).symm⟩
  refine ⟨v, hvS, hv1, w', hw', (hvA w' hw').1, ?_⟩
  have := hfrob.conj c⁻¹
  have e : c⁻¹ * (c * τ * c⁻¹) * c⁻¹⁻¹ = τ := by group
  rw [e] at this
  exact this

end Frobenius

end

end Elliptic
end GroundTheory.Global
