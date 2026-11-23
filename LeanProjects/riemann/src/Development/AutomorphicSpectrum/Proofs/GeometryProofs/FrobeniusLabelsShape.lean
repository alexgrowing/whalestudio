import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankFiniteFlatTorsionSubschemeEqCardPoints
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.AbelianFrobeniusLiftStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FrobeniusShapeOfSidePreservingStatement

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num

section Labels

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def labelEquiv (H : Host E) : (CMType H ⊕ CMType H) ≃ (E →+* ℂ) :=
  Equiv.ofBijective _ (LabelCount.labelCx_bijective H)

def embPrecomp (g : E ≃ₐ[ℚ] E) : (E →+* ℂ) ≃ (E →+* ℂ) where
  toFun σ := σ.comp (g : E →+* E)
  invFun σ := σ.comp (g.symm : E →+* E)
  left_inv σ := RingHom.ext fun x => by simp
  right_inv σ := RingHom.ext fun x => by simp

def labelPerm (H : Host E) (g : E ≃ₐ[ℚ] E) : Equiv.Perm (CMType H ⊕ CMType H) :=
  (labelEquiv H).trans ((embPrecomp g).trans (labelEquiv H).symm)

theorem labelCx_labelPerm (H : Host E) (g : E ≃ₐ[ℚ] E) (s : CMType H ⊕ CMType H) (x : E) :
    LabelCount.labelCx H (labelPerm H g s) x = LabelCount.labelCx H s (g x) := by
  have h : labelEquiv H (labelPerm H g s) = embPrecomp g (labelEquiv H s) := by
    simp [labelPerm]
  exact RingHom.congr_fun h x

theorem labelCx_rt (H : Host E) (s : CMType H ⊕ CMType H) :
    LabelCount.labelCx H s (H.rt : E) = if s.isLeft then H.rt0 else -H.rt0 := by
  rcases s with τ | τ
  · simp [LabelCount.labelCx, τ.2]
  · simp [LabelCount.labelCx, τ.2, HodgeCptTest.imaginary_root_conj]

theorem labelPerm_side (H : Host E) (g : E ≃ₐ[ℚ] E) :
    (∀ σ, (labelPerm H g σ).isLeft = σ.isLeft) ∨ ∀ σ, (labelPerm H g σ).isLeft = σ.isRight := by
  have hsq : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
    simpa using this
  have hg : g (H.rt : E) ^ 2 = (H.rt : E) ^ 2 := by
    rw [← map_pow, hsq]
    simp
  have hne := LabelCount.rt0_ne_neg H
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hg with h | h
  · left
    intro σ
    have h1 := labelCx_labelPerm H g σ (H.rt : E)
    rw [h, labelCx_rt, labelCx_rt] at h1
    cases h2 : (labelPerm H g σ).isLeft <;> cases h3 : σ.isLeft <;> simp [h2, h3] at h1 ⊢
    · exact hne h1.symm
    · exact hne h1
  · right
    intro σ
    have h1 := labelCx_labelPerm H g σ (H.rt : E)
    rw [h, map_neg, labelCx_rt, labelCx_rt] at h1
    have hr : σ.isRight = !σ.isLeft := by cases σ <;> rfl
    rw [hr]
    cases h2 : (labelPerm H g σ).isLeft <;> cases h3 : σ.isLeft <;> simp [h2, h3] at h1 ⊢
    · exact hne h1.symm
    · exact hne h1

variable {H : Host E} {l : Level H}

theorem coe_labelEmb_eq (c : Coeff l) (s : CMType H ⊕ CMType H) (a : 𝓞 E) :
    ((labelEmb c s a : c.F) : ℂ) = LabelCount.labelCx H s (a : E) := by
  rcases s with τ | τ
  · rfl
  · show τ.1 ((H.bar a : 𝓞 E) : E) = (starRingEnd ℂ) (τ.1 (a : E))
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]

def labelInt (c : Coeff l) (s : CMType H ⊕ CMType H) : 𝓞 E →+* 𝓞 c.F :=
  (labelEmb c s).codRestrict (integralClosure ℤ c.F).toSubring fun a =>
    IsIntegral.map (labelEmb c s).toIntAlgHom (RingOfIntegers.isIntegral a)

theorem coe_labelInt (c : Coeff l) (s : CMType H ⊕ CMType H) (a : 𝓞 E) :
    ((labelInt c s a : 𝓞 c.F) : c.F) = labelEmb c s a := rfl

theorem labelPerm_isFrobLabels (c : Coeff l) (p : ℕ) (g : E ≃ₐ[ℚ] E)
    (hg : ∀ (O : Type) [CommRing O] (n : Ideal O), n.IsPrime → (p : O) ∈ n → ∀ (τ : 𝓞 E →+* O) (x : 𝓞 E),
      τ (RingOfIntegers.mapRingEquiv g.toRingEquiv x) - τ x ^ p ∈ n) :
    IsFrobLabels c p (labelPerm H g) := by
  intro n hn hp s a u v hu hv
  have key := hg (𝓞 c.F) n hn hp (labelInt c s) a
  have h1 : u = labelInt c s (RingOfIntegers.mapRingEquiv g.toRingEquiv a) := by
    apply RingOfIntegers.ext
    rw [hu, coe_labelInt]
    apply Subtype.ext
    show ((labelEmb c (labelPerm H g s) a : c.F) : ℂ) =
      ((labelEmb c s (RingOfIntegers.mapRingEquiv g.toRingEquiv a) : c.F) : ℂ)
    rw [coe_labelEmb_eq, coe_labelEmb_eq, labelCx_labelPerm]
    rfl
  have h2 : v = labelInt c s a := by
    apply RingOfIntegers.ext
    rw [hv, coe_labelInt]
  rw [h1, h2]
  exact key

end Labels

theorem exists_frob_labels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E], (∀ a b : E ≃ₐ[ℚ] E, a * b = b * a) → ∀ (H : Host E) (l : Level H) (c : Coeff l) [Fintype (CMType H)] [DecidableEq (CMType H)], ∃ φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H), (∀ p : ℕ, p.Prime → IsFrobLabels c p (φ p)) ∧ FrobShape fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ) := by
  intro E _ _ _ _ hab H l c _ _
  classical
  have h := GlobalTheory.T.abelian_frobenius_lift E hab
  let φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H) := fun p =>
    if hp : p.Prime then labelPerm H (h p hp).choose else 1
  refine ⟨φ, fun p hp => ?_, GlobalTheory.T.frobenius_shape_of_side_preserving _ φ fun p => ?_⟩
  · simp only [φ, dif_pos hp]
    exact labelPerm_isFrobLabels c p _ (h p hp).choose_spec
  · by_cases hp : p.Prime
    · simp only [φ, dif_pos hp]
      exact labelPerm_side H _
    · left
      intro σ
      simp [φ, dif_neg hp]

end GlobalTheory.CompanionTheory.Ar.Num

end
