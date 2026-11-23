import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetD

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

variable {g : ℕ} {Y Y' : Scheme.{0}}

theorem isHolFam_const (u : Sp ℂ ⟶ Y) : IsHolFam (g := g) (fun _ => u) := by
  intro U f
  exact ⟨isOpen_const, differentiableOn_const _⟩

def jetZero (m : ℕ) : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m :=
  jetMap (fun _ => 0) fun _ => Ideal.zero_mem _

theorem jetZero_eq (m : ℕ) (a : Jet ℂ (Fin 1 × Fin g) m) :
    jetZero m a = algebraMap ℂ _ ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) a) := by
  have h : (jetZero m : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) =
      (Algebra.ofId ℂ (Jet ℂ (Fin 1 × Fin g) m)).comp jetAug := by
    apply Ideal.Quotient.algHom_ext
    simp only [jetZero, jetMap, jetAug, liftJet, AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp]
    apply MvPolynomial.algHom_ext
    intro i
    simp
  rw [h]
  rfl

theorem jetPt_const (u : Sp ℂ ⟶ Y) (m : ℕ) :
    spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)) ≫ u = jetPt (fun _ => u) (isHolFam_const u) m := by
  have hl : IsLocalHom ((jetZero m : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) :
      Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) :=
    isLocalHom_jetMap (m := m) (fun _ => 0) (fun _ => Ideal.zero_mem _)
  have h1 := jetPt_precomp (fun _ => u) (fun _ => u) (isHolFam_const u) (isHolFam_const u) rfl m
    ((jetZero m : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) :
      Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m)
    (fun U _ f => by simp only [jetOf_const, AlgHom.coe_toRingHom, AlgHom.commutes])
  rw [← h1]
  have h2 : ((jetZero m : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) :
      Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) =
      (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)).comp
        ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ) := by
    exact RingHom.ext fun a => jetZero_eq m a
  have h3 : spMap ((algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)).comp
        ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ)) =
      spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)) ≫
        spMap ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ) := by
    first
    | rfl
    | (simp only [spMap]; rw [← Spec.map_comp]; rfl)
    | (unfold spMap; rw [← Spec.map_comp]; rfl)
  rw [h2, h3, Category.assoc, jetPt_aug]

theorem jetPt_over (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (p : Y ⟶ Y') (u : Sp ℂ ⟶ Y')
    (he : ∀ z, e z ≫ p = u) (m : ℕ) :
    jetPt e hol m ≫ p = spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)) ≫ u := by
  rw [jetPt_comp e hol p (fun _ => u) (isHolFam_const u) he m, ← jetPt_const u m]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
