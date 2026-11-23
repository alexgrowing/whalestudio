import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CrystallineDeformationFibreProductAmalgamationStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CrLift
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem GlobalTheory.OrdLoc.dcr_amalgamate : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (C : Type) [CommRing C] [Algebra ℚ_[l] C] [Module.Finite ℚ_[l] C] [Algebra O C] [Algebra ℤ_[l] C] [IsScalarTower ℤ_[l] O C] [IsScalarTower ℤ_[l] ℚ_[l] C] [Algebra E C] [IsScalarTower O E C] [IsScalarTower ℚ_[l] E C] (πC : C →ₐ[E] E) (hπC : ∀ a, πC a = 0 → IsNilpotent a) (T : Type) [CommRing T] [Algebra ℚ_[l] T] [Module.Finite ℚ_[l] T] [Algebra O T] [Algebra ℤ_[l] T] [IsScalarTower ℤ_[l] O T] [IsScalarTower ℤ_[l] ℚ_[l] T] [Algebra E T] [IsScalarTower O E T] [IsScalarTower ℚ_[l] E T] (πT : T →ₐ[E] E) (hπT : ∀ a, πT a = 0 → IsNilpotent a) (p₁ : T →ₐ[E] B) (p₂ : T →ₐ[E] C), π.comp p₁ = πT → πC.comp p₂ = πT → (∀ b c, π b = πC c → ∃ t, p₁ t = b ∧ p₂ t = c) → ∀ (r₁ : GQ l →* GG 3 B) (r₂ : GQ l →* GG 3 C), D.InDcr (π : B →+* E) r₁ → D.InDcr (πC : C →+* E) r₂ → ∃ r : GQ l →* GG 3 T, D.InDcr (πT : T →+* E) r ∧ (GG.map (p₁ : T →+* B)).comp r = r₁ ∧ (GG.map (p₂ : T →+* C)).comp r = r₂ := by
  intro hP l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ C _ _ _ _ _ _ _ _ _ _ πC hπC
    T _ _ _ _ _ _ _ _ _ _ πT hπT p₁ p₂ h₁ h₂ hs r₁ r₂ hr₁ hr₂
  let I : Ideal T := RingHom.ker p₁ ⊓ RingHom.ker p₂
  let q : T →ₐ[E] (T ⧸ I) := Ideal.Quotient.mkₐ E I
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective E I
  let q₁ : (T ⧸ I) →ₐ[E] B := Ideal.Quotient.liftₐ I p₁ fun a ha => ha.1
  let q₂ : (T ⧸ I) →ₐ[E] C := Ideal.Quotient.liftₐ I p₂ fun a ha => ha.2
  have e₁ : ∀ t, q₁ (q t) = p₁ t := fun t => rfl
  have e₂ : ∀ t, q₂ (q t) = p₂ t := fun t => rfl
  have f₁ : ∀ t, π (p₁ t) = πT t := fun t => DFunLike.congr_fun h₁ t
  have f₂ : ∀ t, πC (p₂ t) = πT t := fun t => DFunLike.congr_fun h₂ t
  have hn : ∀ a, (π.comp q₁) a = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨t, rfl⟩ := hq a
    exact (hπT t ((f₁ t).symm.trans ha)).map q
  have hc₂ : πC.comp q₂ = π.comp q₁ := by
    refine AlgHom.ext fun a => ?_
    obtain ⟨t, rfl⟩ := hq a
    exact (f₂ t).trans (f₁ t).symm
  have hu : ∀ b c, π b = πC c → ∃! t, q₁ t = b ∧ q₂ t = c := by
    intro b c h
    obtain ⟨t, ht₁, ht₂⟩ := hs b c h
    refine ⟨q t, ⟨ht₁, ht₂⟩, ?_⟩
    rintro s ⟨hs₁, hs₂⟩
    obtain ⟨s, rfl⟩ := hq s
    refine Ideal.Quotient.eq.2 ⟨?_, ?_⟩
    · change p₁ (s - t) = 0
      rw [map_sub, ← e₁ s, hs₁, ht₁, sub_self]
    · change p₂ (s - t) = 0
      rw [map_sub, ← e₂ s, hs₂, ht₂, sub_self]
  obtain ⟨r', hr', g₁, g₂⟩ := GlobalTheory.T.crystalline_deformation_fibre_product_amalgamation D E B π hπ C πC hπC (T ⧸ I) (π.comp q₁) hn q₁ q₂ rfl hc₂ hu
    r₁ r₂ hr₁ hr₂
  obtain ⟨r, hr, rfl⟩ := crLift hP D E T πT hπT (T ⧸ I) (π.comp q₁) hn q hq (AlgHom.ext f₁) r' hr'
  exact ⟨r, hr, by rw [← g₁]; rfl, by rw [← g₂]; rfl⟩
