import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.MemPass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeExistsMultipleIntegralPrimeToLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatMulIntegralMemCmLatticePrimeToStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulPrimePowMemConductorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralDiscMulCoordsOfCmFieldIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationBoundOfMulSqIntegralStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.RoadE

open GlobalTheory.CMVal

variable {E : Type} [Field E] [NumberField E]

def passScaled (t : E) (c : Ideal (OF E)) (y : (Af E)ˣ) (N : ℕ) : Lat (FR E) where
  carrier := {x | ∃ y' ∈ lattice c y, (N : E) * y' = ptE t x}
  add_mem' := fun {x x'} ⟨a, ha, hxa⟩ ⟨b, hb, hxb⟩ => ⟨a + b, (latticeSub c y).add_mem ha hb, by
    have : ptE t (x + x') = ptE t x + ptE t x' := by simp only [ptE, Pi.add_apply, Subfield.coe_add]; ring
    rw [this, ← hxa, ← hxb]; ring⟩
  zero_mem' := ⟨0, (latticeSub c y).zero_mem, by simp [ptE]⟩
  smul_mem' := fun a x ⟨b, hb, hxb⟩ => ⟨algebraMap (OF E) E a * b, mul_mem_lattice (algebraMap_mem_orderC c a) hb, by
    rw [ptE_smul, ← hxb]; ring⟩

end GlobalTheory.RoadE

namespace GlobalTheory.RoadE
open GlobalTheory.CMVal

theorem passl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (y : (Af E)ˣ) (θ : E) (D M₀ : ℕ), IsBaseCond 𝔣 → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → OneOver l y → 0 < D → IsIntegral ℤ θ → (θ - IsCMField.complexConj E θ) ^ 2 = -(D : E) → ¬ l ∣ M₀ → ∃ (M M' : ℕ) (L : Lat (FR E)), ¬ l ∣ M ∧ ¬ l ∣ M' ∧ M₀ ∣ M' ∧ HasLevel (M' * l ^ (padicValNat l D + a0 𝔣 l)) L ∧ (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y' ∈ lattice (condQ 𝔣 Q) y, ((M * D : ℕ) : E) * y' = (x 0 : E) * θ + (x 1 : E)) ∧ (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb (FR E)), Sz l lam (-(padicValNat l D : ℝ) / 2) ((i (v j) : ℝ) : ℂ)) ∧ Sz l lam (-(padicValNat l D : ℝ) / 2) ((M' * l ^ (padicValNat l D + a0 𝔣 l) : ℕ) : ℂ) := by
  intro E _ _ _ l _ lam 𝔣 Q y θ D M₀ hf hQ hy hD hθ hθD hM₀
  have hl : l.Prime := Fact.out
  set c := condQ 𝔣 Q with hc
  obtain ⟨M, hMl, hMint⟩ := GlobalTheory.T.cmLattice_exists_multiple_integral_prime_to_l E l c y hl hy
  obtain ⟨M₁, hM₁l, hM₁c⟩ := GlobalTheory.T.exists_coprime_mul_prime_pow_mem_conductor E l 𝔣 Q hl hf hQ
  have hM₁0 : M₁ ≠ 0 := by rintro rfl; exact hM₁l (dvd_zero l)
  have hM0 : M ≠ 0 := by rintro rfl; exact hMl (dvd_zero l)
  have hR : 0 < M₁ * l ^ a0 𝔣 l := Nat.pos_of_ne_zero (mul_ne_zero hM₁0 (pow_ne_zero _ hl.ne_zero))
  obtain ⟨M₂, hM₂l, hM₂⟩ := GlobalTheory.T.nat_mul_integral_mem_cmLattice_prime_to E l c y (M₁ * l ^ a0 𝔣 l) hl hy hR hM₁c
  obtain ⟨D', hD'⟩ := pow_padicValNat_dvd (p := l) (n := D)
  have hD'l : ¬ l ∣ D' := by
    rintro ⟨e, he⟩
    apply pow_succ_padicValNat_not_dvd (p := l) hD.ne'
    refine ⟨e, ?_⟩
    calc D = l ^ padicValNat l D * D' := hD'
      _ = l ^ (padicValNat l D + 1) * e := by rw [he, pow_succ]; ring
  have hnat : ∀ n : ℕ, IsIntegral ℤ (n : E) := fun n => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (n : ℤ)))
  have hDE : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
  have hDF : (D : FR E) ≠ 0 := by exact_mod_cast hD.ne'
  have key : ∀ x ∈ passScaled θ c y (M * D), ∀ j,
      IsIntegral ℤ ((D : FR E) * ((D : FR E)⁻¹ * x j) ^ 2) ∧ IsIntegral ℤ (x j) := by
    rintro x ⟨y', hy', hxy⟩ j
    have hpt : (((D : FR E)⁻¹ * x 0 : FR E) : E) * θ + (((D : FR E)⁻¹ * x 1 : FR E) : E) = (M : E) * y' := by
      simp only [ptE] at hxy
      push_cast at hxy ⊢
      have h' : (M : E) * y' = (D : E)⁻¹ * (((x 0 : FR E) : E) * θ + ((x 1 : FR E) : E)) := by
        rw [← hxy]; field_simp
      rw [h']; ring
    have h := GlobalTheory.T.isIntegral_disc_mul_coords_of_cmField_integral E θ D (fun j => (D : FR E)⁻¹ * x j) hD hθ hθD (by rw [hpt]; exact hMint y' hy') j
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    simp only [mul_inv_cancel_left₀ hDF] at h2
    exact h2
  refine ⟨M, M₀ * M * D' * M₂ * M₁, passScaled θ c y (M * D), hMl, ?_, ⟨M * D' * M₂ * M₁, by ring⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    exacts [hM₀ h, hMl h, hD'l h, hM₂l h, hM₁l h]
  · refine ⟨fun w hw => ?_, fun x hx => ?_⟩
    · have hwj : ∀ j, IsIntegral ℤ ((w j : FR E) : E) := by
        intro j
        have hwj1 : w j ∈ (1 : Submodule (𝓞 (FR E)) (FR E)) := Submodule.mem_pi.1 hw j (Set.mem_univ j)
        obtain ⟨a, ha⟩ := Submodule.mem_one.1 hwj1
        rw [← ha]
        exact (RingOfIntegers.isIntegral_coe a).map (RingHom.toIntAlgHom (maximalRealSubfield E).subtype)
      have hP : IsIntegral ℤ ((M₀ : E) * (((w 0 : FR E) : E) * θ + ((w 1 : FR E) : E))) :=
        (hnat M₀).mul (((hwj 0).mul hθ).add (hwj 1))
      refine ⟨_, hM₂ _ hP, ?_⟩
      have e : (D : E) = (l : E) ^ padicValNat l D * D' := by exact_mod_cast hD'
      simp only [ptE, Pi.smul_apply, Algebra.smul_def, Subfield.coe_mul, map_natCast]
      push_cast
      linear_combination ((M : E) * M₂ * M₁ * (l : E) ^ a0 𝔣 l * M₀ * (((w 0 : FR E) : E) * θ + ((w 1 : FR E) : E))) * e
    · intro j _
      change x j ∈ (1 : Submodule (𝓞 (FR E)) (FR E))
      rw [Submodule.mem_one]
      exact ⟨⟨x j, (key x hx j).2⟩, rfl⟩
  · intro x; exact Iff.rfl
  · intro w hw j i
    have h1 := (key w hw j).1
    set f : FR E →ₐ[ℤ] ℂ := RingHom.toIntAlgHom (Complex.ofRealHom.comp i) with hf
    have h2 : IsIntegral ℤ ((D : ℂ) * (f ((D : FR E)⁻¹ * w j)) ^ 2) := by
      have := h1.map f
      simpa [map_mul, map_pow, map_natCast] using this
    have h3 := (GlobalTheory.T.algebraicValuation_bound_of_mul_sq_integral l lam D 0 (f ((D : FR E)⁻¹ * w j)) hD h2).1
    have h4 : (D : ℂ) * f ((D : FR E)⁻¹ * w j) = ((i (w j) : ℝ) : ℂ) := by
      rw [← map_natCast f D, ← map_mul, mul_inv_cancel_left₀ hDF]
      rfl
    rwa [h4] at h3
  · have h := (GlobalTheory.T.algebraicValuation_bound_of_mul_sq_integral l lam D (M₀ * M * D' * M₂ * M₁ * l ^ a0 𝔣 l) 0 hD (by simpa using (isIntegral_zero : IsIntegral ℤ (0 : ℂ)))).2
    rwa [show M₀ * M * D' * M₂ * M₁ * l ^ (padicValNat l D + a0 𝔣 l) =
      M₀ * M * D' * M₂ * M₁ * l ^ a0 𝔣 l * l ^ padicValNat l D by ring]

end GlobalTheory.RoadE
