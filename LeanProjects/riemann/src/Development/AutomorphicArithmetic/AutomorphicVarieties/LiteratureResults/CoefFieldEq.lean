import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N UpperTheory.V.Af UpperTheory.V.Published.Kato Polynomial
open CongruenceSubgroup UpperHalfPlane MeasureTheory
open scoped Matrix MatrixGroups ModularForm

namespace UpperTheory.V.Lit

def pet (M k : ℕ) (f h : ℍ → ℂ) : ℂ :=
  ∑ᶠ γ : SL(2, ℤ) ⧸ Gamma1 M, ∫ z in ModularGroup.fd, petersson (k : ℤ) f h (γ.out⁻¹ • z)

def dil (d : ℕ) (hd : 0 < d) (g : ℍ → ℂ) : ℍ → ℂ := fun z => g ((⟨(d : ℝ), Nat.cast_pos.2 hd⟩ : {x : ℝ // 0 < x}) • z)

structure Primitive (k M : ℕ) (χ : DirichletCharacter ℂ M) (f : CuspForm (Gamma1 M) (k : ℤ)) : Prop where
  char : HasChar k χ f
  new : ∀ (M' d : ℕ) (h : M' ∣ M) (hd : 0 < d), M' ≠ M → d * M' ∣ M → ∀ χ' : DirichletCharacter ℂ M',
    DirichletCharacter.changeLevel h χ' = χ → ∀ g : CuspForm (Gamma1 M') (k : ℤ), HasChar k χ' g → pet M k f (dil d hd g) = 0
  eig : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∃ lam : ℂ, IsEigAt k χ f p lam
  one : coef f 1 = 1

section Sel

variable {l : ℕ} [Fact l.Prime] {C V : Type} [CommRing C] [Algebra ℤ_[l] C] [AddCommGroup V] [Module C V]
  [Module ℤ_[l] V] [IsScalarTower ℤ_[l] C V]
  {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [Algebra ℚ_[l] C] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
  [ContinuousConstSMul ℤ_[l] V] (ρ : Representation C (G K Ω) V) (T : Submodule ℤ_[l] V) (hT : ∀ g, ∀ x ∈ T, ρ g x ∈ T)

structure IsSelAll (z : G K Ω → V ⧸ T) : Prop where
  away : ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
    ∃ y ∈ Z1 (ρ.comp (Dec (F := K) A).subtype),
      (∃ x : V, ∀ s : ↥(Dec (F := K) A), (s : G K Ω) ∈ Ine (F := K) A → y s = ρ s x - x) ∧
      ∃ t : V ⧸ T, ∀ s : ↥(Dec (F := K) A), z s - T.mkQ (y s) = quotRep ρ T hT s t - t
  above : ∀ j : Ω →+* Om l,
    ∃ y ∈ Loc.finiteCocycles ((MonoidHom.snd _ _).comp (decJ K j).subtype) (ρ.comp ((MonoidHom.fst _ _).comp (decJ K j).subtype)),
      ∃ t : V ⧸ T, ∀ s : ↥(decJ K j), z s.1.1 - T.mkQ (y s) = quotRep ρ T hT s.1.1 t - t
  arch : ∀ (j : Ω →+* ℂ) (s : G K Ω), (∀ x, j (s x) = starRingEnd ℂ (j x)) → ∃ t : V ⧸ T, z s = quotRep ρ T hT s t - t

def SelAll : Set (H1 (quotRep ρ T hT)) :=
  {x | ∃ z : ↥(Z1 (quotRep ρ T hT)), Submodule.Quotient.mk z = x ∧ IsSelAll ρ T hT z.1}

end Sel

variable {l : ℕ} [Fact l.Prime]

def coefF (f : ℍ → ℂ) (ι : Qbar l ≃+* ℂ) : IntermediateField ℚ_[l] (Qbar l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range fun n => ι.symm (coef f n))

def FrobPoly (k M : ℕ) (χ : DirichletCharacter ℂ M) (f : ℍ → ℂ) {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ι : Qbar l ≃+* ℂ)
    (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 ℚ), ¬ normV w ∣ M * l → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
    (∀ s ∈ Ine (F := ℚ) A, V s = 1) ∧ ∀ σ : G ℚ Ω, IsFrob A (normV w) σ →
      (V σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.map ι.toRingHom =
        X ^ 2 - C (coef f (normV w)) * X + C (χ (normV w : ZMod M) * (normV w : ℂ) ^ (k - 1))

def KatoLit : Prop :=
  ∀ (k M : ℕ), 2 ≤ k → 0 < M → ∀ (χ : DirichletCharacter ℂ M) (f : CuspForm (Gamma1 M) (k : ℤ)), Primitive k M χ f →
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ),
    ∃ V : G ℚ Ω →* GL (Fin 2) ↥(coefF f ι), Continuous V ∧ FrobPoly k M χ f ι (toBar V) ∧
      ∀ (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K] [Algebra K Ω] [IsScalarTower ℚ K Ω] (r : ℕ),
        1 ≤ r → r ≤ k - 1 → 2 * r ≠ k →
        ∀ (T : Submodule ℤ_[l] (Fin 2 → ↥(coefF f ι))) (hT : IsLat (tw V (cycE ℚ Ω (coefF f ι) ^ r)) T),
          (SelAll ((Loc.colRep (tw V (cycE ℚ Ω (coefF f ι) ^ r))).comp
              (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) T (fun s => hT.stable _)).Finite

end UpperTheory.V.Lit
