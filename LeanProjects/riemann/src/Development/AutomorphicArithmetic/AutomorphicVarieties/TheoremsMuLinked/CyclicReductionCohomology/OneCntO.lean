import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PairOLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OmFacts

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private def chRep {A D : Type} (M : Type) [CommRing A] [Group D] [AddCommGroup M] [Module A M] (χ : D →* Aˣ) :
    Representation A D M where
  toFun g := (χ g : A) • LinearMap.id
  map_one' := by ext y; simp
  map_mul' g h := by ext y; simp [smul_smul, mul_comm]

private theorem chRep_apply {A D M : Type} [CommRing A] [Group D] [AddCommGroup M] [Module A M] (χ : D →* Aˣ)
    (g : D) (y : M) : chRep M χ g y = (χ g : A) • y := rfl

private theorem ker_le {A : Type} [CommRing A] (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)] (a : A)
    (h : J ≤ Ideal.span {a}) (S : Submodule A (A ⧸ I)) (hS : ∀ y ∈ S, a • y = 0) :
    Nat.card S ≤ Nat.card (A ⧸ J) := by
  let f : (A ⧸ I) →ₗ[A] (A ⧸ I) := a • LinearMap.id
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  rw [Nat.card_congr (f.quotKerEquivRange).toEquiv] at h1
  have h3 : Nat.card (LinearMap.ker f) = Nat.card ((A ⧸ I) ⧸ LinearMap.range f) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := LinearMap.range f))
    rw [← h2, mul_comm, ← h1]
  have h4 : Nat.card S ≤ Nat.card (LinearMap.ker f) :=
    Nat.card_le_card_of_injective _ (Submodule.inclusion_injective (show S ≤ LinearMap.ker f from hS))
  let p : A →ₗ[A] ((A ⧸ I) ⧸ LinearMap.range f) := (LinearMap.range f).mkQ.comp (Submodule.mkQ I)
  have hp : J ≤ LinearMap.ker p := by
    intro y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 (h hy)
    refine (Submodule.Quotient.mk_eq_zero _).2 ⟨Submodule.mkQ I c, ?_⟩
    exact (map_smul (Submodule.mkQ I) a c).symm
  have hs : Function.Surjective (Submodule.liftQ J p hp) := by
    intro y
    obtain ⟨c, rfl⟩ := ((Submodule.mkQ_surjective (LinearMap.range f)).comp (Submodule.mkQ_surjective I)) y
    exact ⟨Submodule.mkQ J c, rfl⟩
  exact h4.trans (h3.le.trans (Nat.card_le_card_of_surjective _ hs))

theorem UpperTheory.V.Th.oneCntO :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] (ε : D →* ℤ_[l]ˣ) (d : ℕ) (χ : D →* Oˣ), LocCnt D ε d → AdicCont (maximalIdeal O) (fun g => (χ g : O)) → (∃ g, (χ g : O) ≠ algebraMap ℤ_[l] O (ε g : ℤ_[l])) → ∃ C : ℕ, ∀ m, {z : D → Om O m | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + (χ g : O) • z h}.Finite ∧ {z : D → Om O m | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + (χ g : O) • z h}.ncard ≤ Nat.card (ResidueField O) ^ (m * (1 + d) + C) := by
  intro l _ O _ _ _ _ _ D _ _ _ ε d χ hL hχ ⟨g₀, hg₀⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨C, hC⟩ := IsDiscreteValuationRing.associated_pow_irreducible (sub_ne_zero.2 hg₀) hϖ
  refine ⟨C, fun m => ?_⟩
  obtain ⟨hfin, hcard, -, -, hlc⟩ := (omFacts l O).2 m
  obtain ⟨hfinC, hcardC, -⟩ := (omFacts l O).2 C
  obtain ⟨k, τ, hk, hτ, hlin⟩ := pairO l O m
  let e : D →* Oˣ := (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp ε
  have he : ∀ g, (e g : O) = algebraMap ℤ_[l] O (ε g : ℤ_[l]) := fun _ => rfl
  let χ' : D →* Oˣ := e * χ⁻¹
  have hχ' : ∀ g, (χ g : O) * χ' g = e g := fun g => by
    rw [← Units.val_mul]
    congr 1
    simp [χ']
  let b : Om O m →+ Om O m →+ ZMod (l ^ k) := (AddMonoidHom.mul (R := Om O m)).compr₂ τ
  have hb : ∀ y z, b y z = τ (y * z) := fun _ _ => rfl
  have hLC : LC (chRep (Om O m) χ) := fun y =>
    (hlc D _ hχ).comp (fun u => u * y)
  have hD : DualPair k ε (chRep (Om O m) χ) (chRep (Om O m) χ') b :=
    { left := fun y h => hτ y h
      right := fun y h => hτ y fun z => by rw [mul_comm]; exact h z
      equiv := fun g y z => by
        rw [hb, hb, chRep_apply, chRep_apply, smul_mul_smul_comm, hχ', he, Algebra.smul_def, hlin] }
  obtain ⟨hf, hc⟩ := hL k hk O (Om O m) (Om O m) _ _ b hLC hD
  have hinv : Nat.card (chRep (Om O m) χ').invariants ≤ Nat.card (Om O C) := by
    refine ker_le _ _ ((χ g₀ : O) - algebraMap ℤ_[l] O (ε g₀ : ℤ_[l])) ?_ _ fun y hy => ?_
    · rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
      exact (Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_span_singleton.2 hC.dvd)
    · have h1 : (χ' g₀ : O) • y = y := hy g₀
      rw [← he, ← hχ', sub_smul, mul_smul, h1, sub_self]
  refine ⟨hf, ?_⟩
  have h2 : {z : D → Om O m | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + (χ g : O) • z h}.ncard =
      Nat.card (Zl (chRep (Om O m) χ)) := rfl
  rw [h2, hc, hcard, ← pow_mul, pow_add, ← hcardC]
  exact Nat.mul_le_mul_left _ hinv
