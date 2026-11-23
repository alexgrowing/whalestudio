import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FinAm
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AuxiliaryVectorCutByHermitianLinearForm
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

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

theorem UpperTheory.V.Pa.oneCount :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] (ε : D →* ℤ_[l]ˣ) (d : ℕ) (χ : D →* x.Aˣ), LocCount D ε d → AdicCont (IsLocalRing.maximalIdeal x.A) (fun g => (χ g : x.A)) → (∃ g, (χ g : x.A) ≠ algebraMap ℤ_[l] x.A (ε g : ℤ_[l])) → ∃ C : ℕ, ∀ m, {z : D → x.Am m | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + (χ g : x.A) • z h}.Finite ∧ {z : D → x.Am m | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + (χ g : x.A) • z h}.ncard ≤ Nat.card x.K ^ (m * (1 + d) + C) := by
  intro l _ F n x D _ _ _ ε d χ hL hχ ⟨g₀, hg₀⟩
  obtain ⟨C, hC⟩ := IsDiscreteValuationRing.associated_pow_irreducible (sub_ne_zero.2 hg₀)
    (PowerSeries.X_irreducible (R := x.K))
  refine ⟨C, fun m => ?_⟩
  obtain ⟨hfin, hcard, -⟩ := finAm l F n x m 0
  obtain ⟨hfinC, hcardC, -⟩ := finAm l F n x C 0
  obtain ⟨τ, hτ, hlin⟩ := pair1 l F n x m
  let e : D →* x.Aˣ := (Units.map (algebraMap ℤ_[l] x.A).toMonoidHom).comp ε
  have he : ∀ g, (e g : x.A) = algebraMap ℤ_[l] x.A (ε g : ℤ_[l]) := fun _ => rfl
  let χ' : D →* x.Aˣ := e * χ⁻¹
  have hχ' : ∀ g, (χ g : x.A) * χ' g = e g := fun g => by
    rw [← Units.val_mul]
    congr 1
    simp [χ']
  let b : x.Am m →+ x.Am m →+ ZMod l := (AddMonoidHom.mul (R := x.Am m)).compr₂ τ
  have hb : ∀ y z, b y z = τ (y * z) := fun _ _ => rfl
  have hLC : LC (chRep (x.Am m) χ) := fun y => by
    have h1 := hχ m
    have hI : IsLocalRing.maximalIdeal x.A ^ m ≤ Ideal.span {x.t ^ m} := by
      rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow]
    exact h1.comp (fun u => Ideal.Quotient.factor hI u * y)
  have hD : IsDualPair ε (chRep (x.Am m) χ) (chRep (x.Am m) χ') b :=
    { left := fun y h => hτ y h
      right := fun y h => hτ y fun z => by rw [mul_comm]; exact h z
      equiv := fun g y z => by
        rw [hb, hb, chRep_apply, chRep_apply, smul_mul_smul_comm, hχ', he, Algebra.smul_def, hlin]
        rfl }
  obtain ⟨hf, hc⟩ := hL x.A (x.Am m) (x.Am m) _ _ b hLC hD
  have hinv : Nat.card (chRep (x.Am m) χ').invariants ≤ Nat.card (x.Am C) := by
    refine ker_le _ _ _ ((Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_span_singleton.2 hC.dvd)) _ fun y hy => ?_
    have h1 : (χ' g₀ : x.A) • y = y := hy g₀
    rw [← he, ← hχ', sub_smul, mul_smul, h1, sub_self]
  refine ⟨hf, ?_⟩
  have h2 : {z : D → x.Am m | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + (χ g : x.A) • z h}.ncard =
      Nat.card (Zl (chRep (x.Am m) χ)) := rfl
  rw [h2, hc, hcard, ← pow_mul, pow_add, ← hcardC]
  exact Nat.mul_le_mul_left _ hinv
