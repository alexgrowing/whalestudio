import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimeSetBoundDataOfPrimitiveChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern

namespace UpperTheory.V.Odd

section Act

variable {Ω : Type} [Field Ω]

def CycLift (N : ℕ) (b : (ZMod N)ˣ) (σ : Ω ≃+* Ω) : Prop := ∀ x : Ω, x ^ N = 1 → σ x = x ^ (b : ZMod N).val

variable (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def fixMu (N : ℕ) : Subgroup (G E Ω) where
  carrier := {g | ∀ x : Ω, x ^ N = 1 → g x = x}
  one_mem' _ _ := rfl
  mul_mem' {a b} ha hb x hx := by rw [AlgEquiv.mul_apply, hb x hx, ha x hx]
  inv_mem' {a} ha x hx := a.symm_apply_eq.2 (ha x hx).symm

theorem fixMu_le {M N : ℕ} (h : N ∣ M) : fixMu E Ω M ≤ fixMu E Ω N := by
  obtain ⟨k, rfl⟩ := h
  intro g hg x hx
  exact hg x (by rw [pow_mul, hx, one_pow])

variable {E}

def IsCycAct (N : ℕ) (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)) : Prop :=
  ∀ (b : (ZMod N)ˣ) (σ : Ω ≃+* Ω), CycLift N b σ → IsLift (ρ b).toRingEquiv σ

abbrev Gq {N : ℕ} (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)) : Type := (ZMod N)ˣ ⧸ ρ.ker

def piQ {N : ℕ} (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)) : (ZMod N)ˣ →* Gq ρ := QuotientGroup.mk' _

theorem piQ_surjective {N : ℕ} (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)) : Function.Surjective (piQ ρ) :=
  QuotientGroup.mk'_surjective _

variable {Ω} [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]

def actHom (D : LData E Ω l) (e : ℤ) : Representation ℤ_[l] (E ≃ₐ[ℚ] E) (H1 (qzTw D e)) where
  toFun τ := galoisActionOnCohomology D e τ.toRingEquiv
  map_one' := galois_action_cohomology_one D e
  map_mul' a b := galois_action_cohomology_mul D e a.toRingEquiv b.toRingEquiv

def actRep (D : LData E Ω l) (e : ℤ) {N : ℕ} (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)) :
    Representation ℤ_[l] (Gq ρ) (H1 (qzTw D e)) :=
  (actHom D e).comp (QuotientGroup.kerLift ρ)

theorem actRep_piQ (D : LData E Ω l) (e : ℤ) {N : ℕ} (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)) (b : (ZMod N)ˣ) :
    actRep D e ρ (piQ ρ b) = galoisActionOnCohomology D e (ρ b).toRingEquiv := rfl

end Act

example (Ω : Type) [Field Ω] [Algebra ℚ Ω] (N : ℕ) : IsCycAct (E := ℚ) Ω N 1 := fun _ σ _ x => by simp

def UnrHom (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (l : ℕ) : Set (G K Ω → ZMod l) :=
  {φ | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
    ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := K) A, φ g = 0}

def IsInt (l : ℕ) [Fact l.Prime] {Γ : Type} [CommGroup Γ] (z : MonoidAlgebra ℤ_[l] Γ) (y : MonoidAlgebra ℚ Γ) : Prop :=
  ∀ g, ((z.coeff g : ℤ_[l]) : ℚ_[l]) = ((y.coeff g : ℚ) : ℚ_[l])

section Psi

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

def chiOf {N : ℕ} (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)) {O : Subalgebra ℤ_[l] (PadicAlgCl l)} (ψ : (E ≃ₐ[ℚ] E) →* Oˣ) :
    DirichletCharacter (PadicAlgCl l) N :=
  MulChar.ofUnitHom ((Units.map O.val.toRingHom.toMonoidHom).comp (ψ.comp ρ))

theorem chiOf_unit {N : ℕ} (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)) {O : Subalgebra ℤ_[l] (PadicAlgCl l)}
    (ψ : (E ≃ₐ[ℚ] E) →* Oˣ) (b : (ZMod N)ˣ) : chiOf ρ ψ (b : ZMod N) = (((ψ (ρ b) : Oˣ) : O) : PadicAlgCl l) := by
  simp [chiOf]

def alN {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} (k : ℕ) (χ : DirichletCharacter R N) : R := (den N k : R) * Bprim k χ

def parE {N : ℕ} (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)) (k : ℕ) : Set (Subgroup (ZMod N)ˣ) := {K | ρ.ker ≤ K} ∩ parKer N k

variable (Ω : Type) [Field Ω] [Algebra E Ω] [Algebra ℚ Ω] [IsScalarTower ℚ E Ω] [Normal ℚ E]

def psiLen {O : Type} [CommRing O] [Algebra ℤ_[l] O] (e : ℕ) (ψ : (E ≃ₐ[ℚ] E) →* Oˣ) : ℕ∞ :=
  Module.length O (shaEig (twist₂ l (chiO ℚ Ω l O ^ (-(e : ℤ)))) l (galOf ℚ E Ω) ⊤
    ((ψ.comp (AlgEquiv.restrictNormalHom E)).comp (⊤ : Subgroup (G ℚ Ω)).subtype))

end Psi

def StickBound (C : ℝ) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ), 0 < N →
    Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∀ (l : ℕ) [Fact l.Prime] (D : LData E Ω l), Procyc E Ω l → ∀ e : ℕ, 1 ≤ e →
      minusLen D e ≠ ⊤ ∧ ((minusLen D e).toNat : ℝ) * Real.log l ≤
        C * l * (Module.finrank ℚ E : ℝ) ^ 2 * (e + 1) * Real.log ((e : ℝ) * l * N) ^ 2

def PsiBound : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [Algebra ℚ Ω] [IsScalarTower ℚ E Ω]
    [IsAlgClosure E Ω] [IsAlgClosure ℚ Ω] [IsAbelianGalois ℚ E] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)),
    IsCycAct Ω N ρ → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ l ∣ Module.finrank ℚ E →
    ∀ (O : Subalgebra ℤ_[l] (PadicAlgCl l)) [IsDiscreteValuationRing O] [Module.Finite ℤ_[l] O] (e : ℕ), 1 ≤ e →
    ∀ ψ : (E ≃ₐ[ℚ] E) →* Oˣ, chiOf ρ ψ (-1) = (-1) ^ (e + 1) →
    ∀ a : O, (a : PadicAlgCl l) = alN (e + 1) (chiOf ρ ψ) → psiLen (l := l) Ω e ψ ≤ IsDiscreteValuationRing.addVal O a

def PrimeBound : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ), 0 < N →
    Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∀ (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p) (e : ℕ), 1 ≤ e →
      (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ p ∣ Module.finrank ℚ E → minusLen (ld p) e ≠ ⊤) ∧
      ∀ S : Finset Nat.Primes, (∀ l ∈ S, (l : ℕ) ≠ 2 ∧ ¬ (l : ℕ) ∣ Module.finrank ℚ E) →
        ∑ l ∈ S, Real.log (l : ℕ) * ((@minusLen E Ω _ _ _ _ _ _ l ⟨l.2⟩ (@ld l ⟨l.2⟩) e).toNat : ℝ) ≤
          Module.finrank ℚ E * Real.log (bnd N (e + 1))

end UpperTheory.V.Odd

end
