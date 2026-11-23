import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocC
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CovariantDegrees

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LB

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l}
  {A : ValuationSubring Ω} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)

theorem continuous_rHom : Continuous (rHom (E := E) hj) :=
  by apply _root_.UpperTheory.Reformulated.B.CovariantDegrees.continuous_rHom <;> assumption

instance compact_GK (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    CompactSpace ↥K.fixingSubgroup :=
  isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed K).isCompact

def eDec : ↥(Dec (F := E) A) ≃* ↥(KwF (E := E) j).fixingSubgroup :=
  (MulEquiv.ofBijective (rHom hj) ⟨rHom_injective hj, rHom_surjective hj⟩).symm

theorem eDec_comm (g : ↥(Dec (F := E) A)) (x : Ω) :
    ((eDec hj g : ↥(KwF (E := E) j).fixingSubgroup) : GQ l) (j x) = j ((g : G E Ω) x) := by
  rw [← j_rHom hj]
  congr 2
  exact congrArg Subtype.val ((MulEquiv.ofBijective (rHom hj) ⟨rHom_injective hj, rHom_surjective hj⟩).apply_symm_apply g)

theorem continuous_eDec_symm : Continuous (eDec (E := E) hj).symm := continuous_rHom hj

theorem continuous_eDec : Continuous (eDec (E := E) hj) :=
  Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := (MulEquiv.ofBijective (rHom hj) ⟨rHom_injective hj, rHom_surjective hj⟩).toEquiv)
    (continuous_rHom hj)

def bridgeOf (LL : FinExt l)
    (hLL : ∀ (τ : ↥(KwF (E := E) j) →ₐ[ℚ_[l]] Om l) (x : ↥(KwF (E := E) j)), τ x ∈ LL.1) :
    LocBridge l E Ω (Dec (F := E) A) ↥(OL LL) where
  Kw := ⟨KwF (E := E) j, KwF_fin j⟩
  j := j
  j_E := jE_mem j
  j_dense := KwF_le_clE j
  e := eDec hj
  e_cont := continuous_eDec hj
  e_symm_cont := continuous_eDec_symm hj
  e_comm := eDec_comm hj
  LL := LL
  LL_split := hLL
  eO := RingEquiv.refl _
  eO_alg := fun _ => rfl
  eO_cont := continuous_id
  eO_symm_cont := continuous_id

def nclo (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] : FinExt l :=
  ⟨IntermediateField.normalClosure ℚ_[l] K (PadicAlgCl l), inferInstance⟩

theorem mem_nclo (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
    (τ : ↥K →ₐ[ℚ_[l]] Om l) (x : ↥K) : τ x ∈ (nclo K).1 :=
  τ.fieldRange_le_normalClosure ⟨x, rfl⟩

end Formalism.BasicNotions.Examples₂.LB

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc LB

theorem locBridge_nonempty (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    ∃ (j : Ω →+* Om l) (_ : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1), ∀ LL : FinExt l,
      (∀ (τ : ↥(KwF (E := E) j) →ₐ[ℚ_[l]] Om l) (x : ↥(KwF (E := E) j)), τ x ∈ LL.1) →
      ∃ B : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL), B.j = j ∧ B.LL = LL ∧ B.Kw.1 = KwF (E := E) j := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosure ℚ Ω := isAlgClosureQ E Ω
  obtain ⟨j, hj⟩ := exists_emb (l := l) A hA
  exact ⟨j, hj, fun LL hLL => ⟨bridgeOf hj LL hLL, rfl, rfl, rfl⟩⟩

end Formalism.BasicNotions.Examples₂
