import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ExistsCentresLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.XUnip
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ShaLeV
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

namespace UpperTheory.V.PropA

variable (l : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀] [NumberField L₀]

def Descends (γ : G L₀ (AlgebraicClosure L₀)) : Prop :=
  ∀ e : ℕ, 1 ≤ e → ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l m L₀ L₁ →
    shaInv L₁ l e = cokerLen (xTw l l (⊤ : Subgroup (G L₀ (AlgebraicClosure L₀))) e γ ^ l ^ m - 1)

variable {l L₀}

theorem mem_levU_one {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {γ : G k Ω}
    (h : (l : ℤ_[l]) ∣ (cycZ k Ω l γ : ℤ_[l]) - 1) : γ ∈ levU l (⊤ : Subgroup (G k Ω)) 1 := by
  refine ⟨trivial, MonoidHom.mem_ker.2 (Units.ext ?_)⟩
  show PadicInt.toZModPow 1 (cycZ k Ω l γ : ℤ_[l]) = 1
  rw [← sub_eq_zero, ← map_one (PadicInt.toZModPow (p := l) 1), ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    pow_one, Ideal.mem_span_singleton]
  exact h

theorem Descends.eq_twLen {γ : G L₀ (AlgebraicClosure L₀)} (h : Descends l L₀ γ) {e : ℕ} (he : 1 ≤ e) {m : ℕ} {L₁ : Type}
    [Field L₁] [NumberField L₁] [Algebra L₀ L₁] (hL : IsLayer l m L₀ L₁) :
    shaInv L₁ l e = twLen (xRep l l (⊤ : Subgroup (G L₀ (AlgebraicClosure L₀))) γ) (cycZ L₀ _ l γ : ℤ_[l]) e m := by
  rw [h e he m L₁ hL, xTw_apply, zpow_natCast, Units.val_pow_eq_pow_val]
  rfl

theorem aBound_of_descends (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) {R c : ℕ}
    (ht : IsTower l L₀ R) {γ : G L₀ (AlgebraicClosure L₀)} (hu : IsLevel l (cycZ L₀ _ l γ : ℤ_[l]) c)
    (hc : ∃ ζ : L₀, IsPrimitiveRoot ζ (l ^ c)) (h : Descends l L₀ γ) : Win.ABound l R L₀ := by
  have hX : GenBy l R (XP l L₀) := ht.gen
  have hγ := xUnip L₀ (AlgebraicClosure L₀) l l ⊤ isClosed_univ ht.gen.finite γ (mem_levU_one (lteNorm l _ c hu).2.1)
  refine ⟨?_, fun e he m L₁ _ _ _ h₁ L₂ _ _ _ h₂ Ω _ _ _ D => ?_⟩
  · obtain ⟨s, hs⟩ := exists_centres_norm hX hγ hu
    refine ⟨ℚ_[l], inferInstance, inferInstance, inferInstance, c, R, fun i => s i, le_rfl, hc,
      fun e he m L₁ _ _ _ h₁ B hB => ?_⟩
    rw [h.eq_twLen he h₁]
    refine hs e m B fun i => (hB i).trans (le_of_eq ?_)
    rw [PadicInt.norm_def]
    push_cast
    rfl
  · haveI := ht.complex
    haveI : IsTotallyComplex L₂ := isTotallyComplex_of_algebra L₀ L₂
    rw [h.eq_twLen he h₁]
    refine (twLen_le_growth hX hγ hu e m).trans (add_le_add ?_ le_rfl)
    rw [← h.eq_twLen he (m := jZero l R) h₂, ← shaLen_eq_shaInv D]
    exact shaLeV hP hF hT L₂ Ω l (ptCase_of_isTotallyComplex L₂ l) D e

end UpperTheory.V.PropA

end
