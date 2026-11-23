import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.TwistIne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

namespace UpperTheory.V.Cu2

namespace AlgType

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime]

private theorem isAlgPos_mul {χ χ' : HChar K} {n n' : (K →+* ℂ) → ℤ} (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') :
    IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

private theorem isAlgPos_inv {χ : HChar K} {n : (K →+* ℂ) → ℤ} (h : IsAlgPos χ n) : IsAlgPos χ⁻¹ (-n) := fun k hk => by
  have e : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl
  rw [e, Units.val_inv_eq_inv_val, h k hk, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm

def Good (art : Ideles K →* Gab K Ω) (ι : Qbar l ≃+* ℂ) (t : (K →+* ℂ) → ℤ) (ψ : G K Ω →* (Qbar l)ˣ) : Prop :=
  ∃ Y : HChar K, IsAlgPos Y t ∧ IsLAdicOf art ι Y t ψ

theorem good_cong {art : Ideles K →* Gab K Ω} {ι : Qbar l ≃+* ℂ} {t t' : (K →+* ℂ) → ℤ}
    {ψ ψ' : G K Ω →* (Qbar l)ˣ} (h : Good art ι t ψ) (ht : t = t') (hψ : ψ = ψ') : Good art ι t' ψ' := by
  subst ht hψ
  exact h

theorem good_mul {art : Ideles K →* Gab K Ω} {ι : Qbar l ≃+* ℂ} {t t' : (K →+* ℂ) → ℤ}
    {ψ ψ' : G K Ω →* (Qbar l)ˣ} (h : Good art ι t ψ) (h' : Good art ι t' ψ') : Good art ι (t + t') (ψ * ψ') := by
  obtain ⟨Y, h1, h2⟩ := h
  obtain ⟨Y', h1', h2'⟩ := h'
  exact ⟨Y * Y', isAlgPos_mul h1 h1', h2.mul h2'⟩

theorem good_one {art : Ideles K →* Gab K Ω} {ι : Qbar l ≃+* ℂ} {t : (K →+* ℂ) → ℤ}
    {ψ : G K Ω →* (Qbar l)ˣ} (h : Good art ι t ψ) : Good art ι 0 1 := by
  obtain ⟨Y, h1, h2⟩ := h
  exact good_cong ⟨Y * Y⁻¹, isAlgPos_mul h1 (isAlgPos_inv h1), h2.mul h2.inv⟩ (add_neg_cancel t) (mul_inv_cancel ψ)

theorem good_cyc {art : Ideles K →* Gab K Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ) :
    Good art ι (fun _ => 1) (cycBar K Ω l) := by
  have h := GlobalTheory.Published.CharAboveModel.absPow_isAlgPos K 1
  obtain ⟨μ, hμ, hL⟩ := ha.exists_isLAdicOf ι h
  have e : μ = cycBar K Ω l ^ 1 := GlobalTheory.Published.CharAboveModel.eq_cyc_pow ha hμ hL
  rw [pow_one] at e
  subst e
  exact good_cong ⟨_, h, hL⟩ (funext fun _ => Nat.cast_one) rfl

end AlgType

open AlgType in
theorem algType (hP : Af.Hypotheses₂) : AlgType := by
  intro K Ω _ _ _ _ _ l _ ι art Y a κ ha h1 h2 n j
  have H : Good art ι a κ := ⟨Y, h1, h2⟩
  have H1 : Good art ι (fun _ => 1) (cycBar K Ω l) := good_cyc ha ι
  have H0 : Good art ι 0 1 := good_one H
  have key0 : ∀ j : ℕ, Good art ι (fun _ => (j : ℤ)) (cycBar K Ω l ^ j) := by
    intro j
    induction j with
    | zero => exact good_cong H0 (funext fun _ => by simp) (pow_zero _).symm
    | succ j ih =>
      exact good_cong (good_mul ih H1) (funext fun _ => by simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one] <;> ring)
        (pow_succ _ _).symm
  have key : ∀ n : ℕ, Good art ι (fun e => (n : ℤ) * a e + j) (κ ^ n * cycBar K Ω l ^ j) := by
    intro n
    induction n with
    | zero => exact good_cong (key0 j) (funext fun _ => by simp) (by simp)
    | succ n ih =>
      refine good_cong (good_mul ih H) (funext fun e => ?_) ?_
      · simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one] <;> ring
      · rw [pow_succ]
        exact mul_right_comm _ _ _
  exact key n

end UpperTheory.V.Cu2

end
