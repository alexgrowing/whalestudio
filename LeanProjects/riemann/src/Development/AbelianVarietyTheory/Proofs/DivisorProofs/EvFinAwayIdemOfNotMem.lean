import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMemSecFinHyperbolic

noncomputable section

open scoped Matrix NNReal TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.WeilM GlobalTheory.LocIntw
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.SWLit

namespace GlobalTheory.AwayFix

section Idem

variable {F : Type} [Field F] [NumberField F]

open Classical in

def awayFin (S : Finset (HeightOneSpectrum (𝓞 F))) : Af F :=
  ⟨fun v => if v ∈ S then 0 else 1, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ S
    · simp only [h, if_true]; exact zero_mem _
    · simp only [h, if_false]; exact one_mem _⟩

def awayIdem (S : Finset (HeightOneSpectrum (𝓞 F))) : AF F := pairA F 0 (awayFin S)

theorem awayFin_mul_self (S : Finset (HeightOneSpectrum (𝓞 F))) : awayFin S * awayFin S = awayFin S := by
  classical
  refine Subtype.ext (funext fun v => ?_)
  show (if v ∈ S then (0 : Fv F v) else 1) * (if v ∈ S then 0 else 1) = if v ∈ S then 0 else 1
  split_ifs <;> simp

theorem awayIdem_mul_self (S : Finset (HeightOneSpectrum (𝓞 F))) : awayIdem S * awayIdem S = awayIdem S :=
  Prod.ext (zero_mul _) (awayFin_mul_self S)

theorem awayIdem_fst (S : Finset (HeightOneSpectrum (𝓞 F))) : (awayIdem S).1 = 0 := rfl

end Idem

section Pt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {N : ℕ}
  {Q : Matrix (Fin N) (Fin N) E}

def idemMat (e : AF F) (X : Matrix (Fin N) (Fin N) (AE F E)) : Matrix (Fin N) (Fin N) (AE F E) := e • X + (1 - e) • 1

section
variable {e : AF F} (he : e * e = e)
include he

theorem idem_mul_one_sub : e * (1 - e) = 0 := by linear_combination -he
theorem one_sub_mul_idem : (1 - e) * e = 0 := by linear_combination -he
theorem one_sub_idem_mul : (1 - e) * (1 - e) = 1 - e := by linear_combination he

theorem idem_comb_mul (X Y X' Y' : Matrix (Fin N) (Fin N) (AE F E)) :
    (e • X + (1 - e) • Y) * (e • X' + (1 - e) • Y') = e • (X * X') + (1 - e) • (Y * Y') := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, he,
    idem_mul_one_sub he, one_sub_mul_idem he, one_sub_idem_mul he, zero_smul, add_zero, zero_add]

theorem idemMat_mul (X Y : Matrix (Fin N) (Fin N) (AE F E)) : idemMat e (X * Y) = idemMat e X * idemMat e Y := by
  rw [idemMat, idemMat, idemMat, idem_comb_mul he, mul_one]
end

theorem idem_comb_self (e : AF F) (X : Matrix (Fin N) (Fin N) (AE F E)) : e • X + (1 - e) • X = X := by
  rw [← add_smul, add_sub_cancel, one_smul]

theorem idemMat_one (e : AF F) : idemMat e (1 : Matrix (Fin N) (Fin N) (AE F E)) = 1 := idem_comb_self _ _

def idemPt (e : AF F) (he : e * e = e) : UA σ Q →* UA σ Q where
  toFun g := ⟨⟨idemMat e (mat g), idemMat e (mat g⁻¹), by
      rw [← idemMat_mul he, show mat g * mat g⁻¹ = mat (g * g⁻¹) from rfl, mul_inv_cancel]; exact idemMat_one e, by
      rw [← idemMat_mul he, show mat g⁻¹ * mat g = mat (g⁻¹ * g) from rfl, inv_mul_cancel]; exact idemMat_one e⟩, by
    have hg : (mat g)ᵀ * incM F Q * (mat g).map (cA σ) = incM F Q := g.2
    have h1 : (idemMat e (mat g)).map (cA σ) = e • (mat g).map (cA σ) + (1 - e) • 1 := by
      ext i j
      simp only [idemMat, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add, map_smul, Matrix.one_apply,
        apply_ite (cA σ), map_one, map_zero]
    show (idemMat e (mat g))ᵀ * incM F Q * (idemMat e (mat g)).map (cA σ) = incM F Q
    rw [h1, idemMat, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one,
      ← idem_comb_self e (incM F Q), idem_comb_mul he, idem_comb_mul he, hg, one_mul, mul_one]⟩
  map_one' := Subtype.ext (Units.ext (idemMat_one e))
  map_mul' g h := Subtype.ext (Units.ext (idemMat_mul he _ _))

def awayPt (S : Finset (HeightOneSpectrum (𝓞 F))) : UA σ Q →* UA σ Q := idemPt (awayIdem S) (awayIdem_mul_self S)

end Pt

section Fn

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def IsAwayInt (S : Finset (HeightOneSpectrum (𝓞 F))) (z : κ → AF F) : Prop :=
  ∀ i, (z i).1 = 0 ∧ ∀ v, (v ∈ S → evFin F v (z i) = 0) ∧ (v ∉ S → evFin F v (z i) ∈ v.adicCompletionIntegers F)

def IntAway (S : Finset (HeightOneSpectrum (𝓞 F))) (x : κ → AF F) : Prop :=
  ∀ v, v ∉ S → ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F

def AwayFn (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : (κ → AF F) → ℂ) : Prop :=
  Φ ∈ schA F κ ∧ (∀ x z, IsAwayInt S z → Φ (x + z) = Φ x) ∧ ∀ x, Φ x ≠ 0 → IntAway S x

end Fn

section Sub

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n m : ℕ}
  {JV : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} {κ : Type} [Fintype κ]

def fixSub (om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ)) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Subgroup (UA σ J₂) where
  carrier := {g | ∀ Φ, AwayFn S Φ → om (1, g) Φ = Φ}
  one_mem' := fun Φ _ => by rw [Prod.mk_one_one, map_one]; rfl
  mul_mem' := fun {a b} ha hb Φ hΦ => by
    rw [show ((1 : UA σ JV), a * b) = (1, a) * (1, b) by simp, map_mul, Module.End.mul_apply, hb Φ hΦ, ha Φ hΦ]
  inv_mem' := fun {a} ha Φ hΦ => by
    conv_lhs => rw [← ha Φ hΦ]
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, inv_mul_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]

def goodSub (om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ)) : Subgroup (UA σ J₂) where
  carrier := {g | ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → awayPt S g ∈ fixSub om S}
  one_mem' := ⟨∅, fun S _ => by rw [map_one]; exact one_mem _⟩
  mul_mem' := fun {a b} ⟨S₁, h₁⟩ ⟨S₂, h₂⟩ => by
    classical
    exact ⟨S₁ ∪ S₂, fun S hS => by
      rw [map_mul]
      exact mul_mem (h₁ S (Finset.union_subset_left hS)) (h₂ S (Finset.union_subset_right hS))⟩
  inv_mem' := fun {a} ⟨S₀, h⟩ => ⟨S₀, fun S hS => by rw [map_inv]; exact inv_mem (h S hS)⟩

end Sub

end GlobalTheory.AwayFix
