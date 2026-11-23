import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing

namespace GlobalTheory.CharacterUnits

theorem unit_pow_sub_isUnit {l : ℕ} [Fact l.Prime] (u : ℤ_[l]ˣ)
    (hu : orderOf (PadicInt.toZMod (u : ℤ_[l])) = l - 1)
    (a b : ℕ) (ha : a < l - 1) (hb : b < l - 1) (hab : a ≠ b) :
    IsUnit ((u : ℤ_[l]) ^ a - (u : ℤ_[l]) ^ b) := by
  by_contra h
  have h1 : (u : ℤ_[l]) ^ a - (u : ℤ_[l]) ^ b ∈ IsLocalRing.maximalIdeal ℤ_[l] := h
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow, map_pow, sub_eq_zero] at h1
  exact hab (pow_injOn_Iio_orderOf (by rw [hu]; exact ha) (by rw [hu]; exact hb) h1)

theorem chi_sub_isUnit : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (g0 : G H.E N.Om), orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) = N.l i - 1 → R.t + 1 < N.l i → ∀ a ∈ Finset.Icc 1 R.t, ∀ b ∈ Finset.Icc 1 R.t, a ≠ b → IsUnit (((N.chi i a g0 : (N.O i)ˣ) : N.O i) - ((N.chi i b g0 : (N.O i)ˣ) : N.O i)) := by
  intro R H what₂ N i g0 hε hl a ha b hb hab
  rw [Finset.mem_Icc] at ha hb
  set e : (N.O i)ˣ := Units.map (algebraMap ℤ_[N.l i] (N.O i)).toMonoidHom
    (cycZ (F := H.E) (Ω := N.Om) (N.l i) g0) with he_def
  have h3 : ∀ c, 1 ≤ c → c ≤ R.t → N.chi i c g0 = N.chi i 1 g0 * (e⁻¹ ^ (c - 1)) := by
    intro c h1 h2
    rw [N.chi_def i c h1 h2, MonoidHom.mul_apply]
    congr 1
    have h4 : (-(((c : ℕ) : ℤ) - 1)) = -(((c - 1 : ℕ) : ℤ)) := by omega
    rw [h4, _root_.zpow_neg, zpow_natCast, MonoidHom.inv_apply, MonoidHom.pow_apply, inv_pow]
    rfl
  have hu := (unit_pow_sub_isUnit _ hε (b - 1) (a - 1) (by omega) (by omega)
    (by omega)).map (algebraMap ℤ_[N.l i] (N.O i))
  rw [map_sub, map_pow, map_pow] at hu
  have he : algebraMap ℤ_[N.l i] (N.O i) ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
      ((e : (N.O i)ˣ) : N.O i) := rfl
  rw [he] at hu
  rw [h3 a ha.1 ha.2, h3 b hb.1 hb.2]
  set x := N.chi i 1 g0
  have a1 : ((e⁻¹ : (N.O i)ˣ) : N.O i) ^ (a - 1) * (e : N.O i) ^ (a - 1) = 1 := by rw [← mul_pow]; simp
  have a2 : ((e⁻¹ : (N.O i)ˣ) : N.O i) ^ (b - 1) * (e : N.O i) ^ (b - 1) = 1 := by rw [← mul_pow]; simp
  have key : ((x * e⁻¹ ^ (a - 1) : (N.O i)ˣ) : N.O i) - ((x * e⁻¹ ^ (b - 1) : (N.O i)ˣ) : N.O i) =
      ((x * e⁻¹ ^ (a - 1) * e⁻¹ ^ (b - 1) : (N.O i)ˣ) : N.O i) *
        ((e : N.O i) ^ (b - 1) - (e : N.O i) ^ (a - 1)) := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination (-((x : N.O i) * ((e⁻¹ : (N.O i)ˣ) : N.O i) ^ (a - 1))) * a2 +
      ((x : N.O i) * ((e⁻¹ : (N.O i)ˣ) : N.O i) ^ (b - 1)) * a1
  rw [key]
  exact (Units.isUnit _).mul hu

end GlobalTheory.CharacterUnits
