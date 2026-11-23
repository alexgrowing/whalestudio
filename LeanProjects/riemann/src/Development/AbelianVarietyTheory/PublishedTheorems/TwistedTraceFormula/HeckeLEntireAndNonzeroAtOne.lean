import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (Ideles eulerFactor IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleNorm)

namespace GlobalTheory.HeckeOne

variable {K : Type} [Field K] [NumberField K]

def IsNormPow (χ : HChar K) (t : ℝ) : Prop :=
  ∀ x : Ideles K, ((χ.1 x : ℂˣ) : ℂ) = ((ideleNorm x : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)

def IsContAtOne (χ : HChar K) (Λ : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ Λ 1 ∧ ∀ s : ℂ, 1 < s.re → HasProd (eulerFactor χ s) (Λ s)

end GlobalTheory.HeckeOne

namespace GlobalTheory.Published

open GlobalTheory.HeckeOne

def HeckeLEntireAndNonzeroAtOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), χ.IsUnitary →
    ((¬ ∃ t : ℝ, IsNormPow χ t) → ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ) ∧
    (χ ≠ 1 → ∃ Λ : ℂ → ℂ, IsContAtOne χ Λ ∧ Λ 1 ≠ 0)

end GlobalTheory.Published

namespace GlobalTheory.HeckeOne

variable {K : Type} [Field K] [NumberField K]

theorem ideleNorm_pos (x : Ideles K) : 0 < ideleNorm x := by
  refine lt_of_le_of_ne ?_ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero x).symm
  exact mul_nonneg (Finset.prod_nonneg fun v _ => pow_nonneg (norm_nonneg _) _)
    (finprod_nonneg fun v => norm_nonneg _)

theorem cpow_eq_exp (x : Ideles K) (t : ℝ) :
    ((ideleNorm x : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) =
      ((Circle.exp (t * Real.log (ideleNorm x)) : Circle) : ℂ) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (ideleNorm_pos x).ne'), Circle.coe_exp,
    ← Complex.ofReal_log (ideleNorm_pos x).le]
  congr 1
  push_cast
  ring

variable (K) in

def normChar (t : ℝ) : HChar K :=
  ⟨Circle.toUnits.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow K t).toHom,
    Units.continuous_iff.2
      ⟨continuous_subtype_val.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow K t).continuous_toHom,
        continuous_subtype_val.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow K t).continuous_toHom.inv |>.congr
          fun x => by
            rw [Units.val_inv_eq_inv_val]
            exact Circle.coe_inv _⟩,
    fun k => by
      rw [MonoidHom.comp_apply]
      exact (congrArg Circle.toUnits
        ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow K t).map_principal k)).trans (map_one _)⟩

theorem normChar_apply (t : ℝ) (x : Ideles K) :
    (((normChar K t).1 x : ℂˣ) : ℂ) = ((Circle.exp (t * Real.log (ideleNorm x)) : Circle) : ℂ) := rfl

theorem isNormPow_iff (χ : HChar K) (t : ℝ) : IsNormPow χ t ↔ χ = normChar K t := by
  constructor
  · intro h
    exact Subtype.ext (MonoidHom.ext fun x => Units.ext (by rw [h x, cpow_eq_exp, normChar_apply]))
  · rintro rfl x
    rw [cpow_eq_exp, normChar_apply]

theorem isUnitary_normChar (t : ℝ) : (normChar K t).IsUnitary := fun x => by
  rw [normChar_apply]; exact Circle.norm_coe _

theorem isNormPow_one : IsNormPow (1 : HChar K) 0 := fun x => by simp

theorem normChar_zero : normChar K 0 = 1 := ((isNormPow_iff _ _).1 isNormPow_one).symm

theorem normChar_add (s t : ℝ) : normChar K (s + t) = normChar K s * normChar K t :=
  Subtype.ext (MonoidHom.ext fun x => Units.ext (by
    change _ = (((normChar K s).1 x : ℂˣ) : ℂ) * (((normChar K t).1 x : ℂˣ) : ℂ)
    rw [normChar_apply, normChar_apply, normChar_apply, add_mul, Circle.exp_add, Circle.coe_mul]))

theorem ideleNorm_localIdele (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    ideleNorm (Neutral.B1.localIdele K v u) = ‖(u : v.adicCompletion K)‖ := by
  rw [← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.ideleNorm_localIdele]
  rfl

theorem unrAt_normChar (t : ℝ) (v : HeightOneSpectrum (𝓞 K)) : (normChar K t).UnrAt v := fun u hu => by
  apply Units.ext
  change (((normChar K t).1 (Neutral.B1.localIdele K v u) : ℂˣ) : ℂ) = _
  rw [normChar_apply, ideleNorm_localIdele, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.norm_eq_one_of_valued hu]
  simp

theorem not_isNormPow_of_not_unrAt {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)} (h : ¬ χ.UnrAt v) :
    ¬ ∃ t : ℝ, IsNormPow χ t := fun ⟨t, ht⟩ => h ((isNormPow_iff χ t).1 ht ▸ unrAt_normChar t v)

theorem val_normChar (t : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    (((normChar K t).val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) * Complex.I)) := by
  have h := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.valueAt_eq _
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow_isUnramifiedAt t v) (Formalism.L2.Host.unif_spec v)
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow_valueAt] at h
  have hN := NumberField.HeightOneSpectrum.one_lt_absNorm v
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0)),
    ← Complex.natCast_log]
  refine Eq.trans h.symm ?_
  congr 1
  push_cast
  ring

theorem exists_normChar_ne_one : ∃ t : ℝ, normChar K t ≠ 1 := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
  let v : HeightOneSpectrum (𝓞 K) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩
  obtain ⟨t, ht⟩ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.exists_normPow_valueAt_eq_neg_one v
  refine ⟨t, fun h => ?_⟩
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.valueAt_eq _
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow_isUnramifiedAt t v) (Formalism.L2.Host.unif_spec v)] at ht
  have h2 : (((normChar K t).val v : ℂˣ) : ℂ) = -1 := ht
  rw [h] at h2
  have h3 : (1 : ℂ) = -1 := h2
  norm_num at h3

theorem isContAtOne_of_isHeckeL {χ : HChar K} {Λ : ℂ → ℂ} (h : IsHeckeL χ Λ) : IsContAtOne χ Λ :=
  ⟨h.1.analyticAt 1, h.2⟩

theorem IsContAtOne.apply_one_eq {χ : HChar K} {Λ Λ' : ℂ → ℂ} (h : IsContAtOne χ Λ) (h' : IsContAtOne χ Λ') :
    Λ 1 = Λ' 1 := by
  have hc : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 1) (𝓝 1) :=
    (Complex.continuous_ofReal.tendsto' 1 1 (by simp)).mono_left nhdsWithin_le_nhds
  refine tendsto_nhds_unique_of_eventuallyEq (h.1.continuousAt.tendsto.comp hc)
    (h'.1.continuousAt.tendsto.comp hc) ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (h.2 x hx).unique (h'.2 x hx)

theorem exists_entire_ne_zero (H : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) {χ : HChar K} (hu : χ.IsUnitary)
    (hχ : ¬ ∃ t : ℝ, IsNormPow χ t) : ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ ∧ Λ 1 ≠ 0 := by
  obtain ⟨Λ, hΛ⟩ := (H K χ hu).1 hχ
  obtain ⟨Λ', h', h0⟩ := (H K χ hu).2 fun h => hχ ⟨0, h ▸ isNormPow_one⟩
  exact ⟨Λ, hΛ, (isContAtOne_of_isHeckeL hΛ).apply_one_eq h' ▸ h0⟩

end GlobalTheory.HeckeOne
