import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Formalism.LocalToGlobal.UnitaryNorms.CharProd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeakApproxUnitFinitePlace

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.HeckeValField

variable {E : Type} [Field E] [NumberField E]

def unitsIn (M : IntermediateField ℚ ℂ) : Subgroup ℂˣ where
  carrier := {z | (z : ℂ) ∈ M}
  one_mem' := by simpa using M.one_mem
  mul_mem' := fun {a b} ha hb => by simpa using M.mul_mem ha hb
  inv_mem' := fun {a} ha => by simpa using M.inv_mem ha

theorem mem_unitsIn {M : IntermediateField ℚ ℂ} {z : ℂˣ} : z ∈ unitsIn M ↔ (z : ℂ) ∈ M := Iff.rfl

theorem val_mem (χ : HChar E) {M : IntermediateField ℚ ℂ} (hM : valueField χ 0 ≤ M)
    {v : HeightOneSpectrum (𝓞 E)} (hv : χ.UnrAt v) : χ.val v ∈ unitsIn M := by
  have h := hM (IntermediateField.subset_adjoin ℚ (valueSet χ 0) ⟨v, hv, rfl⟩)
  exact mem_unitsIn.2 (by simpa [HChar.valTw] using h)

theorem loc_mem_of_unrAt (χ : HChar E) {G : Subgroup ℂˣ} {v : HeightOneSpectrum (𝓞 E)} (hv : χ.UnrAt v)
    (hval : χ.val v ∈ G) (y : (v.adicCompletion E)ˣ) : χ.loc v y ∈ G := by
  set π := atFin v (unif v)
  have hπ : Valued.v (π : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := unif_spec v
  have hy0 : Valued.v (y : v.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  set k := WithZero.log (Valued.v (y : v.adicCompletion E))
  have hy : Valued.v (y : v.adicCompletion E) = WithZero.exp k := (WithZero.exp_log hy0).symm
  have hu : IsUnitAt v (y * π ^ k) := by
    unfold IsUnitAt
    rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, hy, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp
  have h1 := hv _ hu
  rw [map_mul, map_zpow] at h1
  rw [eq_inv_of_mul_eq_one_left h1]
  exact G.inv_mem (G.zpow_mem hval k)

theorem loc_mem (χ : HChar E) {M : IntermediateField ℚ ℂ} (hM : valueField χ 0 ≤ M)
    (hinf : ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) (v : HeightOneSpectrum (𝓞 E)) (y : (v.adicCompletion E)ˣ) :
    χ.loc v y ∈ unitsIn M := by
  classical
  set G := unitsIn M
  by_cases hv : χ.UnrAt v
  · exact loc_mem_of_unrAt χ hv (val_mem χ hM hv) y
  set R := (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset
  have hR : ∀ w, w ∉ R → χ.UnrAt w := fun w hw => by
    by_contra h
    exact hw ((GlobalTheory.Mem.UnrAe.finite_ramified χ).mem_toFinset.2 h)
  choose nf hnf using GlobalTheory.HeckeSplit.exists_level χ.1 χ.2.1
  set S := insert v R
  set N := S.sup nf
  obtain ⟨a, ha0, hav, haw⟩ := GlobalTheory.HkFin.exists_weak_approx_unit E R v y N
  set k : Eˣ := Units.mk0 a ha0
  have h1 : χ.loc v y = χ.locK v k := by
    have hle : nf v ≤ N := Finset.le_sup (Finset.mem_insert_self v R)
    have e : χ.loc v (atFin v k * y⁻¹) = 1 := by
      apply hnf v
      refine le_trans ?_ (WithZero.exp_le_exp.mpr (by omega : -(N : ℤ) ≤ -(nf v : ℤ)))
      exact hav
    rw [map_mul, map_inv, mul_inv_eq_one] at e
    exact e.symm
  have h2 : ∀ w ∈ S, w ≠ v → χ.locK w k = 1 := by
    intro w hw hwv
    have hwR : w ∈ R := (Finset.mem_insert.1 hw).resolve_left hwv
    have hle : nf w ≤ N := Finset.le_sup hw
    apply hnf w
    have e : ((atFin w k : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 =
        algebraMap E (w.adicCompletion E) (a - 1) := by
      rw [map_sub, map_one]; rfl
    rw [e, PI.FinOrdValD.WA.val_alg]
    exact (haw w hwR hwv).trans (WithZero.exp_le_exp.mpr (by omega))
  have hpr := χ.productRule S (fun w hw => hR w fun h => hw (Finset.mem_insert_of_mem h)) k
  rw [Finset.prod_eq_single_of_mem v (Finset.mem_insert_self v R) (fun w hw hwv => h2 w hw hwv)] at hpr
  have hF : (∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : w ∉ S), χ.val w ^ ordF w k) ∈ G := by
    refine finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun w => ?_
    refine finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun hw => ?_
    exact G.zpow_mem (val_mem χ hM (hR w fun h => hw (Finset.mem_insert_of_mem h))) _
  have h3 : χ.locK v k * (χ.inf k * ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : w ∉ S), χ.val w ^ ordF w k) = 1 := by
    rw [← hpr]; ac_rfl
  rw [h1, eq_inv_of_mul_eq_one_left h3]
  exact G.inv_mem (G.mul_mem (hinf k) hF)

theorem mem_of_inf_eq_one : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (M : IntermediateField ℚ ℂ),
    valueField χ 0 ≤ M → (∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) → ∀ x, (∀ w : InfinitePlace E,
      (x.val : AdeleRing (𝓞 E) E).1 w = 1) → ((χ.1 x : ℂˣ) : ℂ) ∈ M := by
  intro E _ _ χ M hM hinf x hx
  classical
  have hev : ∀ᶠ v in Filter.cofinite, Valued.v ((GlobalTheory.HeckeSplit.finPart E v x : (v.adicCompletion E)ˣ) :
      v.adicCompletion E) = 1 := by
    have h1 : ∀ᶠ v in Filter.cofinite, (x.val.2 : FiniteAdeleRing (𝓞 E) E).1 v ∈ v.adicCompletionIntegers E :=
      x.val.2.2
    have h2 : ∀ᶠ v in Filter.cofinite, (x⁻¹.val.2 : FiniteAdeleRing (𝓞 E) E).1 v ∈ v.adicCompletionIntegers E :=
      x⁻¹.val.2.2
    filter_upwards [h1, h2] with v hv1 hv2
    have e1 : Valued.v ((GlobalTheory.HeckeSplit.finPart E v x : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hv1
    have e2 : Valued.v ((GlobalTheory.HeckeSplit.finPart E v x⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hv2
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀] at e2
    have h0 : 0 < Valued.v ((GlobalTheory.HeckeSplit.finPart E v x : (v.adicCompletion E)ˣ) : v.adicCompletion E) :=
      zero_lt_iff.2 ((Valuation.ne_zero_iff _).mpr (Units.ne_zero _))
    exact le_antisymm e1 ((inv_le_one₀ h0).1 e2)
  have hfin := Filter.eventually_cofinite.1 hev
  set S := hfin.toFinset ∪ (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset
  have hS : ∀ v ∉ S, χ.1 (HeckeValGen.localIdele E v (GlobalTheory.HeckeSplit.finPart E v x)) = 1 := by
    intro v hv
    have hu : ¬ ¬ Valued.v ((GlobalTheory.HeckeSplit.finPart E v x : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1 :=
      fun h => hv (Finset.mem_union_left _ (hfin.mem_toFinset.2 h))
    have hr : χ.UnrAt v := by
      by_contra h
      exact hv (Finset.mem_union_right _ ((GlobalTheory.Mem.UnrAe.finite_ramified χ).mem_toFinset.2 h))
    exact hr _ (not_not.1 hu)
  rw [GlobalTheory.HeckeSplit.char_eq_prod_local χ.1 χ.2.1 x S hS]
  have hinfx : GlobalTheory.HeckeSplit.infPart E x = 1 := Units.ext (funext fun w => hx w)
  rw [hinfx, map_one, map_one, one_mul]
  exact mem_unitsIn.1 ((unitsIn M).prod_mem fun v _ => loc_mem χ hM hinf v _)

end GlobalTheory.HeckeValField
