import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.PropEG
import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes

noncomputable section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Global GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar)

namespace Ad3P.DihedralUnramifiedPlaces

def toH (η : HeckeCharacter ℚ) : Formalism.L2.Host.HChar ℚ :=
  ⟨Circle.toUnits.comp η.toIdele, by
    refine ⟨?_, fun k => ?_⟩
    · refine Units.continuous_iff.2 ⟨continuous_subtype_val.comp η.continuous_toIdele, ?_⟩
      have h : (fun x => ((((Circle.toUnits.comp η.toIdele) x)⁻¹ : ℂˣ) : ℂ)) =
          fun x => (((Circle.toUnits.comp η.toIdele) x⁻¹ : ℂˣ) : ℂ) := by
        funext x
        rw [map_inv]
      rw [h]
      exact continuous_subtype_val.comp (η.continuous_toIdele.comp continuous_inv)
    · exact (congrArg Circle.toUnits (η.toIdele_diagonal k)).trans (map_one _)⟩

theorem ord_eq (v : Ad3.Pl) {x : Ad3.Qv v} (hx : x ≠ 0) : ord x = -WithZero.log (Valued.v x) := by
  have h1 := norm_eq_absNorm_zpow_neg_ord v hx
  have h2 := normalizedAbv_eq_zpow v hx
  rw [normalizedAbv_apply] at h2
  have hq : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm_asIdeal v
  have := zpow_right_injective₀ (by linarith) hq.ne' (h1.symm.trans h2)
  omega

theorem loc_eq (η : HeckeCharacter ℚ) (v : Ad3.Pl) (x : (Ad3.Qv v)ˣ) : (toH η).loc v x = localChar η v x := rfl

theorem val_eq {η : HeckeCharacter ℚ} {v : Ad3.Pl} (h : IsUnramifiedChar (localChar η v)) :
    (toH η).val v = localChar η v (unifUnit (Ad3.Qv v)) := by
  have hu : Valued.v ((Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v) : (Ad3.Qv v)ˣ) : Ad3.Qv v) = WithZero.exp (-1 : ℤ) :=
    Formalism.L2.Host.unif_spec v
  have h1 : ord ((Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v) : (Ad3.Qv v)ˣ) : Ad3.Qv v) = 1 := by
    rw [ord_eq v (Units.ne_zero _), hu, WithZero.log_exp, neg_neg]
  have hord : ord (((unifUnit (Ad3.Qv v)) * (Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v))⁻¹ : (Ad3.Qv v)ˣ) : Ad3.Qv v) = 0 := by
    rw [ord_units_mul, ord_units_inv, h1, ord_unifUnit]
    norm_num
  have h2 := isUnramifiedChar_iff.1 h _ hord
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  show (toH η).loc v (Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v)) = _
  rw [loc_eq]
  exact h2.symm

theorem normV_eq (v : Ad3.Pl) : Formalism.ConjugateSelfDual.normV v = Ad3.pOf v := by
  rw [Formalism.ConjugateSelfDual.normV, Ad3.pOf, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    UpperTheory.V.Af.algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [UpperTheory.V.Af.algSat]

theorem pair_of (q : ℕ) (hq : 0 < q) {B : Multiset ℂˣ} {c : ℂ}
    (h : ((UpperTheory.V.Af.algSat 2 q B).map fun b => X - C b).prod = X ^ 2 - C 0 * X + C c) :
    ∃ α : ℂˣ, B = {α, -α} := by
  rw [algSat_eq] at h
  have hcard := natDegree_multiset_prod_X_sub_C_eq_card
    (B.map fun α : ℂˣ => (((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ))
  rw [h, map_zero, zero_mul, sub_zero, natDegree_X_pow_add_C, Multiset.card_map] at hcard
  obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 hcard.symm
  refine ⟨α, ?_⟩
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton] at h
  set s : ℂ := (((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) with hs
  have hs0 : s ≠ 0 := Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (Nat.cast_pos.2 hq) _).ne'
  have h0 := congrArg (eval 0) h
  have h1 := congrArg (eval 1) h
  simp only [eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_C] at h0 h1
  have hsum : s * ((α : ℂ) + β) = 0 := by linear_combination h0 - h1
  have hab : (α : ℂ) + β = 0 := (mul_eq_zero.1 hsum).resolve_left hs0
  have hb : β = -α := Units.ext (by rw [Units.val_neg]; linear_combination hab)
  rw [hb]

end Ad3P.DihedralUnramifiedPlaces
