import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.RepNewformOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AbsExpo

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Polynomial GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Rn.unitTw :
    UpperTheory.V.Af.Rn.UnitTw := by
  intro k hk1 j π hπ
  set s : ℝ := 1 - (k : ℝ) / 2 + j with hs
  let χ := GlobalTheory.HeckeGal.Model.absPow ℚ (-s)
  have hE := GlobalTheory.HeckeGal.Model.absPow_isAbsPow ℚ (-s)
  have hi : ∀ v, (π.twist χ).HasInfChar v {((k : ℂ) - 1) / 2, -(((k : ℂ) - 1) / 2)} := fun v => by
    have := (hπ v).twist χ
    rw [absExpo ℚ (-s) v] at this
    convert this using 1
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, hs]
    exact congrArg₂ (fun a b : ℂ => a ::ₘ {b}) (by push_cast; ring) (by push_cast; ring)
  refine ⟨π.twist χ, hi, fun w => ⟨(χ⁻¹).val w, fun B => ?_, fun α β => ?_⟩⟩
  · have hu0 : χ.UnrAt w := fun u hu => hE.1 w u hu
    have hu : (χ⁻¹).UnrAt w := fun u hu => by
      have := hE.1 w u hu
      exact inv_eq_one.2 this
    constructor
    · intro hsat
      have h3 := hsat.twist hu
      rwa [← TR.CuspSub.twist_mul, mul_inv_cancel, TR.CuspSub.twist_one] at h3
    · intro hsat
      have h3 := hsat.twist hu0
      have e : (χ⁻¹).val w = (χ.val w)⁻¹ := rfl
      rw [Multiset.map_map, e] at h3
      simpa using h3
  have hp := (places w).1
  have hq := (places w).2.2.1
  have hq0 : (0 : ℝ) < normV w := by exact_mod_cast hp.pos
  have hval0 : ((χ.val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ (-(-s)) : ℝ) : ℂ) := by
    rw [hE.2.1 w, hq, Complex.ofReal_cpow hq0.le]; simp
  have hval : (((χ⁻¹).val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ (-s) : ℝ) : ℂ) := by
    have e : (χ⁻¹).val w = (χ.val w)⁻¹ := rfl
    rw [e, Units.val_inv_eq_inv_val, hval0, ← Complex.ofReal_inv, ← Real.rpow_neg hq0.le, neg_neg]
  set r : ℂ := (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) with hr
  have key : ∀ a : ℂˣ, (normV w : ℂ) ^ j * ((((normV w : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * ((a * (χ⁻¹).val w : ℂˣ) : ℂ)) =
      r * a := fun a => by
    have : ((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) =
        (normV w : ℝ) ^ j * ((normV w : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) * (normV w : ℝ) ^ (-s)) := by
      rw [← Real.rpow_intCast, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
      congr 1
      rw [hs]; push_cast; ring
    rw [hr, this, Units.val_mul, hval]; push_cast; ring
  have hrr : r * r = (normV w : ℂ) ^ (k - 1) := by
    rw [hr, ← Complex.ofReal_mul, ← Real.rpow_add hq0, add_halves, ← Nat.cast_pred hk1, Real.rpow_natCast]
    push_cast; rfl
  simp only [algSat, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Multiset.pure_def, Multiset.bind_def, Multiset.cons_bind, Multiset.singleton_bind,
    Multiset.singleton_add, key]
  rw [← hrr]
  simp only [Units.val_mul, C_mul, C_add]
  ring
