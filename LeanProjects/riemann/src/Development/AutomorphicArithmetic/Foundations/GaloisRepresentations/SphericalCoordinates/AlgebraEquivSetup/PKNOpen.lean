import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.LevRefine
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed

private def sg {E : Type} [Field E] [NumberField E] (U : Set (Plc E)) (N : ℕ) : AddSubgroup (Af E) where
  carrier := {x | ∀ w ∈ U, Valued.v (pLoc E w x) ≤ Valued.v (N : w.adicCompletion E)}
  zero_mem' := fun w _ => by simp
  add_mem' := fun {a b} ha hb w hw => by
    rw [map_add]
    exact (Valuation.map_add _ _ _).trans (max_le (ha w hw) (hb w hw))
  neg_mem' := fun {a} ha w hw => by
    rw [map_neg, Valuation.map_neg]
    exact ha w hw

private theorem isOpen_sg_univ {E : Type} [Field E] [NumberField E] {N : ℕ} (hN : 0 < N) :
    IsOpen (sg (E := E) Set.univ N : Set (Af E)) := by
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨c, hc⟩ : ∃ c : Af E, c * (N : Af E) = 1 := by
    refine ⟨algebraMap E (Af E) ((N : E)⁻¹), ?_⟩
    have h : algebraMap E (Af E) ((N : E)⁻¹) * algebraMap E (Af E) (N : E) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hNE, map_one]
    simpa using h
  have hv : ∀ w : Plc E, Valued.v (pLoc E w c) * Valued.v (N : w.adicCompletion E) = 1 := fun w => by
    have h := congrArg (pLoc E w) hc
    rw [map_mul, map_natCast, map_one] at h
    rw [← map_mul, h, map_one]
  have h1 : IsOpen {f : Af E | ∀ w : Plc E, (f w : w.adicCompletion E) ∈
      ((Valued.v.integer : Subring (w.adicCompletion E)) : Set (w.adicCompletion E))} :=
    RestrictedProduct.isOpen_forall_mem (fun w => Valued.isOpen_integer _)
  have h2 : Continuous (fun x : Af E => c * x) := continuous_const.mul continuous_id
  have h3 := h1.preimage h2
  convert h3 using 1
  ext x
  have hm : ∀ w : Plc E, (((c * x : Af E) w : w.adicCompletion E) ∈
      ((Valued.v.integer : Subring (w.adicCompletion E)) : Set (w.adicCompletion E))) ↔
      Valued.v (pLoc E w c) * Valued.v (pLoc E w x) ≤ 1 := fun w => by
    rw [← map_mul, ← map_mul]
    exact Valuation.mem_integer_iff _ _
  constructor
  · intro hx w
    refine (hm w).2 ?_
    calc Valued.v (pLoc E w c) * Valued.v (pLoc E w x)
        ≤ Valued.v (pLoc E w c) * Valued.v (N : w.adicCompletion E) := by
          gcongr
          exact hx w trivial
      _ = 1 := hv w
  · intro hx w _
    have h := (hm w).1 (hx w)
    calc Valued.v (pLoc E w x)
        = Valued.v (pLoc E w c) * Valued.v (pLoc E w x) * Valued.v (N : w.adicCompletion E) := by
          rw [mul_right_comm, hv, one_mul]
      _ ≤ 1 * Valued.v (N : w.adicCompletion E) := by gcongr
      _ = _ := one_mul _

private theorem principalCongruence_map_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (N : ℕ) (w : Plc E)
    (M : GL (Fin n) (Af E)) :
    Cong1 N w (GeneralLinearGroup.map (pLoc E w) M) ↔
      ∀ i k, Valued.v (pLoc E w ((M.val - 1) i k)) ≤ Valued.v (N : w.adicCompletion E) := by
  have h : ∀ i k, ((GeneralLinearGroup.map (pLoc E w) M).val - 1) i k = pLoc E w ((M.val - 1) i k) := by
    intro i k
    by_cases hik : i = k <;> simp [Matrix.sub_apply, Matrix.one_apply, hik]
  simp only [Cong1, h]

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.pKNOpen :
    KNIff → KNOpen := by
  intro hI E _ _ _ A n p _ S T N hN
  have hO : IsOpen ((sg {w : Plc E | (p : 𝓞 E) ∉ w.asIdeal} N : AddSubgroup (Af E)) : Set (Af E)) :=
    AddSubgroup.isOpen_mono (H₁ := sg Set.univ N) (fun x hx w _ => hx w trivial) (isOpen_sg_univ hN)
  have hm : Continuous (fun g : GUf E n => mat g) := continuous_fst.comp continuous_subtype_val
  have hc1 : Continuous (fun g : GUf E n => (T.a * mat g * T.a⁻¹ : GL (Fin n) (Af E)).val) :=
    Units.continuous_val.comp ((continuous_const.mul hm).mul continuous_const)
  have hc2 : Continuous (fun g : GUf E n => (T.a * mat g⁻¹ * T.a⁻¹ : GL (Fin n) (Af E)).val) := by
    simp only [map_inv]
    exact Units.continuous_val.comp ((continuous_const.mul hm.inv).mul continuous_const)
  have key : (((S.L.KN N).comap T.j : Subgroup (GUf E n)) : Set (GUf E n)) =
      ⋂ (i : Fin n) (k : Fin n),
        ((fun g : GUf E n => ((T.a * mat g * T.a⁻¹ : GL (Fin n) (Af E)).val - 1) i k) ⁻¹'
            (sg {w : Plc E | (p : 𝓞 E) ∉ w.asIdeal} N : Set (Af E)) ∩
         (fun g : GUf E n => ((T.a * mat g⁻¹ * T.a⁻¹ : GL (Fin n) (Af E)).val - 1) i k) ⁻¹'
            (sg {w : Plc E | (p : 𝓞 E) ∉ w.asIdeal} N : Set (Af E))) := by
    ext g
    have e1 := (hI E A n p S T g).2 N hN
    have e2 := (hI E A n p S T g⁻¹).2 N hN
    rw [map_inv] at e2
    have hmem : g ∈ (((S.L.KN N).comap T.j : Subgroup (GUf E n)) : Set (GUf E n)) ↔
        S.L.CongOne N (T.j g) ∧ S.L.CongOne N (T.j g)⁻¹ := Iff.rfl
    rw [hmem, e1, e2]
    simp only [principalCongruence_map_iff, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩ i k
      exact ⟨fun w hw => h1 w hw i k, fun w hw => h2 w hw i k⟩
    · intro h
      exact ⟨fun w hw i k => (h i k).1 w hw, fun w hw i k => (h i k).2 w hw⟩
  rw [key]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => IsOpen.inter ?_ ?_
  · exact hO.preimage ((hc1.matrix_elem i k).sub continuous_const)
  · exact hO.preimage ((hc2.matrix_elem i k).sub continuous_const)
