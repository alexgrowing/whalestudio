import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsLeviOntoS

noncomputable section

open scoped Classical TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Polynomial Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.Pf.NormSteps.LeviOntoSPf

namespace SIdemPf

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def OverG (v : HeightOneSpectrum (𝓞 X.B.I.F)) : Prop := ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal

theorem g_ne_zero : X.B.g ≠ 0 := by
  exact Formalism.L2.SG.Pf.modulus_g_ne_zero X

theorem val_g (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    Valued.v ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) = v.intValuation ((X.B.g : ℕ) : 𝓞 X.B.I.F) := by
  have h : ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) =
      ((algebraMap (𝓞 X.B.I.F) X.B.I.F ((X.B.g : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) : v.adicCompletion X.B.I.F) := by
    rw [map_natCast]
    first
    | (simp only [map_natCast, UniformSpace.Completion.coe_natCast]; rfl)
    | (induction X.B.g with
        | zero =>
          simp only [Nat.cast_zero]
          first
          | rfl
          | (rw [WithVal.equiv_symm_zero]; rfl)
          | (simp only [map_zero, UniformSpace.Completion.coe_zero]; rfl)
        | succ n ih =>
          push_cast
          rw [ih, map_add, map_one, UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_one]
          rfl)
  rw [h, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]

def eS : Af X.B.I.F :=
  ⟨fun v => if OverG X v then 1 else 0, Filter.Eventually.of_forall fun v => by
    show (if OverG X v then 1 else 0 : v.adicCompletion X.B.I.F) ∈ v.adicCompletionIntegers X.B.I.F
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

theorem eS_apply (v : HeightOneSpectrum (𝓞 X.B.I.F)) : eS X v = if OverG X v then 1 else 0 := rfl

def tS : Af X.B.I.F :=
  ⟨fun v => if OverG X v then 0 else ((X.B.g : ℕ) : v.adicCompletion X.B.I.F)⁻¹,
    Filter.Eventually.of_forall fun v => by
      show (if OverG X v then 0 else ((X.B.g : ℕ) : v.adicCompletion X.B.I.F)⁻¹) ∈ v.adicCompletionIntegers X.B.I.F
      split_ifs with h
      · exact zero_mem _
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, val_g]
        have h1 : v.intValuation ((X.B.g : ℕ) : 𝓞 X.B.I.F) = 1 := by
          refine le_antisymm (v.intValuation_le_one _) (not_lt.1 fun hl => h ?_)
          exact (v.intValuation_lt_one_iff_mem _).1 hl
        rw [h1, inv_one]⟩

theorem tS_apply (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    tS X v = if OverG X v then 0 else ((X.B.g : ℕ) : v.adicCompletion X.B.I.F)⁻¹ := rfl

theorem eS_int : eS X ∈ Formalism.UG.intAd X.B.I.F := fun v => by
  show eS X v ∈ v.adicCompletionIntegers X.B.I.F
  rw [eS_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem natCast_apply (v : HeightOneSpectrum (𝓞 X.B.I.F)) (m : ℕ) :
    ((m : Af X.B.I.F) : Af X.B.I.F) v = (m : v.adicCompletion X.B.I.F) := by
  induction m with
  | zero => rfl
  | succ n ih =>
    rw [Nat.cast_succ, Nat.cast_succ, ← ih]
    rfl

theorem val_g_lt (v : HeightOneSpectrum (𝓞 X.B.I.F)) (h : OverG X v) :
    Valued.v ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) < 1 := by
  rw [val_g]
  exact (v.intValuation_lt_one_iff_mem _).2 h

theorem val_g_eq (v : HeightOneSpectrum (𝓞 X.B.I.F)) (h : ¬ OverG X v) :
    Valued.v ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) = 1 := by
  rw [val_g]
  exact le_antisymm (v.intValuation_le_one _)
    (not_lt.1 fun hl => h ((v.intValuation_lt_one_iff_mem _).1 hl))

theorem tS_int : tS X ∈ Formalism.UG.intAd X.B.I.F := fun v => by
  show tS X v ∈ v.adicCompletionIntegers X.B.I.F
  rw [tS_apply]
  split_ifs with h
  · exact zero_mem _
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, val_g_eq X v h, inv_one]

theorem one_sub_eS : (1 : Af X.B.I.F) - eS X = ((X.B.g : ℕ) : Af X.B.I.F) * tS X := by
  ext v : 1
  show (1 : v.adicCompletion X.B.I.F) - eS X v = ((X.B.g : ℕ) : Af X.B.I.F) v * tS X v
  rw [natCast_apply, eS_apply, tS_apply]
  split_ifs with h
  · simp
  · have hne : ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) ≠ 0 := by
      intro h0
      have := val_g_eq X v h
      rw [h0, map_zero] at this
      exact zero_ne_one this
    rw [sub_zero, mul_inv_cancel₀ hne]

theorem eS_idem : eS X * eS X = eS X := by
  ext v : 1
  show eS X v * eS X v = eS X v
  rw [eS_apply]
  split_ifs <;> simp

theorem unit_on_S (d : ↥(Formalism.UG.intAd X.B.I.F)) :
    ∃ z ∈ Formalism.UG.intAd X.B.I.F, eS X * ((1 + ((X.B.g : ℕ) : Af X.B.I.F) * d) * z) = eS X := by

  have hval : ∀ v, OverG X v →
      Valued.v (1 + ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) * (d : Af X.B.I.F) v) = 1 := by
    intro v hv
    refine Valuation.map_one_add_of_lt _ ?_
    rw [map_mul]
    have hd : Valued.v ((d : Af X.B.I.F) v) ≤ 1 := d.2 v
    calc Valued.v ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) * Valued.v ((d : Af X.B.I.F) v)
        ≤ Valued.v ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) := mul_le_of_le_one_right' hd
      _ < 1 := val_g_lt X v hv
  have hmem : ∀ v, (if OverG X v then (1 + ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) *
      (d : Af X.B.I.F) v)⁻¹ else 0) ∈ v.adicCompletionIntegers X.B.I.F := by
    intro v
    split_ifs with hv
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval v hv, inv_one]
    · exact zero_mem _
  let z : Af X.B.I.F := ⟨fun v => if OverG X v then (1 + ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) *
      (d : Af X.B.I.F) v)⁻¹ else 0, Filter.Eventually.of_forall hmem⟩
  refine ⟨z, fun v => hmem v, ?_⟩
  ext v : 1
  show eS X v * ((1 + ((X.B.g : ℕ) : Af X.B.I.F) v * (d : Af X.B.I.F) v) * z v) = eS X v
  rw [natCast_apply, eS_apply]
  show _ * (_ * (if OverG X v then _ else 0)) = _
  split_ifs with hv
  · have hne : (1 + ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) * (d : Af X.B.I.F) v) ≠ 0 := by
      intro h0
      have := hval v hv
      rw [h0, map_zero] at this
      exact zero_ne_one this
    rw [mul_inv_cancel₀ hne, mul_one]
  · rw [zero_mul]

def phi : ↥(Formalism.UG.intAd X.B.I.F) →+* X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
  (Algebra.TensorProduct.includeRight : Af X.B.I.F →ₐ[X.B.I.F] X.B.I.E ⊗[X.B.I.F] Af X.B.I.F).toRingHom.comp
    (Formalism.UG.intAd X.B.I.F).subtype

theorem phi_apply (a : ↥(Formalism.UG.intAd X.B.I.F)) : phi X a = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] (a : Af X.B.I.F) := rfl

theorem phi_mem (a : ↥(Formalism.UG.intAd X.B.I.F)) : phi X a ∈ IntAf X.B.I.F X.B.I.E :=
  Subring.subset_closure (Set.mem_union_right _ ⟨a, rfl⟩)

theorem integral_of_mem {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hs : s ∈ IntAf X.B.I.F X.B.I.E) :
    ∃ p : Polynomial ↥(Formalism.UG.intAd X.B.I.F), p.Monic ∧ p.eval₂ (phi X) s = 0 := by
  show (phi X).IsIntegralElem s
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨x, hx⟩, rfl⟩ | ⟨y, rfl⟩
    · obtain ⟨y, rfl⟩ := hx
      have hi : IsIntegral ℤ (algebraMap (𝓞 X.B.I.E) X.B.I.E y) := y.isIntegral_coe
      obtain ⟨q, hq, hev⟩ := hi
      let f : X.B.I.E →+* X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := (Algebra.TensorProduct.includeLeft :
        X.B.I.E →ₐ[X.B.I.F] X.B.I.E ⊗[X.B.I.F] Af X.B.I.F).toRingHom
      show (phi X).IsIntegralElem (f (algebraMap (𝓞 X.B.I.E) X.B.I.E y))
      refine ⟨q.map (Int.castRingHom ↥(Formalism.UG.intAd X.B.I.F)), hq.map _, ?_⟩
      rw [Polynomial.eval₂_map, show (phi X).comp (Int.castRingHom ↥(Formalism.UG.intAd X.B.I.F)) =
        f.comp (algebraMap ℤ X.B.I.E) from RingHom.ext_int _ _, ← Polynomial.hom_eval₂, hev, map_zero]
    · exact (phi X).isIntegralElem_map
  | zero => simpa using (phi X).isIntegralElem_map (x := 0)
  | one => simpa using (phi X).isIntegralElem_map (x := 1)
  | add x y _ _ hx hy => exact RingHom.IsIntegralElem.add _ hx hy
  | neg x _ hx =>
    have e : -x = phi X (-1) * x := by rw [map_neg, map_one, neg_one_mul]
    rw [e]
    exact RingHom.IsIntegralElem.mul _ (phi X).isIntegralElem_map hx
  | mul x y _ _ hx hy => exact RingHom.IsIntegralElem.mul _ hx hy

theorem eval₂_mem (r : Polynomial ↥(Formalism.UG.intAd X.B.I.F)) {u : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (hu : u ∈ IntAf X.B.I.F X.B.I.E) : r.eval₂ (phi X) u ∈ IntAf X.B.I.F X.B.I.E := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (phi_mem X _) (Subring.pow_mem _ hu _)

theorem near_inv {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hs : s ∈ IntAf X.B.I.F X.B.I.E) :
    ∃ w ∈ IntAf X.B.I.F X.B.I.E, ∃ d : ↥(Formalism.UG.intAd X.B.I.F),
      (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * w =
        phi X (1 + ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * d) := by
  obtain ⟨p, hp, hps⟩ := integral_of_mem X hs
  have hgphi : phi X ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) = ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := map_natCast _ _
  have hsc : (p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F))).eval₂ (phi X)
      (phi X ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * s) = 0 := Polynomial.scaleRoots_eval₂_eq_zero (phi X) hps

  have hdvd : Polynomial.C ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) ∣
      p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) - Polynomial.X ^ p.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_scaleRoots, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · rw [if_neg hi.ne, sub_zero]
      exact Dvd.dvd.mul_left (dvd_pow_self _ (Nat.sub_ne_zero_of_lt hi)) _
    · rw [hi, if_pos rfl, Nat.sub_self, pow_zero, mul_one, hp.coeff_natDegree, sub_self]
      exact dvd_zero _
    · rw [if_neg hi.ne', Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul, sub_zero]
      exact dvd_zero _
  obtain ⟨q, hq⟩ := hdvd
  have hsr : p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) =
      Polynomial.X ^ p.natDegree + Polynomial.C ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * q := by
    rw [← hq]; ring
  have hP2 : ((p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F))).comp (Polynomial.X - 1)).eval₂ (phi X)
      (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) = 0 := by
    rw [Polynomial.eval₂_comp, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_one]
    have e : 1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s - 1 = phi X ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * s := by
      rw [hgphi]; ring
    rw [e]; exact hsc
  obtain ⟨Q, hQ⟩ := Polynomial.X_dvd_sub_C (p := (p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F))).comp (Polynomial.X - 1))
  rw [Polynomial.coeff_zero_eq_eval_zero] at hQ
  have hev := congrArg (Polynomial.eval₂ (phi X) (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s)) hQ
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_X, hP2,
    zero_sub] at hev
  have h0 : ((p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F))).comp (Polynomial.X - 1)).eval 0 =
      (-1) ^ p.natDegree + ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * q.eval (-1) := by
    rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, zero_sub, hsr,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  refine ⟨phi X ((-1) ^ (p.natDegree + 1)) * Q.eval₂ (phi X) (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s),
    Subring.mul_mem _ (phi_mem X _) (eval₂_mem X Q ?_), (-1) ^ p.natDegree * q.eval (-1), ?_⟩
  · refine Subring.add_mem _ (Subring.one_mem _) (Subring.mul_mem _ ?_ hs)
    rw [← hgphi]; exact phi_mem X _
  · have h2 : ((-1 : ↥(Formalism.UG.intAd X.B.I.F)) ^ p.natDegree) * (-1) ^ p.natDegree = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    calc (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * (phi X ((-1) ^ (p.natDegree + 1)) *
          Q.eval₂ (phi X) (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s))
        = phi X ((-1) ^ (p.natDegree + 1)) * ((1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) *
          Q.eval₂ (phi X) (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s)) := by ring
      _ = phi X ((-1) ^ (p.natDegree + 1)) * -(phi X (((p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F))).comp
          (Polynomial.X - 1)).eval 0)) := by rw [hev]
      _ = phi X (-((-1) ^ (p.natDegree + 1)) * ((p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F))).comp
          (Polynomial.X - 1)).eval 0) := by rw [map_mul, map_neg]; ring
      _ = phi X (1 + ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * ((-1) ^ p.natDegree * q.eval (-1))) := by
          congr 1
          rw [h0, pow_succ]
          linear_combination h2

theorem idempotent_places_exists : SIdem X := by
  have hes : (⟨eS X, eS_int X⟩ : ↥(Formalism.UG.intAd X.B.I.F)) * ⟨eS X, eS_int X⟩ = ⟨eS X, eS_int X⟩ :=
    Subtype.ext (eS_idem X)
  have hone : 1 - (⟨eS X, eS_int X⟩ : ↥(Formalism.UG.intAd X.B.I.F)) = ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * ⟨tS X, tS_int X⟩ :=
    Subtype.ext (by push_cast; exact one_sub_eS X)
  refine ⟨phi X ⟨eS X, eS_int X⟩, phi_mem X _, by rw [← map_mul, hes], ?_,
    ⟨phi X ⟨tS X, tS_int X⟩, phi_mem X _, by
      rw [← map_one (phi X), ← map_sub, hone, map_mul, map_natCast]⟩, ?_⟩
  · rw [phi_apply]
    simp [Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
  · intro s hs
    obtain ⟨w, hw, d, hwd⟩ := near_inv X hs
    obtain ⟨z, hz, hzd⟩ := unit_on_S X d
    refine ⟨w * phi X ⟨z, hz⟩, Subring.mul_mem _ hw (phi_mem X _), ?_⟩
    have hR : (⟨eS X, eS_int X⟩ : ↥(Formalism.UG.intAd X.B.I.F)) * ((1 + ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * d) * ⟨z, hz⟩) =
        ⟨eS X, eS_int X⟩ := Subtype.ext (by push_cast; exact hzd)
    calc phi X ⟨eS X, eS_int X⟩ * ((1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * (w * phi X ⟨z, hz⟩))
        = phi X ⟨eS X, eS_int X⟩ * (((1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * w) * phi X ⟨z, hz⟩) := by ring
      _ = phi X ((⟨eS X, eS_int X⟩ : ↥(Formalism.UG.intAd X.B.I.F)) * ((1 + ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * d) * ⟨z, hz⟩)) := by
          rw [hwd, map_mul, map_mul]
      _ = phi X ⟨eS X, eS_int X⟩ := by rw [hR]

end SIdemPf

end Formalism.L2.SG.Pf.NormSteps.LeviOntoSPf
