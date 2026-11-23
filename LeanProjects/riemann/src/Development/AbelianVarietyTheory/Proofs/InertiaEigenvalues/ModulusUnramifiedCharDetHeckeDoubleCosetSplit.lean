import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMatrixLattice

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDetValue

open GlobalTheory.SplitHecke

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem valued_unit (u : (v.adicCompletionIntegers F)ˣ) :
    Valued.v (algebraMap (v.adicCompletionIntegers F) (Fv F v) u) = 1 := by
  by_contra hne
  exact (GlobalTheory.SplitUnif.mem_max v u).2 (lt_of_le_of_ne (u : v.adicCompletionIntegers F).2 hne) u.isUnit

theorem valued_irreducible {p : v.adicCompletionIntegers F} (hp : Irreducible p) :
    Valued.v (algebraMap (v.adicCompletionIntegers F) (Fv F v) p) = WithZero.exp (-1) := by
  obtain ⟨t, ht⟩ := v.intValuation_exists_uniformizer
  have hφ : ∀ s : 𝓞 F, Valued.v (algebraMap F (Fv F v) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  let p₀ : v.adicCompletionIntegers F := ⟨algebraMap F (Fv F v) t, GlobalTheory.SplitUnif.map_mem v _ t⟩
  have hp₀ : Valued.v (p₀ : Fv F v) = WithZero.exp (-1) := (hφ t).trans ht
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.associated_of_irreducible _ hp
    (GlobalTheory.SplitUnif.irreducible_of_valued v p₀ hp₀)
  have := congrArg (fun y : v.adicCompletionIntegers F => Valued.v (y : Fv F v)) hw
  change Valued.v ((p : Fv F v) * (w : v.adicCompletionIntegers F)) = Valued.v (p₀ : Fv F v) at this
  rw [map_mul, hp₀] at this
  have hw1 := valued_unit v w
  rw [← this]
  change _ = _ * Valued.v (algebraMap (v.adicCompletionIntegers F) (Fv F v) w)
  rw [hw1, mul_one]
  rfl

theorem card_residue_eq :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  have hφ : ∀ s : 𝓞 F, Valued.v (algebraMap F (Fv F v) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  exact GlobalTheory.SplitUnif.card_residueField v (algebraMap F (Fv F v)) v (fun _ => rfl) fun s => by
    rw [hφ, HeightOneSpectrum.intValuation_lt_one_iff_mem]

end Local

section Chart

variable {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}

theorem chi_of_unit_gen (hπ : Chart e v π) {x d : (AE D)ˣ} (hx1 : (1 - e) * (x : AE D) = 1 - e)
    (hd1 : (1 - e) * (d : AE D) = 1 - e) {A : Type} [CommGroup A] {χ : (AE D)ˣ →* A}
    (hχ : ∀ y : (AE D)ˣ, (1 - e) * (y : AE D) = 1 - e → finPart D (e * (y : AE D)) ∈ intAE D →
      finPart D (e * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D → χ y = 1) {u : (Ov D v)ˣ}
    (h1 : π (d : AE D) = π (x : AE D) * algebraMap (Ov D v) (Fv D.host.F v) u) : χ d = χ x := by
  have h3 : π ((x⁻¹ * d : (AE D)ˣ) : AE D) = algebraMap (Ov D v) (Fv D.host.F v) u := by
    rw [Units.val_mul, π.map_mul, h1, ← mul_assoc, ← π.map_mul, Units.inv_mul, π.map_one, one_mul]
  have h4 := hχ (x⁻¹ * d) ?_ ((hπ.2.2.2 _).2 ⟨u, h3.symm⟩) ((hπ.2.2.2 _).2 ⟨(u⁻¹ : (Ov D v)ˣ), ?_⟩)
  · rwa [χ.map_mul, χ.map_inv, inv_mul_eq_one, eq_comm] at h4
  · have h5 : (1 - e) * ((x⁻¹ : (AE D)ˣ) : AE D) = 1 - e := by
      conv_lhs => rw [← hx1, mul_assoc, Units.mul_inv, mul_one]
    rw [Units.val_mul, ← mul_assoc, h5, hd1]
  · rw [map_units_inv, map_units_inv, h3]

end Chart

set_option maxHeartbeats 1000000 in

theorem det_modulus_chi : ∀ (D : D7) (V : HSp D) (P : Pl D.host.E) (e : AE D), IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ x : (AE D)ˣ, (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → ∀ (k : ℕ) (α : GA D V), IsHeckeElt V e (ϖ : D.host.E) k α → ∀ k₁ ∈ Mult.locPart V (KsphC V ∅) e, ∀ k₂ ∈ Mult.locPart V (KsphC V ∅) e, ∀ z : (AE D)ˣ, IsDetAt e V (k₁ * α * k₂) z → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D z = (((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ k)⁻¹ ∧ ∀ (A : Type) [CommGroup A] (χ : (AE D)ˣ →* A), (∀ y : (AE D)ˣ, (1 - e) * (y : AE D) = 1 - e → finPart D (e * (y : AE D)) ∈ intAE D → finPart D (e * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D → χ y = 1) → χ z = χ x ^ k := by
  intro D V P e hP ϖ hϖ hϖ2 x hx k α hα k₁ hk₁ k₂ hk₂ z hz
  have he := hP.1
  obtain ⟨v, π, hπ⟩ := GlobalTheory.T.exists_place_chart_of_splitIdempotent e he
  obtain ⟨⟨p, hpϖ, hp⟩, hq⟩ := GlobalTheory.T.splitChart_uniformiser_and_residueCard e P v π hP hπ ϖ hϖ hϖ2
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_splitFrame_selfDualLattice_completion e v π he hπ V
  have st := GlobalTheory.T.mem_hyperspecial_iff_gInt_of_suppAt_split e v π he hπ V β hβ
  have hH : Hk (Ov D v) p k (rho V π β (k₁ * α * k₂)) := by
    rw [map_mul, map_mul]
    exact (GlobalTheory.T.heckeElement_component_mem_standardDoubleCoset e v π he hπ V β hβ (ϖ : D.host.E) p k α hpϖ hα).mul ((st _ hk₁.2).1 hk₁.1)
      ((st _ hk₂.2).1 hk₂.1)
  obtain ⟨u, hu⟩ := hH.2.2
  have hx1 : (1 - e) * (x : AE D) = 1 - e := by
    rw [hx]
    exact one_sub_mul_idem he.1 _
  have hx2 : π x = algebraMap (Ov D v) (Fv D.host.F v) p := by
    rw [hx, π.map_add, π.map_mul, π.map_sub, π.map_one, hπ.map_e he.1, one_mul, sub_self, add_zero, hpϖ]
  have hz1 : (1 - e) * (z : AE D) = 1 - e := by
    rw [hz]
    exact one_sub_mul_idem he.1 _
  have hz2 : π (z : AE D) = algebraMap (Ov D v) (Fv D.host.F v) (p ^ k * u) := by
    rw [rho_val, Matrix.det_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul] at hu
    rw [hz, π.map_add, π.map_mul, π.map_sub, π.map_one, hπ.map_e he.1, one_mul, sub_self, add_zero]
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    exact hu
  refine ⟨?_, fun A _ χ hχ => ?_⟩
  · rw [GlobalTheory.SplitLinear.absFin_split D e v π he hπ z hz1, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
    have e1 : ((Units.map π.toMonoidHom z : (Fv D.host.F v)ˣ) : Fv D.host.F v) = π (z : AE D) := rfl
    have e2 : Ideal.absNorm v.asIdeal = Ideal.absNorm P.asIdeal := by
      rw [← card_residue_eq, hq]
    have hv1 : Valued.v (algebraMap (Ov D v) (Fv D.host.F v) p) = WithZero.exp (-1) := valued_irreducible v hp
    have hv2 : Valued.v (algebraMap (Ov D v) (Fv D.host.F v) u) = 1 := valued_unit v u
    rw [e1, hz2, map_mul, map_mul, map_pow, map_pow, hv1, hv2, mul_one, e2,
      ← WithZero.exp_nsmul, WithZero.log_exp, nsmul_eq_mul, mul_neg_one, _root_.zpow_neg, zpow_natCast]
  · have h1 : π (z : AE D) = π ((x ^ k : (AE D)ˣ) : AE D) * algebraMap (Ov D v) (Fv D.host.F v) u := by
      rw [hz2, Units.val_pow_eq_pow_val, π.map_pow, hx2, ← RingHom.map_pow, ← RingHom.map_mul]
    have h2 : ∀ j : ℕ, (1 - e) * ((x ^ j : (AE D)ˣ) : AE D) = 1 - e := fun j => by
      induction j with
      | zero => rw [pow_zero, Units.val_one, mul_one]
      | succ j ih => rw [pow_succ, Units.val_mul, ← mul_assoc, ih, hx1]
    exact (chi_of_unit_gen hπ (h2 k) hz1 hχ h1).trans (χ.map_pow x k)

end GlobalTheory.SplitDetValue
