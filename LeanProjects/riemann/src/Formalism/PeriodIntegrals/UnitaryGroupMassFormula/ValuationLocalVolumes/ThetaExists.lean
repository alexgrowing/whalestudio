import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.AbsVDetBigL

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolV

open Formalism.L2.SG.Pf.NcVal Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

section Box

variable (r : ℕ)

def pSet (g : ℕ) (p : Fin (r + 1) × Fin (r + 1)) : Set (Fv F v ⊗[F] E) :=
  if p.1 < p.2 then {y | y * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v}
  else if p.1 = p.2 then
    {y | y ∈ OEv (E := E) v ∧ (y + sigR (Fv F v) σ y) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v}
  else OEv (E := E) v

theorem famL_image
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + sigR (Fv F v) σ w)
    {g : ℕ} (hg0 : g ≠ 0) {θ : Fv F v ⊗[F] E} (hθO : θ ∈ OEv (E := E) v)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (p : Fin (r + 1) × Fin (r + 1)) (y : Fv F v ⊗[F] E) :
    y ∈ famL v r (g : Fv F v) θ p '' OEv (E := E) v ↔ y ∈ pSet σ v r g p := by
  have hgv : (g : Fv F v) ≠ 0 := VolTU.natCast_ne_zero v hg0
  unfold famL pSet
  split_ifs with h1 h2
  · simp only [Set.mem_setOf_eq, Set.mem_image, LinearMap.smul_apply, LinearMap.id_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← VolTU.sc_mul_eq_smul, mul_comm, ← mul_assoc, ← VolTU.sc_mul, inv_mul_cancel₀ hgv, VolTU.sc_one,
        one_mul]
      exact hz
    · intro h
      refine ⟨y * sc (E := E) v (g : Fv F v)⁻¹, h, ?_⟩
      rw [← VolTU.sc_mul_eq_smul, mul_comm, mul_assoc, ← VolTU.sc_mul, inv_mul_cancel₀ hgv, VolTU.sc_one,
        mul_one]
  · exact mem_aL_image v σ htr hg0 hθO hθ y
  · simp

theorem box_meas (hfin : Module.finrank F E = 2)
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + sigR (Fv F v) σ w)
    {g : ℕ} (hg0 : g ≠ 0) (hg : absV v (g : Fv F v) = (g : ℝ)⁻¹) {θ Δ : Fv F v ⊗[F] E}
    (hθO : θ ∈ OEv (E := E) v) (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1)
    (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0) (hΔ0 : Δ ≠ 0)
    (μ : Measure (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure]
    (hK : μ (VolTO (E := E) v (Fin (r + 1) × Fin (r + 1))) = 1) :
    μ {Y | ∀ p, Y p ∈ pSet σ v r g p} = ((g : ℝ≥0∞) ^ ((r + 1) ^ 2))⁻¹ := by
  obtain ⟨hD, hA⟩ := absV_det_bigL v r hfin hg0 hg θ Δ hθ hΔ hΔ0
  have himg : bigL v r (g : Fv F v) θ '' VolTO (E := E) v (Fin (r + 1) × Fin (r + 1)) =
      {Y | ∀ p, Y p ∈ pSet σ v r g p} := by
    ext Y
    simp only [Set.mem_image, Set.mem_setOf_eq, VolTO]
    constructor
    · rintro ⟨Z, hZ, rfl⟩ p
      exact (famL_image σ v r htr hg0 hθO hθ p _).1 ⟨Z p, hZ p, rfl⟩
    · intro h
      have : ∀ p, ∃ z, z ∈ OEv (E := E) v ∧ famL v r (g : Fv F v) θ p z = Y p := fun p =>
        (famL_image σ v r htr hg0 hθO hθ p _).2 (h p)
      choose Z hZ using this
      exact ⟨Z, fun p => (hZ p).1, funext fun p => (hZ p).2⟩
  have hgpos : (0 : ℝ) < g := by exact_mod_cast Nat.pos_of_ne_zero hg0
  rw [← himg, meas_image v _ μ _ hD _ (VolUL.volTO_meas v _), hK, mul_one, hA,
    ENNReal.ofReal_pow (inv_nonneg.2 hgpos.le), ENNReal.ofReal_inv_of_pos hgpos, ENNReal.ofReal_natCast,
    ENNReal.inv_pow]

theorem diag_key
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + sigR (Fv F v) σ w)
    {θ : Fv F v ⊗[F] E} (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (c y : Fv F v ⊗[F] E)
    (hc : sigR (Fv F v) σ c = c) :
    (y - c * θ) + sigR (Fv F v) σ (y - c * θ) = y + sigR (Fv F v) σ y - c := by
  have h1 : θ + sigR (Fv F v) σ θ = 1 := by rw [← htr, hθ, map_one]
  rw [map_sub, map_mul, hc]
  linear_combination (-c) * h1

def ctr (θ : Fv F v ⊗[F] E) (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E))
    (p : Fin (r + 1) × Fin (r + 1)) : Fv F v ⊗[F] E :=
  if p.1 < p.2 then c p.1 p.2 else if p.1 = p.2 then c p.1 p.2 * θ else 0

theorem hermBox_eq
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + sigR (Fv F v) σ w)
    {g : ℕ} (hg0 : g ≠ 0) {θ : Fv F v ⊗[F] E} (hθO : θ ∈ OEv (E := E) v)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1)
    (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) (hc : VolTHermInt σ v r c) :
    VolUHm.hermBox σ v g r c =
      {Y | (fun p => Y p - ctr v r θ c p) ∈ {Y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E |
        ∀ p, Y p ∈ pSet σ v r g p}} := by
  have hgO : sc (E := E) v (g : Fv F v) ∈ OEv (E := E) v := VolUTr.TrW.alg_mem v (VolTU.natCast_memO v g)
  ext Y
  simp only [VolUHm.hermBox, Set.mem_setOf_eq]
  constructor
  · intro h p
    obtain ⟨i, j⟩ := p
    obtain ⟨hO, hup, hdg⟩ := h i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp only [ctr, pSet, if_pos hij, Set.mem_setOf_eq]
      exact hup hij
    · subst hij
      simp only [ctr, pSet, lt_irrefl, if_false, if_true, Set.mem_setOf_eq]
      refine ⟨Submodule.sub_mem _ hO (VolUTr.TrW.mul_mem v (hc.2 i i) hθO), ?_⟩
      rw [diag_key σ v htr hθ _ _ (hc.1 i i).symm]
      exact hdg rfl
    · have h1 : ¬ i < j := not_lt.2 hij.le
      have h2 : i ≠ j := hij.ne'
      simp only [ctr, pSet, if_neg h1, if_neg h2, sub_zero]
      exact hO
  · intro h i j
    have hp := h (i, j)
    rcases lt_trichotomy i j with hij | hij | hij
    · simp only [ctr, pSet, if_pos hij, Set.mem_setOf_eq] at hp
      have hO : Y (i, j) ∈ OEv (E := E) v := by
        have e : Y (i, j) = sc (E := E) v (g : Fv F v) * ((Y (i, j) - c i j) * sc (E := E) v (g : Fv F v)⁻¹) +
            c i j := by
          rw [mul_comm, mul_assoc, ← VolTU.sc_mul, inv_mul_cancel₀ (VolTU.natCast_ne_zero v hg0), VolTU.sc_one,
            mul_one, sub_add_cancel]
        rw [e]
        exact Submodule.add_mem _ (VolUTr.TrW.mul_mem v hgO hp) (hc.2 i j)
      exact ⟨hO, fun _ => hp, fun h => absurd h hij.ne⟩
    · subst hij
      simp only [ctr, pSet, lt_irrefl, if_false, if_true, Set.mem_setOf_eq] at hp
      have hO : Y (i, i) ∈ OEv (E := E) v := by
        rw [← sub_add_cancel (Y (i, i)) (c i i * θ)]
        exact Submodule.add_mem _ hp.1 (VolUTr.TrW.mul_mem v (hc.2 i i) hθO)
      refine ⟨hO, fun h => absurd h (lt_irrefl _), fun _ => ?_⟩
      rw [← diag_key σ v htr hθ _ _ (hc.1 i i).symm]
      exact hp.2
    · have h1 : ¬ i < j := not_lt.2 hij.le
      have h2 : i ≠ j := hij.ne'
      simp only [ctr, pSet, if_neg h1, if_neg h2, sub_zero] at hp
      exact ⟨hp, fun h => absurd h h1, fun h => absurd h h2⟩

theorem hermBox_meas (hfin : Module.finrank F E = 2)
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + sigR (Fv F v) σ w)
    {g : ℕ} (hg0 : g ≠ 0) (hg : absV v (g : Fv F v) = (g : ℝ)⁻¹) {θ Δ : Fv F v ⊗[F] E}
    (hθO : θ ∈ OEv (E := E) v) (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1)
    (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0) (hΔ0 : Δ ≠ 0)
    (μ : Measure (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure]
    (hK : μ (VolTO (E := E) v (Fin (r + 1) × Fin (r + 1))) = 1)
    (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) (hc : VolTHermInt σ v r c) :
    μ (VolUHm.hermBox σ v g r c) = ((g : ℝ≥0∞) ^ ((r + 1) ^ 2))⁻¹ := by
  rw [hermBox_eq σ v r htr hg0 hθO hθ c hc, VolUH.sub_pre v _ μ,
    box_meas σ v r hfin htr hg0 hg hθO hθ hΔ hΔ0 μ hK]

end Box

theorem theta_exists (hinv : ∀ y, σ (σ y) = y) (hnt : ∃ x, σ x ≠ x) (hfin : Module.finrank F E = 2)
    (a t : 𝓞 E) (ht : σ (a : E) = (t : E)) (e : 𝓞 F)
    (he : ((a : E) - t) ^ 2 = algebraMap F E (e : F)) (hev : e ∉ v.asIdeal) :
    ∃ θ Δ : Fv F v ⊗[F] E, θ ∈ OEv (E := E) v ∧ Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1 ∧
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0 ∧ Δ ≠ 0 := by
  have hst : σ (t : E) = a := by rw [← ht, hinv]
  have hTa : Algebra.trace F E ((a : E) - t) = 0 := by
    apply (algebraMap F E).injective
    rw [VolUTr.TrW.trace_eq_add σ hinv hnt hfin, map_sub, ht, hst, map_zero]
    ring
  have hTb : Algebra.trace F E ((a : E) * ((a : E) - t)) = e := by
    apply (algebraMap F E).injective
    rw [VolUTr.TrW.trace_eq_add σ hinv hnt hfin, map_mul, map_sub, ht, hst, ← he]
    ring
  set ev := algebraMap F (Fv F v) (e : F) with hevdef
  have hval : Valued.v ev = 1 := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) v (algebraMap (𝓞 F) F e)
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hev] at h
    exact h
  have he0 : ev ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hval
    exact zero_ne_one hval
  have hinvm : ev⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  have hθ1 : Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
      (sc (E := E) v ev⁻¹ * inclR (F := F) (Fv F v) ((a : E) * ((a : E) - t))) = 1 := by
    rw [VolUTr.TrW.sc_eq, ← Algebra.smul_def, map_smul, PI.UnitaryGroupMassFormula.LocJacTyp.Sd.trace_inclR, hTb, smul_eq_mul,
      inv_mul_cancel₀ he0]
  refine ⟨sc (E := E) v ev⁻¹ * inclR (F := F) (Fv F v) ((a : E) * ((a : E) - t)),
    inclR (F := F) (Fv F v) ((a : E) - t), ?_, hθ1, ?_, ?_⟩
  · refine VolUTr.TrW.mul_mem v (VolUTr.TrW.alg_mem v hinvm) ?_
    have e1 : (((a * (a - t) : 𝓞 E)) : E) = (a : E) * ((a : E) - t) := by push_cast; ring
    rw [← e1]
    exact VolUTr.TrW.inclR_mem' (E := E) v (a * (a - t))
  · rw [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.trace_inclR, hTa, map_zero]
  · intro h0
    rw [show inclR (F := F) (Fv F v) ((a : E) * ((a : E) - t)) =
        inclR (F := F) (Fv F v) (a : E) * inclR (F := F) (Fv F v) ((a : E) - t) from map_mul _ _ _, h0,
      mul_zero, mul_zero, map_zero] at hθ1
    exact zero_ne_one hθ1

end Formalism.L2.SG.Pf.NcVal.VolV
