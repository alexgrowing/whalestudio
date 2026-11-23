import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneSubMemIdS
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open NumberField IsDedekindDomain Matrix Formalism.L2.Col GlobalTheory.InertNbr
open Formalism.L2.DIV (Pl kP St resS oToS idS cmpS)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.InertNbr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_den_idem {Q w : Pl E} {ε : E ⊗[F] Formalism.L2.Herm.Af F} (h : IdemOf F Q ε) (hw : w ≠ Q)
    (a : E ⊗[F] Formalism.L2.Herm.Af F) :
    ∃ t : 𝓞 E, t ∉ w.asIdeal ∧ ∃ hm : iA F E (algebraMap (𝓞 E) E t) * (ε * a) ∈ Formalism.L2.Herm.intAf F E,
      resS F w ⟨_, hm⟩ = 0 := by
  obtain ⟨N, hN, hNa⟩ := GlobalTheory.PlaceDatum.exists_den_adele (F := F) (E := E) a
  have hN0 : (N : 𝓞 E) ≠ 0 := by exact_mod_cast hN.ne'
  have hv0 : Q.intValuation (N : 𝓞 E) ≠ 0 := Q.intValuation_ne_zero _ hN0
  set k : ℕ := (-(WithZero.log (Q.intValuation (N : 𝓞 E)))).toNat with hk
  have hvk : Q.intValuation (N : 𝓞 E) = WithZero.exp (-(k : ℤ)) := by
    have h1 := Q.intValuation_le_one (N : 𝓞 E)
    rw [← WithZero.exp_log hv0] at h1 ⊢
    have h2 : WithZero.log (Q.intValuation (N : 𝓞 E)) ≤ 0 := by
      rw [← WithZero.exp_le_exp]; simpa using h1
    congr 1
    rw [hk]; omega
  obtain ⟨t, htk, htw⟩ : ∃ t ∈ Q.asIdeal ^ k, t ∉ w.asIdeal := by
    by_contra hn
    push Not at hn
    have hle : Q.asIdeal ≤ w.asIdeal := w.isPrime.le_of_pow_le hn
    exact hw (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le w.isPrime.ne_top hle)).symm
  have hNE : ((N : 𝓞 E) : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hval : Q.valuation E ((t : E) * ((N : 𝓞 E) : E)⁻¹) ≤ 1 := by
    rw [map_mul, map_inv₀, show (t : E) = algebraMap (𝓞 E) E t from rfl,
      show ((N : 𝓞 E) : E) = algebraMap (𝓞 E) E (N : 𝓞 E) from rfl,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hvk,
      mul_inv_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), one_mul]
    exact (Q.intValuation_le_pow_iff_mem t k).2 htk
  have hNc : ((N : ℕ) : E ⊗[F] Formalism.L2.Herm.Af F) = iA F E ((N : 𝓞 E) : E) := by simp
  have hinv : iA F E ((N : 𝓞 E) : E) * iA F E (((N : 𝓞 E) : E))⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hNE, map_one]
  have e : iA F E (algebraMap (𝓞 E) E t) * (ε * a) =
      ε * iA F E ((t : E) * ((N : 𝓞 E) : E)⁻¹) * ((N : E ⊗[F] Formalism.L2.Herm.Af F) * a) := by
    rw [hNc, map_mul, show algebraMap (𝓞 E) E t = (t : E) from rfl]
    linear_combination (-(iA F E (t : E) * ε * a)) * hinv
  have hm : iA F E (algebraMap (𝓞 E) E t) * (ε * a) ∈ Formalism.L2.Herm.intAf F E := by
    rw [e]; exact mul_mem (h.mul_mem_of_val hval) hNa
  have hm2 : ε * (iA F E (algebraMap (𝓞 E) E t) * a) ∈ Formalism.L2.Herm.intAf F E := by
    rw [mul_left_comm]; exact hm
  refine ⟨t, htw, hm, ?_⟩
  have e2 : (⟨_, hm⟩ : Formalism.L2.Herm.intAf F E) = ⟨_, hm2⟩ := Subtype.ext (mul_left_comm _ _ _)
  rw [e2]
  exact h.resS_eq_zero hw hm2

section Lat

variable [StarRing E] {n : ℕ} [NeZero n]

theorem pullV_mul_idem {ε : E ⊗[F] Formalism.L2.Herm.Af F} (x g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hg : ε • ((g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) = (g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1)
    (v : Fin n → E) (i : Fin n) :
    pullV (x * g⁻¹) v i = pullV x v i +
      ε * ((((g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) *ᵥ pullV x v) i) := by
  rw [pullV_mul_inv]
  conv_lhs => rw [← sub_add_cancel (g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) 1, ← hg]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, add_comm]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem mem_localization_globLat_mul_inv_of_ne {Q w : Pl E} {ε : E ⊗[F] Formalism.L2.Herm.Af F} (h : IdemOf F Q ε) (hw : w ≠ Q)
    (x g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hg : ε • ((g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) = (g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1)
    (v : Fin n → E) (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))) :
    v ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.UG.CS.globLat (x * g⁻¹) (stdLat E n)) ∧
      ∀ i, redA w (pullV (x * g⁻¹) v i) = redA w (pullV x v i) := by
  obtain ⟨s, hs, hsu⟩ := pullV_den hv
  set c := ((g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) *ᵥ pullV x v with hc
  choose t ht hm hz using fun i => exists_den_idem h hw (c i)
  have hT : (∏ i, t i) ∉ w.asIdeal := fun hT => by
    obtain ⟨i, _, hi⟩ := (w.isPrime.prod_mem_iff).1 hT
    exact ht i hi
  have hTc : ∀ i, iA F E (algebraMap (𝓞 E) E (∏ j, t j)) * (ε * c i) ∈ Formalism.L2.Herm.intAf F E := by
    intro i
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem t (Finset.mem_univ i)
    rw [hr, map_mul, map_mul, mul_comm (iA F E (algebraMap (𝓞 E) E (t i))), mul_assoc]
    exact mul_mem (iA_mem r) (hm i)
  refine ⟨(Formalism.L2.Col.mem_locP w _ v).2 ⟨s * ∏ j, t j, fun hh => (w.isPrime.mem_or_mem hh).elim hs hT,
    (mem_globLat _ _).2 fun i => ?_⟩, fun i => ?_⟩
  · rw [pullV_osmul, pullV_mul_idem x g hg, map_mul, map_mul, mul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm (iA F E (algebraMap (𝓞 E) E s)), mul_assoc]
      exact mul_mem (iA_mem _) (hsu i)
    · rw [mul_assoc]
      exact mul_mem (iA_mem _) (hTc i)
  · have h1 : iA F E (algebraMap (𝓞 E) E (s * t i)) * pullV x v i ∈ Formalism.L2.Herm.intAf F E := by
      rw [map_mul, map_mul, mul_comm (iA F E (algebraMap (𝓞 E) E s)), mul_assoc]
      exact mul_mem (iA_mem _) (hsu i)
    have h2 : iA F E (algebraMap (𝓞 E) E (s * t i)) * (ε * c i) ∈ Formalism.L2.Herm.intAf F E := by
      rw [map_mul, map_mul, mul_assoc]
      exact mul_mem (iA_mem _) (hm i)
    have hst : s * t i ∉ w.asIdeal := fun hh => (w.isPrime.mem_or_mem hh).elim hs (ht i)
    rw [pullV_mul_idem x g hg, redA_add w hst h1 h2]
    have h0 : redA w (ε * c i) = 0 := redA_eq w (ht i) (hm i) (by rw [mul_zero, hz i])
    rw [h0, add_zero]

end Lat

theorem decoRaw_mul_idem [StarRing E] {n : ℕ} [NeZero n] (ST SG : Finset (Pl E)) (Q : Pl E)
    (ε : E ⊗[F] Formalism.L2.Herm.Af F) (h : IdemOf F Q ε) (hQT : Q ∉ ST) (hQG : Q ∉ SG)
    (y b : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hb : ε • (b.1 - 1) = b.1 - 1) :
    (decoRaw ST SG (y * b)).f = (decoRaw ST SG y).f ∧ (decoRaw ST SG (y * b)).be = (decoRaw ST SG y).be := by
  have hb' : ε • (((b⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) =
      ((b⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1 := by
    have e : ((b⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1 =
        -(((b⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
          ((b : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1)) := by
      rw [Matrix.mul_sub, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      abel
    rw [e, smul_neg, ← Matrix.mul_smul]
    congr 2
  have hiff : ∀ w : Pl E, w ≠ Q → ∀ v : Fin n → E,
      v ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.UG.CS.globLat (y * b) (stdLat E n)) ↔
        v ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.UG.CS.globLat y (stdLat E n)) := by
    intro w hw v
    constructor
    · intro hv
      have := (mem_localization_globLat_mul_inv_of_ne h hw (y * b) b hb v hv).1
      rwa [mul_inv_cancel_right] at this
    · intro hv
      have := (mem_localization_globLat_mul_inv_of_ne h hw y b⁻¹ hb' v hv).1
      rwa [inv_inv] at this
  have hred : ∀ w : Pl E, w ≠ Q → ∀ v : Fin n → E,
      v ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.UG.CS.globLat y (stdLat E n)) →
        ∀ i, redA w (pullV (y * b) v i) = redA w (pullV y v i) := by
    intro w hw v hv i
    have := (mem_localization_globLat_mul_inv_of_ne h hw y b⁻¹ hb' v hv).2 i
    rwa [inv_inv] at this
  refine ⟨funext fun P => funext fun v => ?_, funext fun w => funext fun v => ?_⟩
  · have hP : P.1 ≠ Q := fun e => hQT (e ▸ P.2)
    simp only [decoRaw]
    by_cases hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat y (stdLat E n))
    · rw [if_pos ((hiff P.1 hP v).2 hv), if_pos hv, hred P.1 hP v hv]
    · rw [if_neg (fun h' => hv ((hiff P.1 hP v).1 h')), if_neg hv]
  · have hP : w.1 ≠ Q := fun e => hQG (e ▸ w.2)
    simp only [decoRaw]
    by_cases hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.UG.CS.globLat y (stdLat E n))
    · rw [if_pos ((hiff w.1 hP v).2 hv), if_pos hv]
      funext i
      exact hred w.1 hP v hv i
    · rw [if_neg (fun h' => hv ((hiff w.1 hP v).1 h')), if_neg hv]

end GlobalTheory.InertNbr
