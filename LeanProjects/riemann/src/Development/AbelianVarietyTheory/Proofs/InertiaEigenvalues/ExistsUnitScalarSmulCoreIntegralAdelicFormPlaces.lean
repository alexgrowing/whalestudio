import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalSectionBoundedNonzeroMultiple
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGoodOfBddAll
import Formalism.LocalToGlobal.ProjectiveLattices.ModelAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsAllEmbeddingsOfInclusionReadingStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ScaleInt

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 K) ∈ la.asIdeal := by
  have : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot la.asIdeal la.ne_bot
  have : la.asIdeal.IsMaximal := la.isMaximal
  let _ : Field (𝓞 K ⧸ la.asIdeal) := Ideal.Quotient.field _
  refine ⟨ringChar (𝓞 K ⧸ la.asIdeal), CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem exists_avoid {K : Type} [Field K] [NumberField K] (q : Ideal (𝓞 K)) (hq : q.IsPrime)
    (s : Finset (HeightOneSpectrum (𝓞 K))) (hs : ∀ p ∈ s, p.asIdeal ≠ q) (N : HeightOneSpectrum (𝓞 K) → ℕ) :
    ∃ t : 𝓞 K, t ∉ q ∧ ∀ p ∈ s, t ∈ p.asIdeal ^ N p := by
  have hle : ¬ (s.prod fun p => p.asIdeal ^ N p) ≤ q := by
    rw [hq.prod_le]
    rintro ⟨p, hp, hpq⟩
    rcases Nat.eq_zero_or_pos (N p) with h0 | hpos
    · rw [h0, pow_zero, Ideal.one_eq_top, top_le_iff] at hpq
      exact hq.ne_top hpq
    · have h1 : p.asIdeal ≤ q := hq.le_of_pow_le hpq
      exact hs p hp (p.isMaximal.eq_of_le hq.ne_top h1)
  obtain ⟨t, ht, htq⟩ := SetLike.not_le_iff_exists.1 hle
  exact ⟨t, htq, fun p hp => (Ideal.prod_le_inf.trans (Finset.inf_le hp)) ht⟩

theorem le_vLa_of_mem {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) {t : 𝓞 K} (n : ℕ)
    (ht : t ∈ p.asIdeal ^ n) (ht0 : t ≠ 0) : (n : ℤ) ≤ vLa p (t : K) := by
  have h := (p.intValuation_le_pow_iff_mem t n).2 ht
  have hne : p.intValuation t ≠ 0 := HeightOneSpectrum.intValuation_ne_zero p t ht0
  have e : p.valuation K (t : K) = p.intValuation t := p.valuation_of_algebraMap t
  unfold vLa
  rw [e]
  have := (WithZero.log_le_log hne (by simp)).2 h
  simp at this
  omega

theorem vLa_eq_zero_of_not_mem {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) {t : 𝓞 K}
    (ht : t ∉ p.asIdeal) : vLa p (t : K) = 0 := by
  unfold vLa
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem p).mpr ht, WithZero.log_one, neg_zero]

end GlobalTheory.ScaleInt

namespace GlobalTheory.ScaleInt

set_option maxHeartbeats 800000 in

theorem smul_mem_baseInt : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)), κ.LastPos →
    ∀ (q : Ideal (𝓞 T.Q.c.F)), q.IsPrime → ∀ (P : Set (HeightOneSpectrum (𝓞 T.Q.c.F))), P.Finite →
    ∀ ψ ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n {p | p.asIdeal = q},
      ∃ t : 𝓞 T.Q.c.F, t ∉ q ∧ T.σ₀ (t : T.Q.c.F) • ψ ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n P := by
  intro D T hT i κ hκ q hq P hP ψ hψ
  obtain ⟨f, ⟨hfs, hfh, hfv⟩, rfl⟩ := hψ
  have hj : InR D ((i : ℕ) + 1) := inR i
  have hcusp : f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.U ((i : ℕ) + 1)) (wtA κ) κ.n := GlobalTheory.T.mem_cuspForms_allEmbeddings_of_inclusion_reading D T hT _ hj κ hκ f hfs hfh
  have hbd : ∀ p : HeightOneSpectrum (𝓞 T.Q.c.F), ∃ κ' : T.Q.c.F, κ' ≠ 0 ∧
      GlobalTheory.GoodPts.BddAll (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p κ' f := by
    intro p
    obtain ⟨pr, hpr, hmem⟩ := exists_prime_mem p
    exact GlobalTheory.CuspBound.exists_bddAll_cusp _ _ _ _ _ _ _ (T.U ((i : ℕ) + 1)) (hT.unf _ hj) p pr hpr hmem
      (goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne pr hpr) _ _ f
      (dom_wtA κ) hcusp
  choose κ' hκ0 hκb using hbd
  obtain ⟨t, htq, htm⟩ := exists_avoid q hq (hP.toFinset.filter fun p => p.asIdeal ≠ q)
    (fun p hp => (Finset.mem_filter.1 hp).2) (fun p => (vLa p (κ' p)).toNat)
  have ht0 : t ≠ 0 := fun h => htq (h ▸ q.zero_mem)
  have htK : (t : T.Q.c.F) ≠ 0 := by exact_mod_cast ht0
  refine ⟨t, htq, (t : T.Q.c.F) • f, ⟨(sec _ _ _ _).smul_mem _ hfs, ?_, ?_⟩, ?_⟩
  · rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ hfh
  · intro la hla v hv
    have hV := isVal_valSet la v hv
    rw [hV.smul _ _ htK]
    by_cases hlq : la.asIdeal = q
    · have h0 : vAdd la (t : T.Q.c.F) = 0 := vLa_eq_zero_of_not_mem la (hlq ▸ htq)
      rw [h0]
      simpa using hfv la hlq v hv
    · have hmem : la ∈ hP.toFinset.filter fun p => p.asIdeal ≠ q :=
        Finset.mem_filter.2 ⟨hP.mem_toFinset.2 hla, hlq⟩
      have hge : (vLa la (κ' la) : ℤ) ≤ vAdd la (t : T.Q.c.F) :=
        (Int.self_le_toNat _).trans (le_vLa_of_mem la _ (htm la hmem) ht0)
      obtain ⟨y, rfl⟩ := hv
      have hb := (GlobalTheory.GoodPtsModel.bddAll_iff_vAtV (hκ0 la) f).1 (hκb la) y
      exact hb.trans (add_le_add (by exact_mod_cast hge) le_rfl)
  · simp only [CoreJ.phiJ, map_smulₛₗ, LinearMap.map_smul, smul_comm ((lieFac _ _ _ : ℝ) : ℂ)]
    rfl

end GlobalTheory.ScaleInt
