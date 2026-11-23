import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.BlattnerShiftsSignedParameters

open Formalism.BasicNotions.TH Formalism.L2.Theta Matrix

noncomputable section

namespace GlobalTheory.CoverDS

variable {p q : ℕ} {T : GrpData p q}

def UnitEquiv (R R' : DSRep T) : Prop :=
  ∃ U : R.U.H ≃ₗᵢ[ℂ] R'.U.H, ∀ g x, U (R.U.π g x) = R'.U.π g (U x)

def InCone (lam μ : Ix p q → ℚ) : Prop :=
  ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → lam b < lam a) ∧
    μ = fun c => blattner lam c +
      ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0))

def HasTypes (R : DSRep T) (lam : Ix p q → ℚ) : Prop :=
  Module.finrank ℂ ↥(hwSub R.HK.act (blattner lam)) = 1 ∧
  (∀ v, casimir R.HK.act v = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • v) ∧
  ∀ (μ : Ix p q → ℚ) v, IsHW R.HK.act μ v → InCone lam μ

end GlobalTheory.CoverDS

namespace GlobalTheory.Published

open GlobalTheory.CoverDS

def DiscreteSeriesCover : Prop :=
  ∀ (p q : ℕ), 1 ≤ p + q → ∀ T : GrpData p q,
    ∃ D : {lam : Ix p q → ℚ // IsParam lam} → DSRep T,
      (∀ lam, HasTypes (D lam) lam.1) ∧ ∀ R : DSRep T, ∃ lam, UnitEquiv R (D lam)

end GlobalTheory.Published

namespace GlobalTheory.CoverDS

open GlobalTheory.Published

variable {p q : ℕ} {T : GrpData p q}

theorem UnitEquiv.symm {R R' : DSRep T} (h : UnitEquiv R R') : UnitEquiv R' R := by
  obtain ⟨U, hU⟩ := h
  exact ⟨U.symm, fun g x => U.injective (by rw [hU, U.apply_symm_apply, U.apply_symm_apply])⟩

theorem UnitEquiv.trans {R R' R'' : DSRep T} (h : UnitEquiv R R') (h' : UnitEquiv R' R'') : UnitEquiv R R'' := by
  obtain ⟨U, hU⟩ := h
  obtain ⟨V, hV⟩ := h'
  exact ⟨U.trans V, fun g x => by simp [hU, hV]⟩

theorem exists_decomp (Z : Mat p q) : ∃ X ∈ upq p q, ∃ Y ∈ upq p q, Z = X + Complex.I • Y := by
  have hJ := GlobalTheory.RealPar.KStabLie.Jm_sq p q
  have hJ' : ∀ A : Mat p q, Jm p q * (Jm p q * A) = A := fun A => by rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have hc := GlobalTheory.RealPar.KStabLie.Jm_ct p q
  refine ⟨(1 / 2 : ℂ) • (Z - Jm p q * Zᴴ * Jm p q), ?_, (-Complex.I / 2) • (Z + Jm p q * Zᴴ * Jm p q), ?_, ?_⟩
  · change _ + _ = 0
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hc, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_assoc, hJ, hJ', Matrix.mul_one]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp, ← smul_add]
    simp
  · change _ + _ = 0
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hc, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc, hJ, hJ', Matrix.mul_one]
    rw [show star (-Complex.I / 2 : ℂ) = -(-Complex.I / 2) by simp [neg_div]]
    module
  · rw [smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by
      rw [← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg]]
    module

theorem kFin_map {R R' : DSRep T} (U : R.U.H ≃ₗᵢ[ℂ] R'.U.H) (hU : ∀ g x, U (R.U.π g x) = R'.U.π g (U x))
    {x : R.U.H} (hx : KFin T R.U.π x) : KFin T R'.U.π (U x) := by
  unfold KFin at hx ⊢
  refine Submodule.finiteDimensional_of_le
    (S₂ := (Submodule.span ℂ (Set.range fun k : T.Kset => R.U.π k x)).map U.toLinearEquiv.toLinearMap) ?_
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, hU k x⟩

theorem exists_moduleEquiv {R R' : DSRep T} (U : R.U.H ≃ₗᵢ[ℂ] R'.U.H)
    (hU : ∀ g x, U (R.U.π g x) = R'.U.π g (U x)) :
    ∃ e : R.HK.V ≃ₗ[ℂ] R'.HK.V, (∀ v, R'.ι (e v) = U (R.ι v)) ∧ ∀ Z v, e (R.HK.act Z v) = R'.HK.act Z (e v) := by
  have hr : (LinearMap.range R.ι).map U.toLinearEquiv.toLinearMap = LinearMap.range R'.ι := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (R'.ι_range _).2 (kFin_map U hU ((R.ι_range x).1 hx))
    · intro y hy
      refine ⟨U.symm y, (R.ι_range _).2 (kFin_map U.symm (fun g x => U.injective ?_) ((R'.ι_range y).1 hy)),
        U.apply_symm_apply y⟩
      rw [hU, U.apply_symm_apply, U.apply_symm_apply]
  let e : R.HK.V ≃ₗ[ℂ] R'.HK.V := (LinearEquiv.ofInjective R.ι R.ι_inj).trans
    ((U.toLinearEquiv.ofSubmodules _ _ hr).trans (LinearEquiv.ofInjective R'.ι R'.ι_inj).symm)
  have he : ∀ v, R'.ι (e v) = U (R.ι v) := fun v => by
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.ofInjective_symm_apply]
    rfl
  have hX : ∀ X ∈ upq p q, ∀ v, e (R.HK.act X v) = R'.HK.act X (e v) := by
    intro X hX v
    refine R'.ι_inj ?_
    have h1 := R'.der X hX (e v)
    have h2 := ((U.toContinuousLinearEquiv : R.U.H →L[ℂ] R'.U.H).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) (R.der X hX v)
    rw [he]
    refine HasDerivAt.unique h2 ?_
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only [he, ← hU]
    rfl
  refine ⟨e, he, fun Z v => ?_⟩
  obtain ⟨X, h1, Y, h2, rfl⟩ := exists_decomp Z
  simp [hX X h1, hX Y h2]

theorem mem_hwSub_iff {V : Type*} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (μ : Ix p q → ℚ) (v : V) : v ∈ hwSub act μ ↔
      (∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) ∧ ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp [hwSub, wtSub, Submodule.mem_iInf, sub_eq_zero]

theorem HasTypes.of_equiv {R R' : DSRep T} {lam : Ix p q → ℚ} (h : HasTypes R' lam) (hR : UnitEquiv R R') :
    HasTypes R lam := by
  obtain ⟨U, hU⟩ := hR
  obtain ⟨e, -, he⟩ := exists_moduleEquiv U hU
  have hm : ∀ μ v, e v ∈ hwSub R'.HK.act μ ↔ v ∈ hwSub R.HK.act μ := fun μ v => by
    simp only [mem_hwSub_iff, ← he, ← map_smul, e.injective.eq_iff, e.map_eq_zero_iff]
  refine ⟨?_, fun v => e.injective ?_, fun μ v hv => h.2.2 μ (e v) ⟨e.map_ne_zero_iff.2 hv.1, (hm μ v).2 hv.2⟩⟩
  · have hq : (hwSub R.HK.act (blattner lam)).map e.toLinearMap = hwSub R'.HK.act (blattner lam) := by
      ext w
      obtain ⟨v, rfl⟩ := e.surjective w
      rw [hm, Submodule.mem_map_equiv, e.symm_apply_apply]
    rw [← h.1, ← hq, LinearEquiv.finrank_map_eq]
  · rw [map_smul, ← h.2.1]
    simp [casimir, LinearMap.sum_apply, he]

theorem vogan_add_le {lam μ : Ix p q → ℚ} (hl : IsParam lam) (h : InCone lam μ) :
    vogan (blattner lam) + ∑ c, (μ c - blattner lam c) ^ 2 ≤ vogan μ := by
  classical
  obtain ⟨m, hm, hμ⟩ := h
  set x : Ix p q → ℚ := fun c => blattner lam c + rhoOfIndex c with hx
  have mono : ∀ a b, lam b < lam a → x b ≤ x a := by
    intro a b hab
    simp only [hx, GlobalTheory.SignedParTest.blattner_add_rho2C hl]
    have h1 : ((Finset.univ.filter fun c => lam c < lam b).card : ℚ) ≤
        (Finset.univ.filter fun c => lam c < lam a).card := by
      exact_mod_cast Finset.card_le_card fun c hc => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *; linarith
    have h2 : ((Finset.univ.filter fun c => lam a < lam c).card : ℚ) ≤
        (Finset.univ.filter fun c => lam b < lam c).card := by
      exact_mod_cast Finset.card_le_card fun c hc => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *; linarith
    linarith
  have hdot : 0 ≤ ∑ c, x c * (μ c - blattner lam c) := by
    have : ∑ c, x c * (μ c - blattner lam c) = ∑ a, ∑ b, (m a b : ℚ) * (x a - x b) := by
      have hr : ∀ a b, x a - x b = ∑ c, x c * ((if c = a then 1 else 0) - (if c = b then 1 else 0)) := by
        intro a b
        simp [mul_sub, Finset.sum_sub_distrib]
      simp only [hμ, add_sub_cancel_left, hr, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
    rw [this]
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    by_cases h0 : m a b = 0
    · simp [h0]
    · exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 (mono a b (hm a b h0)))
  have : vogan μ = vogan (blattner lam) + ∑ c, (μ c - blattner lam c) ^ 2 +
      2 * ∑ c, x c * (μ c - blattner lam c) := by
    simp only [vogan, hx, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  linarith

theorem HasTypes.exists_isHW {R : DSRep T} {lam : Ix p q → ℚ} (h : HasTypes R lam) :
    ∃ v, IsHW R.HK.act (blattner lam) v := by
  have : hwSub R.HK.act (blattner lam) ≠ ⊥ := fun h0 => by
    have := h.1
    rw [h0, finrank_bot] at this
    exact zero_ne_one this
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 this
  exact ⟨v, h0, hv⟩

theorem HasTypes.hasParam {R : DSRep T} {lam : Ix p q → ℚ} (hl : IsParam lam) (h : HasTypes R lam) :
    HasParam R lam := by
  refine ⟨h.exists_isHW, fun μ v hv => ?_⟩
  have h1 := vogan_add_le hl (h.2.2 μ v hv)
  have h2 : 0 ≤ ∑ c, (μ c - blattner lam c) ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  linarith

theorem HasTypes.eq_of_hasParam {R : DSRep T} {lam lam' : Ix p q → ℚ} (hl : IsParam lam) (hl' : IsParam lam')
    (h' : HasTypes R lam') (h : HasParam R lam) : lam = lam' := by
  obtain ⟨v, hv⟩ := h.1
  obtain ⟨w, hw⟩ := h'.exists_isHW
  have h1 := vogan_add_le hl' (h'.2.2 _ v hv)
  have h2 := h.2 _ w hw
  have h3 : ∑ c, (blattner lam c - blattner lam' c) ^ 2 = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg fun c _ => sq_nonneg _)
  refine GlobalTheory.SignedParTest.blattner_inj hl hl' (funext fun c => ?_)
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1
    ((Finset.sum_eq_zero_iff_of_nonneg fun c _ => sq_nonneg _).1 h3 c (Finset.mem_univ c)))

theorem hasTypes_zero {T : GrpData 0 0} (R : DSRep T) (lam : Ix 0 0 → ℚ) : HasTypes R lam := by
  refine ⟨?_, fun v => by simp [casimir, normSq, rhoSq], fun μ v _ => ⟨0, by simp, Subsingleton.elim _ _⟩⟩
  obtain ⟨v, hv, -⟩ := (GlobalTheory.SignedParTest.hasParam_zero R lam).1
  have hs : ∀ g, ∃ c : ℂ, R.U.π g = c • 1 := by
    intro g
    have hg : T.cov g = 1 := Units.ext (Subsingleton.elim _ _)
    rcases GlobalTheory.RealPar.Cover.trivial_or_twist R with h | h
    · exact ⟨1, by rw [h g hg, one_smul]⟩
    · refine ⟨((T.sq g : ℂˣ) : ℂ), ?_⟩
      have h1 : ((T.sq g : ℂˣ) : ℂ)⁻¹ • R.U.π g = 1 := h g hg
      rw [← h1, smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  have h0 : R.ι v ≠ 0 := fun h => hv (R.ι_inj (h.trans (map_zero _).symm))
  have htop := (R.irred (Submodule.span ℂ {R.ι v}) (Submodule.closed_of_finiteDimensional _) fun g x hx => by
    obtain ⟨c, hc⟩ := hs g
    rw [hc]
    exact Submodule.smul_mem _ c hx).resolve_left (by simpa using h0)
  have hw : hwSub R.HK.act (blattner lam) = ⊤ := by simp [hwSub, wtSub]
  rw [hw, finrank_top, finrank_eq_one_iff_of_nonzero' v hv]
  intro w
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (htop.symm ▸ Submodule.mem_top : R.ι w ∈ Submodule.span ℂ {R.ι v})
  exact ⟨c, R.ι_inj (by rw [map_smul, hc])⟩

theorem rank_cases {P : ℕ → ℕ → Prop} (h0 : P 0 0) (h1 : ∀ p q, 1 ≤ p + q → P p q) (p q : ℕ) : P p q := by
  by_cases h : 1 ≤ p + q
  · exact h1 p q h
  · obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by omega
    exact h0

theorem exists_hasParam (H : DiscreteSeriesCover) (p q : ℕ) :
    ∀ (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam := by
  refine rank_cases (P := fun p q => ∀ (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam →
    ∃ R : DSRep T, HasParam R lam) ?_ ?_ p q
  · exact fun T lam _ => ⟨GlobalTheory.RealPar.Cover.trivZero T, GlobalTheory.SignedParTest.hasParam_zero _ _⟩
  · intro p q hn T lam hl
    obtain ⟨D, hD, -⟩ := H p q hn T
    exact ⟨D ⟨lam, hl⟩, (hD ⟨lam, hl⟩).hasParam hl⟩

theorem unitEquiv_of_hasParam (H : DiscreteSeriesCover) (hn : 1 ≤ p + q) {lam : Ix p q → ℚ} (hl : IsParam lam)
    {R R' : DSRep T} (h : HasParam R lam) (h' : HasParam R' lam) : UnitEquiv R R' := by
  obtain ⟨D, hD, hE⟩ := H p q hn T
  obtain ⟨l, e⟩ := hE R
  obtain ⟨l', e'⟩ := hE R'
  have h1 := ((hD l).of_equiv e).eq_of_hasParam hl l.2 h
  have h2 := ((hD l').of_equiv e').eq_of_hasParam hl l'.2 h'
  obtain rfl : l = l' := Subtype.ext (h1.symm.trans h2)
  exact e.trans e'.symm

theorem hasTypes_of_hasParam (H : DiscreteSeriesCover) (p q : ℕ) :
    ∀ (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∀ R : DSRep T, HasParam R lam → HasTypes R lam := by
  refine rank_cases (P := fun p q => ∀ (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam →
    ∀ R : DSRep T, HasParam R lam → HasTypes R lam) (fun T lam _ R _ => hasTypes_zero R lam) ?_ p q
  intro p q hn T lam hl R h
  obtain ⟨D, hD, hE⟩ := H p q hn T
  obtain ⟨l, e⟩ := hE R
  have h1 := (hD l).of_equiv e
  rwa [h1.eq_of_hasParam hl l.2 h]

theorem admissibleDiscreteSeries_of_hasParam (H : DiscreteSeriesCover) (X : ProvA)
    (h : ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → HasParam (X.ds p q lam) lam) : Formalism.MainNotions.SchurIrreducible.DiscreteSeriesBlattner X :=
  fun p q lam hl => hasTypes_of_hasParam H p q _ lam hl _ (h p q lam hl)

end GlobalTheory.CoverDS

end
