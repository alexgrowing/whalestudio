import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpIffHasInfQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Formalism.LocalToGlobal.UnitaryNorms.CharProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharLocPowEqOneOnLocalUnitsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationEmbeddingGeneratorEqOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationSqrtAbsNormEqOneStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.UnitOverP

theorem val_eq_one_of_pow (A : ValuationSubring ℂ) {z : ℂ} {m : ℕ} (hm : m ≠ 0) (h : A.valuation (z ^ m) = 1) :
    A.valuation z = 1 := by
  rw [map_pow] at h
  exact ((pow_eq_one_iff).1 h).resolve_right hm

theorem exists_gen {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    ∃ h : ℕ, 0 < h ∧ ∃ α : 𝓞 K, Ideal.span {α} = P.asIdeal ^ h := by
  have hP : P.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero P.ne_bot
  set h := Fintype.card (ClassGroup (𝓞 K))
  have hPh : P.asIdeal ^ h ∈ nonZeroDivisors (Ideal (𝓞 K)) := pow_mem hP h
  have h1 : ClassGroup.mk0 ⟨P.asIdeal ^ h, hPh⟩ = 1 := by
    have e : (⟨P.asIdeal ^ h, hPh⟩ : nonZeroDivisors (Ideal (𝓞 K))) = ⟨P.asIdeal, hP⟩ ^ h := Subtype.ext (by simp)
    rw [e, map_pow, pow_card_eq_one]
  haveI := (ClassGroup.mk0_eq_one_iff hPh).1 h1
  exact ⟨h, Fintype.card_pos, _, Ideal.span_singleton_generator _⟩

end GlobalTheory.UnitOverP

namespace GlobalTheory.UnitOverP

open Formalism.L2.Host in

theorem val_mul_sqrt_unit : ∀ (D : D7) (V W : HSp D) (B : Base V W), B.Good → ∀ χ : Formalism.L2.Host.HChar D.host.E, ChrEq (B.mu * B.eta⁻¹) χ → ∀ (p : ℕ) (A : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ A.nonunits → ∀ bad : ℕ, p ∣ bad → (∀ PP, PP ∈ B.G.Pg ∨ PP ∈ B.de.Q → (bad : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ P : HeightOneSpectrum (𝓞 D.host.E), (bad : 𝓞 D.host.E) ∉ P.asIdeal → ((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ) ∈ A ∧ (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ A := by
  intro D V W B hB χ hχ p A hp hpA bad hpb hbad P hP
  classical
  have hpP : ((p : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro h
    apply hP
    obtain ⟨r, rfl⟩ := hpb
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h
  have hinf : ∀ τ, HasInfExp D (B.mu * B.eta⁻¹) τ
      (((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2) + -(1 / 2)) := fun τ =>
    GlobalTheory.Chain.StepVac.hasInfExp_mul (GlobalTheory.RealFockAction.hasInfExp_mul_of_isOpen_ker (hB.inf τ) hB.de.isOpen)
      (GlobalTheory.Chain.StepVac.hasInfExp_inv (hB.eta.2.2.2 τ))
  obtain ⟨n, -, hχinf⟩ := GlobalTheory.HeckeInfExp.hasInfQ_of_hasInfExp D _ χ _ hχ hinf
  obtain ⟨h, hh, α, hα⟩ := exists_gen P
  have hα0 : (α : D.host.E) ≠ 0 := by
    intro h0
    have h1 : α = 0 := by exact_mod_cast h0
    rw [h1, Ideal.span_singleton_eq_bot.2 rfl] at hα
    exact (pow_ne_zero h P.ne_bot) hα.symm
  set k : D.host.Eˣ := Units.mk0 _ hα0 with hk
  have hmem : ∀ v : HeightOneSpectrum (𝓞 D.host.E), α ∈ v.asIdeal ↔ v = P := by
    intro v
    constructor
    · intro hv
      have h1 : P.asIdeal ^ h ≤ v.asIdeal := by
        rw [← hα, Ideal.span_le, Set.singleton_subset_iff]; exact hv
      have h2 : P.asIdeal ≤ v.asIdeal := v.isPrime.le_of_pow_le h1
      exact HeightOneSpectrum.ext ((P.isMaximal.eq_of_le v.isPrime.ne_top h2).symm)
    · rintro rfl
      have h1 : α ∈ Ideal.span {α} := Ideal.subset_span rfl
      rw [hα] at h1
      exact Ideal.pow_le_self hh.ne' h1
  have hval : ∀ v : HeightOneSpectrum (𝓞 D.host.E), v.valuation D.host.E (k : D.host.E) = v.intValuation α := fun v =>
    HeightOneSpectrum.valuation_of_algebraMap v α
  have hv1 : ∀ v, v ≠ P → v.valuation D.host.E (k : D.host.E) = 1 := fun v hv => by
    rw [hval]
    exact le_antisymm (v.intValuation_le_one α)
      (not_lt.1 fun h' => hv ((hmem v).1 ((v.intValuation_lt_one_iff_mem α).1 h')))
  have hord : ∀ v, v ≠ P → ordF v k = 0 := fun v hv => by
    unfold ordF; rw [hv1 v hv]; simp
  have hatFin : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (x : D.host.Eˣ),
      Valued.v ((atFin v x : (v.adicCompletion D.host.E)ˣ) : v.adicCompletion D.host.E) = v.valuation D.host.E (x : D.host.E) :=
    fun v x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : D.host.E)
  set N := ordF P k with hNdef
  have hPv : P.valuation D.host.E (k : D.host.E) = WithZero.exp (-N) := by
    have h0 : P.valuation D.host.E (k : D.host.E) ≠ 0 := by simp
    rw [hNdef, ordF, neg_neg]
    exact (WithZero.exp_log h0).symm
  have hN : 0 < N := by
    have h1 : P.valuation D.host.E (k : D.host.E) < 1 := by
      rw [hval]; exact (P.intValuation_lt_one_iff_mem α).2 ((hmem P).2 rfl)
    rw [hPv, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    omega

  have hfin := GlobalTheory.Mem.UnrAe.finite_ramified χ
  set S := insert P hfin.toFinset with hSdef
  have hS : ∀ v, v ∉ S → χ.UnrAt v := fun v hv => by
    by_contra h'
    exact hv (Finset.mem_insert_of_mem (hfin.mem_toFinset.2 h'))
  have hpr := χ.productRule S hS k
  have hfp : (∏ᶠ (v : HeightOneSpectrum (𝓞 D.host.E)) (_ : v ∉ S), χ.val v ^ ordF v k) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by
      rw [finprod_eq_if]
      split_ifs with hv
      · rfl
      · rw [hord v (fun e => hv (e ▸ Finset.mem_insert_self _ _)), zpow_zero]
  rw [hfp, mul_one, ← Finset.mul_prod_erase S _ (Finset.mem_insert_self P _)] at hpr
  set u : D.host.Eˣ := k * (unif P ^ N)⁻¹ with hudef
  have hku : k = u * unif P ^ N := by rw [hudef, inv_mul_cancel_right]
  have hlocP : χ.locK P k = χ.locK P u * χ.val P ^ N := by
    rw [hku, map_mul, map_zpow]; rfl
  have hu : IsUnitAt P (atFin P u) := by
    have h1 := unif_spec P
    unfold IsUnifAt at h1
    unfold IsUnitAt
    rw [hudef, map_mul, map_inv, map_zpow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
      map_inv₀, map_zpow₀, h1, hatFin, hPv, ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  have hroot : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (x : D.host.Eˣ), IsUnitAt v (atFin v x) →
      A.valuation ((χ.locK v x : ℂˣ) : ℂ) = 1 := by
    intro v x hx
    obtain ⟨m, hm, hxm⟩ := GlobalTheory.T.heckeChar_loc_pow_eq_one_on_localUnits _ χ v _ hx
    apply val_eq_one_of_pow A hm.ne'
    rw [← Units.val_pow_eq_pow_val, show χ.locK v x = χ.loc v (atFin v x) from rfl, hxm, Units.val_one, map_one]
  have hw : ∀ τ, A.valuation (tauE D τ (k : D.host.E) / ((‖tauE D τ (k : D.host.E)‖ : ℝ) : ℂ)) = 1 := by
    intro τ
    apply val_eq_one_of_pow A two_ne_zero
    have hz : tauE D τ (k : D.host.E) ≠ 0 := (map_ne_zero _).2 k.ne_zero
    have hz' : starRingEnd ℂ (tauE D τ (k : D.host.E)) ≠ 0 := (map_ne_zero _).2 hz
    have hn : ((‖tauE D τ (k : D.host.E)‖ : ℝ) : ℂ) ^ 2 = tauE D τ (k : D.host.E) * starRingEnd ℂ (tauE D τ (k : D.host.E)) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    have e : (tauE D τ (k : D.host.E) / ((‖tauE D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ 2 =
        tauE D τ (k : D.host.E) / starRingEnd ℂ (tauE D τ (k : D.host.E)) := by
      rw [div_pow, hn]; field_simp
    have h1 : A.valuation (tauE D τ (k : D.host.E)) = 1 := GlobalTheory.T.valuation_embedding_generator_eq_one' _ A p hp hpA P hpP α h hα (tauE D τ)
    have h2 : A.valuation (starRingEnd ℂ (tauE D τ (k : D.host.E))) = 1 :=
      GlobalTheory.T.valuation_embedding_generator_eq_one' _ A p hp hpA P hpP α h hα ((starRingEnd ℂ).comp (tauE D τ))
    rw [e, map_div₀, h1, h2, div_one]
  have hinfv : A.valuation ((χ.inf k : ℂˣ) : ℂ) = 1 := by
    rw [hχinf k, map_prod]
    exact Finset.prod_eq_one fun τ _ => by rw [map_zpow₀, hw τ, _root_.one_zpow]
  have hrest : A.valuation ((∏ v ∈ S.erase P, χ.locK v k : ℂˣ) : ℂ) = 1 := by
    rw [Units.coe_prod, map_prod]
    refine Finset.prod_eq_one fun v hv => hroot v k ?_
    unfold IsUnitAt
    rw [hatFin]
    exact hv1 v (Finset.ne_of_mem_erase hv)
  have key := congrArg (fun x : ℂˣ => A.valuation (x : ℂ)) hpr
  simp only [hlocP, Units.val_mul, map_mul, Units.val_one, map_one, Units.val_zpow_eq_zpow_val, map_zpow₀, hinfv, hrest,
    hroot P u hu, one_mul, mul_one] at key
  have hvalP : A.valuation ((χ.val P : ℂˣ) : ℂ) = 1 := by
    obtain ⟨M, hM⟩ := Int.eq_ofNat_of_zero_le hN.le
    rw [hM, zpow_natCast] at key
    refine val_eq_one_of_pow A (m := M) (by have h3 := hN; rw [hM] at h3; omega) ?_
    rw [map_pow]; exact key
  have hfinal : A.valuation (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ)) = 1 := by
    rw [map_mul, hvalP, GlobalTheory.T.valuation_sqrt_absNorm_eq_one' _ A p hp hpA P hpP, one_mul]
  exact ⟨(A.valuation_le_one_iff _).1 hfinal.le, (A.valuation_le_one_iff _).1 (by rw [map_inv₀, hfinal, inv_one])⟩

end GlobalTheory.UnitOverP
