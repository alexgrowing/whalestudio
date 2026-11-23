import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipMatch

open GlobalTheory.LFun GlobalTheory.LFun.SplitTie

section Place

variable {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem complMap_apply_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl F} {w : Pl E} (h : w.under (𝓞 F) = v) (b : Af F) :
    complMap h (b v) = GlobalTheory.AdeleBaseChange.locMap F w (b (w.under (𝓞 F))) := by
  subst h; rfl

theorem piW_tmul (b : AF D.host.F) (x : D.host.E) : piW τ (b ⊗ₜ[D.host.F] x) = evFin D.host.F v b * τ x := by
  show splitProj τ (compFin D.host.F D.host.E v (b ⊗ₜ[D.host.F] x)) = _
  rw [compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
  rfl

theorem cpt_tmul (w : Pl D.host.E) (b : AF D.host.F) (x : D.host.E) :
    cpt (D := D) w (toEAf D (b ⊗ₜ[D.host.F] x)) =
      algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.locMap D.host.F w (b.2 (w.under (𝓞 D.host.F))) := by
  have e : toEAf D (b ⊗ₜ[D.host.F] x) = x ⊗ₜ[D.host.F] b.2 := rfl
  rw [e]
  show (toAd D (x ⊗ₜ[D.host.F] b.2)) w = _
  rw [toAd_spec]
  rfl

theorem isPlaceIso_complEquiv : IsPlaceIso τ (splitPrime τ) (complEquiv τ (splitPrime_under τ)) := by
  intro a
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul b x =>
    rw [piW_tmul, cpt_tmul, complEquiv_apply, map_mul, complMap_apply_emb, mul_comm]
    congr 1
    exact complMap_apply_under (splitPrime_under τ) b.2
  | add x y hx hy =>
    rw [RingHom.map_add (piW τ), RingEquiv.map_add, RingHom.map_add (toEAf D), RingHom.map_add (cpt _), hx, hy]

theorem isEquiv_Fv {F : Type} [Field F] [NumberField F] (v : Pl F) :
    (ValuativeRel.valuation (Fv F v)).IsEquiv (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))) :=
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  ValuativeRel.isEquiv _ _

theorem valued_complEquiv_symm (y : Kw (D := D) (splitPrime τ)) :
    Valued.v ((complEquiv τ (splitPrime_under τ)).symm y) = Valued.v y := by
  conv_rhs => rw [← (complEquiv τ (splitPrime_under τ)).apply_symm_apply y]
  rw [complEquiv_apply, SplitTie.valued_complMap]

theorem continuous_complEquiv_symm : Continuous (complEquiv τ (splitPrime_under τ)).symm := by
  refine continuous_of_continuousAt_zero (complEquiv τ (splitPrime_under τ)).symm ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have h0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨k, hk⟩ : ∃ k : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = WithZero.exp k :=
    ⟨_, (WithZero.exp_log h0).symm⟩
  filter_upwards [(GlobalTheory.Idele.isOpen_valued_le (K := D.host.E) (splitPrime τ) (-((k.natAbs + 1 : ℕ) : ℤ))).mem_nhds
    (by simp)] with a ha
  rw [Valuation.restrict_lt_iff_lt_embedding, hk, valued_complEquiv_symm]
  exact ha.trans_lt (WithZero.exp_lt_exp.2 (by omega))

theorem isLocIso_complEquiv : IsLocIso (complEquiv τ (splitPrime_under τ)) := by
  refine ⟨SplitChart.continuous_complMap _, continuous_complEquiv_symm τ, fun x => ?_⟩
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, (Good.isEquiv_Kw (D := D) _).le_one_iff_le_one,
    (isEquiv_Fv v).le_one_iff_le_one, complEquiv_apply, SplitTie.valued_complMap]

end Place

section Chars

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem chrW_nu {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) (X : Chars D.host.F D.host.E)
    (hα : X.α = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (hβ : X.β = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j)
    {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : (Fv D.host.F v)ˣ) :
    chrW X.ν τ x = (locGrid G t (splitPrime τ)).nu i j
      (Units.map ((complEquiv τ (splitPrime_under τ) : Fv D.host.F v →* Kw (splitPrime τ))) x) := by
  have e1 : X.ν = G.nu t i (j + 1) := by
    show X.α / X.β = _
    rw [hα, hβ]
    exact mul_div_mul_right_eq_div _ _ _
  have e2 : chrW X.ν τ x = locChar X.ν (splitPrime τ)
      (Units.map ((complEquiv τ (splitPrime_under τ) : Fv D.host.F v →* Kw (splitPrime τ))) x) := rfl
  rw [e2, e1, locChar_eq_of_chrEq (SqNum.chrEq_nu G t i j hL)]
  have hj : (j : ℕ) < D.R.m := j.2
  simp only [SqNum.nuH, Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Formalism.L2.Host.HChar.loc_mul,
    Formalism.L2.Host.HChar.loc_inv, div_eq_mul_inv]
  rfl

end Chars

section Psi

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem at_atPl {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (y : Kw (D := D) (splitPrime τ)) :
    At (evFin D.host.F v) (atPl (splitPrime τ) y) := by
  classical
  intro u hu
  refine ae_ext ?_ fun Q => ?_
  · rw [Algebra.smul_def, RingHom.map_mul, (atPl_spec _ y).1, mul_zero, map_zero]
  · rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, (atPl_spec _ y).2, map_zero, map_zero]
    by_cases h : Q = splitPrime τ
    · subst h
      have h1 : cpt (D := D) (splitPrime τ) (toEAf D (algebraMap (AF D.host.F) (AE D) u)) =
          GlobalTheory.AdeleBaseChange.locMap D.host.F (splitPrime τ) (u.2 ((splitPrime τ).under (𝓞 D.host.F))) :=
        (comp_toAd D).base u (splitPrime τ)
      rw [h1, ← complMap_apply_under (splitPrime_under τ)]
      have h2 : u.2 v = 0 := hu
      rw [h2, map_zero, zero_mul]
    · rw [Pi.single_eq_of_ne h, mul_zero]

theorem psiLoc_eq_psiAt (W : G.Weil) {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : Fv D.host.F v) :
    psiLoc W.ψ v x = psiAt W (splitPrime τ) ((xiAt (splitPrime τ))⁻¹ * complEquiv τ (splitPrime_under τ) x) := by
  classical
  set w := splitPrime τ with hw
  set jj := complEquiv τ (splitPrime_under τ) with hjj
  have hξ : xiAt (D := D) w ≠ 0 := (map_ne_zero _).2 cmHost_imaginaryGenerator_ne_zero
  have hz : incA D D.host.xi0 * atPl w ((xiAt w)⁻¹ * jj x) = atPl w (jj x) := by
    rw [← Good.atPl_mul]
    congr 1
    rw [← mul_assoc]
    change xiAt w * (xiAt w)⁻¹ * jj x = jj x
    rw [mul_inv_cancel₀ hξ, one_mul]
  have hcm := isCMExt_host D
  have hp1 : piW τ (atPl w (jj x)) = x :=
    jj.injective (by rw [isPlaceIso_complEquiv τ, (atPl_spec w _).2, Pi.single_eq_same])
  have hp2 : piW (τ.comp D.sp.cm.sig) (atPl w (jj x)) = 0 :=
    (complEquiv (τ.comp D.sp.cm.sig) (splitPrime_under _)).injective (by
      rw [isPlaceIso_complEquiv (τ.comp D.sp.cm.sig), (atPl_spec w _).2, Pi.single_eq_of_ne (splitPrime_comp_ne hcm τ),
        map_zero])
  show psiLoc W.ψ v x = W.ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * atPl w ((xiAt w)⁻¹ * jj x)))
  rw [hz, GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v τ _ (at_atPl τ _), hp1, hp2, add_zero]
  rfl

end Psi

theorem exists_placeIso_chars : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (t : T) (i j : Fin D.R.m) (X : Chars D.host.F D.host.E), X.α = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j → X.β = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j →
    ∀ {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E), splitPrime τ = w →
    ∃ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso τ w jj ∧ IsLocIso jj ∧
      (∀ x, chrW X.ν τ x = (locGrid G t w).nu i j (Units.map (jj : Fv D.host.F v →* Kw w) x)) ∧
      ∀ x, psiLoc W.ψ v x = psiAt W w ((xiAt w)⁻¹ * jj x) := by
  intro D T L sc G μ₀ hL W t i j X hα hβ v τ w hw
  subst hw
  exact ⟨complEquiv τ (splitPrime_under τ), isPlaceIso_complEquiv τ, isLocIso_complEquiv τ,
    fun x => chrW_nu hL t i j X hα hβ τ x, fun x => psiLoc_eq_psiAt W τ x⟩

end GlobalTheory.FlipMatch
