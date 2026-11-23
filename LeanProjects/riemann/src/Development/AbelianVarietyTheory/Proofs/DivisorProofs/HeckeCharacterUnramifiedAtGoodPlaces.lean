import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLogHomIsMultipleOfLogAbs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesAboveAndNontrivialAbs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullySplitPrimesDensityOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialOfDensityOneStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.CtTypGlob

open GlobalTheory.IdeleLogHom GlobalTheory.CtTyp GroundTheory.Global GroundTheory.Global.AdeleBaseChange

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finiteAdeleMap_eq (a : Af F) : finiteAdeleMap F E a = GlobalTheory.AdeleBaseChange.adMap F E a := by
  refine FiniteAdeleRing.ext _ fun w => ?_
  have hd := HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F) (w.under (𝓞 F))
  have h := hd.equalizer (SemiLocal.continuous_completionMap (below F w) w)
    (SplitChart.continuous_complMap (rfl : w.under (𝓞 F) = _)) (funext fun k => by
      refine (SemiLocal.completionMap_algebraMap (below F w) w k).trans ?_
      refine (IsScalarTower.algebraMap_apply F E (w.adicCompletion E) k).trans ?_
      exact (complMap_algebraMap (rfl : w.under (𝓞 F) = _) k).symm)
  exact congrFun h (a (w.under (𝓞 F)))

theorem equiv_extZero (y : Af F ⊗[F] E) :
    adeleTensorAlgEquivLeft F E (extZero F E y) = ((0 : InfiniteAdeleRing E), finAdEquiv F E y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | tmul a x =>
    refine (adeleTensorAlgEquivLeft_tmul (((0 : InfiniteAdeleRing F), a) : AF F) x).trans (Prod.ext ?_ ?_)
    · change algebraMap E (InfiniteAdeleRing E) x *
        GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (0 : InfiniteAdeleRing F) = 0
      rw [map_zero, mul_zero]
    · change algebraMap E (FiniteAdeleRing (𝓞 E) E) x * finiteAdeleMap F E a = toFinAd F E (a ⊗ₜ[F] x)
      rw [toFinAd_tmul, finiteAdeleMap_eq, mul_comm]
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb, map_add]
    exact Prod.ext (add_zero _) rfl

theorem toE_locIdele (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) :
    toE F E (locIdele F w x) = HeckeValGen.localIdele E w x := by
  refine Units.ext ?_
  change adeleTensorAlgEquivLeft F E (locIdele F w x : AF F ⊗[F] E) = _
  rw [coe_locIdele, map_add, map_sub, map_one, equiv_extZero, equiv_extZero, map_one, RingEquiv.apply_symm_apply]
  refine Prod.ext ?_ ?_
  · change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
    rw [sub_zero, add_zero]
  · change (1 : FiniteAdeleRing (𝓞 E) E) - 1 + Neutral.B1.finiteSingle E w x = HeckeValGen.finiteSingle E w x
    rw [sub_self, zero_add]
    rfl

theorem continuous_twAbs {c : Chr F E} (hc : Continuous c) (s : ℝ) :
    Continuous fun t => ((twAbs c s t : ℂˣ) : ℂ) := by
  simp only [coe_twAbs]
  refine (continuous_subtype_val.comp hc).mul (Complex.continuous_ofReal.comp ?_)
  exact (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE).rpow_const fun t => Or.inl (absE_pos t).ne'

theorem eq_one_of_density (ξ : (AE F E)ˣ →* ℂˣ) (hc : Continuous fun t => ((ξ t : ℂˣ) : ℂ))
    (hE : ∀ x : Eˣ, ξ (Units.map (inclR (F := F) (AF F)).toMonoidHom x) = 1) (hu : ∀ t, ‖((ξ t : ℂˣ) : ℂ)‖ = 1)
    {S : Set (HeightOneSpectrum (𝓞 E))} (hS : NumberField.Set.HasDirichletDensity S 1)
    (h : ∀ w ∈ S, ∀ x, ξ (locIdele F w x) = 1) : ξ = 1 := by
  have hc' : Continuous ξ := Units.continuous_iff.2 ⟨hc, by
    simp only [Units.val_inv_eq_inv_val]
    exact hc.inv₀ fun t => Units.ne_zero _⟩
  have key := GlobalTheory.T.trivial_of_density_one E (ξ.comp (ofE F E)) ⟨hc'.comp (continuous_ofE F E), fun k => by
      have : ofE F E (IdeleGroup.diagonal E k) = Units.map (inclR (F := F) (AF F)).toMonoidHom k := by
        rw [← toE_inclR F E, ofE_toE]
      exact (congrArg ξ this).trans (hE k)⟩ (fun y => hu _) S hS
    (fun w hw => GlobalTheory.IndefiniteRowSideFullHecke.TrivialOfDensityOneCharacters.valueOneAt_of_trivAt fun x => by
      have : ofE F E (HeckeValGen.localIdele E w x) = locIdele F w x := by
        rw [← toE_locIdele (F := F), ofE_toE]
      exact (congrArg ξ this).trans (h w hw x))
  refine MonoidHom.ext fun t => ?_
  have := DFunLike.congr_fun key (toE F E t)
  rw [← ofE_toE F E t]
  exact this

theorem eq_twAbs (χ : (AE F E)ˣ →* ℂˣ) (hc : Continuous fun t => ((χ t : ℂˣ) : ℂ))
    (hE : ∀ x : Eˣ, χ (Units.map (inclR (F := F) (AF F)).toMonoidHom x) = 1) {c : Chr F E} (hH : IsHecke F E c)
    {s : ℝ} (hs : ∀ t, Real.log ‖((χ t : ℂˣ) : ℂ)‖ = s * Real.log (absE F E t : ℝ))
    {S : Set (HeightOneSpectrum (𝓞 E))} (hS : NumberField.Set.HasDirichletDensity S 1)
    (h : ∀ w ∈ S, ∀ x, χ (locIdele F w x) = twAbs c s (locIdele F w x)) : χ = twAbs c s := by
  rw [← div_eq_one]
  refine eq_one_of_density _ ?_ (fun x => ?_) (fun t => ?_) hS fun w hw x => ?_
  · simp only [MonoidHom.div_apply, Units.val_div_eq_div_val]
    exact hc.div (continuous_twAbs hH.1 s) fun t => Units.ne_zero _
  · rw [MonoidHom.div_apply, hE, div_eq_one]
    refine Units.ext ?_
    rw [coe_twAbs, hH.2, GlobalTheory.Doubling.absE_inclR]
    simp
  · rw [MonoidHom.div_apply, Units.val_div_eq_div_val, norm_div, norm_twAbs, Real.rpow_def_of_pos (absE_pos t),
      mul_comm, ← hs, Real.exp_log (norm_pos_iff.2 (Units.ne_zero _)), div_self (norm_ne_zero_iff.2 (Units.ne_zero _))]
  · rw [MonoidHom.div_apply, h w hw x, div_self']

theorem exists_log_norm (χ : (AE F E)ˣ →* ℂˣ) (hc : Continuous fun t => ((χ t : ℂˣ) : ℂ))
    (hE : ∀ x : Eˣ, χ (Units.map (inclR (F := F) (AF F)).toMonoidHom x) = 1) :
    ∃ s : ℝ, ∀ t, Real.log ‖((χ t : ℂˣ) : ℂ)‖ = s * Real.log (absE F E t : ℝ) := by
  obtain ⟨A, hA⟩ := exists_eq_mul_log_absE F E (fun t => (Real.log ‖((χ t : ℂˣ) : ℂ)‖ : ℂ))
    (Complex.continuous_ofReal.comp (hc.norm.log fun t => norm_ne_zero_iff.2 (Units.ne_zero _)))
    (fun s t => by
      rw [map_mul, Units.val_mul, norm_mul,
        Real.log_mul (norm_ne_zero_iff.2 (Units.ne_zero _)) (norm_ne_zero_iff.2 (Units.ne_zero _)), Complex.ofReal_add])
    (fun γ => by rw [hE]; simp)
  refine ⟨A.re, fun t => ?_⟩
  have := congrArg Complex.re (hA t)
  rwa [Complex.ofReal_re, Complex.re_mul_ofReal] at this

theorem exp_eq {χ : (AE F E)ˣ →* ℂˣ} {s r : ℝ}
    (hs : ∀ t, Real.log ‖((χ t : ℂˣ) : ℂ)‖ = s * Real.log (absE F E t : ℝ)) {c : Chr F E}
    {w : HeightOneSpectrum (𝓞 E)} (h : ∀ x, χ (locIdele F w x) = twAbs c r (locIdele F w x)) : s = r := by
  obtain ⟨x, hx⟩ := GlobalTheory.PlaceAbove.exists_absE_locIdele_ne_one (F := F) w
  have h1 := hs (locIdele F w x)
  rw [h x, norm_twAbs, Real.log_rpow (absE_pos _)] at h1
  exact (mul_right_cancel₀ (fun h0 => hx (log_absE_eq_zero.1 h0)) h1).symm

theorem eq_or_eq : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ χ : (AE F E)ˣ →* ℂˣ, Continuous (fun t => ((χ t : ℂˣ) : ℂ)) →
    (∀ x : Eˣ, χ (Units.map (inclR (F := F) (AF F)).toMonoidHom x) = 1) →
    (∀ v, X.Good v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
      (∀ x, χ (locIdele F w x) = GlobalTheory.CtTyp.twAbs X.α ((a' : ℝ) / 2) (locIdele F w x)) ∨
        ∀ x, χ (locIdele F w x) = GlobalTheory.CtTyp.twAbs X.β ((a : ℝ) / 2) (locIdele F w x)) →
    χ = GlobalTheory.CtTyp.twAbs X.α ((a' : ℝ) / 2) ∨ χ = GlobalTheory.CtTyp.twAbs X.β ((a : ℝ) / 2) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT χ hc hE h
  obtain ⟨s, hs⟩ := exists_log_norm χ hc hE
  have hS := GlobalTheory.T.fully_split_primes_density_one F E hT.base.galois X.T
  have hlt : (a' : ℝ) < a := by exact_mod_cast hT.geo.lt
  by_cases h1 : s = (a' : ℝ) / 2
  · subst h1
    refine Or.inl (eq_twAbs χ hc hE hT.chars.heckeα hs hS fun w hw => (h _ hw w rfl).resolve_right fun h2 => ?_)
    have := exp_eq hs h2
    linarith
  · have h2 : ∀ v, X.Good v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
        ∀ x, χ (locIdele F w x) = twAbs X.β ((a : ℝ) / 2) (locIdele F w x) :=
      fun v hv w hw => (h v hv w hw).resolve_left fun h3 => h1 (exp_eq hs h3)
    obtain ⟨w₁, hw₁⟩ := GlobalTheory.PlaceAbove.exists_under_eq' (E := E) B.v₁
    obtain rfl := exp_eq hs (h2 _ hT.chars.good w₁ hw₁)
    exact Or.inr (eq_twAbs χ hc hE hT.chars.heckeβ hs hS fun w hw => h2 _ hw w rfl)

end GlobalTheory.CtTypGlob
