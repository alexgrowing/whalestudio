import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDomainWeightBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPointsDeepLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwSecOfConst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VAddGeOfMemProdZpow
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatShort

open NumberField IsDedekindDomain Module NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

theorem prod_places_eq (r : (K →+* ℂ) → ℝ) (hr : ∀ σ, r (ComplexEmbedding.conjugate σ) = r σ) :
    ∏ w : InfinitePlace K, r w.embedding ^ w.mult = ∏ σ : K →+* ℂ, r σ := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ (fun σ : K →+* ℂ => InfinitePlace.mk σ) r]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h : ∀ σ ∈ (Finset.univ.filter fun σ : K →+* ℂ => InfinitePlace.mk σ = w), r σ = r w.embedding := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    rw [← hσ.2]
    rcases InfinitePlace.embedding_mk_eq σ with h | h <;> rw [h]
    exact (hr σ).symm
  rw [Finset.prod_congr rfl h, Finset.prod_const, InfinitePlace.card_filter_mk_eq]

theorem apply_embedding_mk (r : (K →+* ℂ) → ℝ) (hr : ∀ σ, r (ComplexEmbedding.conjugate σ) = r σ)
    (σ : K →+* ℂ) : r (InfinitePlace.mk σ).embedding = r σ := by
  rcases InfinitePlace.embedding_mk_eq σ with h | h <;> rw [h]
  exact hr σ

end GlobalTheory.FlatShort

namespace GlobalTheory.FlatShort

open NumberField IsDedekindDomain Module NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

def idealOf (N : ℕ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.spanSingleton _ (N : K) * ∏ w ∈ S, (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ ⌊-ρ w⌋

theorem idealOf_ne_zero {N : ℕ} (hN : N ≠ 0) (ρ : HeightOneSpectrum (𝓞 K) → ℝ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    idealOf N ρ S ≠ 0 :=
  mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 (Nat.cast_ne_zero.2 hN))
    (Finset.prod_ne_zero_iff.2 fun w _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot))

theorem count_idealOf {N : ℕ} (hN : N ≠ 0) (ρ : HeightOneSpectrum (𝓞 K) → ℝ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ w, w ∉ S → ρ w = 0) (w : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K w (idealOf N ρ S) = vAdd w (N : K) + ⌊-ρ w⌋ := by
  classical
  rw [idealOf, FractionalIdeal.count_mul K w (FractionalIdeal.spanSingleton_ne_zero_iff.2 (Nat.cast_ne_zero.2 hN))
    (Finset.prod_ne_zero_iff.2 fun w _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot)),
    FractionalIdeal.count_prod K w S _ (fun w _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot))]
  congr 1
  · exact (GlobalTheory.Core.Int.ProdPrimePow.vAdd_eq_count w (Nat.cast_ne_zero.2 hN)).symm
  rw [Finset.sum_congr rfl fun w' _ => by rw [FractionalIdeal.count_zpow, FractionalIdeal.count_maximal]]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [hS w h, neg_zero, Int.floor_zero]

theorem le_vAdd_of_mem {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) (ρ : HeightOneSpectrum (𝓞 K) → ℝ)
    (hI : GlobalTheory.FlatTw.IntOff B ρ) (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ w, w ∉ S → ρ w = 0) {a : K}
    (ha : a ∈ idealOf (∏ p ∈ B, p) ρ S) (ha0 : a ≠ 0) (w : HeightOneSpectrum (𝓞 K)) :
    0 ≤ (vAdd w a : ℝ) + ρ w := by
  have hN : (∏ p ∈ B, p) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (hB p hp).ne_zero
  have h1 : FractionalIdeal.count K w (idealOf (∏ p ∈ B, p) ρ S) ≤ vAdd w a := by
    rw [GlobalTheory.Core.Int.ProdPrimePow.vAdd_eq_count w ha0]; exact FractionalIdeal.count_mono K w (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha0)
      (FractionalIdeal.spanSingleton_le_iff_mem.2 ha)
  rw [count_idealOf hN ρ S hS] at h1
  have hNK : ((∏ p ∈ B, p : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hsp : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((∏ p ∈ B, p : ℕ) : K) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.2 hNK
  have h0 : 0 ≤ vAdd w ((∏ p ∈ B, p : ℕ) : K) := by
    have := FractionalIdeal.count_mono K w hsp (J := 1)
      (FractionalIdeal.spanSingleton_le_iff_mem.2 ((FractionalIdeal.mem_one_iff _).2 ⟨((∏ p ∈ B, p : ℕ) : 𝓞 K), by simp⟩))
    rwa [FractionalIdeal.count_one, ← GlobalTheory.Core.Int.ProdPrimePow.vAdd_eq_count w hNK] at this
  by_cases h : ∀ p ∈ B, ((p : ℕ) : 𝓞 K) ∉ w.asIdeal
  · obtain ⟨m, hm⟩ := hI w h
    rw [hm, ← Int.cast_neg, Int.floor_intCast] at h1
    rw [hm]
    have : (-m : ℤ) ≤ vAdd w a := by linarith
    have : ((-m : ℤ) : ℝ) ≤ (vAdd w a : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  · push_neg at h
    obtain ⟨p, hp, hpw⟩ := h
    have hmem : ((∏ p ∈ B, p : ℕ) : 𝓞 K) ∈ w.asIdeal :=
      Ideal.mem_of_dvd _ (Nat.cast_dvd_cast (Finset.dvd_prod_of_mem _ hp)) hpw
    have h2 : 1 ≤ vAdd w ((∏ p ∈ B, p : ℕ) : K) := by
      have := FractionalIdeal.count_mono K w hsp (J := (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K))
        (FractionalIdeal.spanSingleton_le_iff_mem.2 ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hmem, by simp⟩))
      rwa [FractionalIdeal.count_self, ← GlobalTheory.Core.Int.ProdPrimePow.vAdd_eq_count w hNK] at this
    have h3 := Int.lt_floor_add_one (-ρ w)
    have h4 : ((vAdd w ((∏ p ∈ B, p : ℕ) : K) + ⌊-ρ w⌋ : ℤ) : ℝ) ≤ (vAdd w a : ℝ) := by exact_mod_cast h1
    have h5 : ((1 : ℤ) : ℝ) ≤ (vAdd w ((∏ p ∈ B, p : ℕ) : K) : ℝ) := by exact_mod_cast h2
    push_cast at h4 h5
    linarith

end GlobalTheory.FlatShort

namespace GlobalTheory.FlatShort

open NumberField IsDedekindDomain Module NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

theorem absNorm_idealOf (N : ℕ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ((FractionalIdeal.absNorm (idealOf N ρ S) : ℚ) : ℝ) =
      (N : ℝ) ^ finrank ℚ K * ∏ w ∈ S, ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ⌊-ρ w⌋ := by
  rw [idealOf, map_mul, FractionalIdeal.absNorm_span_singleton (𝓞 K), map_prod,
    show (N : K) = algebraMap ℚ K (N : ℚ) from (map_natCast _ N).symm, Algebra.norm_algebraMap]
  simp only [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
  push_cast
  rw [abs_of_nonneg (by positivity)]

theorem absNorm_idealOf_pos {N : ℕ} (hN : N ≠ 0) (ρ : HeightOneSpectrum (𝓞 K) → ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : 0 < ((FractionalIdeal.absNorm (idealOf N ρ S) : ℚ) : ℝ) := by
  rw [absNorm_idealOf]
  refine mul_pos (pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)) _) (Finset.prod_pos fun w _ => zpow_pos ?_ _)
  exact Nat.cast_pos.2 (Nat.pos_of_ne_zero (by
    have := one_lt_absNorm_real w
    intro h; rw [h] at this; norm_num at this))

theorem log_absNorm_idealOf_le {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) (ρ : HeightOneSpectrum (𝓞 K) → ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ w, w ∉ S → ρ w = 0) :
    Real.log ((FractionalIdeal.absNorm (idealOf (∏ p ∈ B, p) ρ S) : ℚ) : ℝ) ≤
      (finrank ℚ K : ℝ) * (GlobalTheory.FlatTw.logSum B - ∑ᶠ w, ρ w * lw K w) := by
  have hNw : ∀ w : HeightOneSpectrum (𝓞 K), (0 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := fun w => by
    have := one_lt_absNorm_real w; linarith
  have hn : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.2 finrank_pos
  have hN : (0 : ℝ) < ((∏ p ∈ B, p : ℕ) : ℝ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2 fun p hp => (hB p hp).ne_zero))
  rw [absNorm_idealOf, Real.log_mul (pow_pos hN _).ne' (Finset.prod_pos fun w _ => zpow_pos (hNw w) _).ne',
    Real.log_pow, Real.log_prod (fun w _ => (zpow_pos (hNw w) _).ne')]
  have hlog : Real.log ((∏ p ∈ B, p : ℕ) : ℝ) = GlobalTheory.FlatTw.logSum B := by
    rw [Nat.cast_prod, Real.log_prod (fun p hp => Nat.cast_ne_zero.2 (hB p hp).ne_zero), GlobalTheory.FlatTw.logSum]
  have hfin : ∑ᶠ w, ρ w * lw K w = ∑ w ∈ S, ρ w * lw K w := by
    refine finsum_eq_sum_of_support_subset _ fun w hw => ?_
    by_contra h
    exact hw (by simp [hS w h])
  rw [hlog, hfin, mul_sub, Finset.mul_sum]
  have key : ∀ w ∈ S, Real.log (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ⌊-ρ w⌋) ≤
      -((finrank ℚ K : ℝ) * (ρ w * lw K w)) := by
    intro w _
    rw [Real.log_zpow, lw]
    have h0 : 0 ≤ Real.log ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := Real.log_nonneg (by
      have := one_lt_absNorm_real w; linarith)
    have h1 : ((⌊-ρ w⌋ : ℤ) : ℝ) ≤ -ρ w := Int.floor_le _
    have e : (finrank ℚ K : ℝ) * (ρ w * (Real.log ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) / (finrank ℚ K : ℝ))) =
        ρ w * Real.log ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by field_simp
    rw [e]
    nlinarith
  have := Finset.sum_le_sum key
  rw [Finset.sum_neg_distrib] at this
  linarith

end GlobalTheory.FlatShort

namespace GlobalTheory.FlatShort

open NumberField IsDedekindDomain Module NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory ENNReal
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

theorem exists_short_elt (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) (r : (K →+* ℂ) → ℝ) (hr : ∀ σ, 0 < r σ)
    (hc : ∀ σ, r (ComplexEmbedding.conjugate σ) = r σ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ)
    (hρ : (Function.support ρ).Finite) (hI : GlobalTheory.FlatTw.IntOff B ρ) :
    ∃ a : K, a ≠ 0 ∧ (∀ w, 0 ≤ (vAdd w a : ℝ) + ρ w) ∧ ∀ σ : K →+* ℂ,
      Real.log (r σ * ‖σ a‖) ≤ -GlobalTheory.FlatLine.lineDeg r ρ +
        Real.log |(discr K : ℝ)| / (2 * (finrank ℚ K : ℝ)) + GlobalTheory.FlatTw.logSum B + 1 := by
  classical
  set S := hρ.toFinset with hSdef
  have hS : ∀ w, w ∉ S → ρ w = 0 := fun w h => by
    rw [hSdef, Set.Finite.mem_toFinset, Function.mem_support, not_not] at h; exact h
  set n := finrank ℚ K with hn_def
  have hn : 0 < n := finrank_pos
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hN : (∏ p ∈ B, p) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (hB p hp).ne_zero
  set J1 := idealOf (K := K) (∏ p ∈ B, p) ρ S with hJ1def
  have hJ1 : J1 ≠ 0 := idealOf_ne_zero hN ρ S
  set A : ℝ := ((FractionalIdeal.absNorm J1 : ℚ) : ℝ) with hAdef
  have hA : 0 < A := absNorm_idealOf_pos hN ρ S
  have hD : 0 < Real.sqrt |(discr K : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K)))
  set P : ℝ := ∏ σ, r σ with hPdef
  have hP : 0 < P := Finset.prod_pos fun σ _ => hr σ
  set X : ℝ := A * Real.sqrt |(discr K : ℝ)| * P with hX_def
  have hX : 0 < X := mul_pos (mul_pos hA hD) hP
  set R : ℝ := 5 / 2 * X ^ ((n : ℝ)⁻¹) with hR_def
  have hR : 0 < R := by positivity
  have hRn : R ^ n = (5 / 2) ^ n * X := by
    rw [hR_def, mul_pow, ← Real.rpow_natCast (X ^ ((n : ℝ)⁻¹)), ← Real.rpow_mul hX.le,
      inv_mul_cancel₀ hn'.ne', Real.rpow_one]
  let J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 J1 hJ1
  let f : InfinitePlace K → NNReal := fun w => ⟨R / r w.embedding, (div_pos hR (hr _)).le⟩
  have hL : (minkowskiBound K J).toReal =
      A * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| * 2 ^ n := by
    simp_rw [minkowskiBound, volume_fundamentalDomain_fractionalIdealLatticeBasis,
      volume_fundamentalDomain_latticeBasis, toReal_mul, toReal_pow, toReal_inv, coe_toReal, toReal_ofNat,
      mixedEmbedding.finrank]
    rw [ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _))]
    simp only [J, Units.val_mk0, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs, hAdef]
    ring
  have hV : volume (convexBodyLT K f) ≠ ⊤ := by
    rw [convexBodyLT_volume]; exact mul_ne_top coe_ne_top coe_ne_top
  have hR' : (volume (convexBodyLT K f)).toReal = (convexBodyLTFactor K : ℝ) * (R ^ n / P) := by
    rw [convexBodyLT_volume, toReal_mul, coe_toReal, coe_toReal]
    congr 1
    rw [NNReal.coe_prod]
    have e : ∀ w : InfinitePlace K, ((f w ^ w.mult : NNReal) : ℝ) = R ^ w.mult / r w.embedding ^ w.mult :=
      fun w => by rw [NNReal.coe_pow, ← div_pow]; rfl
    rw [Finset.prod_congr rfl fun w _ => e w, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, sum_mult_eq,
      prod_places_eq r hc]
  have h : minkowskiBound K J < volume (convexBodyLT K f) := by
    rw [← ENNReal.toReal_lt_toReal (minkowskiBound_lt_top K J).ne hV, hL, hR', hRn]
    have h1 : (1 : ℝ) ≤ convexBodyLTFactor K := by exact_mod_cast one_le_convexBodyLTFactor K
    have h2 : (2 : ℝ)⁻¹ ^ nrComplexPlaces K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h3 : (2 : ℝ) ^ n < (5 / 2) ^ n := pow_lt_pow_left₀ (by norm_num) (by norm_num) hn.ne'
    have e : (5 / 2 : ℝ) ^ n * X / P = (5 / 2) ^ n * (A * Real.sqrt |(discr K : ℝ)|) := by
      rw [hX_def]; field_simp
    rw [e]
    have hY : 0 < A * Real.sqrt |(discr K : ℝ)| := mul_pos hA hD
    calc A * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| * 2 ^ n
        = (A * Real.sqrt |(discr K : ℝ)| * 2 ^ n) * (2 : ℝ)⁻¹ ^ nrComplexPlaces K := by ring
      _ ≤ (A * Real.sqrt |(discr K : ℝ)| * 2 ^ n) * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ < (A * Real.sqrt |(discr K : ℝ)|) * (5 / 2) ^ n := by rw [mul_one]; exact mul_lt_mul_of_pos_left h3 hY
      _ = 1 * ((5 / 2) ^ n * (A * Real.sqrt |(discr K : ℝ)|)) := by ring
      _ ≤ (convexBodyLTFactor K : ℝ) * ((5 / 2) ^ n * (A * Real.sqrt |(discr K : ℝ)|)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
  obtain ⟨a, ha, hne, hlt⟩ := exists_ne_zero_mem_ideal_lt K J h
  refine ⟨a, hne, le_vAdd_of_mem hB ρ hI S hS ha hne, fun σ => ?_⟩
  have h1 : ‖σ a‖ < R / r σ := by
    have := hlt (InfinitePlace.mk σ)
    rw [InfinitePlace.apply] at this
    rw [← apply_embedding_mk r hc σ]
    exact this
  have h2 : r σ * ‖σ a‖ < R := by
    rw [lt_div_iff₀ (hr σ)] at h1; linarith
  have h3 : 0 < r σ * ‖σ a‖ := mul_pos (hr σ) (norm_pos_iff.2 ((map_ne_zero σ).2 hne))
  have h4 : Real.log (r σ * ‖σ a‖) ≤ Real.log R := Real.log_le_log h3 h2.le
  have hlogR : Real.log R = Real.log (5 / 2) + Real.log A / n + Real.log |(discr K : ℝ)| / (2 * n) +
      (∑ σ, Real.log (r σ)) / n := by
    rw [hR_def, Real.log_mul (by norm_num) (by positivity), Real.log_rpow hX, hX_def,
      Real.log_mul (mul_pos hA hD).ne' hP.ne', Real.log_mul hA.ne' hD.ne', Real.log_sqrt (abs_nonneg _), hPdef,
      Real.log_prod (fun σ _ => (hr σ).ne')]
    ring
  have h52 : Real.log (5 / 2) ≤ 1 := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (by norm_num) (by linarith [Real.exp_one_gt_d9])
  have hAle := log_absNorm_idealOf_le hB ρ S hS
  have h5 : Real.log A / n ≤ GlobalTheory.FlatTw.logSum B - ∑ᶠ w, ρ w * lw K w := by
    rw [div_le_iff₀ hn']; linarith
  unfold GlobalTheory.FlatLine.lineDeg
  linarith

end GlobalTheory.FlatShort

namespace GlobalTheory.FlatShort

theorem exists_short_flat_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (B : Finset ℕ), Nonempty (GlobalTheory.ShFam.KeySec Xo c) → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → 1 ≤ Dw.p + Dw.q → (∀ p ∈ B, p.Prime) → GlobalTheory.FlatTw.UnramPts Xo c B → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt U x c₁ → ∀ (Z : Comp Xo c), GlobalTheory.FlatLine.HasPts U Z → ∀ w : Psi H → ℤ, ∃ t : GlobalTheory.FlatTw.TwSec U x Z (wtOf Dw (GlobalTheory.FlatLine.parWt Dw w) 0), (∀ v, 0 ≤ t.lo v) ∧ ∀ σ, Real.log (t.cInf σ) ≤ (|c₁| + (Dw.q : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E) * ∑ τ, |(w τ : ℝ)| + GlobalTheory.FlatTw.logSum B + Real.log |(NumberField.discr c.F : ℝ)| / (2 * (Module.finrank ℚ c.F : ℝ)) + 1 := by
  intro E _ _ _ H Dw l Xo c r U x B hK hU hpq hBp hUn c₁ hF Z hZ w
  obtain ⟨t, htI, -, hdeg⟩ := (GlobalTheory.FlatTwisting.twSec_of_flat E H Dw l Xo c r U x B hK hU hpq hUn).2 ⟨c₁, hF⟩ Z w hZ
  have hc1 : ∀ τ, c1 U x τ = c₁ := fun τ => hF.c1_eq ⟨Z⟩ τ
  have hconj : ∀ σ, t.cInf (NumberField.ComplexEmbedding.conjugate σ) = t.cInf σ :=
    fun σ => t.cInf_congr (GlobalTheory.CompHt.goodOf_conj σ)
  obtain ⟨a, ha0, hval, hlog⟩ := exists_short_elt B hBp t.cInf t.cInf_pos hconj t.lo t.finite_lo htI
  obtain ⟨-, hci, hlo, -, -⟩ := TwSec.const_spec (x := x) hZ a ha0
  refine ⟨(t.mul (TwSec.const x hZ a ha0)).copy (add_zero _), fun v => ?_, fun σ => ?_⟩
  · show 0 ≤ t.lo v + (TwSec.const x hZ a ha0).lo v
    rw [hlo]; linarith [hval v]
  · show Real.log (t.cInf σ * (TwSec.const x hZ a ha0).cInf σ) ≤ _
    rw [hci]
    have h1 := hlog σ
    have e : t.degLo = GlobalTheory.FlatLine.lineDeg t.cInf t.lo := rfl
    simp only [hc1] at hdeg
    have hs : -(∑ τ, (w τ : ℝ) * c₁) ≤ |c₁| * ∑ τ, |(w τ : ℝ)| := by
      rw [← Finset.sum_mul, mul_comm |c₁|]
      refine (neg_le_abs _).trans ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
    have h2 : -t.degLo ≤ (|c₁| + (Dw.q : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E) * ∑ τ, |(w τ : ℝ)| := by
      rw [add_mul]; linarith
    linarith

end GlobalTheory.FlatShort
