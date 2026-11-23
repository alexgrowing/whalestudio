import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Definitions.Divisors.GenSubHwOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLiftCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartInvariantSubmoduleEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviLiftMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerOfCoef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadMinorMulDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticPowOfRestrictsToQuadraticSig
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenCardOfNotLone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtAlgebraMapSgnAdSubOne
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.RealLift

open Classical

theorem exists_form_of_one_eq {F L : Type} [Field F] [Field L] {φ : F →+* L} {t δ : F} {X Y : L}
    (e : (1 : L) = φ t * (X ^ 2 - φ δ * Y ^ 2)) :
    ∃ x y : L, φ t = x ^ 2 - φ δ * y ^ 2 :=
  ⟨φ t * X, φ t * Y, by linear_combination (φ t) * e⟩

theorem ringEquivReal_evInf_algebraMap {F : Type} [Field F] [NumberField F] {v : InfinitePlace F}
    (hv : v.IsReal) (c : F) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hv (evInf F v (algebraMap F (AF F) c)) =
      InfinitePlace.embedding_of_isReal hv c := by
  rw [AlgHom.commutes]
  exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv _).symm c)

theorem neg_at_real {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (w : InfinitePlace F) (τ : EmbOver E w) (hw : w.IsReal) {δ : F}
    (hδ : ∀ (R : Type) [CommRing R] [Algebra F R], ∀ x y : R, ∃ z : R ⊗[F] E,
      z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2)) :
    InfinitePlace.embedding_of_isReal hw δ ≤ 0 := by
  set σw := InfinitePlace.embedding_of_isReal hw
  letI : Algebra F ℝ := σw.toAlgebra
  letI : Algebra F ℂ := (Complex.ofRealHom.comp σw).toAlgebra
  let f : ℝ →ₐ[F] ℂ := { Complex.ofRealHom with commutes' := fun _ => rfl }
  have hτ : ∀ c : F, τ.1 (algebraMap F E c) = (σw c : ℂ) := by
    intro c
    have h1 := congrArg (fun g : F →+* ℂ => g c) τ.2
    simp only [RingHom.coe_comp, Function.comp_apply] at h1
    rw [h1, InfinitePlace.embedding_of_isReal_apply]
  let g : E →ₐ[F] ℂ := { τ.1 with commutes' := hτ }
  let Φ := Algebra.TensorProduct.productMap f g
  have hconj : ∀ z : ℝ ⊗[F] E, Φ (sigR ℝ σ z) = starRingEnd ℂ (Φ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r e =>
      show Φ (Algebra.TensorProduct.map (AlgHom.id F ℝ) σ (r ⊗ₜ e)) = _
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.productMap_apply_tmul,
        Algebra.TensorProduct.productMap_apply_tmul]
      show (r : ℂ) * τ.1 (σ e) = starRingEnd ℂ ((r : ℂ) * τ.1 e)
      rw [hcm.2.2.2, map_mul, Complex.conj_ofReal]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨z, hz⟩ := hδ ℝ 0 1
  have h2 := congrArg Φ hz
  rw [map_mul, hconj, Complex.mul_conj, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one] at h2
  have h3 : Complex.normSq (Φ z) = -σw δ := by
    have h4 : f (algebraMap ℝ ℝ ((0 : ℝ) ^ 2 - algebraMap F ℝ δ * 1 ^ 2)) = ((-σw δ : ℝ) : ℂ) := by
      show (((0 : ℝ) ^ 2 - σw δ * 1 ^ 2 : ℝ) : ℂ) = _
      congr 1
      ring
    exact_mod_cast h2.trans h4
  linarith [Complex.normSq_nonneg (Φ z)]

theorem even_mα_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (X : Chars F E) (a a' : ℕ), B.IsGood σ → X.IsGood B a a' →
    ∀ w, Even (B.mα w + (a' : ℤ)) := by
  intro F E _ _ _ _ _ σ B X a a' hB hX w
  have hcm : IsCMExt F E σ := hB.cm
  haveI : IsTotallyReal F := hcm.1
  have hw : w.IsReal := IsTotallyReal.isReal w
  set σw := InfinitePlace.embedding_of_isReal hw with hσw
  obtain ⟨δ, hδ, hh⟩ := GlobalTheory.T.quadraticExt_norm_form_over_algebra F E σ hcm.2.2.1 (GlobalTheory.ResEtaFOfPow.sig_invol hcm)
    (GlobalTheory.ResEtaFOfPow.sig_ne hcm)
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  have hneg : σw δ < 0 := lt_of_le_of_ne (neg_at_real hcm w (B.emb w) hw (fun R _ _ => (hh R).2))
    (fun h => hδ0 (σw.injective (h.trans (map_zero σw).symm)))
  let δu : Fˣ := Units.mk0 δ hδ0
  let u : (AF F)ˣ := ⟨sgnAd w, sgnAd w, sgnAd_mul_self w, sgnAd_mul_self w⟩
  let z : (AE F E)ˣ := Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) u
  have hz : At (evI F) ((z : AE F E) - 1) := at_algebraMap_sgnAd_sub_one w
  have hpi : ∀ v, piInf (B.emb v) (z : AE F E) = if v = w then -1 else 1 := by
    intro v
    show piInf (B.emb v) (algebraMap (AF F) (AE F E) (sgnAd w)) = _
    rw [piInf_algebraMap, evInf_sgnAd]
    split_ifs <;> simp
  have hexp : ∀ m : InfinitePlace F → ℤ,
      ∏ v, (piInf (B.emb v) (z : AE F E) / ‖piInf (B.emb v) (z : AE F E)‖) ^ m v = (-1 : ℂ) ^ m w := by
    intro m
    rw [Finset.prod_eq_single w (fun v _ hv => by rw [hpi, if_neg hv]; simp) (fun h => absurd (Finset.mem_univ w) h),
      hpi, if_pos rfl]
    simp
  have eα := hX.expα z hz
  rw [hexp] at eα
  have rα : (X.α z : ℂ) = _ := hX.resα u

  split_ifs at rα with hm
  · exfalso
    obtain ⟨_, ⟨t, rfl⟩, _, ⟨n, rfl⟩, htn⟩ := Subgroup.mem_sup.1 hm
    obtain ⟨x, y, hxy, -⟩ := (hh (AF F)).1 (n : AE F E)
    have E0 : sgnAd w = algebraMap F (AF F) (t : F) * (x ^ 2 - algebraMap F (AF F) δ * y ^ 2) := by
      have := congrArg (fun q : (AF F)ˣ => (q : AF F)) htn
      simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at this
      rw [← hxy]
      exact this.symm

    have hfin : ∀ v : HeightOneSpectrum (𝓞 F), t ∈ GlobalTheory.HilbertRecip.nrm (.inl v) δu := by
      intro v
      let π : AF F →+* v.adicCompletion F :=
        { toFun := fun q => (q.2 : FiniteAdeleRing (𝓞 F) F) v, map_one' := rfl, map_mul' := fun _ _ => rfl,
          map_zero' := rfl, map_add' := fun _ _ => rfl }
      have hc : ∀ c : F, π (algebraMap F (AF F) c) = algebraMap F (v.adicCompletion F) c := fun _ => rfl
      have h1 : π (sgnAd w) = 1 := rfl
      have e := congrArg π E0
      rw [h1, map_mul, map_sub, map_mul, map_pow, map_pow, hc, hc] at e
      exact exists_form_of_one_eq e

    have hval : ∀ (v : InfinitePlace F) (hv : v.IsReal),
        (if v = w then -1 else 1 : ℝ) = InfinitePlace.embedding_of_isReal hv (t : F) *
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hv (evInf F v x)) ^ 2 -
            InfinitePlace.embedding_of_isReal hv δ *
              (InfinitePlace.Completion.ringEquivRealOfIsReal hv (evInf F v y)) ^ 2) := by
      intro v hv
      let φ : AF F →+* ℝ := (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toRingHom.comp (evInf F v).toRingHom
      have hc : ∀ c : F, φ (algebraMap F (AF F) c) = InfinitePlace.embedding_of_isReal hv c :=
        ringEquivReal_evInf_algebraMap hv
      have h1 : φ (sgnAd w) = if v = w then -1 else 1 := by
        show InfinitePlace.Completion.ringEquivRealOfIsReal hv (evInf F v (sgnAd w)) = _
        rw [evInf_sgnAd]
        split_ifs <;> simp
      have e := congrArg φ E0
      rw [h1, map_mul, map_sub, map_mul, map_pow, map_pow, hc, hc] at e
      exact e
    have hEq : ∀ (v v' : InfinitePlace F) (h : v.IsReal) (h' : v'.IsReal), v = v' →
        InfinitePlace.embedding_of_isReal h = InfinitePlace.embedding_of_isReal h' := by
      rintro v _ h h' rfl
      rfl
    have hreal : ∀ σ' : F →+* ℝ, σ' ≠ σw → t ∈ GlobalTheory.HilbertRecip.nrm (.inr σ') δu := by
      intro σ' hne
      have hφ : NumberField.ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ') := by
        rw [NumberField.ComplexEmbedding.isReal_iff]
        ext x
        simp
      have hv := InfinitePlace.isReal_mk_iff.2 hφ
      have he : InfinitePlace.embedding_of_isReal hv = σ' := by
        ext x
        apply Complex.ofReal_injective
        rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
        simp
      have hvw : InfinitePlace.mk (Complex.ofRealHom.comp σ') ≠ w := fun h =>
        hne (he.symm.trans (hEq _ _ hv hw h))
      have e := hval _ hv
      rw [if_neg hvw, he] at e
      exact exists_form_of_one_eq e
    have hwn : t ∉ GlobalTheory.HilbertRecip.nrm (.inr σw) δu := by
      rintro ⟨p, q, hpq⟩
      have e := hval w hw
      rw [if_pos rfl] at e
      change σw (t : F) = p ^ 2 - σw δ * q ^ 2 at hpq
      change (-1 : ℝ) = σw (t : F) * (_ ^ 2 - σw δ * _ ^ 2) at e
      generalize InfinitePlace.Completion.ringEquivRealOfIsReal hw (evInf F w x) = X at e
      generalize InfinitePlace.Completion.ringEquivRealOfIsReal hw (evInf F w y) = Y at e
      have hs : 0 ≤ σw (t : F) := by rw [hpq]; nlinarith [sq_nonneg p, sq_nonneg q]
      have hN : 0 ≤ X ^ 2 - σw δ * Y ^ 2 := by nlinarith [sq_nonneg X, sq_nonneg Y]
      nlinarith [mul_nonneg hs hN]
    have hprod := GlobalTheory.HilbertRecip.prod_hs t δu {.inr σw} (by
      rintro (v | σ') hp
      · exact absurd (hfin v) hp
      · by_cases h : σ' = σw
        · rw [h]; exact Finset.mem_singleton_self _
        · exact absurd (hreal σ' h) hp)
    rw [Finset.prod_singleton] at hprod
    exact hwn (GlobalTheory.HilbertRecip.hs_eq_one_iff.1 hprod)
  have hab : (-1 : ℂ) ^ B.mα w = (-1) ^ a' := by rw [← eα, rα]
  rcases Int.even_or_odd (B.mα w + (a' : ℤ)) with h | h
  · exact h
  · exfalso
    have h1 := h.neg_one_zpow (α := ℂ)
    rw [zpow_add₀ (by norm_num), hab, zpow_natCast, ← pow_add, ← two_mul, pow_mul] at h1
    norm_num at h1

end GlobalTheory.RealLift
