import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceRingFractionEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliarySetFieldDataCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliarySetLAdicPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSqrtNegPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLowerBoundProductStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CxPtSizes

theorem val_le_of_gen {E : Type} [Field E] [NumberField E] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ)
    (hl : (l : R) ∈ IsLocalRing.maximalIdeal R) (hl0 : (l : R) ≠ 0) (σ : E →+* FractionRing R) (ξ ξ' : E) (h0 : ξ' ≠ 0) (n : ℕ) (hn : IsUnit (n : R))
    (a : OF E) (h : (n : E) * ξ' = algebraMap (OF E) E a * ξ) :
    ξ ≠ 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ ξ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ ξ') := by
  have hn0 : (n : E) ≠ 0 := by
    intro h; have : n = 0 := by exact_mod_cast h
    subst this; simp at hn
  have hξ : ξ ≠ 0 := by rintro rfl; simp [hn0, h0] at h
  refine ⟨hξ, ?_⟩
  have hint : IsIntegral ℤ (algebraMap (OF E) E a) := (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (IsScalarTower.toAlgHom ℤ (OF E) E)
  have hint2 : IsIntegral R (σ (algebraMap (OF E) E a)) :=
    IsIntegral.map_of_comp_eq (algebraMap ℤ R) σ (RingHom.ext_int _ _) hint
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint2
  set v := (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) with hv
  have h1 : v (σ (algebraMap (OF E) E a)) ≤ 1 := hb ▸ HeightOneSpectrum.valuation_le_one _ _
  have h2 : v (σ (n : E)) = 1 := by
    have : σ (n : E) = algebraMap R (FractionRing R) (n : R) := by simp
    rw [this, HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact fun hm => (IsLocalRing.mem_maximalIdeal _).1 hm hn
  have h3 : v (σ ξ') ≤ v (σ ξ) := by
    have := congrArg (fun x => v (σ x)) h
    simp only [map_mul, h2, _root_.one_mul] at this
    rw [this]; exact mul_le_of_le_one_left' h1
  have hs : σ ξ ≠ 0 := (map_ne_zero σ).2 hξ
  have hs' : σ ξ' ≠ 0 := (map_ne_zero σ).2 h0
  have hlK : (l : FractionRing R) = algebraMap R (FractionRing R) (l : R) := by simp
  have hlv : v (l : FractionRing R) < 1 := by rw [hlK, HeightOneSpectrum.valuation_lt_one_iff_mem]; exact hl
  have hlv0 : v (l : FractionRing R) ≠ 0 := by
    rw [hlK]; exact (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hl0)
  have hpos : 0 < GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (l : FractionRing R) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw; rw [← hv]; have := (WithZero.log_lt_log hlv0 one_ne_zero).2 hlv; simp at this; omega
  have hle : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (σ ξ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (σ ξ') := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw; rw [← hv]
    have := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 hs') ((Valuation.ne_zero_iff _).2 hs)).2 h3; omega
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp, hs, hs', if_false, WithTop.coe_le_coe]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (by exact_mod_cast hpos.le)

theorem scale_size : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (c₀ : 𝔠.elt)
      (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 →
      (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 (FR E)), n.Coprime l ∧ n • c = t • c₀) →
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) (2 • ψ₀) →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) →
      (∀ i (g : Fin n → R), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) = Submodule.span R {g} →
        ∃ r : Rˣ, ∀ x, ψ₀ (eH.symm g) x = (r : R) * e i (hL.toLie X₀.rm x)) →
    ∀ (D : R) (cv : ℚ), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (D)) = (cv : WithTop ℚ) → (cv : ℝ) = c_vp 𝔣 l →
    ∀ (e' f' : I → (Fin n → R)), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) e' f' →
      (∀ i, 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (ψ₀ (eH.symm (e' i)) (eH.symm (f' i)))) ∧ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (ψ₀ (eH.symm (e' i)) (eH.symm (f' i)))) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (D))) →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p), m.IsBC → ∀ (ψ : LinearMap.BilinForm ℂ (HdR X.A)), IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ →
    ∀ (yv ev : I → HdR X.A) (w : I → ℂ), (∀ i, U.IsCMVec i (yv i) (w i)) →
      (∀ i, m.Corr (eH.symm (f' i)) (yv i)) → (∀ i, m.Corr (eH.symm (e' i)) (ev i)) →
      (∀ i, ((e i (hL.toLie X₀.rm (eH.symm (f' i))) : R) : ℂ) = a i * w i) →
    ∀ i, (Real.pi : ℂ) * (U.h i : ℂ) * ((D : ℂ) / ψ (ev i) (yv i)) * w i ^ 2 ≠ 0 ∧
      Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0)
        (a i * (a i * ((Real.pi : ℂ) * (U.h i : ℂ) * ((D : ℂ) / ψ (ev i) (yv i)) * w i ^ 2) / (D : ℂ)) * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹ := by
  intro hPC hADR hADC hPM E _ _ _ _ I _ d φ hFD 𝔣 h𝔣 l _ Q hQ hQl y hy lam 𝔠 R _ hR X₀ X U p cm hpull hcm hα j hj φK hφK
    e a he hL n eH c₀ ψ₀ hc₀ hgen hpol hCM hψ₀ D cv hD hcv e' f' hgens hval m hm ψ hψ yv ev w hcmv hyc hec hew
  obtain ⟨ξ, hξgen, hrat⟩ := GlobalTheory.T.auxiliary_set_field_data_congruence hPC hADR hADC hPM E I d φ hFD 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR X₀ X U p cm hpull hcm hα j hj φK hφK
    e a he hL n eH c₀ ψ₀ hc₀ hgen hpol hCM hψ₀ D cv hD hcv e' f' hgens hval m hm ψ hψ yv ev w hcmv hyc hec hew
  obtain ⟨j', hj', hchar, hlm, -, -, hSz⟩ := GlobalTheory.PlaceRingFacts.place_ring_facts E l lam R hR
  have hgenv : ξ ≠ 0 ∧ ∀ σ : E →+* FractionRing R, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ ξ) ≤ 0 := by
    have hc : condQ 𝔣 Q ≠ ⊥ := mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
    obtain ⟨ξ', hp', hg'⟩ := (((hPM E hFD.2.2.1 I φ hFD.2.2.2.2.2.2.1 1).1 _ hc y).2.2.2 l Fact.out).1
    obtain ⟨h0', hv'⟩ := GlobalTheory.T.auxiliary_set_l_adic_place hPM E I d φ hFD 𝔣 h𝔣 l Q hQ hQl y hy lam R hR j hj ξ' 1 hp' hg'
    obtain ⟨n', hn', a', ha'⟩ := hξgen.2 ξ' hg'.1
    have hl0 : (l : R) ≠ 0 := by
      haveI := hchar; exact_mod_cast (Fact.out : l.Prime).ne_zero
    have hu : IsUnit (n' : R) := by
      have hc := (Nat.isCoprime_iff_coprime.2 hn').map (Int.castRingHom R)
      simp only [eq_intCast, Int.cast_natCast] at hc
      obtain ⟨s, t, hst⟩ := hc
      by_contra hnu
      have : (1 : R) ∈ IsLocalRing.maximalIdeal R := hst ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 hnu)) (Ideal.mul_mem_left _ _ hlm)
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)
    exact ⟨by rintro rfl; have : (n' : E) ≠ 0 := (fun h => by have : n' = 0 := (by exact_mod_cast h); subst this; simp at hu); simp [this, h0'] at ha',
      fun σ => (val_le_of_gen R l hlm hl0 σ ξ ξ' h0' n' hu a' ha').2.trans (hv' σ)⟩
  obtain ⟨hξ0, hξv⟩ := hgenv
  have hjj : j' = j := IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun x => by simp [hj, hj'])
  subst hjj
  obtain ⟨δ, hδ2, hδφ⟩ := hFD.2.2.2.2.2.2.2
  have hdp : d.Prime := hFD.1
  intro i
  set P0 : R := ψ₀ (eH.symm (e' i)) (eH.symm (f' i)) with hP0def
  obtain ⟨r, hr⟩ := hψ₀ i (e' i) (hgens i).1
  have hP0c : ((P0 : R) : ℂ) = ((r : R) : ℂ) * (a i * w i) := by
    rw [hP0def, hr, ← hew i]; push_cast; ring
  have vtop : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (0 : FractionRing R) = ⊤ := by simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp]
  have hD0 : D ≠ 0 := by
    rintro rfl; rw [map_zero, vtop] at hD; exact WithTop.top_ne_coe hD
  have hvP : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) P0) ≤ (cv : WithTop ℚ) := hD ▸ (hval i).2
  have hP00 : P0 ≠ 0 := by
    intro h0; rw [h0, map_zero, vtop] at hvP; exact absurd hvP (by simp)
  have hD0c : (D : ℂ) ≠ 0 := fun h => hD0 (Subtype.ext h)
  have hP0c0 : ((P0 : R) : ℂ) ≠ 0 := fun h => hP00 (Subtype.ext h)
  have hr0 : ((r : R) : ℂ) ≠ 0 := fun h => r.ne_zero (Subtype.ext h)
  have hφξ : φ i ξ ≠ 0 := (map_ne_zero (φ i)).2 hξ0
  obtain ⟨hh0, hrat'⟩ := hrat i
  have hhc : ((U.h i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hh0
  have hψ0 : ψ (ev i) (yv i) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hrat'
    exact mul_ne_zero hhc hP0c0 hrat'.symm
  have haw : a i * w i ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hP0c; exact hP0c0 hP0c
  have ha0 : a i ≠ 0 := left_ne_zero_of_mul haw
  have hw0 : w i ≠ 0 := right_ne_zero_of_mul haw
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hdp.pos)
    exact_mod_cast this.ne'
  refine ⟨?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero hpi hhc) (div_ne_zero hD0c hψ0)) (pow_ne_zero _ hw0)
  · have hunit : ∀ q : ℕ, q.Prime → q ≠ l → IsUnit (q : R) := by
      intro q hq hql
      haveI := Fact.mk hq
      have hv : 0 ≤ padicValRat l ((q : ℚ)⁻¹) := by
        rw [padicValRat.inv, padicValRat.of_nat, padicValNat_primes (Ne.symm hql)]; simp
      have hmem := hR.2.2.1 _ hv
      refine IsUnit.of_mul_eq_one (b := ⟨_, hmem⟩) (Subtype.ext ?_)
      have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
      simp [hq0]
    have hl0 : (l : R) ≠ 0 := by
      haveI := hchar; exact_mod_cast (Fact.out : l.Prime).ne_zero
    have hδ0 : δ ≠ 0 := by
      rintro rfl
      have : ((d : ℕ) : E) = 0 := by simpa using hδ2
      exact hdp.ne_zero (by exact_mod_cast this)
    haveI := hchar
    have hvδ := GlobalTheory.T.valuation_sqrt_neg_prime E l R hlm hunit d hdp δ hδ2 (φK i)
    have hz := GlobalTheory.T.valuation_lower_bound_product R l hlm hl0 (algebraMap R (FractionRing R) P0) (φK i ξ) (φK i δ) r cv (if l = d then 1 / 2 else 0)
      ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hP00) ((map_ne_zero (φK i)).2 hξ0)
      ((map_ne_zero (φK i)).2 hδ0) hvP (hξv (φK i)) hvδ
    have hS := hSz _ (cv + if l = d then 1 / 2 else 0) (by simpa using hz)
    have hφj : ∀ t : E, j' (φK i t) = φ i t := fun t => by rw [← hφK i]; rfl
    have key : j' ((algebraMap R (FractionRing R) (r : R)) ^ 2 / (algebraMap R (FractionRing R) P0 * (φK i δ * φK i ξ))) =
        (a i * (a i * ((Real.pi : ℂ) * (U.h i : ℂ) * ((D : ℂ) / ψ (ev i) (yv i)) * w i ^ 2) / (D : ℂ)) * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹ := by
      have h2I : (2 * Complex.I * φ i ξ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hφξ
      have hψv : ψ (ev i) (yv i) = (U.h i : ℂ) * ((P0 : R) : ℂ) / (2 * Complex.I * φ i ξ) := eq_div_of_mul_eq h2I hrat'
      rw [map_div₀, map_pow, map_mul, map_mul, hj', hj', hφj, hφj, hδφ i, hψv, hP0c]
      field_simp
    have hcast : (((cv + if l = d then 1 / 2 else 0 : ℚ)) : ℝ) = c_vp 𝔣 l + if l = d then 1 / 2 else 0 := by
      rw [Rat.cast_add, hcv]; split_ifs <;> norm_num
    rw [← hcast, ← key]; exact hS

end GlobalTheory.CxPtSizes
