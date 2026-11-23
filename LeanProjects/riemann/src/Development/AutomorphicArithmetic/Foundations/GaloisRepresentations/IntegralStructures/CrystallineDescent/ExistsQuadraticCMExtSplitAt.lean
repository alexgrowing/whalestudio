import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InfinitelyManyRealQuadraticSteps
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InfinitePrimesNegIsSquare

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.HeckeGal GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open GlobalTheory.GalCut GlobalTheory.Cong GlobalTheory.CongL UpperTheory.Gal.UnramifiedFromSplittingCriterion
open private UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.normV_mem' UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.normV_pos' UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.val_lt_of_dvd UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.fix_of_val UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.moved_at_ram UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.unram_of_fix UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.down UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.nonsplit_of_sqrt_conductor from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NonsplitOfSqrtConductor

set_option maxHeartbeats 800000 in
theorem UpperTheory.Gal.Int.Core.exists_quadratic_CM_ext_split_at : UpperTheory.Gal.Int.Core.Quad2Ex := by
  intro E Y Ω _ _ _ _ _ _ _ _ _ δ hδ T hT
  have hTP := twoPrimes (primeWith decGen)
  have hS := sqrtFix
  have hMk := mkQ
  have hUL := unrLarge
  have hSI := splitIff
  have hIS := inertSplit decGen
  have hRS := realSpan
  let F := maximalRealSubfield Y
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed Y, Algebra.IsAlgebraic.trans _ Y Ω⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed Y
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, Algebra.IsAlgebraic.trans ℚ Y Ω⟩
  have hRfin := GlobalTheory.T.finite_places_inertia_not_le_openSubgroup Ω F (fixGrp F Ω Y) (isOpen_fixGrp F Ω Y)
  have hQfin := GlobalTheory.T.finite_places_inertia_not_le_openSubgroup Ω ℚ (fixGrp ℚ Ω Y) (isOpen_fixGrp ℚ Ω Y)
  set R := hRfin.toFinset with hRdef
  set R' := hQfin.toFinset with hR'def
  set TT := hT.toFinset with hTTdef
  obtain ⟨c, hc0, hc2, hc3, hcT, hcR, hcQ⟩ : ∃ c : ℕ, 0 < c ∧ 2 ∣ c ∧ 3 ∣ c ∧ (∀ t ∈ T, normV t ∣ c) ∧ (∀ v ∈ R, normV v ∣ c) ∧
      ∀ v ∈ R', normV v ∣ c := by
    refine ⟨6 * ((∏ v ∈ R, normV v) * ((∏ t ∈ TT, normV t) * ∏ t ∈ R', normV t)), ?_, Dvd.dvd.mul_right (by norm_num) _,
      Dvd.dvd.mul_right (by norm_num) _, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
    · exact Nat.mul_pos (by norm_num) (Nat.mul_pos (Finset.prod_pos fun v _ => UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.normV_pos' v)
        (Nat.mul_pos (Finset.prod_pos fun v _ => UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.normV_pos' v) (Finset.prod_pos fun v _ => UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.normV_pos' v)))
    · exact (((Finset.dvd_prod_of_mem _ (hT.mem_toFinset.2 ht)).mul_right _).mul_left _).mul_left _
    · exact ((Finset.dvd_prod_of_mem _ ht).mul_right _).mul_left _
    · exact (((Finset.dvd_prod_of_mem _ ht).mul_left _).mul_left _).mul_left _
  obtain ⟨B₀, hB₀⟩ := hUL Y
  obtain ⟨p₁, p₂, h1, h2, hB, hlt, hM, hTw⟩ := hTP E Y Ω δ hδ (8 * c) (max B₀ c) (by omega)
  have hB0 : B₀ < p₁ := lt_of_le_of_lt (le_max_left _ _) hB
  have hBc : c < p₁ := lt_of_le_of_lt (le_max_right _ _) hB
  have hc2le : 2 ≤ c := Nat.le_of_dvd hc0 hc2
  set p : ℕ := p₁ * p₂ with hp
  have hp0 : 0 < p := Nat.mul_pos h1.pos h2.pos
  set a : ℤ := -(p : ℤ) with ha
  obtain ⟨x, hx2'⟩ := IsAlgClosed.exists_pow_nat_eq ((a : ℤ) : Ω) two_pos
  have hx2 : x ^ 2 = ((a : ℤ) : Ω) := hx2'
  have hd : ((8 * c : ℕ) : ℤ) ∣ a - 1 := by
    have h : ((8 * c : ℕ) : ℤ) ∣ ((p + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 hM
    have h' : a - 1 = -((p + 1 : ℕ) : ℤ) := by rw [ha]; push_cast; ring
    rw [h']
    exact h.neg_right

  obtain ⟨u, hu⟩ := GlobalTheory.ExSplitCM.exists_mem_of_prime (F := Y) h1
  obtain ⟨A₀, hA₀⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
  obtain ⟨τ₀, hτ₀, hτ₀x⟩ := UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.moved_at_ram hS A₀ u hA₀ p₁ p₂ h1 h2 (by omega) hlt hu (hB₀ p₁ h1 hB0 u) x hx2
  obtain ⟨Q, hxQ, -, hfixQ⟩ := hMk Y Ω x a hx2 ⟨τ₀, hτ₀x⟩
  have hu_notT : u ∉ T := by
    intro huT
    have hmem : ((c : ℕ) : 𝓞 Y) ∈ u.asIdeal := by
      obtain ⟨k, hk⟩ := hcT u huT
      rw [hk, Nat.cast_mul]
      exact u.asIdeal.mul_mem_right _ (UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.normV_mem' u)
    have hcop : Nat.Coprime p₁ c := (Nat.Prime.coprime_iff_not_dvd h1).2 fun h => by
      have := Nat.le_of_dvd hc0 h; omega
    exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
      have := GlobalTheory.CMFam.dvd_of_mem u h1 hu hmem
      exact absurd this ((Nat.Prime.coprime_iff_not_dvd h1).1 hcop)))
  have haux := fun (w : HeightOneSpectrum (𝓞 ↥Q.K)) (hw : ¬ IsSplitAt w) (A : ValuationSubring Ω)
      (hA : IsPlaceOver A w) =>
    UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.nonsplit_of_sqrt_conductor hSI hRS hS Q x hxQ p hp0 hx2 δ hδ.1.choose hδ.1.choose_spec.1 hδ.1.choose_spec.2 c hc0.ne' hc2 hd
      (fun A hv h hh hhδ y => hTw A (by simpa [hp] using hv) h hh hhδ y) w hw A hA
  have hunderY : ∀ (w : HeightOneSpectrum (𝓞 ↥Q.K)) (A : ValuationSubring Ω), IsPlaceOver A w →
      IsPlaceOver A (w.under (𝓞 Y)) := fun w A hA x => by
    rw [IsScalarTower.algebraMap_apply Y ↥Q.K Ω]
    exact hA (algebraMap (𝓞 Y) (𝓞 ↥Q.K) x)
  have hunderF : ∀ (w : HeightOneSpectrum (𝓞 Y)) (A : ValuationSubring Ω), IsPlaceOver A w →
      IsPlaceOver A (w.under (𝓞 F)) := fun w A hA x => by
    rw [IsScalarTower.algebraMap_apply F Y Ω]
    exact hA (algebraMap (𝓞 F) (𝓞 Y) x)

  have hIneY : ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v →
      ¬ A.valuation (c : Ω) < 1 → ∀ τ ∈ Ine (F := F) A, Fixes Y τ := by
    intro v A hA hvc τ hτ
    by_contra hnf
    have hvR : v ∈ R := hRfin.mem_toFinset.2 ⟨A, hA, fun hle => hnf (hle hτ)⟩
    exact hvc (UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.val_lt_of_dvd A v hA (hcR v hvR))
  have hX2 : (⟨x, hxQ⟩ : ↥Q.K) ^ 2 = -(p : ↥Q.K) := Subtype.ext (by simpa [ha] using hx2)
  have hall : ∀ (w : HeightOneSpectrum (𝓞 ↥Q.K)), ¬ IsSplitAt w → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
      ¬ A.valuation (c : Ω) < 1 ∧ (∀ τ ∈ Ine (F := F) A, Fixes Y τ ∧ τ x = x) ∧
        ∃ g ∈ Dec (F := F) A, ¬ Fixes Y g := by
    intro w hw A hA
    obtain ⟨hvc, hv2, hg⟩ := haux w hw A hA
    exact ⟨hvc, fun τ hτ => ⟨hIneY _ A (hunderF _ A (hunderY w A hA)) hvc τ hτ, (hS F Ω A x a hx2).2 hv2 τ hτ⟩, hg⟩
  have hS1 : Step1 T Q := by
   refine ⟨⟨⟨x, hxQ⟩, p, hp0, hX2⟩, GlobalTheory.CMFam.even_finrank Y Ω Q, ?_, ?_, u, hu_notT, A₀, hA₀, τ₀, hτ₀,
     fun h => hτ₀x (h ⟨x, hxQ⟩)⟩
   · intro t ht A hA g hg
     exact hfixQ Y g (fun y => g.commutes y)
       (UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.fix_of_val hS A x a hx2 c hc0.ne' hd (UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.val_lt_of_dvd A t hA (hcT t ht)) g hg)
   · intro w hw
     obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
     refine ⟨fun hT' => (hall w hw A hA).1 (UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.val_lt_of_dvd A _ (hunderY w A hA) (hcT _ hT')), ?_, ?_⟩
     · have hfix : ∀ σ ∈ Ine (F := maximalRealSubfield ↥Q.K) A, ∀ z : ↥Q.K,
           σ (algebraMap ↥Q.K Ω z) = algebraMap ↥Q.K Ω z := by
         intro σ hσ
         have hσ' : UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.down Q σ ∈ Ine (F := F) A :=
           mem_Ine.2 ⟨(GlobalTheory.AboveL.mem_dec_congr A (UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.down Q σ) σ (fun _ => rfl)).2 (Ine_le_Dec A hσ), (mem_Ine.1 hσ).2⟩
         obtain ⟨h3, h4⟩ := (hall w hw A hA).2.1 _ hσ'
         exact hfixQ _ σ h3 h4
       exact UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.unram_of_fix ↥Q.K Ω w A hA hfix
     · intro A' hA' h hh
       obtain ⟨-, hI, hg⟩ := hall w hw A' hA'
       exact hfixQ Y h (fun y => h.commutes y)
         (hIS Y Ω A' (w.under (𝓞 Y)) (hunderY w A' hA') x a hx2 hI hg h hh)
  refine ⟨Q, hS1, fun w hw => ?_, p, ⟨hp0, _, hX2⟩, fun w hw => ⟨by_contra fun h => (hS1.2.2.2.1 w h).1 hw, fun q hq hqw => ?_⟩⟩
  · obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
    obtain ⟨hvc, hv2, -⟩ := haux w hw A hA
    have hAv : IsPlaceOver A (w.under (𝓞 (maximalRealSubfield ↥Q.K))) := fun x => by
      rw [IsScalarTower.algebraMap_apply (maximalRealSubfield ↥Q.K) ↥Q.K Ω]
      exact hA (algebraMap (𝓞 (maximalRealSubfield ↥Q.K)) (𝓞 ↥Q.K) x)
    generalize w.under (𝓞 (maximalRealSubfield ↥Q.K)) = v at hAv ⊢
    have hn : ∀ k : ℕ, k ∣ c → ((k : ℕ) : 𝓞 (maximalRealSubfield ↥Q.K)) ∉ v.asIdeal := by
      rintro k ⟨j, rfl⟩ hk
      refine hvc (GlobalTheory.TameCoupledEx.val_g_lt A v hAv ?_)
      rw [Nat.cast_mul]
      exact v.asIdeal.mul_mem_right _ hk
    refine ⟨by exact_mod_cast hn 2 hc2, ?_, ?_⟩
    · have h1 := Ideal.absNorm_mem v.asIdeal
      have h2 : Ideal.absNorm v.asIdeal ≠ 0 := (UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.normV_pos' v).ne'
      have h3 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
      have h4 : Ideal.absNorm v.asIdeal ≠ 2 := fun h => hn 2 hc2 (h ▸ h1)
      have h5 : Ideal.absNorm v.asIdeal ≠ 3 := fun h => hn 3 hc3 (h ▸ h1)
      omega
    · have hA0 : IsPlaceOver A (v.under (𝓞 ℚ)) := fun x => by
        rw [IsScalarTower.algebraMap_apply ℚ (maximalRealSubfield ↥Q.K) Ω]
        exact hAv (algebraMap (𝓞 ℚ) (𝓞 (maximalRealSubfield ↥Q.K)) x)
      obtain ⟨-, he⟩ := GlobalTheory.InertFixVal.ramificationIdx_eq_one A (v.under (𝓞 ℚ)) v hA0 hAv fun τ hτ z => by
        refine hfixQ ℚ τ ?_ ((hS ℚ Ω A x a hx2).2 hv2 τ hτ) (z : ↥Q.K)
        by_contra hnf
        exact hvc (UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.val_lt_of_dvd A _ hA0 (hcQ _ (hQfin.mem_toFinset.2 ⟨A, hA0, fun hle => hnf (hle hτ)⟩)))
      have hu1 : Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal := Ideal.ramificationIdx_eq_one_iff.1 he
      have hu2 : Algebra.FormallyUnramified ℤ (𝓞 ℚ) := Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ (𝓞 ℚ))
        fun y => ⟨Rat.ringOfIntegersEquiv y, by simpa using (eq_intCast Rat.ringOfIntegersEquiv.symm _).symm.trans (Rat.ringOfIntegersEquiv.symm_apply_apply y)⟩
      have hu3 : Algebra.IsUnramifiedAt ℤ v.asIdeal := Algebra.FormallyUnramified.comp ℤ (𝓞 ℚ) _
      rw [← Ideal.dvd_iff_le]
      exact not_dvd_differentIdeal_iff.2 hu3
  · haveI : Fact q.Prime := ⟨hq⟩
    have h1 : q ∣ c := by
      refine (GlobalTheory.CMFam.dvd_of_mem (w.under (𝓞 Y)) hq ?_ (UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan.normV_mem' _)).trans (hcT _ hw)
      show algebraMap (𝓞 Y) (𝓞 ↥Q.K) _ ∈ w.asIdeal
      rwa [map_natCast]
    refine GlobalTheory.RealGal.PrimesNegSquare.isSquare_neg_of_dvd q p ?_
    exact_mod_cast (Nat.mul_dvd_mul_left 8 h1).trans hM
