import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularUnitsOfRootMemKummerAdjoin

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

private theorem exists_limit {K L : Type} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (φ : Finset K → (L →+* L)) (hφ : ∀ T, ∀ t ∈ T, φ T (algebraMap K L t) = algebraMap K L t) :
    ∃ ψ : L ≃ₐ[K] L, ∀ z, ∃ T, φ T z = ψ z := by
  classical
  let U : Ultrafilter (Finset K) := Ultrafilter.of Filter.atTop
  have hU : (U : Filter (Finset K)) ≤ Filter.atTop := Ultrafilter.of_le _
  have ev : ∀ P : Prop, (∀ᶠ _T in (U : Filter (Finset K)), P) → P :=
    fun P h => h.exists.elim fun _ h => h
  have hfix : ∀ t : K, ∀ᶠ T in (U : Filter (Finset K)), φ T (algebraMap K L t) = algebraMap K L t := by
    intro t
    filter_upwards [hU (Filter.eventually_ge_atTop {t})] with T hT
    exact hφ T t (hT (Finset.mem_singleton_self t))
  have key : ∀ z : L, ∃ w : L, ∀ᶠ T in (U : Filter (Finset K)), φ T z = w := by
    intro z
    obtain ⟨p, hp0, hpz⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) z
    let S : Finset K := p.support.image p.coeff
    have hroot : ∀ᶠ T in (U : Filter (Finset K)),
        φ T z ∈ ((p.map (algebraMap K L)).roots.toFinset : Set L) := by
      filter_upwards [hU (Filter.eventually_ge_atTop S)] with T hT
      have hmap : p.map (algebraMap K L) = p.map ((φ T).comp (algebraMap K L)) := by
        ext n
        simp only [Polynomial.coeff_map, RingHom.comp_apply]
        by_cases hn : p.coeff n = 0
        · simp [hn]
        · rw [hφ T _ (hT (Finset.mem_image_of_mem _ (Polynomial.mem_support_iff.mpr hn)))]
      have hne : p.map (algebraMap K L) ≠ 0 := Polynomial.map_ne_zero hp0
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      rw [Polynomial.mem_roots hne]
      change Polynomial.eval _ _ = 0
      have h0 : Polynomial.eval₂ (algebraMap K L) z p = 0 := hpz
      rw [hmap, Polynomial.eval_map, ← Polynomial.hom_eval₂, h0, map_zero]
    obtain ⟨w, -, hw⟩ := Ultrafilter.eq_pure_of_finite_mem
      (f := U.map (fun T => φ T z)) (Finset.finite_toSet _) (Ultrafilter.mem_map.mpr hroot)
    refine ⟨w, ?_⟩
    have hmem : ({w} : Set L) ∈ U.map (fun T => φ T z) := by
      rw [hw]
      exact Ultrafilter.mem_pure.mpr rfl
    exact Ultrafilter.mem_map.mp hmem
  choose ψ0 hψ0 using key
  let ψ1 : L →ₐ[K] L :=
    { toFun := ψ0
      map_one' := ev _ ((hψ0 1).mono fun T h => by rw [← h, map_one])
      map_mul' := fun x y => ev _ (((hψ0 x).and ((hψ0 y).and (hψ0 (x * y)))).mono
        fun T h => by rw [← h.1, ← h.2.1, ← h.2.2, map_mul])
      map_zero' := ev _ ((hψ0 0).mono fun T h => by rw [← h, map_zero])
      map_add' := fun x y => ev _ (((hψ0 x).and ((hψ0 y).and (hψ0 (x + y)))).mono
        fun T h => by rw [← h.1, ← h.2.1, ← h.2.2, map_add])
      commutes' := fun t => ev _ (((hψ0 (algebraMap K L t)).and (hfix t)).mono
        fun T h => by rw [← h.1, h.2]) }
  refine ⟨AlgEquiv.ofBijective ψ1 (Algebra.IsAlgebraic.algHom_bijective ψ1), fun z => ?_⟩
  obtain ⟨T, hT⟩ := (hψ0 z).exists
  exact ⟨T, hT⟩

theorem UpperTheory.V.Z.Kato.Sym.kumUn :
    UpperTheory.V.Z.Kato.Sym.KumUn := by
  unfold UpperTheory.V.Z.Kato.Sym.KumUn
  rintro Ω _ _ _ ε X m hm φ f ⟨θ, hθ, hka⟩ hU
  rw [Tower.Un, Set.mem_setOf_eq]
  intro W hW
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hinj : Function.Injective (Polynomial.aeval (R := Ω) X.jK) :=
    transcendental_iff_injective.mp (jK_transcendental X)
  let P : Polynomial Ω →ₐ[Ω] X.K := Polynomial.aeval X.jK
  let Λ : RatFunc Ω →ₐ[Ω] X.K :=
    RatFunc.liftAlgHom P (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj)
  letI : Algebra (Polynomial Ω) X.K := P.toRingHom.toAlgebra
  letI : Algebra (RatFunc Ω) X.K := Λ.toRingHom.toAlgebra
  have hΛP : ∀ p : Polynomial Ω, Λ (algebraMap (Polynomial Ω) (RatFunc Ω) p) = P p := fun p => by
    simpa using RatFunc.liftAlgHom_apply_div P
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj) p 1
  haveI : IsScalarTower (Polynomial Ω) (RatFunc Ω) X.K :=
    IsScalarTower.of_algebraMap_eq fun p => (hΛP p).symm
  haveI : Algebra.IsAlgebraic (RatFunc Ω) X.K := by
    refine ⟨fun g => ?_⟩
    obtain ⟨p, hp0, hpg⟩ := X.alg_j g
    have hle : ∀ y ∈ IntermediateField.adjoin Ω {X.jK}, ∃ r, Λ r = y := by
      intro y hy
      have hsub : IntermediateField.adjoin Ω {X.jK} ≤ Λ.fieldRange :=
        IntermediateField.adjoin_simple_le_iff.mpr
          (AlgHom.mem_fieldRange.mpr ⟨algebraMap _ _ Polynomial.X, by rw [hΛP]; simp [P]⟩)
      exact AlgHom.mem_fieldRange.mp (hsub hy)
    have hl : p.map (algebraMap (IntermediateField.adjoin Ω {X.jK}) X.K) ∈ Polynomial.lifts Λ.toRingHom := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      exact hle _ (p.coeff n).2
    obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).mp hl
    refine ⟨q, ?_, ?_⟩
    · rintro rfl
      exact hp0 ((Polynomial.map_eq_zero _).mp (by rw [← hq, Polynomial.map_zero]))
    · have h0 : Polynomial.eval₂ Λ.toRingHom g q = 0 := by
        rw [Polynomial.eval₂_eq_eval_map, hq, ← Polynomial.eval₂_eq_eval_map]
        exact hpg
      exact h0
  obtain ⟨B, hB⟩ := UnRoot.exists_comap_eq (io X) W
  have hf0 : (f : X.K) ≠ 0 := f.ne_zero
  have hTex : ∃ T : Finset X.K, ∀ φ' : Kb X →+* Kb X,
      (∀ x, B.valuation x ≤ 1 → B.valuation (φ' x - x) < 1) →
      (∀ t ∈ T, φ' (algebraMap X.K (Kb X) t) = algebraMap X.K (Kb X) t) → φ' θ = θ := by
    by_contra hcon
    push_neg at hcon
    choose φ' hin hfx hne using hcon
    obtain ⟨ψ, hψ⟩ := exists_limit φ' hfx
    let h : RingAut (Kb X) := ψ.toRingEquiv
    have hInD : InD X h := fun g => ψ.commutes g
    have hiner : ∀ z, B.valuation z ≤ 1 → B.valuation (h z - z) < 1 := by
      intro z hz
      obtain ⟨T, hT⟩ := hψ z
      have hv := hin T z hz
      rw [hT] at hv
      exact hv
    have hOver : X.OverY (B.comap (io X)) := hB ▸ hW
    have h0 : φ h = 0 := hU B h hOver hInD hiner
    have hk : lg X m (h θ) θ = 0 := by
      change ka X m θ h = 0
      rw [hka h hInD, h0]
    obtain ⟨-, hlg2, -⟩ := lgB Ω ε X m hm
    have hθ0 : θ ≠ 0 := by
      rintro rfl
      rw [zero_pow hm.ne'] at hθ
      exact hf0 ((map_eq_zero (io X)).mp hθ.symm)
    have hpow : (h θ) ^ m = θ ^ m := by
      rw [← map_pow, hθ]
      exact hInD f
    have hfix : h θ = θ := by
      have h1 := hlg2 (h θ) θ hθ0 hpow
      rw [hk] at h1
      simpa using h1
    obtain ⟨T, hT⟩ := hψ θ
    exact hne T (hT.trans hfix)
  obtain ⟨T, hT⟩ := hTex
  have hP : ∀ p : Polynomial Ω, algebraMap X.K (Kb X) (algebraMap (Polynomial Ω) X.K p) ∈ B := by
    intro p
    have hpW : Polynomial.aeval X.jK p ∈ W := by
      refine Polynomial.induction_on p (fun a => ?_) (fun p q hp hq => ?_) (fun n a ih => ?_)
      · rw [Polynomial.aeval_C]
        exact hW.1 a
      · rw [map_add]
        exact W.add_mem _ _ hp hq
      · rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
        exact W.mul_mem _ _ ih hW.2
    rw [← hB] at hpW
    exact hpW
  obtain ⟨c, hc0, hcv⟩ := UnRoot.core (k := Ω) B hP hm (f : X.K) hf0 θ hθ T hT
  refine ⟨Units.mk0 c hc0, ?_⟩
  rw [← hB]
  exact (UnRoot.val_comap_eq_one (io X) B _).mpr hcv
