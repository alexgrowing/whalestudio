import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldDegreeLeAndRootDiscrBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOneMemOfIsRayFieldIn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRayFieldInRestrictScalars
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CurveOverOfRayFieldAny
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeSupAdd
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIrreducibleComponentsWeberValues
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberLeAbsDiscrOfFinrankEqTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaloisRatComplexImageRayClassField

set_option autoImplicit false

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
open GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.CovTop.SizedCover

theorem stable_of_normal (R : IntermediateField ℚ ℂ) [hN : Normal ℚ R] (s : ℂ ≃+* ℂ) (a : ℂ) (ha : a ∈ R) : s a ∈ R := by
  have h := @AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ R (by convert hN; exact Subsingleton.elim _ _)
    (s.toRingHom.toRatAlgHom.comp R.val)
  exact h.le ⟨⟨a, ha⟩, rfl⟩

theorem exists_ray (hRF : GlobalTheory.NT.RayField) {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n : ℕ) (hn : 3 ≤ n) :
    ∃ (R : IntermediateField ℚ ℂ) (a b : ℝ), Sz R a b ∧ a + b ≤ 20 * (Real.log n + Real.log H.d + 1) ∧
      (∀ s : ℂ ≃+* ℂ, ∀ z ∈ R, s z ∈ R) ∧ H.rt0 ∈ R ∧ zeta n ∈ R ∧ ∀ F, R ≤ F → GlobalTheory.FinalJoin.WeberIn H F n := by
  have hdm := H.d_mod
  have hd0 : 0 < H.d := H.d_prime.pos
  obtain ⟨hfin, h2⟩ := RayExistCurve.finrank_adjoin hd0 H.sqrt_neg_disc_sq
  have hr0 : H.rt0 ∈ ℚ⟮H.rt0⟯ := IntermediateField.mem_adjoin_simple_self ℚ H.rt0
  generalize ℚ⟮H.rt0⟯ = K₀ at hfin h2 hr0
  have hNF : NumberField K₀ := NumberField.mk
  have hr : (⟨H.rt0, hr0⟩ : K₀) ^ 2 = -(H.d : K₀) := Subtype.ext (by simpa using H.sqrt_neg_disc_sq)
  have hD : discr K₀ = -(H.d : ℤ) := discr_eq_neg_of_sq_eq h2 H.d_prime.squarefree (by omega) hr
  have hTC : IsTotallyComplex K₀ := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have h1 : InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩ ^ 2 = -(H.d : ℝ) := by
      rw [← map_pow, hr, map_neg, map_natCast]
    have h3 : (0 : ℝ) < H.d := by exact_mod_cast hd0
    nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩)]
  have hQ : Algebra.IsQuadraticExtension ℚ K₀ := ⟨h2⟩
  have hG : IsGalois ℚ K₀ := inferInstance
  obtain ⟨w, hw, hgen⟩ := exists_integer_generator_of_sq_eq_neg h2 H.d_prime.squarefree (by omega) hr
  let φ : K₀ →+* ℂ := algebraMap K₀ ℂ
  have hw' : φ w = (1 + H.rt0) / 2 := by
    have := congrArg φ hw
    rw [map_mul, map_add, map_one, map_ofNat] at this
    change _ = 1 + H.rt0 at this
    linear_combination this / 2
  have hc : ∀ a b : ℤ, φ ((a : 𝓞 K₀) + b * w : 𝓞 K₀) = a + b * ((1 + H.rt0) / 2) := fun a b => by
    rw [← hw']
    simp
  have hn0 : (n : 𝓞 K₀) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  obtain ⟨L, _, _, _, hL⟩ := GlobalTheory.Mem.Fld.rayField_iff.1 hRF K₀ (Ideal.span {(n : 𝓞 K₀)})
    (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let ψ : L →ₐ[K₀] ℂ := IsAlgClosed.lift
  let e₀ : L ≃ₐ[K₀] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  have hfR : FiniteDimensional K₀ ψ.fieldRange := e₀.toLinearEquiv.finiteDimensional
  have hLR := fun (_ : NumberField ψ.fieldRange) => hL.of_algEquiv e₀
  generalize ψ.fieldRange = R at hfR hLR
  have hNR : NumberField R := NumberField.of_module_finite K₀ R
  have hin := (hLR hNR).isRayFieldIn_restrictScalars
  obtain ⟨hab, hR⟩ := hLR hNR
  change IsRay R (Ideal.span {(n : 𝓞 K₀)}) at hR
  have hGR : IsGalois ℚ R := GlobalTheory.RayNatGalois.isGalois_of_isRay_nat ℚ (L := K₀) (by omega) hR
  have hGR' : Normal ℚ (R.restrictScalars ℚ) := hGR.to_normal
  obtain ⟨hdeg, hsz⟩ := GlobalTheory.Mem.Fld.RaySize.degOver_le_and_sz K₀ _ n _ hin (by omega)
  have hNR' : NumberField (R.restrictScalars ℚ) := hNR
  have hdpos := GlobalTheory.Mem.Fld.degOver_pos _ _ hin.emb_mem
  refine ⟨R.restrictScalars ℚ, _, _, hsz, ?_, stable_of_normal _, R.algebraMap_mem (⟨H.rt0, hr0⟩ : K₀),
    GlobalTheory.Mem.RayRoots.rootOne_mem_of_isRayFieldIn K₀ _ n n _ (by omega) dvd_rfl hin, fun F hRle P hP => ?_⟩
  · have hcl := classNumber_le_abs_discr_of_finrank_eq_two K₀ h2
    generalize GlobalTheory.Mem.Fld.degOver _ _ hin.emb_mem = m at hdeg hdpos
    rw [h2] at hdeg
    rw [hD] at hcl
    rw [h2, hD]
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast, Nat.cast_ofNat] at hcl ⊢
    have hd1 : (1 : ℝ) ≤ H.d := by exact_mod_cast hd0
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hm : (0 : ℝ) < m := by exact_mod_cast hdpos
    have hm' : (m : ℝ) ≤ H.d * (n : ℝ) ^ 2 := by
      have : (m : ℝ) ≤ classNumber K₀ * (n : ℝ) ^ 2 := by exact_mod_cast hdeg
      exact this.trans (by gcongr)
    have h1 := Real.log_le_log hm hm'
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
    have h3 := Real.log_nonneg hd1
    have h4 := Real.log_nonneg hn1
    have h5 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    push_cast at h1
    linarith
  · have hW := GlobalTheory.T.weberInvariantTorsionValues_subset_rayClassField K₀ h2 (by omega) P (fun z => ?_) n hn R hR
    · exact ⟨hRle (hW (Set.mem_insert _ _)), fun s hs => hRle (hW (Set.mem_insert_of_mem _
        ⟨_, (hP _).2 ⟨s, rfl⟩, hs, rfl⟩))⟩
    · rw [hP]
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨_, hc s.1 s.2⟩
      · rintro ⟨a, rfl⟩
        obtain ⟨a, b, rfl⟩ := hgen a
        exact ⟨(a, b), hc a b⟩

set_option maxHeartbeats 1000000 in

theorem exists_good_sized : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (T : Core D), T.Q.Pins → ∀ j : ℕ, InR D j → 5 ≤ D.host.splitBound → Nat.Coprime 15 (D.host.g 0 * D.host.g 1) → ∀ e : ℕ, ∃ Y : Deep T j, Y.Good e (fieldSz T.Q.c.F + 20 * (Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * 15 ^ e) + Real.log D.host.d + 1)) := by
  intro hRF D T hQ j hj h5 h15 e
  obtain ⟨s, hs⟩ := Inhab.exists_root h5
  have hpos := Inhab.rank_pos T hQ j hj
  obtain ⟨I, hK, hp, hI⟩ := Inhab.exists_half T.Q.H s (by rw [hQ.1.1]; exact hs) e
  obtain ⟨l₂, l1, l2, l3, l4, l5, l6⟩ := GlobalTheory.CoverHalf.exists_coverLevel T.Q.l hQ.2.1.2 (15 ^ e) I (Odd.pow (by decide))
    (by rw [hQ.2.1.1]; exact h15.pow_left e) hK hp hI
  obtain ⟨Xo₂⟩ := GlobalTheory.Moduli.moduli_scheme_exists _ _ (T.Q.Dw j) l₂ hpos
  have hM' : l₂.M' = l₂.M := by
    show Nat.lcm l₂.M l₂.A = l₂.M
    rw [l6, Nat.lcm_one_right]
  obtain ⟨R, a, b, hsz, hab, hst, hrt, hz, hW⟩ := exists_ray hRF T.Q.H l₂.M l₂.three_le
  haveI := T.Q.c.fin
  have hsz0 : Sz T.Q.c.F (Real.log (Module.finrank ℚ T.Q.c.F))
      (Real.log |(discr T.Q.c.F : ℝ)| / (Module.finrank ℚ T.Q.c.F : ℝ)) := ⟨T.Q.c.fin, le_rfl, le_rfl⟩
  obtain ⟨hN, hN1, hN2⟩ := GlobalTheory.FieldSize.sz_sup _ _ _ _ _ _ hsz0 hsz
  have h1 : T.Q.c.F ≤ T.Q.c.F ⊔ R := le_sup_left
  have h2 : R ≤ T.Q.c.F ⊔ R := le_sup_right
  have hst' : ∀ s : ℂ ≃+* ℂ, (∀ a ∈ T.Q.c.F, s a = a) → ∀ a ∈ T.Q.c.F ⊔ R, s a ∈ T.Q.c.F ⊔ R := fun s hs a ha => by
    have : T.Q.c.F ⊔ R ≤ (T.Q.c.F ⊔ R).comap s.toRingHom.toRatAlgHom :=
      sup_le (fun x hx => show s x ∈ T.Q.c.F ⊔ R from (hs x hx).symm ▸ h1 hx) fun x hx => h2 (hst s x hx)
    exact this ha
  have hKA : KA l₂ ≤ T.Q.c.F ⊔ R := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro x (rfl | rfl)
    · exact h2 hrt
    · rw [l6]
      simpa [zeta] using one_mem (T.Q.c.F ⊔ R)
  generalize T.Q.c.F ⊔ R = N at hN hN1 hN2 h1 h2 hst' hKA
  haveI : NumberField N := NumberField.mk
  let c' : Coeff T.Q.l := ⟨N, hN, fun τ a => h1 (T.Q.c.conj τ a), h1 T.Q.c.zeta_mem, T.Q.c.le.trans h1⟩
  let c₂ : Coeff l₂ := ⟨N, hN, fun τ a => h1 (T.Q.c.conj τ a), hM' ▸ h2 hz, hKA⟩
  have hfa : FnAlgClosed Xo₂ c₂ := GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn D T.Q hQ j hj l₂ Xo₂ c₂ l₂.M
    (by have := l₂.three_le; omega) hM'.dvd (Or.inl (hW N h2))
  have hsize : fieldSz c₂.F ≤ fieldSz T.Q.c.F + 20 * (Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * 15 ^ e) +
      Real.log D.host.d + 1) := by
    rw [l2, hQ.2.1.1, hQ.1.1] at hab
    push_cast at hab
    unfold fieldSz
    have h3 : Real.log (Module.finrank ℚ c₂.F : ℝ) ≤ _ := hN1
    have h4 : Real.log |(discr c₂.F : ℝ)| / (Module.finrank ℚ c₂.F : ℝ) ≤ _ := hN2
    linarith
  obtain ⟨⟨pd', I', l₂', Xo₂', c₂', hF, r, mm, nab, cδ, φ₀⟩, a1, a2, a3, e₁, e₂, -, a4, a5⟩ :=
    GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ _ _ (T.Q.Xo j) c' hpos 0 (15 ^ e) I l₂ Xo₂ c₂ rfl l1 l2 l3 l4 l5
  dsimp only at a3 e₁ e₂
  subst a3
  obtain rfl := eq_of_heq e₁
  obtain rfl := eq_of_heq e₂
  obtain ⟨U, dict, Kf, h⟩ := Inhab.exists_good_of_cover T hQ j hj c' h1 _ e a1 a4 l6 hfa hst'
  exact ⟨_, h.mono hsize⟩

end GlobalTheory.CovTop.SizedCover
