import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocG

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

theorem norm_le_one_iff_val {F C : Type} [Field F] [NumberField F] [NormedField C] (φ : F →+* C)
    (w : HeightOneSpectrum (𝓞 F)) (h1 : ∀ x : 𝓞 F, ‖φ (x : F)‖ ≤ 1)
    (h2 : ∀ x : 𝓞 F, x ∈ w.asIdeal ↔ ‖φ (x : F)‖ < 1) (x : F) : ‖φ x‖ ≤ 1 ↔ w.valuation F x ≤ 1 := by
  have hu : ∀ d : 𝓞 F, d ∉ w.asIdeal → ‖φ (d : F)‖ = 1 := fun d hd =>
    le_antisymm (h1 d) (not_lt.mp fun h => hd ((h2 d).mpr h))
  have key : ∀ y : F, w.valuation F y ≤ 1 → ∃ n : 𝓞 F, ‖φ y‖ = ‖φ (n : F)‖ ∧
      w.valuation F y = w.valuation F (n : F) := fun y hy => by
    obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer y hy
    have hd : w.valuation F (algebraMap (𝓞 F) F d) = 1 := w.valuation_eq_one_iff_notMem.mpr d.2
    refine ⟨n, ?_, ?_⟩
    · have := congrArg (fun t => ‖φ t‖) h
      simp only [map_mul, norm_mul] at this
      rwa [show ‖φ (algebraMap (𝓞 F) F d)‖ = 1 from hu _ d.2, mul_one] at this
    · have := congrArg (w.valuation F) h
      rwa [map_mul, hd, mul_one] at this
  refine ⟨fun h => not_lt.mp fun hlt => ?_, fun h => ?_⟩
  · have hx : x ≠ 0 := by rintro rfl; simp at hlt
    have hi : w.valuation F x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hlt
    obtain ⟨n, e1, e2⟩ := key _ hi.le
    have hn : n ∈ w.asIdeal := (w.valuation_lt_one_iff_mem n).mp (e2 ▸ hi)
    have := (h2 n).mp hn
    rw [← e1, map_inv₀, norm_inv, inv_lt_one₀ (norm_pos_iff.mpr ((map_ne_zero φ).mpr hx))] at this
    exact absurd h (not_le.mpr this)
  · obtain ⟨n, e1, -⟩ := key x h
    rw [e1]; exact h1 n

theorem resChar_mem' (D : D7) (w : D.what₂.places.Pl) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  have hp := D.what₂.places.resChar_prime w
  have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h := D.what₂.places.val_resChar w
  rw [D.val_eq w _ hne] at h
  have h1 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) :=
    WithTop.coe_injective h
  have h2 : (0 : ℤ) < D.what₂.places.ramIdx w := by exact_mod_cast D.what₂.places.ramIdx_pos w
  rw [← (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL)]
  show (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL _) < 1
  have hv := (Valuation.ne_zero_iff ((D.plEq w).valuation D.what₂.LL)).mpr hne
  rw [map_natCast, ← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  unfold vAdd at h1
  omega

theorem mem_intW_iff (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    x ∈ intW D.what₂.places w ↔ (D.plEq w).valuation D.what₂.LL x ≤ 1 := by
  show (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔ _
  by_cases hx : x = 0
  · subst hx; simp
  · have hv := (Valuation.ne_zero_iff ((D.plEq w).valuation D.what₂.LL)).mpr hx
    rw [D.val_eq w x hx, ← WithTop.coe_zero, WithTop.coe_le_coe, vAdd, neg_nonneg]
    conv_rhs => rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_le_exp]

theorem exists_lamExt {K : Type} [Field K] [NumberField K] (e : K →+* ℂ) {C : Type} [Field C] [IsAlgClosed C]
    (f : K →+* C) : ∃ lam : (algebraicClosure ℚ ℂ) →+* C, ∀ x : K, ∃ hx : e x ∈ algebraicClosure ℚ ℂ,
      f x = lam ⟨e x, hx⟩ := by
  have hmem : ∀ x : K, e x ∈ algebraicClosure ℚ ℂ := fun x =>
    (mem_algebraicClosure_iff).mpr ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom e.toRatAlgHom)
  let j : K →+* algebraicClosure ℚ ℂ := e.codRestrict (algebraicClosure ℚ ℂ).toSubring hmem
  let _ : Algebra K (algebraicClosure ℚ ℂ) := j.toAlgebra
  let _ : Algebra K C := f.toAlgebra
  have h0 : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have : Algebra.IsAlgebraic K (algebraicClosure ℚ ℂ) := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let l : algebraicClosure ℚ ℂ →ₐ[K] C := IsAlgClosed.lift
  exact ⟨l.toRingHom, fun x => ⟨hmem x, (l.commutes x).symm⟩⟩

theorem exists_placeEmb (D : D7) (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime] :
    ∃ (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
      (iL : D.what₂.LL →+* ℂ_[D.what₂.places.resChar w]),
      (∀ x, ∃ hx : D.what₂.embLL x ∈ algebraicClosure ℚ ℂ, iL x = lam ⟨D.what₂.embLL x, hx⟩) ∧
      ∀ x, x ∈ intW D.what₂.places w ↔ ‖iL x‖ ≤ 1 := by
  obtain ⟨φ, hφ⟩ := LB.exists_embAt (l := D.what₂.places.resChar w) (D.plEq w) (resChar_mem' D w)
  let iL := (algebraMap (PadicAlgCl (D.what₂.places.resChar w)) ℂ_[D.what₂.places.resChar w]).comp φ
  have hn : ∀ x, ‖iL x‖ = ‖φ x‖ := fun x => PadicComplex.norm_extends _ (φ x)
  obtain ⟨lam, hl⟩ := exists_lamExt D.what₂.embLL iL
  refine ⟨lam, iL, hl, fun x => ?_⟩
  rw [mem_intW_iff, hn]
  refine (norm_le_one_iff_val φ _ (fun y => ?_) hφ x).symm
  have hi : IsIntegral ℤ (φ (y : D.what₂.LL)) := (RingOfIntegers.isIntegral_coe y).map φ.toIntAlgHom
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl (D.what₂.places.resChar w)))
    ).isIntegral_iff_v_le_one.mp hi.tower_top
  exact_mod_cast (show ‖φ (y : D.what₂.LL)‖₊ ≤ 1 from h2)

theorem exists_hom_of_basis {L S M ι : Type} [Field L] [Field S] [Field M] [Algebra L S] [Algebra L M]
    [IsAlgClosed M] (x : ι → S) (y : ι → M) (hx : IsTranscendenceBasis L x) (hy : AlgebraicIndependent L y) :
    Nonempty (S →ₐ[L] M) := by
  let _ : Algebra (MvPolynomial ι L) S := (MvPolynomial.aeval x : MvPolynomial ι L →ₐ[L] S).toRingHom.toAlgebra
  let _ : Algebra (MvPolynomial ι L) M := (MvPolynomial.aeval y : MvPolynomial ι L →ₐ[L] M).toRingHom.toAlgebra
  have : FaithfulSMul (MvPolynomial ι L) S := (faithfulSMul_iff_algebraMap_injective _ _).mpr hx.1
  have : FaithfulSMul (MvPolynomial ι L) M := (faithfulSMul_iff_algebraMap_injective _ _).mpr hy
  have hA := hx.isAlgebraic
  have : Algebra.IsAlgebraic (MvPolynomial ι L) S := ⟨fun s => by
    obtain ⟨q, hq0, hq⟩ := hA.isAlgebraic s
    let e := hx.1.aevalEquiv.symm.toRingEquiv.toRingHom
    refine ⟨q.map e, (Polynomial.map_ne_zero_iff hx.1.aevalEquiv.symm.injective).mpr hq0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hq, Polynomial.aeval_def]
    congr 1
    ext t
    obtain ⟨r, rfl⟩ := hx.1.aevalEquiv.surjective t
    show MvPolynomial.aeval x (hx.1.aevalEquiv.symm (hx.1.aevalEquiv r)) = _
    rw [AlgEquiv.symm_apply_apply]
    exact (hx.1.algebraMap_aevalEquiv r).symm⟩
  let l : S →ₐ[MvPolynomial ι L] M := IsAlgClosed.lift
  exact ⟨{ l.toRingHom with
    commutes' := fun a => by
      have h := l.commutes (MvPolynomial.C a)
      simpa [RingHom.algebraMap_toAlgebra] using h }⟩

theorem exists_endo {L C : Type} [Field L] [NumberField L] [Field C] [CharZero C] [IsAlgClosed C]
    (a b : L →+* C) : ∃ α : C →+* C, α.comp a = b := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ C
  have ind : ∀ f : L →+* C, letI := f.toAlgebra; IsTranscendenceBasis L ((↑) : s → C) := fun f => by
    let _ := f.toAlgebra
    have : IsScalarTower ℚ L C := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    exact (Algebra.IsAlgebraic.isTranscendenceBasis_iff ℚ L).mp hs
  obtain ⟨α⟩ := @exists_hom_of_basis L C C s _ _ _ a.toAlgebra b.toAlgebra _ _ _ (ind a) (ind b).1
  exact ⟨@AlgHom.toRingHom L C C _ _ _ a.toAlgebra b.toAlgebra α,
    RingHom.ext fun x => @AlgHom.commutes L C C _ _ _ a.toAlgebra b.toAlgebra α x⟩

theorem exists_iK {L K C : Type} [Field L] [NumberField L] [Field K] [Field C] [CharZero C] [IsAlgClosed C]
    (f : L →+* K) (i0 : K →+* C) (iL : L →+* C) : ∃ iK : K →+* C, ∀ x, iK (f x) = iL x := by
  obtain ⟨α, h⟩ := exists_endo (i0.comp f) iL
  exact ⟨α.comp i0, fun x => RingHom.congr_fun h x⟩

end Formalism.BasicNotions.Examples₂
