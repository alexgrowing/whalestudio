import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSquareMulInfinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsKum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CyclicKummerNormFixedHilbert90
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HerbrandPrimeOrder
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PIdxUnitsFiniteExtensionAdicCompletion
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSubgroupIndexTwo

open NumberField IsDedekindDomain
open scoped WithZero

namespace GlobalTheory.QuadSymbol

namespace NormBaseChange

open NormIndex

def IndexTwo (B : Type) [Field B] : Prop :=
  ∀ d : B, ¬ IsSquare d → (∃ c : B, c ≠ 0 ∧ ¬ Nm d c) ∧
    ∀ x y : B, x ≠ 0 → y ≠ 0 → ¬ Nm d x → ¬ Nm d y → Nm d (x * y)

def NormsEscape (A B : Type) [Field A] [Field B] [Algebra A B] : Prop :=
  ∀ d : A, ¬ IsSquare (algebraMap A B d) → ∃ x : B, x ≠ 0 ∧ ¬ Nm d (Algebra.norm A x)

theorem nm_map {A B : Type} [Field A] [Field B] (f : A →+* B) {d x : A} (h : Nm d x) :
    Nm (f d) (f x) := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨f a, f b, by simp⟩

theorem IndexTwo.of_ringEquiv {A B : Type} [Field A] [Field B] (e : A ≃+* B) (h : IndexTwo B) :
    IndexTwo A := by
  have hi : ∀ d x : A, Nm (e d) (e x) ↔ Nm d x := fun d x =>
    ⟨fun h => by simpa using nm_map (e.symm : B →+* A) h, nm_map (e : A →+* B)⟩
  intro d hd
  obtain ⟨⟨c, hc0, hc⟩, h2⟩ := h (e d) (fun h => hd (by simpa using h.map e.symm))
  refine ⟨⟨e.symm c, by simpa using hc0, fun h => hc (by simpa using (hi _ _).2 h)⟩,
    fun x y hx0 hy0 hx hy => ?_⟩
  rw [← hi, map_mul]
  exact h2 _ _ (by simpa using hx0) (by simpa using hy0) (by rwa [hi]) (by rwa [hi])

theorem indexTwo_real : IndexTwo ℝ := by
  intro d hd
  rw [Real.isSquare_iff, not_le] at hd
  refine ⟨⟨-1, by norm_num, ?_⟩, fun x y _ _ hx hy => Nm.of_isSquare _ ?_⟩
  · rintro ⟨a, b, h⟩
    nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg (neg_nonneg.2 hd.le) (sq_nonneg b)]
  · have h1 : x < 0 := not_le.1 fun h => hx (Nm.of_isSquare _ (Real.isSquare_iff.2 h))
    have h2 : y < 0 := not_le.1 fun h => hy (Nm.of_isSquare _ (Real.isSquare_iff.2 h))
    exact Real.isSquare_iff.2 (mul_pos_of_neg_of_neg h1 h2).le

theorem indexTwo_of_isAlgClosed (B : Type) [Field B] [IsAlgClosed B] : IndexTwo B :=
  fun d hd => absurd (IsAlgClosed.exists_eq_mul_self d) hd

theorem indexTwo_of_finite_real (B : Type) [Field B] [Algebra ℝ B] [Algebra.IsAlgebraic ℝ B] :
    IndexTwo B := by
  rcases Real.nonempty_algEquiv_or B with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact indexTwo_real.of_ringEquiv e.toRingEquiv
  · exact (indexTwo_of_isAlgClosed ℂ).of_ringEquiv e.toRingEquiv

theorem indexTwo_infinite (F : Type) [Field F] (w : InfinitePlace F) (B : Type) [Field B]
    [Algebra w.Completion B] [FiniteDimensional w.Completion B] : IndexTwo B := by
  rcases w.isReal_or_isComplex with hw | hw
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    letI : Algebra ℝ w.Completion := (e.symm : ℝ →+* w.Completion).toAlgebra
    letI : Algebra ℝ B := ((algebraMap w.Completion B).comp (e.symm : ℝ →+* w.Completion)).toAlgebra
    haveI : IsScalarTower ℝ w.Completion B := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Algebra.IsAlgebraic ℝ w.Completion := ⟨fun x => by
      have : x = algebraMap ℝ w.Completion (e x) := (e.symm_apply_apply x).symm
      rw [this]
      exact isAlgebraic_algebraMap _⟩
    haveI : Algebra.IsAlgebraic ℝ B := Algebra.IsAlgebraic.trans ℝ w.Completion B
    exact indexTwo_of_finite_real B
  · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    haveI : IsAlgClosed w.Completion := IsAlgClosed.of_ringEquiv ℂ _ e.symm
    haveI : IsAlgClosed B := IsAlgClosed.of_ringEquiv w.Completion _
      (RingEquiv.ofBijective (algebraMap w.Completion B)
        (IsAlgClosed.algebraMap_bijective_of_isIntegral))
    exact indexTwo_of_isAlgClosed B

section Tower

variable {A B C : Type} [Field A] [Field B] [Field C]

theorem nm_norm [Algebra A B] [FiniteDimensional A B] {d : A} {x : B}
    (h : Nm (algebraMap A B d) x) : Nm d (Algebra.norm A x) := by
  classical
  obtain ⟨a, b, rfl⟩ := h
  let e := Module.finBasis A B
  let R := QuadraticAlgebra A d 0
  let φ : B →ₐ[A] Matrix (Fin (Module.finrank A B)) (Fin (Module.finrank A B)) R :=
    (AlgHom.mapMatrix (Algebra.ofId A R)).comp (Algebra.leftMulMatrix e)
  let t : R := QuadraticAlgebra.omega
  have ht : t * t = algebraMap A R d := by
    ext <;> simp [t, R]
  have hst : star t = -t := by
    ext <;> simp [t, R]
  have hφ : ∀ y : B, (φ y).map (starRingEnd R) = φ y := fun y => by
    ext1 i j
    ext <;> simp [φ, R, starRingEnd_apply]
  have h1 : φ (a ^ 2 - algebraMap A B d * b ^ 2) = (φ a + t • φ b) * (φ a - t • φ b) := by
    have hc : φ a * φ b = φ b * φ a := by rw [← map_mul, ← map_mul, mul_comm]
    rw [map_sub, map_mul, AlgHom.commutes, ← Algebra.smul_def, pow_two, pow_two, map_mul, map_mul,
      add_mul, mul_sub, mul_sub, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
      smul_smul, ht, algebraMap_smul, hc]
    abel
  have h2 : (φ a - t • φ b).det = star (φ a + t • φ b).det := by
    rw [← starRingEnd_apply, RingHom.map_det]
    congr 1
    ext1 i j
    have ha := congrFun (congrFun (hφ a) i) j
    have hb := congrFun (congrFun (hφ b) i) j
    simp only [Matrix.map_apply] at ha hb
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, map_add, map_mul, ha, hb]
    rw [starRingEnd_apply, hst]
    ring
  have h3 : algebraMap A R (Algebra.norm A (a ^ 2 - algebraMap A B d * b ^ 2)) =
      (φ (a ^ 2 - algebraMap A B d * b ^ 2)).det := by
    rw [Algebra.norm_eq_matrix_det e, RingHom.map_det]
    rfl
  rw [h1, Matrix.det_mul, h2, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star] at h3
  rw [(algebraMap A R).injective h3, QuadraticAlgebra.norm_def]
  exact ⟨(φ a + t • φ b).det.re, (φ a + t • φ b).det.im, by ring⟩

theorem nm_iff [CharZero A] [Algebra A B] [FiniteDimensional A B] (hB : IndexTwo B)
    (h : NormsEscape A B) {d : A} (hd : d ≠ 0) {x : B} (hx : x ≠ 0) :
    Nm (algebraMap A B d) x ↔ Nm d (Algebra.norm A x) := by
  haveI : CharZero B := charZero_of_injective_algebraMap (algebraMap A B).injective
  refine ⟨nm_norm, fun hn => ?_⟩
  by_cases hs : IsSquare (algebraMap A B d)
  · exact Nm.of_isSquare_left two_ne_zero ((map_ne_zero _).2 hd) hs x
  obtain ⟨y, hy0, hy⟩ := h d hs
  by_contra hc
  have := nm_norm ((hB _ hs).2 y x hy0 hx (fun h => hy (nm_norm h)) hc)
  rw [map_mul] at this
  exact hy (Nm.of_mul (Algebra.norm_ne_zero_iff.2 hx) hn this)

theorem NormsEscape.trans [CharZero A] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [FiniteDimensional A B] [FiniteDimensional B C] (hB : IndexTwo B)
    (h1 : NormsEscape A B) (h2 : NormsEscape B C) : NormsEscape A C := by
  intro d hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hd (by simp)
  obtain ⟨x, hx0, hx⟩ := h2 (algebraMap A B d) (by rwa [← IsScalarTower.algebraMap_apply])
  rw [nm_iff hB h1 hd0 (Algebra.norm_ne_zero_iff.2 hx0), Algebra.norm_norm] at hx
  exact ⟨x, hx0, hx⟩

theorem NormsEscape.of_odd_top [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [FiniteDimensional A B] [FiniteDimensional B C]
    (hodd : Odd (Module.finrank B C)) (h : NormsEscape A C) : NormsEscape A B := by
  intro d hd
  obtain ⟨x, hx0, hx⟩ := h d (by
    rintro ⟨r, hr⟩
    have h1 := congrArg (Algebra.norm B) hr
    obtain ⟨k, hk⟩ := hodd
    rw [IsScalarTower.algebraMap_apply A B C, Algebra.norm_algebraMap, map_mul, hk] at h1
    have h0 : algebraMap A B d ≠ 0 := fun h => hd (h ▸ IsSquare.zero)
    refine hd ⟨Algebra.norm B r / algebraMap A B d ^ k, ?_⟩
    field_simp
    linear_combination h1)
  exact ⟨Algebra.norm B x, Algebra.norm_ne_zero_iff.2 hx0, by rwa [Algebra.norm_norm]⟩

theorem normsEscape_of_odd [Algebra A B] (hA : IndexTwo A) (hodd : Odd (Module.finrank A B)) :
    NormsEscape A B := by
  intro d hd
  obtain ⟨c, hc0, hc⟩ := (hA d fun h => hd (h.map _)).1
  refine ⟨algebraMap A B c, (map_ne_zero _).2 hc0, fun h => hc ?_⟩
  obtain ⟨k, hk⟩ := hodd
  rw [Algebra.norm_algebraMap, hk] at h
  refine Nm.of_mul (pow_ne_zero 2 (pow_ne_zero k hc0)) (Nm.sq _ _) ?_
  rwa [show c * (c ^ k) ^ 2 = c ^ (2 * k + 1) by ring]

theorem exists_sqrt_basis (A B : Type) [Field A] [Field B] [CharZero A] [Algebra A B]
    (hr : Module.finrank A B = 2) : ∃ (δ : A) (e : Module.Basis (Fin 2) A B),
      ¬ IsSquare δ ∧ e 0 = 1 ∧ e 1 * e 1 = algebraMap A B δ := by
  haveI : Algebra.IsQuadraticExtension A B := ⟨hr⟩
  have hcard : Nat.card (B ≃ₐ[A] B) = 2 := (IsGalois.card_aut_eq_finrank A B).trans hr
  obtain ⟨σ, hσ, hall⟩ := (Nat.card_eq_two_iff' (1 : B ≃ₐ[A] B)).1 hcard
  have hσσ : σ * σ = 1 := by
    by_contra h
    exact hσ (by simpa using hall _ h)
  obtain ⟨δ, e, hδ, h0, -, h1⟩ := GlobalTheory.QuadNormBase.exists_basis A B (σ : B →ₐ[A] B) hr
    (fun x => DFunLike.congr_fun hσσ x) (by
      by_contra h
      push Not at h
      exact hσ (AlgEquiv.ext h))
  exact ⟨δ, e, hδ, h0, h1⟩

theorem normsEscape_of_two [CharZero A] [Algebra A B] (hA : IndexTwo A)
    (hr : Module.finrank A B = 2) : NormsEscape A B := by
  intro d hd
  obtain ⟨δ, e, hδ, h0, h1⟩ := exists_sqrt_basis A B hr
  haveI : FiniteDimensional A B := Module.Finite.of_basis e
  by_contra hall
  push Not at hall
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  have hdA : ¬ IsSquare d := fun h => hd (h.map _)
  have hd0 : d ≠ 0 := fun h => hdA (h ▸ IsSquare.zero)
  have H1 : ∀ c : A, c ≠ 0 → Nm δ c → Nm d c := by
    rintro c hc ⟨a, b, h⟩
    have hn := GlobalTheory.QuadNormBase.norm_of_basis e δ h0
      (by rw [h1, h0, Algebra.algebraMap_eq_smul_one]) a b
    rw [← h] at hn
    rw [← hn]
    exact hall _ (Algebra.norm_ne_zero_iff.1 (by rw [hn]; exact hc))
  have H2 : ∀ c : A, c ≠ 0 → Nm d c → Nm δ c := by
    intro c hc hn
    obtain ⟨c', hc', hn'⟩ := (hA d hdA).1
    by_contra h
    exact hn' (Nm.of_mul hc hn (H1 _ (mul_ne_zero hc' hc)
      ((hA δ hδ).2 c' c hc' hc (fun h => hn' (H1 _ hc' h)) h)))
  have hdδ : ¬ IsSquare (d * δ) := by
    rintro ⟨r, hr⟩
    have ht : e 1 ≠ 0 := e.ne_zero 1
    refine hd ⟨algebraMap A B r / e 1, ?_⟩
    have := congrArg (algebraMap A B) hr
    rw [map_mul, map_mul, ← h1] at this
    field_simp
    linear_combination this
  obtain ⟨c, hc0, hc⟩ := (hA _ hdδ).1
  have hcs : ¬ IsSquare c := fun h => hc (Nm.of_isSquare _ h)
  refine hc (Nm.symm two_ne_zero (mul_ne_zero hd0 hδ0) ?_)
  by_cases h : Nm c d
  · exact h.mul ((H2 c hc0 (h.symm two_ne_zero hd0)).symm two_ne_zero hc0)
  · exact (hA c hcs).2 d δ hd0 hδ0 h
      fun h' => h ((H1 c hc0 (h'.symm two_ne_zero hδ0)).symm two_ne_zero hc0)

end Tower

section Galois

variable {A : Type} [Field A] [CharZero A]
  (hA : ∀ (B : Type) [Field B] [Algebra A B] [FiniteDimensional A B], IndexTwo B)

include hA

theorem normsEscape_of_pow_two (M : Type) [Field M] [Algebra A M] [FiniteDimensional A M]
    [IsGalois A M] : ∀ (m : ℕ) (K : IntermediateField A M) (n : ℕ), Module.finrank A K = m →
      Module.finrank K M = 2 ^ n → NormsEscape A K := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro K n hm hn
    rcases Nat.even_or_odd (Module.finrank A K) with hev | hodd
    swap
    · exact normsEscape_of_odd (hA A) hodd
    have hdvd : 2 ^ (n + 1) ∣ Nat.card (M ≃ₐ[A] M) := by
      rw [IsGalois.card_aut_eq_finrank, ← Module.finrank_mul_finrank A K M, hn, pow_succ']
      exact Nat.mul_dvd_mul_right hev.two_dvd _
    obtain ⟨H, hH, hle⟩ := Sylow.exists_subgroup_card_pow_succ (H := K.fixingSubgroup) hdvd
      (by rw [IsGalois.card_fixingSubgroup_eq_finrank, hn])
    let K' := IntermediateField.fixedField H
    have hK' : K' ≤ K := by
      rw [← IsGalois.fixedField_fixingSubgroup K]
      exact IntermediateField.fixedField_le hle
    have hn' : Module.finrank K' M = 2 ^ (n + 1) := by
      rw [IntermediateField.finrank_fixedField_eq_card, hH]
    letI : Algebra K' K := (IntermediateField.inclusion hK').toRingHom.toAlgebra
    haveI : IsScalarTower A K' K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower K' K M := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : FiniteDimensional K' K := Module.Finite.of_restrictScalars_finite A K' K
    have h2 : Module.finrank K' K = 2 := by
      have := Module.finrank_mul_finrank K' K M
      rw [hn, hn', pow_succ'] at this
      exact Nat.eq_of_mul_eq_mul_right (by positivity) this
    have hlt : Module.finrank A K' < m := by
      have := Module.finrank_mul_finrank A K' K
      have hpos : 0 < Module.finrank A K' := Module.finrank_pos
      rw [h2, hm] at this
      omega
    haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap A K').injective
    exact NormsEscape.trans (hA K') (ih _ hlt K' _ rfl hn') (normsEscape_of_two (hA K') h2)

theorem normsEscape (B : Type) [Field B] [Algebra A B] [FiniteDimensional A B] :
    NormsEscape A B := by
  let M := IntermediateField.normalClosure A B (AlgebraicClosure B)
  haveI : IsGalois A M := {}
  haveI : FiniteDimensional B M := Module.Finite.of_restrictScalars_finite A B M
  haveI : IsGalois B M := IsGalois.tower_top_of_isGalois A B M
  let P : Sylow 2 (M ≃ₐ[B] M) := default
  let C := IntermediateField.fixedField (P : Subgroup (M ≃ₐ[B] M))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 P.isPGroup'
  have hC : Module.finrank C M = 2 ^ n := by
    rw [IntermediateField.finrank_fixedField_eq_card, hn]
  have hodd : Odd (Module.finrank B C) := by
    have h1 := Module.finrank_mul_finrank B C M
    have h2 := (P : Subgroup (M ≃ₐ[B] M)).index_mul_card
    rw [IsGalois.card_aut_eq_finrank, ← h1, hn, hC] at h2
    rw [← Nat.eq_of_mul_eq_mul_right (by positivity) h2, ← Nat.not_even_iff_odd,
      even_iff_two_dvd]
    exact P.not_dvd_index
  have h : NormsEscape A C :=
    normsEscape_of_pow_two hA M _ (C.restrictScalars A) n rfl hC
  exact h.of_odd_top hodd

end Galois

section Finite

open GlobalTheory.CNorm

theorem indexTwo_finite (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (B : Type) [Field B] [Algebra (v.adicCompletion F) B]
    [FiniteDimensional (v.adicCompletion F) B] : IndexTwo B := by
  first
  | (rename_i h_1 h_2 h_5 h_6 h_7; revert F h_1 h_2 v B h_5 h_6 h_7; exact @_root_.GlobalTheory.QuadraticValuationIndexTwo.norm_index_two)
  | exact @_root_.GlobalTheory.QuadraticValuationIndexTwo.norm_index_two
  | exact _root_.GlobalTheory.QuadraticValuationIndexTwo.norm_index_two
  | (apply _root_.GlobalTheory.QuadraticValuationIndexTwo.norm_index_two <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuadraticValuationIndexTwo.norm_index_two <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuadraticValuationIndexTwo.norm_index_two <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuadraticValuationIndexTwo.norm_index_two ..)

end Finite

theorem baseChangeAt (F E K L A : Type) [Field F] [CharZero F] [Field E] [Field K] [Field L]
    [Field A] [Algebra F E] [Algebra F K] [Algebra K L] [Algebra E L] [Algebra F L] [Algebra F A]
    [IsScalarTower F K L] [IsScalarTower F E L] (hE : Module.finrank F E = 2)
    (hL : Module.finrank K L = 2) (hgen : Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤)
    (hA : ∀ (B : Type) [Field B] [Algebra A B] [FiniteDimensional A B], IndexTwo B) :
    BaseChangeAt F E K L A := by
  haveI : CharZero A := charZero_of_injective_algebraMap (algebraMap F A).injective
  obtain ⟨δ, e, hδ, h0, h1⟩ := exists_sqrt_basis F E hE
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  have hli : LinearIndependent K ![(1 : L), algebraMap E L (e 1)] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro c hc
    have hbot : (⊤ : Subalgebra K L) ≤ ⊥ := by
      rw [← hgen, Algebra.adjoin_le_iff]
      rintro _ ⟨y, rfl⟩
      rw [← e.sum_repr y, Fin.sum_univ_two, h0, map_add, Algebra.smul_def, Algebra.smul_def,
        map_mul, map_mul, map_one, ← hc, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F K L,
        IsScalarTower.algebraMap_apply F K L]
      exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (one_mem _))
        (mul_mem (Subalgebra.algebraMap_mem _ _) (Subalgebra.smul_mem _ (one_mem _) _))
    have := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 (top_le_iff.1 hbot)
    omega
  let e' : Module.Basis (Fin 2) K L := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hL])
  have h0' : e' 0 = 1 := by simp [e']
  have h1' : e' 1 * e' 1 = algebraMap K L (algebraMap F K δ) := by
    have : e' 1 = algebraMap E L (e 1) := by simp [e']
    rw [this, ← map_mul, h1, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  intro B _ _ _ _ _ _ _ x
  have key : x ∈ normGroup K L B ↔
      Units.map (Algebra.norm A : B →* A) x ∈ normGroup F E A := by
    rw [mem_normGroup_iff_form e' h0' h1', mem_normGroup_iff_form e h0 h1,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F A B]
    exact nm_iff (hA B) (normsEscape hA B) ((map_ne_zero _).2 hδ0) x.ne_zero
  unfold eta
  rw [key]

end NormBaseChange

open NormBaseChange in

theorem baseChange : ∀ (F E K L : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra F E] [Algebra F K] [Algebra K L]
    [Algebra E L] [Algebra F L] [IsScalarTower F K L] [IsScalarTower F E L]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsQuadraticExtension K L],
    Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ →
    (∀ v : HeightOneSpectrum (𝓞 F), BaseChangeAt F E K L (v.adicCompletion F)) ∧
    ∀ v : InfinitePlace F, BaseChangeAt F E K L v.Completion := by
  intro F E K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hgen
  have hE := Algebra.IsQuadraticExtension.finrank_eq_two F E
  have hL := Algebra.IsQuadraticExtension.finrank_eq_two K L
  exact ⟨fun v => baseChangeAt F E K L _ hE hL hgen (indexTwo_finite F v),
    fun w => baseChangeAt F E K L _ hE hL hgen (indexTwo_infinite F w)⟩

end GlobalTheory.QuadSymbol
