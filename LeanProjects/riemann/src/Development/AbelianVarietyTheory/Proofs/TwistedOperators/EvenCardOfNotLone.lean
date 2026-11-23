import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSquareMulInfinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlmostNormFinDiag
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsApproxModLocalSquares
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLocalNonnormOfNonsquareAdicCompletion
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexSquaresSUnitsNumberField
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitValuationEqOfAdm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissibleSupersetFinitePlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsQuadraticSqrtExtensionOfNotSquare
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsQuadraticSqrtExtensionBasicFacts
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsSupUnitsLocalNormsSqrtNeTop
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingHomAdicCompletionUnder
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAuxiliaryPlacesSquarePatternsSUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsUnionSupLocalSquaresEqTop
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfSUnitLocalSquareFiniteRealPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitMemGlobalNormOfMemLocalNorms
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexUnitsLocalSquaresFiniteRealPlacesLe

open NumberField IsDedekindDomain GlobalTheory.QNorm GlobalTheory.QuadSymbol.NormIndex

noncomputable section

namespace GlobalTheory.HilbertRecip

abbrev Place (F : Type) [Field F] [NumberField F] : Type :=
  HeightOneSpectrum (𝓞 F) ⊕ (F →+* ℝ)

variable {F : Type} [Field F] [NumberField F]

def nrm : Place F → Fˣ → Subgroup Fˣ
  | .inl v, δ => normSub (algebraMap F (v.adicCompletion F)) (δ : F)
  | .inr σ, δ => normSub σ (δ : F)

def sqr : Place F → Subgroup Fˣ
  | .inl v => sqSub (algebraMap F (v.adicCompletion F))
  | .inr σ => sqSub σ

def Over (S : Finset (HeightOneSpectrum (𝓞 F))) : Place F → Prop
  | .inl v => v ∈ S
  | .inr _ => True

def Lone (p : Place F) : Prop := ∃ a b : Fˣ, a ∉ nrm p b ∧ ∀ q, q ≠ p → a ∈ nrm q b

open Classical in

def hs (p : Place F) (a b : Fˣ) : ℤˣ := if a ∈ nrm p b then 1 else -1

theorem hs_eq_one_iff {p : Place F} {a b : Fˣ} : hs p a b = 1 ↔ a ∈ nrm p b := by
  have h1 : (-1 : ℤˣ) ≠ 1 := by decide
  unfold hs
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false h1 h

theorem hs_eq_neg_one_iff {p : Place F} {a b : Fˣ} : hs p a b = -1 ↔ a ∉ nrm p b := by
  have h1 : (1 : ℤˣ) ≠ -1 := by decide
  unfold hs
  split_ifs with h
  · exact iff_of_false h1 (not_not.mpr h)
  · exact iff_of_true rfl h

theorem exists_field (p : Place F) : ∃ (A : Type) (_ : Field A) (_ : CharZero A) (φ : F →+* A),
    (∀ δ : Fˣ, nrm p δ = normSub φ (δ : F)) ∧ sqr p = sqSub φ ∧
    ∀ d x y : A, d ≠ 0 → x ≠ 0 → y ≠ 0 → ¬ Nm d x → ¬ Nm d y → Nm d (x * y) := by
  rcases p with v | σ
  · haveI : CharZero (v.adicCompletion F) :=
      charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
    refine ⟨v.adicCompletion F, inferInstance, inferInstance, algebraMap F (v.adicCompletion F),
      fun δ => rfl, rfl, ?_⟩
    intro d x y hd hx hy hnx hny
    exact nm_mul_adicCompletion F v hd hx hy hnx hny
  · refine ⟨ℝ, inferInstance, inferInstance, σ, fun δ => rfl, rfl, ?_⟩
    intro d x y _ _ _ hnx hny
    have key : ∀ z : ℝ, 0 ≤ z → Nm d z := fun z hz =>
      ⟨Real.sqrt z, 0, by rw [Real.sq_sqrt hz]; ring⟩
    have hx' : x < 0 := by
      by_contra h
      exact hnx (key x (not_lt.mp h))
    have hy' : y < 0 := by
      by_contra h
      exact hny (key y (not_lt.mp h))
    exact key _ (mul_pos_of_neg_of_neg hx' hy').le

theorem nrm_symm {p : Place F} {a b : Fˣ} (h : a ∈ nrm p b) : b ∈ nrm p a := by
  obtain ⟨A, _, _, φ, hn, -, -⟩ := exists_field p
  simp only [hn, mem_normSub] at h ⊢
  exact Nm.symm (two_ne_zero : (2 : A) ≠ 0) ((map_ne_zero φ).mpr a.ne_zero) h

theorem mul_mem_nrm_of_not {p : Place F} {a a' b : Fˣ} (h : a ∉ nrm p b) (h' : a' ∉ nrm p b) :
    a * a' ∈ nrm p b := by
  obtain ⟨A, _, _, φ, hn, -, hm⟩ := exists_field p
  simp only [hn, mem_normSub] at h h' ⊢
  simp only [Units.val_mul, map_mul]
  exact hm _ _ _ ((map_ne_zero φ).mpr b.ne_zero) ((map_ne_zero φ).mpr a.ne_zero)
    ((map_ne_zero φ).mpr a'.ne_zero) h h'

theorem sqr_le_nrm (p : Place F) (b : Fˣ) : sqr p ≤ nrm p b := by
  obtain ⟨A, _, _, φ, hn, hs, -⟩ := exists_field p
  rw [hn, hs]
  exact sqSub_le_normSub φ _

theorem mem_nrm_of_sqr {p : Place F} {b : Fˣ} (h : b ∈ sqr p) (a : Fˣ) : a ∈ nrm p b := by
  obtain ⟨A, _, _, φ, hn, hs, -⟩ := exists_field p
  rw [hn]
  rw [hs] at h
  exact mem_normSub_of_isSquare φ b ((mem_sqSub φ b).mp h) a

theorem mem_sqr_of_isSquare (p : Place F) {b : Fˣ} (h : IsSquare (b : F)) : b ∈ sqr p := by
  obtain ⟨A, _, _, φ, -, hs, -⟩ := exists_field p
  rw [hs, mem_sqSub]
  exact h.map φ

theorem sq_mem_sqr (p : Place F) (b : Fˣ) : b ^ 2 ∈ sqr p := mem_sqr_of_isSquare p ⟨b, by push_cast; ring⟩

theorem mem_nrm_of_eq (p : Place F) {a δ : Fˣ} {x y : F} (h : (a : F) = x ^ 2 - δ * y ^ 2) :
    a ∈ nrm p δ := by
  obtain ⟨A, _, _, φ, hn, -, -⟩ := exists_field p
  rw [hn, mem_normSub]
  exact ⟨φ x, φ y, by rw [h, map_sub, map_mul, map_pow, map_pow]⟩

theorem neg_mem_nrm (p : Place F) (b : Fˣ) : -b ∈ nrm p b := mem_nrm_of_eq p (x := 0) (y := 1) (by rw [Units.val_neg]; ring)

theorem hs_comm (p : Place F) (a b : Fˣ) : hs p a b = hs p b a := by
  unfold hs
  by_cases h : a ∈ nrm p b
  · rw [if_pos h, if_pos (nrm_symm h)]
  · rw [if_neg h, if_neg (fun h' => h (nrm_symm h'))]

theorem hs_mul_left (p : Place F) (a a' b : Fˣ) : hs p (a * a') b = hs p a b * hs p a' b := by
  unfold hs
  by_cases h : a ∈ nrm p b <;> by_cases h' : a' ∈ nrm p b
  · rw [if_pos h, if_pos h', if_pos (mul_mem h h'), mul_one]
  · rw [if_pos h, if_neg h', if_neg, one_mul]
    intro hm
    exact h' (by simpa using mul_mem (inv_mem h) hm)
  · rw [if_neg h, if_pos h', if_neg, mul_one]
    intro hm
    exact h (by simpa using mul_mem hm (inv_mem h'))
  · rw [if_neg h, if_neg h', if_pos (mul_mem_nrm_of_not h h')]
    decide

theorem hs_mul_right (p : Place F) (a b b' : Fˣ) : hs p a (b * b') = hs p a b * hs p a b' := by
  rw [hs_comm p a (b * b'), hs_mul_left, hs_comm p b a, hs_comm p b' a]

theorem hs_mul_self (p : Place F) (a b : Fˣ) : hs p a b * hs p a b = 1 := Int.units_mul_self _

theorem mem_locNorm_iff {S : Finset (HeightOneSpectrum (𝓞 F))} {δ x : Fˣ} :
    x ∈ locNorm F (δ : F) S ↔ ∀ p, Over S p → x ∈ nrm p δ := by
  simp only [locNorm, Subgroup.mem_inf, Subgroup.mem_iInf]
  constructor
  · rintro ⟨h1, h2⟩ (v | σ) hp
    · exact h1 v hp
    · exact h2 σ
  · intro h
    exact ⟨fun v hv => h (.inl v) hv, fun σ => h (.inr σ) trivial⟩

theorem mem_locSq_iff {S : Finset (HeightOneSpectrum (𝓞 F))} {x : Fˣ} :
    x ∈ locSq F S ↔ ∀ p, Over S p → x ∈ sqr p := by
  simp only [locSq, finSq, Subgroup.mem_inf, Subgroup.mem_iInf]
  constructor
  · rintro ⟨h1, h2⟩ (v | σ) hp
    · exact h1 v hp
    · exact h2 σ
  · intro h
    exact ⟨fun v hv => h (.inl v) hv, fun σ => h (.inr σ) trivial⟩

theorem finite_over (S : Finset (HeightOneSpectrum (𝓞 F))) : {p : Place F | Over S p}.Finite := by
  have hsub : {p : Place F | Over S p} ⊆ (Sum.inl '' (S : Set (HeightOneSpectrum (𝓞 F)))) ∪
      Set.range Sum.inr := by
    rintro (v | σ) hp
    · exact Or.inl ⟨v, hp, rfl⟩
    · exact Or.inr ⟨σ, rfl⟩
  exact ((S.finite_toSet.image _).union (Set.finite_range _)).subset hsub

theorem Over.mono {S T : Finset (HeightOneSpectrum (𝓞 F))} (h : S ⊆ T) {p : Place F}
    (hp : Over S p) : Over T p := by
  cases p with
  | inl v => exact h hp
  | inr σ => trivial

theorem exists_over (p : Place F) : ∃ S, Over S p := by
  cases p with
  | inl v => exact ⟨{v}, Finset.mem_singleton_self v⟩
  | inr σ => exact ⟨∅, trivial⟩

private lemma not_nm_of_valuation_eq_exp_neg_one {K : Type} [Field K] (w : Valuation K (WithZero (Multiplicative ℤ))) {B z : K}
    (hE : EvenNorms w B) (hz : w z = WithZero.exp (-1)) : ¬ Nm B z := by
  rintro ⟨x, y, rfl⟩
  have hne : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    rw [hc.1, hc.2] at hz
    have h0 : w ((0 : K) ^ 2 - B * 0 ^ 2) = 0 := by simp
    rw [h0] at hz
    exact WithZero.exp_ne_zero hz.symm
  obtain ⟨n, hn⟩ := hE x y hne
  rw [hn, WithZero.exp_inj] at hz
  omega

private lemma isSquare_of_valued_sub_one_lt_four {v : HeightOneSpectrum (𝓞 F)}
    (h2 : Valued.v (2 : v.adicCompletion F) = 1) (x : v.adicCompletion F)
    (hx : Valued.v (x - 1) < Valued.v (4 : v.adicCompletion F)) : IsSquare x := by
  have h4 : Valued.v (4 : v.adicCompletion F) = 1 := by
    rw [show (4 : v.adicCompletion F) = 2 * 2 by norm_num, map_mul, h2, one_mul]
  rw [h4] at hx
  by_cases hx1 : x - 1 = 0
  · rw [sub_eq_zero.1 hx1]
    exact ⟨1, by simp⟩
  obtain ⟨n, hn⟩ := Defect.exists_exp Valued.v hx1
  have hxv : Valued.v x = 1 := by
    have hsplit : x = (x - 1) + 1 := by ring
    rw [hsplit, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one])]
    exact map_one _
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hxv
    exact zero_ne_one hxv
  have hle : Valued.v (x - 1) ≤ WithZero.exp (-(((2 * 0 + 1 : ℕ)) : ℤ)) := by
    rw [hn] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    push_cast
    omega
  have hmem : Units.mk0 x hx0 ∈
      hiUnits (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (2 * 0 + 1) :=
    ⟨hxv, hle⟩
  obtain ⟨y, -, hy⟩ := hiUnits_le_sqs_hiUnits F v 0 (by rw [h2]; simp) hmem
  refine ⟨(y : v.adicCompletion F), ?_⟩
  have hyx := congrArg Units.val hy
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0] at hyx
  rw [← hyx, sq]

theorem mem_nrm_of_unit {v : HeightOneSpectrum (𝓞 F)} {a b : Fˣ} (h2 : v.valuation F 2 = 1)
    (ha : v.valuation F (a : F) = 1) (hb : v.valuation F (b : F) = 1) : a ∈ nrm (.inl v) b := by
  set K := v.adicCompletion F
  have hval : ∀ x : F, (Valued.v (algebraMap F K x) : WithZero (Multiplicative ℤ)) = v.valuation F x := fun x =>
    v.valuedAdicCompletion_eq_valuation' x
  show ∃ x y : K, algebraMap F K (a : F) = x ^ 2 - algebraMap F K (b : F) * y ^ 2
  have h2' : Valued.v (2 : K) = 1 := by
    have := hval 2
    rw [map_ofNat] at this
    rw [this, h2]
  have hK2 : (2 : K) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h2'
    exact zero_ne_one h2'
  have hA0 : algebraMap F K (a : F) ≠ 0 := (map_ne_zero _).2 a.ne_zero
  have hB0 : algebraMap F K (b : F) ≠ 0 := (map_ne_zero _).2 b.ne_zero
  by_cases hsq : IsSquare (algebraMap F K (b : F))
  · exact Nm.of_isSquare_left hK2 hB0 hsq _
  · have hB1 : Valued.v (algebraMap F K (b : F)) = 1 := by rw [hval, hb]
    have h4 : Valued.v (4 : K) = 1 := by
      rw [show (4 : K) = 2 * 2 by norm_num, map_mul, h2', one_mul]
    have hle : Valued.v (algebraMap F K (b : F) - 1) ≤ Valued.v (4 : K) := by
      rw [h4]
      refine (Valuation.map_sub _ _ _).trans ?_
      rw [hB1, map_one, max_self]
    have hE := Defect.evenNorms_of_le_four Valued.v hK2 (isSquare_of_valued_sub_one_lt_four h2') _ hB1 hsq hle
    by_contra hA
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    have hP : Valued.v (algebraMap F K π) = WithZero.exp (-1) := by rw [hval, hπ]
    have hP0 : algebraMap F K π ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hP
      exact WithZero.exp_ne_zero hP.symm
    have hPn := not_nm_of_valuation_eq_exp_neg_one _ hE hP
    have hprod := nm_mul_adicCompletion F v hB0 hA0 hP0 hA hPn
    refine not_nm_of_valuation_eq_exp_neg_one _ hE ?_ hprod
    rw [map_mul, hval, ha, one_mul, hP]

theorem mem_nrm_of_not_over {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : admitted F S) {a b : Fˣ}
    (ha : a ∈ sUnits F S) (hb : b ∈ sUnits F S) {p : Place F} (hp : ¬ Over S p) : a ∈ nrm p b := by
  cases p with
  | inl v =>
    have hv : v ∉ S := hp
    exact mem_nrm_of_unit (hS v hv).1 ((mem_sUnits F S a).1 ha v hv) ((mem_sUnits F S b).1 hb v hv)
  | inr σ => exact (hp (show Over S (Sum.inr σ) from trivial)).elim

theorem sUnits_mono {S T : Finset (HeightOneSpectrum (𝓞 F))} (h : S ⊆ T) :
    sUnits F S ≤ sUnits F T := by
  intro x hx
  rw [mem_sUnits] at hx ⊢
  exact fun v hv => hx v (fun h' => hv (h h'))

theorem exists_approx (S : Finset (HeightOneSpectrum (𝓞 F))) (y : Place F → Fˣ) :
    ∃ x : Fˣ, ∀ p, Over S p → x * y p ∈ sqr p := by
  obtain ⟨x, hx0, hS, hR⟩ := exists_approx_mod_squares F S
    (fun v => algebraMap F (v.adicCompletion F) (y (.inl v) : F)) (fun σ => σ (y (.inr σ) : F))
    (fun v => (map_ne_zero _).2 (y _).ne_zero) (fun σ => (map_ne_zero _).2 (y _).ne_zero)
  refine ⟨Units.mk0 x hx0, fun p hp => ?_⟩
  cases p with
  | inl v =>
    show _ ∈ sqSub _
    rw [mem_sqSub, Units.val_mul, Units.val_mk0, map_mul]
    exact hS v hp
  | inr σ =>
    show _ ∈ sqSub _
    rw [mem_sqSub, Units.val_mul, Units.val_mk0, map_mul]
    have h := hR σ
    exact ⟨Real.sqrt _, (Real.mul_self_sqrt h.le).symm⟩

theorem exists_not_mem_nrm {p : Place F} {b : Fˣ} (h : b ∉ sqr p) : ∃ a : Fˣ, a ∉ nrm p b := by
  classical
  cases p with
  | inl v =>
    set K := v.adicCompletion F
    have hb : ¬ IsSquare (algebraMap F K (b : F)) := fun hs => h ((mem_sqSub _ _).2 hs)
    obtain ⟨x, hx0, hxn⟩ := exists_local_nonnorm F v (algebraMap F K (b : F))
      ((map_ne_zero _).2 b.ne_zero) hb
    obtain ⟨t, ht0, htS, -⟩ := exists_approx_mod_squares F {v}
      (Pi.mulSingle v x) (fun _ => 1)
      (fun w => by
        by_cases hw : w = v
        · subst hw
          simpa using hx0
        · rw [Pi.mulSingle_eq_of_ne hw]
          exact one_ne_zero) (fun _ => one_ne_zero)
    refine ⟨Units.mk0 t ht0, fun hmem => hxn ?_⟩
    have hsq := htS v (Finset.mem_singleton_self v)
    rw [Pi.mulSingle_eq_same] at hsq
    have hmem' : ∃ c d : K, algebraMap F K (Units.mk0 t ht0 : F) =
        c ^ 2 - algebraMap F K (b : F) * d ^ 2 := hmem
    rw [Units.val_mk0] at hmem'
    exact norm_of_isSquare_mul ((map_ne_zero _).2 ht0) hsq hmem'
  | inr σ =>
    have hb : ¬ IsSquare (σ (b : F)) := fun hs => h ((mem_sqSub _ _).2 hs)
    have hneg : σ (b : F) < 0 := by
      by_contra hc
      push_neg at hc
      exact hb ⟨Real.sqrt _, (Real.mul_self_sqrt hc).symm⟩
    refine ⟨-1, fun hmem => ?_⟩
    obtain ⟨c, d, hcd⟩ : ∃ c d : ℝ, σ ((-1 : Fˣ) : F) = c ^ 2 - σ (b : F) * d ^ 2 := hmem
    simp only [Units.val_neg, Units.val_one, map_neg, map_one] at hcd
    nlinarith [sq_nonneg c, sq_nonneg d, mul_nonneg (neg_nonneg.2 hneg.le) (sq_nonneg d)]

theorem exists_single (S : Finset (HeightOneSpectrum (𝓞 F))) {p : Place F} (hp : Over S p)
    {b : Fˣ} (h : b ∉ sqr p) :
    ∃ x : Fˣ, x ∉ nrm p b ∧ ∀ q, Over S q → q ≠ p → x ∈ sqr q := by
  classical
  obtain ⟨a, ha⟩ := exists_not_mem_nrm h
  obtain ⟨x, hx⟩ := exists_approx S (fun q => if q = p then a else 1)
  refine ⟨x, fun hxm => ha ?_, fun q hq hqp => ?_⟩
  · have hxa : x * a ∈ sqr p := by simpa using hx p hp
    have h1 : x * a ∈ nrm p b := sqr_le_nrm p b hxa
    have h2 := (nrm p b).mul_mem ((nrm p b).inv_mem hxm) h1
    simpa using h2
  · simpa [hqp] using hx q hq

theorem finite_not_mem_nrm (a b : Fˣ) : {p : Place F | a ∉ nrm p b}.Finite := by
  classical
  obtain ⟨S₀, -, hS₀⟩ := exists_superset_mem_sUnits F {a, b} ∅
  obtain ⟨S, hS₀S, hadm⟩ := exists_admissible_superset_finite_places F S₀
  refine (finite_over S).subset fun p hp => ?_
  by_contra hno
  exact hp (mem_nrm_of_not_over hadm (hS₀ S hS₀S a (by simp)) (hS₀ S hS₀S b (by simp)) hno)

private lemma exists_vec_one_smul_mem_of_first_coord {p : Place F} {a δ b : Fˣ} (hb : b ∉ sqr p) :
    ∃ n₁ n₂ : Fˣ, a = n₁ * n₂ ∧ n₁ ∈ nrm p δ ∧ n₂ ∈ nrm p (b * δ) := by
  have hne : (1 : ℤˣ) ≠ -1 := by decide
  by_cases h1 : a ∈ nrm p δ
  · exact ⟨a, 1, (mul_one a).symm, h1, one_mem _⟩
  by_cases h2 : a ∈ nrm p (b * δ)
  · exact ⟨1, a, (one_mul a).symm, one_mem _, h2⟩
  by_cases h3 : ∃ c, c ∈ nrm p δ ∧ c ∉ nrm p (b * δ)
  · obtain ⟨c, hc1, hc2⟩ := h3
    exact ⟨c⁻¹, c * a, (inv_mul_cancel_left c a).symm, inv_mem hc1, mul_mem_nrm_of_not hc2 h2⟩
  push_neg at h3
  exfalso
  obtain ⟨x, hx⟩ := exists_not_mem_nrm hb
  have key : ∀ c : Fˣ, hs p c b = -1 → hs p c δ = -1 := by
    intro c hc
    by_contra hcd
    have hcd' : c ∈ nrm p δ := hs_eq_one_iff.1 ((Int.units_eq_one_or _).resolve_right hcd)
    have e : hs p c (b * δ) = 1 := hs_eq_one_iff.2 (h3 c hcd')
    rw [hs_mul_right, hc, hs_eq_one_iff.2 hcd', mul_one] at e
    exact hne e.symm
  have hxb : hs p x b = -1 := hs_eq_neg_one_iff.2 hx
  have hxd := key x hxb
  have had : hs p a δ = -1 := hs_eq_neg_one_iff.2 h1
  have habd : hs p a (b * δ) = -1 := hs_eq_neg_one_iff.2 h2
  have hab : hs p a b = 1 := by
    rw [hs_mul_right, had] at habd
    rcases Int.units_eq_one_or (hs p a b) with h | h
    · exact h
    · rw [h, neg_one_mul, neg_neg] at habd
      exact absurd habd hne
  have hh := key (a * x) (by rw [hs_mul_left, hab, hxb, one_mul])
  rw [hs_mul_left, had, hxd, neg_one_mul, neg_neg] at hh
  exact hne hh

theorem exists_coords {p : Place F} {a δ b : Fˣ} (hb : b ∉ sqr p)
    (h : ∀ q, q ≠ p → a ∈ nrm q δ) : ∃ x₀ x₁ y₀ y₁ : F,
      (a : F) = x₀ ^ 2 - δ * y₀ ^ 2 + b * (x₁ ^ 2 - δ * y₁ ^ 2) ∧ x₀ * x₁ - δ * (y₀ * y₁) = 0 := by
  have hbF : ¬ IsSquare (b : F) := fun h' => hb (mem_sqr_of_isSquare p h')
  obtain ⟨E, _, _, _, θ, σ, hq⟩ := exists_isQuad F (b : F) hbF
  obtain ⟨n₁, n₂, hn, hn₁, hn₂⟩ := exists_vec_one_smul_mem_of_first_coord (a := a) (δ := δ) hb
  have hδ0 : algebraMap F E (δ : F) ≠ 0 := by simp
  have ha0 : algebraMap F E (a : F) ≠ 0 := by simp
  have hreal : ∀ τ : E →+* ℝ, ∃ A B : ℝ,
      τ (algebraMap F E a) = A ^ 2 - τ (algebraMap F E δ) * B ^ 2 := by
    intro τ
    have hne : (Sum.inr (τ.comp (algebraMap F E)) : Place F) ≠ p := by
      intro hp
      apply hb
      rw [← hp]
      show b ∈ sqSub (τ.comp (algebraMap F E))
      rw [mem_sqSub]
      refine ⟨τ θ, ?_⟩
      rw [RingHom.comp_apply, ← hq.sq, map_pow, sq]
    obtain ⟨A, B, hAB⟩ := (mem_normSub (τ.comp (algebraMap F E)) (δ : F) a).1 (h _ hne)
    exact ⟨A, B, hAB⟩
  have hfin : ∀ w : HeightOneSpectrum (𝓞 E), ∃ A B : w.adicCompletion E,
      algebraMap E (w.adicCompletion E) (algebraMap F E a) =
        A ^ 2 - algebraMap E (w.adicCompletion E) (algebraMap F E δ) * B ^ 2 := by
    intro w
    obtain ⟨ψ, hψ⟩ := exists_ringHom_adicCompletion_under F E w
    by_cases hqp : (Sum.inl (w.under (𝓞 F)) : Place F) = p
    · subst hqp
      obtain ⟨A, B, hAB⟩ := (mem_normSub _ _ n₁).1 hn₁
      obtain ⟨C, D, hCD⟩ := (mem_normSub _ _ n₂).1 hn₂
      have ht : (algebraMap E (w.adicCompletion E) θ) ^ 2 =
          ψ (algebraMap F ((w.under (𝓞 F)).adicCompletion F) (b : F)) := by
        rw [hψ, ← hq.sq, map_pow]
      refine ⟨ψ A * ψ C + ψ (algebraMap F _ (δ : F)) * ψ B * algebraMap E (w.adicCompletion E) θ * ψ D,
        ψ A * algebraMap E (w.adicCompletion E) θ * ψ D + ψ B * ψ C, ?_⟩
      rw [← hψ, ← hψ, hn, Units.val_mul, map_mul, map_mul, hAB, hCD]
      simp only [map_sub, map_mul, map_pow, Units.val_mul]
      linear_combination (ψ A ^ 2 - ψ (algebraMap F _ (δ : F)) * ψ B ^ 2) *
        ψ (algebraMap F _ (δ : F)) * ψ D ^ 2 * ht
    · obtain ⟨A, B, hAB⟩ := (mem_normSub _ _ a).1 (h _ hqp)
      refine ⟨ψ A, ψ B, ?_⟩
      rw [← hψ, ← hψ, hAB]
      simp only [map_sub, map_mul, map_pow]
  obtain ⟨X, Y, hXY⟩ := hasseNormSt E (algebraMap F E δ) (algebraMap F E a) hδ0 ha0 hreal hfin
  obtain ⟨x₀, x₁, hX⟩ := hq.span X
  obtain ⟨y₀, y₁, hY⟩ := hq.span Y
  have e := hq.coord_indep ((x₀ ^ 2 - δ * y₀ ^ 2 + b * (x₁ ^ 2 - δ * y₁ ^ 2)) - a)
    (2 * (x₀ * x₁ - δ * (y₀ * y₁))) (by
      rw [hX, hY] at hXY
      have hθ := hq.sq
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
      linear_combination (-1 : E) * hXY - ((algebraMap F E x₁) ^ 2 -
        algebraMap F E (δ : F) * (algebraMap F E y₁) ^ 2) * hθ)
  refine ⟨x₀, x₁, y₀, y₁, by linear_combination -e.1, ?_⟩
  exact (mul_eq_zero.1 e.2).resolve_left two_ne_zero

private lemma hs_mul_sq_right (q : Place F) (a b c : Fˣ) : hs q a (b * c ^ 2) = hs q a b := by
  rw [hs_mul_right, hs_eq_one_iff.mpr (mem_nrm_of_sqr (sq_mem_sqr q c) a), mul_one]

theorem hs_of_add (q : Place F) {α β γ : Fˣ} (h : (α : F) + β = γ) :
    hs q α β = hs q (-(α * β)) γ := by
  have hinv : ∀ x : Fˣ, hs q x γ⁻¹ = hs q x γ := by
    intro x
    have e : γ⁻¹ = γ * γ⁻¹ ^ 2 := by group
    rw [e, hs_mul_sq_right]
  have h1 : hs q (α * γ⁻¹) (β * γ⁻¹) = 1 := by
    rw [hs_eq_one_iff]
    apply mem_nrm_of_eq q (x := 1) (y := 1)
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, one_pow, mul_one]
    rw [eq_sub_iff_add_eq, ← add_mul, h, mul_inv_cancel₀ γ.ne_zero]
  have e1 : hs q (α * γ⁻¹) (β * γ⁻¹) = hs q α β * hs q α γ * (hs q β γ * hs q γ γ) := by
    rw [hs_mul_left q α γ⁻¹, hs_mul_right q α β γ⁻¹, hinv α, hs_comm q γ⁻¹ (β * γ⁻¹),
      hinv (β * γ⁻¹), hs_mul_left q β γ⁻¹ γ, hs_comm q γ⁻¹ γ, hinv γ]
  have e2 : hs q (-(α * β)) γ = hs q (-1) γ * hs q α γ * hs q β γ := by
    have e : -(α * β) = -1 * α * β := by rw [mul_assoc, neg_one_mul]
    rw [e, hs_mul_left, hs_mul_left]
  have e3 : hs q (-1) γ * hs q γ γ = 1 := by
    rw [← hs_mul_left, neg_one_mul]
    exact hs_eq_one_iff.mpr (neg_mem_nrm q γ)
  rw [e2]
  rw [e1] at h1
  rcases Int.units_eq_one_or (hs q α β) with hA | hA <;>
  rcases Int.units_eq_one_or (hs q α γ) with hB | hB <;>
  rcases Int.units_eq_one_or (hs q β γ) with hC | hC <;>
  rcases Int.units_eq_one_or (hs q γ γ) with hD | hD <;>
  rcases Int.units_eq_one_or (hs q (-1) γ) with hE | hE <;>
  rw [hA, hB, hC, hD] at h1 <;> rw [hD, hE] at e3 <;> rw [hA, hB, hC, hE] <;>
  revert h1 e3 <;> decide

theorem hs_sq_right (q : Place F) (a b c : Fˣ) : hs q a (b * c ^ 2) = hs q a b := by
  rw [hs_mul_right, hs_eq_one_iff.mpr (mem_nrm_of_sqr (sq_mem_sqr q c) a), mul_one]

theorem Lone.exists_left {p : Place F} (hp : Lone p) {b : Fˣ} (hb : b ∉ sqr p) :
    ∃ c : Fˣ, c ∉ nrm p b ∧ ∀ q, q ≠ p → c ∈ nrm q b := by
  obtain ⟨a, d, had, hq⟩ := hp
  suffices h : ∃ c : Fˣ, ∀ q, hs q c b = hs q a d by
    obtain ⟨c, hc⟩ := h
    refine ⟨c, ?_, fun q hq' => ?_⟩
    · rw [← hs_eq_neg_one_iff, hc, hs_eq_neg_one_iff]
      exact had
    · rw [← hs_eq_one_iff, hc, hs_eq_one_iff]
      exact hq q hq'
  have hdns : ¬ IsSquare (d : F) := fun h' => had (mem_nrm_of_sqr (mem_sqr_of_isSquare p h') a)
  obtain ⟨x₀, x₁, y₀, y₁, ha, h0⟩ := exists_coords hb hq
  have hN1 : x₁ ^ 2 - d * y₁ ^ 2 ≠ 0 := by
    intro h1
    apply had
    have hy : y₁ = 0 := by
      by_contra hy
      exact hdns ⟨x₁ / y₁, by
        rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hy hy)]
        linear_combination -h1⟩
    have hx : x₁ = 0 := by
      subst hy
      simpa using h1
    exact mem_nrm_of_eq p (x := x₀) (y := y₀) (by rw [ha, hx, hy]; ring)
  by_cases hN0 : x₀ ^ 2 - d * y₀ ^ 2 = 0
  · have hy : y₀ = 0 := by
      by_contra hy
      exact hdns ⟨x₀ / y₀, by
        rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hy hy)]
        linear_combination -hN0⟩
    have hx : x₀ = 0 := by
      subst hy
      simpa using hN0
    refine ⟨d, fun q => ?_⟩
    have hbW : b = a * Units.mk0 _ hN1 * ((Units.mk0 _ hN1)⁻¹) ^ 2 := by
      ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [ha, hx, hy]
      field_simp
      ring
    rw [hbW, hs_sq_right, hs_mul_right, hs_comm q d a, hs_comm q d (Units.mk0 _ hN1),
      hs_eq_one_iff.2 (mem_nrm_of_eq q (a := Units.mk0 _ hN1) (δ := d) (x := x₁) (y := y₁) (by simp)), mul_one]
  · have huw : (x₀ ^ 2 - d * y₀ ^ 2) * (x₁ ^ 2 - d * y₁ ^ 2) = -(d * (x₀ * y₁ - x₁ * y₀) ^ 2) := by
      linear_combination (x₀ * x₁ - d * (y₀ * y₁)) * h0
    have hs0 : x₀ * y₁ - x₁ * y₀ ≠ 0 := fun h' =>
      mul_ne_zero hN0 hN1 (by rw [huw, h']; ring)
    have E1 : ((Units.mk0 _ hN0 : Fˣ) : F) + ((b * Units.mk0 _ hN1 : Fˣ) : F) = a := by
      simp only [Units.val_mul, Units.val_mk0]
      rw [ha]
    have E2 : -(Units.mk0 _ hN0 * (b * Units.mk0 _ hN1)) = b * d * (Units.mk0 _ hs0) ^ 2 := by
      ext
      simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
      linear_combination (-(b : F)) * huw
    have E3 : Units.mk0 _ hN1 = (d * -Units.mk0 _ hN0) * (Units.mk0 _ hs0 * (Units.mk0 _ hN0)⁻¹) ^ 2 := by
      ext
      simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
        Units.val_mk0]
      have hinv : (x₀ ^ 2 - d * y₀ ^ 2) * (x₀ ^ 2 - d * y₀ ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hN0
      linear_combination ((x₀ ^ 2 - d * y₀ ^ 2) * ((x₀ ^ 2 - d * y₀ ^ 2)⁻¹) ^ 2) * huw +
        (-(x₁ ^ 2 - d * y₁ ^ 2) * (1 + (x₀ ^ 2 - d * y₀ ^ 2) * (x₀ ^ 2 - d * y₀ ^ 2)⁻¹)) * hinv
    refine ⟨Units.mk0 _ hN0 * a, fun q => ?_⟩
    have e1 : hs q (Units.mk0 _ hN0) (b * Units.mk0 _ hN1) = hs q a b * hs q a d := by
      rw [hs_of_add q E1, E2, hs_comm, hs_sq_right, hs_mul_right]
    have e2 : hs q (Units.mk0 _ hN0) (Units.mk0 _ hN1) = 1 := by
      rw [E3, hs_sq_right, hs_mul_right, hs_comm q _ (-Units.mk0 _ hN0),
        hs_eq_one_iff.2 (neg_mem_nrm q (Units.mk0 _ hN0)), mul_one]
      exact hs_eq_one_iff.2 (mem_nrm_of_eq q (a := Units.mk0 _ hN0) (δ := d) (x := x₀) (y := y₀) (by simp))
    rw [hs_mul_right, e2, mul_one] at e1
    rw [hs_mul_left, e1, mul_comm (hs q a b), mul_assoc, hs_mul_self, mul_one]

theorem exists_index_le_two {δ : Fˣ} (hns : ¬ IsSquare (δ : F))
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : admitted F S) (hδ : δ ∈ sUnits F S) :
    ∃ S', S ⊆ S' ∧ (sUnits F S' ⊔ locNorm F δ S').index ∣ 2 := by
  classical
  obtain ⟨T, hdisj, hcard, hsqT, hpat⟩ := exists_auxiliary_places F δ S hS hδ hns
  refine ⟨S ∪ T, Finset.subset_union_left, ?_⟩
  set U := sUnits F (S ∪ T) with hUeq
  have htop : sUnits F (S ∪ T) ⊔ finSq F T = ⊤ := sUnits_union_sup_finSq_eq_top F S T hS hdisj hpat

  have hrel : (locSq F S).relIndex U = 2 ^ ((S ∪ T).card + Fintype.card (InfinitePlace F)) := by
    rw [← relIndex_sqs_sUnits F (S ∪ T)]
    unfold Subgroup.relIndex
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact mem_sqs_sUnits_of_isSquare F (S ∪ T) x x.2
        (isSquare_of_mem_locSq F S T hS htop x x.2 hx)
    · intro hx
      exact sqs_le_locSq F U S hx
  obtain ⟨hne, hle⟩ := index_locSq_le F S
  have hsplit := index_eq_relIndex_mul_index_sup U (locSq F S)
  rw [hrel] at hsplit
  have hcardST : (S ∪ T).card = S.card + T.card := Finset.card_union_of_disjoint hdisj
  have hpow : (4 : ℕ) ^ (S.card + Fintype.card (InfinitePlace F)) =
      2 ^ ((S ∪ T).card + Fintype.card (InfinitePlace F)) * 2 := by
    rw [hcardST, ← pow_succ, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    congr 1
    omega
  have hX : (U ⊔ locSq F S).index ≤ 2 := by
    have h1 : 2 ^ ((S ∪ T).card + Fintype.card (InfinitePlace F)) * (U ⊔ locSq F S).index ≤
        2 ^ ((S ∪ T).card + Fintype.card (InfinitePlace F)) * 2 := by
      rw [← hsplit, ← hpow]; exact hle
    exact Nat.le_of_mul_le_mul_left h1 (by positivity)
  have hX0 : (U ⊔ locSq F S).index ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsplit
    exact hne hsplit

  have hsqnorm : locSq F S ≤ locNorm F (δ : F) (S ∪ T) := by
    intro x hx
    rw [mem_locSq_iff] at hx
    rw [mem_locNorm_iff]
    intro p hp
    rcases p with v | σ
    · have hv : v ∈ S ∪ T := hp
      rcases Finset.mem_union.mp hv with hvS | hvT
      · exact sqr_le_nrm _ _ (hx (.inl v) hvS)
      · exact mem_nrm_of_sqr (p := .inl v) ((GlobalTheory.QNorm.mem_sqSub _ _).mpr (hsqT v hvT)) x
    · exact sqr_le_nrm _ _ (hx (.inr σ) trivial)
  have hdvd : (U ⊔ locNorm F (δ : F) (S ∪ T)).index ∣ (U ⊔ locSq F S).index :=
    Subgroup.index_dvd_of_le (sup_le_sup_left hsqnorm U)
  have hle2 : (U ⊔ locNorm F (δ : F) (S ∪ T)).index ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hX0) hdvd).trans hX
  have hpos : 0 < (U ⊔ locNorm F (δ : F) (S ∪ T)).index :=
    Nat.pos_of_ne_zero (fun h => hX0 (Nat.eq_zero_of_zero_dvd (h ▸ hdvd)))
  interval_cases h : (U ⊔ locNorm F (δ : F) (S ∪ T)).index <;> simp

def hsLeft (p : Place F) (b : Fˣ) : Fˣ →* ℤˣ := MonoidHom.mk' (fun a => hs p a b)
  fun a a' => hs_mul_left p a a' b

open Classical in
theorem hs_prod (L : Finset (Place F)) (c : Place F → Fˣ) (q : Place F) (b : Fˣ)
    (h1 : q ∈ L → c q ∉ nrm q b) (h2 : ∀ p ∈ L, p ≠ q → c p ∈ nrm q b) :
    hs q (∏ p ∈ L, c p) b = if q ∈ L then -1 else 1 := by
  have key : hs q (∏ p ∈ L, c p) b = ∏ p ∈ L, hs q (c p) b := by
    exact map_prod (hsLeft q b) c L
  rw [key]
  split_ifs with hq
  · rw [Finset.prod_eq_single q (fun p hp hpq => hs_eq_one_iff.mpr (h2 p hp hpq))
      (fun h => absurd hq h)]
    exact hs_eq_neg_one_iff.mpr (h1 hq)
  · exact Finset.prod_eq_one (fun p hp => hs_eq_one_iff.mpr (h2 p hp (fun h => hq (h ▸ hp))))

theorem even_of_prod_mem {G ι : Type} [CommGroup G] {H : Subgroup G} (hH : H.index = 2)
    (L : Finset ι) (x : ι → G) (hx : ∀ i ∈ L, x i ∉ H) : ∏ i ∈ L, x i ∈ H ↔ Even L.card := by
  classical
  induction L using Finset.induction_on with
  | empty => simp [H.one_mem]
  | insert a s ha ih =>
    have hxa : x a ∉ H := hx a (Finset.mem_insert_self a s)
    have ih' := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Subgroup.mul_mem_iff_of_index_two hH,
      ih', Nat.even_add_one]
    tauto

theorem even_card_of_not_lone {a b : Fˣ} (L : Finset (Place F)) (hL : ∀ p, p ∈ L ↔ a ∉ nrm p b)
    (hl : ∀ p ∈ L, ¬ Lone p) : Even L.card := by
  classical
  by_cases hsq : IsSquare (b : F)
  · have hL0 : L = ∅ := Finset.eq_empty_of_forall_notMem fun p hp =>
      (hL p).1 hp (mem_nrm_of_sqr (mem_sqr_of_isSquare p hsq) a)
    simp [hL0]
  obtain ⟨S₁, -, hS₁⟩ := exists_superset_mem_sUnits F {a, b} ∅
  obtain ⟨S₂, hS₁₂, hS₂⟩ := exists_admissible_superset_finite_places F S₁
  obtain ⟨S, hS₂S, hidx⟩ := exists_index_le_two hsq hS₂ (hS₁ S₂ hS₁₂ b (by simp))
  have hS : admitted F S := hS₂.mono hS₂S
  have ha : a ∈ sUnits F S := hS₁ S (hS₁₂.trans hS₂S) a (by simp)
  have hb : b ∈ sUnits F S := hS₁ S (hS₁₂.trans hS₂S) b (by simp)
  have hH : (sUnits F S ⊔ locNorm F (b : F) S).index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h | h
    · exact absurd (Subgroup.index_eq_one.1 h) (sUnits_sup_locNorm_ne_top F b S hS hb hsq)
    · exact h
  have hover : ∀ p ∈ L, Over S p := by
    intro p hp
    by_contra hno
    exact (hL p).1 hp (mem_nrm_of_not_over hS ha hb hno)
  have hns : ∀ p ∈ L, b ∉ sqr p := fun p hp hb' => (hL p).1 hp (mem_nrm_of_sqr hb' a)
  have hc : ∀ p ∈ L, ∃ x : Fˣ, x ∉ nrm p b ∧ ∀ q, Over S q → q ≠ p → x ∈ sqr q :=
    fun p hp => exists_single S (hover p hp) (hns p hp)
  choose! c hc1 hc2 using hc
  have hcH : ∀ p ∈ L, c p ∉ sUnits F S ⊔ locNorm F (b : F) S := by
    intro p hp hmem
    obtain ⟨u, hu, n, hn, hun⟩ := Subgroup.mem_sup.1 hmem
    rw [mem_locNorm_iff] at hn
    apply hl p hp
    refine ⟨u, b, ?_, ?_⟩
    · intro hu'
      apply hc1 p hp
      rw [← hun]
      exact mul_mem hu' (hn p (hover p hp))
    · intro q hqp
      by_cases hq : Over S q
      · have hu_eq : u = c p * n⁻¹ := by rw [← hun]; group
        rw [hu_eq]
        exact mul_mem (sqr_le_nrm q b (hc2 p hp q hq hqp)) (inv_mem (hn q hq))
      · exact mem_nrm_of_not_over hS hu hb hq
  have hprod : ∏ p ∈ L, c p ∈ sUnits F S ⊔ locNorm F (b : F) S := by
    have hx : a * ∏ p ∈ L, c p ∈ locNorm F (b : F) S := by
      rw [mem_locNorm_iff]
      intro q hq
      have h := hs_prod L c q b (fun hqL => hc1 q hqL)
        (fun p hp hpq => sqr_le_nrm q b (hc2 p hp q hq (Ne.symm hpq)))
      rw [← hs_eq_one_iff, hs_mul_left]
      by_cases hqL : q ∈ L
      · rw [if_pos hqL] at h
        rw [h, hs_eq_neg_one_iff.2 ((hL q).1 hqL)]
        simp
      · rw [if_neg hqL] at h
        rw [h, hs_eq_one_iff.2 (not_not.1 (mt (hL q).2 hqL))]
        simp
    have he : ∏ p ∈ L, c p = a⁻¹ * (a * ∏ p ∈ L, c p) := by group
    rw [he]
    exact mul_mem (inv_mem (Subgroup.mem_sup_left ha)) (Subgroup.mem_sup_right hx)
  exact (even_of_prod_mem hH L c hcH).1 hprod

theorem exists_lone_family (b : Fˣ) : ∃ c : Place F → Fˣ, ∀ p, Lone p → b ∉ sqr p →
    c p ∉ nrm p b ∧ ∀ q, q ≠ p → c p ∈ nrm q b := by
  classical
  have h : ∀ p : Place F, ∃ c : Fˣ, Lone p → b ∉ sqr p →
      c ∉ nrm p b ∧ ∀ q, q ≠ p → c ∈ nrm q b := by
    intro p
    by_cases hp : Lone p ∧ b ∉ sqr p
    · obtain ⟨c, hc⟩ := hp.1.exists_left hp.2
      exact ⟨c, fun _ _ => hc⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ hp⟩
  choose c hc using h
  exact ⟨c, hc⟩

theorem prod_hs_of_not_lone (a b : Fˣ) (T : Finset (Place F)) (hT : ∀ p ∈ T, ¬ Lone p)
    (hT' : ∀ p, ¬ Lone p → a ∉ nrm p b → p ∈ T) : ∏ p ∈ T, hs p a b = 1 := by
  classical
  obtain ⟨c, hc⟩ := exists_lone_family (F := F) b
  have hfin : {p : Place F | a ∉ nrm p b ∧ Lone p}.Finite :=
    (finite_not_mem_nrm a b).subset fun p hp => hp.1
  have hΛ : ∀ p, p ∈ hfin.toFinset ↔ a ∉ nrm p b ∧ Lone p := fun p => by simp
  have hbΛ : ∀ p ∈ hfin.toFinset, b ∉ sqr p := fun p hp hb' =>
    ((hΛ p).1 hp).1 (mem_nrm_of_sqr hb' a)
  have hP := fun q => hs_prod hfin.toFinset c q b
    (fun hq => (hc q ((hΛ q).1 hq).2 (hbΛ q hq)).1)
    (fun p hp hpq => (hc p ((hΛ p).1 hp).2 (hbΛ p hp)).2 q (Ne.symm hpq))
  have hlone : ∀ q, Lone q → a * ∏ p ∈ hfin.toFinset, c p ∈ nrm q b := by
    intro q hq
    have h := hP q
    rw [← hs_eq_one_iff, hs_mul_left]
    by_cases hqΛ : q ∈ hfin.toFinset
    · rw [if_pos hqΛ] at h
      rw [h, hs_eq_neg_one_iff.2 ((hΛ q).1 hqΛ).1]
      simp
    · rw [if_neg hqΛ] at h
      have ha : a ∈ nrm q b := by
        by_contra ha
        exact hqΛ ((hΛ q).2 ⟨ha, hq⟩)
      rw [h, hs_eq_one_iff.2 ha]
      simp
  have hnl : ∀ q, ¬ Lone q → hs q (a * ∏ p ∈ hfin.toFinset, c p) b = hs q a b := by
    intro q hq
    have h := hP q
    have hqΛ : q ∉ hfin.toFinset := fun h' => hq ((hΛ q).1 h').2
    rw [if_neg hqΛ] at h
    rw [hs_mul_left, h, mul_one]
  have hfin' := finite_not_mem_nrm (a * ∏ p ∈ hfin.toFinset, c p) b
  have hL' : ∀ p, p ∈ hfin'.toFinset ↔ a * ∏ p ∈ hfin.toFinset, c p ∉ nrm p b :=
    fun p => by simp
  have hl' : ∀ p ∈ hfin'.toFinset, ¬ Lone p := fun p hp hlp => (hL' p).1 hp (hlone p hlp)
  have hsub : hfin'.toFinset ⊆ T := by
    intro p hp
    have hpl := hl' p hp
    refine hT' p hpl ?_
    rw [← hs_eq_neg_one_iff, ← hnl p hpl, hs_eq_neg_one_iff]
    exact (hL' p).1 hp
  calc ∏ p ∈ T, hs p a b = ∏ p ∈ T, hs p (a * ∏ p ∈ hfin.toFinset, c p) b :=
        Finset.prod_congr rfl fun p hp => (hnl p (hT p hp)).symm
    _ = ∏ p ∈ hfin'.toFinset, hs p (a * ∏ p ∈ hfin.toFinset, c p) b :=
        (Finset.prod_subset hsub fun p _ hp =>
          hs_eq_one_iff.2 (by by_contra h; exact hp ((hL' p).2 h))).symm
    _ = ∏ p ∈ hfin'.toFinset, (-1 : ℤˣ) :=
        Finset.prod_congr rfl fun p hp => hs_eq_neg_one_iff.2 ((hL' p).1 hp)
    _ = 1 := by
        rw [Finset.prod_const]
        exact (even_card_of_not_lone hfin'.toFinset hL' hl').neg_one_pow

private lemma not_mem_nrm_of_uniformizer_of_nonsquare_unit {r : HeightOneSpectrum (𝓞 F)} {u π : Fˣ} (h2 : r.valuation F 2 = 1)
    (hu : r.valuation F (u : F) = 1) (hus : u ∉ sqr (.inl r))
    (hπ : r.valuation F (π : F) = WithZero.exp (-1)) : π ∉ nrm (.inl r) u := by
  set K := r.adicCompletion F
  have hval : ∀ x : F, (Valued.v (algebraMap F K x) : WithZero (Multiplicative ℤ)) =
      r.valuation F x := fun x => r.valuedAdicCompletion_eq_valuation' x
  have h2' : Valued.v (2 : K) = 1 := by
    have := hval 2
    rw [map_ofNat] at this
    rw [this, h2]
  have hK2 : (2 : K) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h2'
    exact zero_ne_one h2'
  have hsq : ¬ IsSquare (algebraMap F K (u : F)) := fun h => hus ((mem_sqSub (algebraMap F K) u).2 h)
  have hB1 : Valued.v (algebraMap F K (u : F)) = 1 := by rw [hval, hu]
  have h4 : Valued.v (4 : K) = 1 := by
    rw [show (4 : K) = 2 * 2 by norm_num, map_mul, h2', one_mul]
  have hle : Valued.v (algebraMap F K (u : F) - 1) ≤ Valued.v (4 : K) := by
    rw [h4]
    refine (Valuation.map_sub _ _ _).trans ?_
    rw [hB1, map_one, max_self]
  have hE := Defect.evenNorms_of_le_four Valued.v hK2 (isSquare_of_valued_sub_one_lt_four h2') _ hB1 hsq hle
  have hP : Valued.v (algebraMap F K (π : F)) = WithZero.exp (-1) := by rw [hval, hπ]
  intro hmem
  exact not_nm_of_valuation_eq_exp_neg_one _ hE hP ((mem_normSub (algebraMap F K) (u : F) π).1 hmem)

theorem isSquare_of_sqr {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : admitted F S) {u : Fˣ}
    (hu : u ∈ sUnits F S) (h : ∀ p, Over S p → ¬ Lone p → u ∈ sqr p) : IsSquare (u : F) := by
  classical
  by_contra hns
  have hw : ∀ p : Place F, ∃ c : Fˣ, Over S p → u ∉ sqr p →
      c ∉ nrm p u ∧ ∀ q, q ≠ p → c ∈ nrm q u := by
    intro p
    by_cases hp : Over S p ∧ u ∉ sqr p
    · have hl : Lone p := by
        by_contra hl
        exact hp.2 (h p hp.1 hl)
      obtain ⟨c, hc1, hc2⟩ := hl.exists_left hp.2
      exact ⟨c, fun _ _ => ⟨hc1, hc2⟩⟩
    · exact ⟨1, fun h1 h2 => (hp ⟨h1, h2⟩).elim⟩
  choose c hc using hw
  obtain ⟨S₁, hSS₁, hS₁⟩ := exists_superset_mem_sUnits F ((finite_over S).toFinset.image c) S
  have hcS : ∀ p, Over S p → c p ∈ sUnits F S₁ := fun p hp =>
    hS₁ S₁ (Finset.Subset.refl S₁) (c p)
      (Finset.mem_image.2 ⟨p, (finite_over S).mem_toFinset.2 hp, rfl⟩)
  have hA₁ : admitted F S₁ := hS.mono hSS₁
  have huS₁ : u ∈ sUnits F S₁ := sUnits_mono hSS₁ hu
  have hUG : ∀ y ∈ sUnits F S₁, y ∈ sUnits F S₁ ⊔ locNorm F (u : F) S₁ :=
    fun y hy => Subgroup.mem_sup_left hy
  have hpm : ∀ q (x : Fˣ), hs q x u ≠ -1 → hs q x u = 1 := fun q x hx =>
    (Int.units_eq_one_or _).resolve_right hx
  have L2 : ∀ (X : Finset (Place F)) (x : Fˣ),
      (∀ q, Over S₁ q → hs q x u = -1 → Over S q ∧ q ∈ X) →
        x ∈ sUnits F S₁ ⊔ locNorm F (u : F) S₁ := by
    intro X
    refine Finset.induction_on X ?_ ?_
    · intro x hx
      apply Subgroup.mem_sup_right
      rw [mem_locNorm_iff]
      intro q hq
      rw [← hs_eq_one_iff]
      exact hpm q x (fun h' => by simpa using (hx q hq h').2)
    · intro p X _ ih x hx
      by_cases hb : Over S₁ p ∧ hs p x u = -1
      · obtain ⟨hpS, -⟩ := hx p hb.1 hb.2
        have hus : u ∉ sqr p := fun hsq => by
          have h1 := hs_eq_one_iff.2 (mem_nrm_of_sqr hsq x)
          rw [hb.2] at h1
          exact absurd h1 (by decide)
        obtain ⟨hc1, hc2⟩ := hc p hpS hus
        have hxc : x * c p ∈ sUnits F S₁ ⊔ locNorm F (u : F) S₁ := by
          apply ih
          intro q hq hq'
          rw [hs_mul_left] at hq'
          by_cases hqp : q = p
          · rw [hqp, hb.2, hs_eq_neg_one_iff.2 hc1] at hq'
            exact absurd hq' (by decide)
          · rw [hs_eq_one_iff.2 (hc2 q hqp), mul_one] at hq'
            obtain ⟨h1, h2⟩ := hx q hq hq'
            exact ⟨h1, (Finset.mem_insert.1 h2).resolve_left hqp⟩
        have he : x = x * c p * (c p)⁻¹ := by group
        rw [he]
        exact mul_mem hxc (inv_mem (hUG _ (hcS p hpS)))
      · apply ih
        intro q hq hq'
        obtain ⟨h1, h2⟩ := hx q hq hq'
        refine ⟨h1, (Finset.mem_insert.1 h2).resolve_left ?_⟩
        rintro rfl
        exact hb ⟨hq, hq'⟩
  have L1 : ∀ (X : Finset (HeightOneSpectrum (𝓞 F))) (x : Fˣ),
      (∀ q, Over S₁ q → hs q x u = -1 → Over S q ∨ ∃ r ∈ X, q = .inl r) →
        x ∈ sUnits F S₁ ⊔ locNorm F (u : F) S₁ := by
    intro X
    refine Finset.induction_on X ?_ ?_
    · intro x hx
      apply L2 (finite_over S).toFinset x
      intro q hq hq'
      rcases hx q hq hq' with h1 | ⟨r, hr, -⟩
      · exact ⟨h1, (finite_over S).mem_toFinset.2 h1⟩
      · simp at hr
    · intro r X _ ih x hx
      by_cases hb : r ∈ S₁ ∧ r ∉ S ∧ hs (.inl r) x u = -1
      · obtain ⟨hr1, hr2, hr3⟩ := hb
        obtain ⟨h2, π, hπ, hπ'⟩ := hS r hr2
        have hπ0 : π ≠ 0 := by
          intro h0
          rw [h0, map_zero] at hπ
          exact WithZero.exp_ne_zero hπ.symm
        obtain ⟨πu, hπu⟩ : ∃ πu : Fˣ, (πu : F) = π := ⟨Units.mk0 π hπ0, rfl⟩
        subst hπu
        have hus : u ∉ sqr (.inl r) := fun hsq => by
          have h1 := hs_eq_one_iff.2 (mem_nrm_of_sqr hsq x)
          rw [hr3] at h1
          exact absurd h1 (by decide)
        have hur : r.valuation F (u : F) = 1 := (mem_sUnits F S u).1 hu r hr2
        have hπr : hs (.inl r) πu u = -1 :=
          hs_eq_neg_one_iff.2 (not_mem_nrm_of_uniformizer_of_nonsquare_unit h2 hur hus hπ)
        have hπw : ∀ w, w ∉ S → w ≠ r → hs (.inl w) πu u = 1 := by
          intro w hw hwr
          apply hs_eq_one_iff.2
          exact mem_nrm_of_unit (hS w hw).1 (hπ' w hw hwr) ((mem_sUnits F S u).1 hu w hw)
        have hπS : πu ∈ sUnits F S₁ := by
          rw [mem_sUnits]
          intro w hw
          exact hπ' w (fun h' => hw (hSS₁ h')) (fun h' => hw (h' ▸ hr1))
        have hxπ : x * πu ∈ sUnits F S₁ ⊔ locNorm F (u : F) S₁ := by
          apply ih
          intro q hq hq'
          rw [hs_mul_left] at hq'
          rcases q with w | σ
          · by_cases hwS : w ∈ S
            · exact Or.inl hwS
            · by_cases hwr : w = r
              · rw [hwr, hr3, hπr] at hq'
                exact absurd hq' (by decide)
              · rw [hπw w hwS hwr, mul_one] at hq'
                rcases hx (.inl w) hq hq' with h1 | ⟨r', hr', hq''⟩
                · exact Or.inl h1
                · refine Or.inr ⟨r', ?_, hq''⟩
                  rcases Finset.mem_insert.1 hr' with h3 | h3
                  · exact (hwr ((Sum.inl.inj hq'').trans h3)).elim
                  · exact h3
          · exact Or.inl trivial
        have he : x = x * πu * πu⁻¹ := by group
        rw [he]
        exact mul_mem hxπ (inv_mem (hUG _ hπS))
      · apply ih
        intro q hq hq'
        rcases hx q hq hq' with h1 | ⟨r', hr', hq''⟩
        · exact Or.inl h1
        · rcases Finset.mem_insert.1 hr' with h3 | h3
          · rw [hq'', h3] at hq hq'
            by_cases hrS : r ∈ S
            · exact Or.inl (hq'' ▸ h3 ▸ hrS)
            · exact (hb ⟨hq, hrS, hq'⟩).elim
          · exact Or.inr ⟨r', h3, hq''⟩
  apply sUnits_sup_locNorm_ne_top F u S₁ hA₁ huS₁ hns
  rw [eq_top_iff]
  intro x _
  apply L1 S₁ x
  intro q hq _
  rcases q with w | σ
  · exact Or.inr ⟨w, hq, rfl⟩
  · exact Or.inl trivial

theorem relIndex_sq_le {G : Type} [CommGroup G] (B : G →* G →* ℤˣ) (W U : Subgroup G)
    (hW0 : W.index ≠ 0) (hW : ∀ x, ∀ w ∈ W, B x w = 1) (hker : ∀ x, (∀ y, B x y = 1) → x ∈ W)
    (hU : ∀ x ∈ U, ∀ y ∈ U, B x y = 1) : W.relIndex U ^ 2 ≤ W.index := by
  classical
  set H := U ⊔ W with hH
  have hsplit : W.index = W.relIndex U * H.index := index_eq_relIndex_mul_index_sup U W
  have hH0 : H.index ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsplit
    exact hW0 hsplit
  haveI : H.FiniteIndex := ⟨hH0⟩
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _

  have hkill : ∀ f ∈ U.map B, H ≤ f.ker := by
    rintro f ⟨x, hx, rfl⟩
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact MonoidHom.mem_ker.mpr (hU x hx y hy)
    · exact MonoidHom.mem_ker.mpr (hW x y hy)
  let ψ : ℤˣ →* ℚ := (Int.castRingHom ℚ).toMonoidHom.comp (Units.coeHom ℤ)
  have hψ : Function.Injective ψ := by
    intro a b hab
    have h' : ((a : ℤ) : ℚ) = ((b : ℤ) : ℚ) := hab
    exact Units.ext (by exact_mod_cast h')
  let g : (U.map B) → ((G ⧸ H) →* ℚ) := fun f =>
    QuotientGroup.lift H (ψ.comp f.1) (fun y hy => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.mp (hkill f.1 f.2 hy), map_one])
  have hg : Function.Injective g := by
    intro f1 f2 h
    apply Subtype.ext
    apply MonoidHom.ext
    intro y
    have h' := congrArg (fun φ : (G ⧸ H) →* ℚ => φ (y : G ⧸ H)) h
    simp only [g, QuotientGroup.lift_mk, MonoidHom.comp_apply] at h'
    exact hψ h'
  have hli : LinearIndependent ℚ (fun f : U.map B => ((g f : (G ⧸ H) →* ℚ) : G ⧸ H → ℚ)) :=
    (linearIndependent_monoidHom (G ⧸ H) ℚ).comp g hg
  haveI : Finite (U.map B) := hli.finite_of_isNoetherian
  letI : Fintype (U.map B) := Fintype.ofFinite _
  have hcard : Fintype.card (U.map B) ≤ Fintype.card (G ⧸ H) := by
    have h' := hli.fintype_card_le_finrank
    rwa [Module.finrank_fintype_fun_eq_card] at h'
  have hcardN : Nat.card (U.map B) ≤ H.index := by
    rw [Nat.card_eq_fintype_card, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    exact hcard
  have hkerW : B.ker ≤ W := by
    intro x hx
    refine hker x (fun y => ?_)
    have h1 : B x = 1 := hx
    exact DFunLike.congr_fun h1 y
  have hrk : B.ker.relIndex U = Nat.card (U.map B) := Subgroup.relIndex_ker (K := U) B
  have hpos : 0 < Nat.card (U.map B) := Nat.card_pos
  have hm : W.relIndex U ≤ H.index :=
    (Subgroup.relIndex_le_of_le_left hkerW (by rw [hrk]; exact hpos.ne')).trans (by rw [hrk]; exact hcardN)
  calc W.relIndex U ^ 2 = W.relIndex U * W.relIndex U := sq _
    _ ≤ W.relIndex U * H.index := Nat.mul_le_mul_left _ hm
    _ = W.index := hsplit.symm

theorem not_lone (p₀ : Place F) : ¬ Lone p₀ := by
  classical
  intro hlone
  obtain ⟨a, b, hab, -⟩ := id hlone
  have hb : b ∉ sqr p₀ := fun h => hab (mem_nrm_of_sqr h a)
  obtain ⟨S₀, hS₀⟩ := exists_over p₀
  obtain ⟨S, hS₀S, hS⟩ := exists_admissible_superset_finite_places F S₀
  have hp₀ : Over S p₀ := hS₀.mono hS₀S
  set N : Finset (Place F) := (finite_over S).toFinset.filter (fun q => ¬ Lone q) with hN
  have hmemN : ∀ q, q ∈ N ↔ Over S q ∧ ¬ Lone q := fun q => by simp [hN]
  set W : Subgroup Fˣ := ⨅ (q : Place F) (_ : Over S q ∧ ¬ Lone q), sqr q with hWdef
  have hmemW : ∀ x, x ∈ W ↔ ∀ q, Over S q → ¬ Lone q → x ∈ sqr q := by
    intro x
    simp only [hWdef, Subgroup.mem_iInf]
    exact ⟨fun h q h1 h2 => h q ⟨h1, h2⟩, fun h q hq => h q hq.1 hq.2⟩
  let B : Fˣ →* Fˣ →* ℤˣ := MonoidHom.mk'
    (fun x => MonoidHom.mk' (fun y => ∏ q ∈ N, hs q x y)
      (fun y y' => by simp only [hs_mul_right, Finset.prod_mul_distrib]))
    (fun x x' => MonoidHom.ext fun y => by
      simp only [MonoidHom.mk'_apply, MonoidHom.mul_apply, hs_mul_left, Finset.prod_mul_distrib])
  have hB : ∀ x y, B x y = ∏ q ∈ N, hs q x y := fun x y => rfl
  have hle : locSq F S ≤ W := fun x hx => (hmemW x).2 fun q hq _ => (mem_locSq_iff.1 hx) q hq
  have hW0 : W.index ≠ 0 := fun h0 =>
    (index_locSq_le F S).1 (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.index_dvd_of_le hle))
  have hWB : ∀ x, ∀ w ∈ W, B x w = 1 := by
    intro x w hw
    rw [hB]
    refine Finset.prod_eq_one fun q hq => ?_
    obtain ⟨h1, h2⟩ := (hmemN q).1 hq
    exact hs_eq_one_iff.2 (mem_nrm_of_sqr ((hmemW w).1 hw q h1 h2) x)
  have hker : ∀ x, (∀ y, B x y = 1) → x ∈ W := by
    intro x hx
    rw [hmemW]
    intro q hq hql
    by_contra hxq
    obtain ⟨y, hy1, hy2⟩ := exists_single S hq hxq
    have h1 : ∏ r ∈ N, hs r x y = hs q x y :=
      Finset.prod_eq_single_of_mem q ((hmemN q).2 ⟨hq, hql⟩) fun r hr hrq => by
        rw [hs_comm, hs_eq_one_iff]
        exact sqr_le_nrm r x (hy2 r ((hmemN r).1 hr).1 hrq)
    have h := hx y
    rw [hB, h1, hs_comm, hs_eq_one_iff] at h
    exact hy1 h
  have hU : ∀ x ∈ sUnits F S, ∀ y ∈ sUnits F S, B x y = 1 := by
    intro x hx y hy
    rw [hB]
    refine prod_hs_of_not_lone x y N (fun q hq => ((hmemN q).1 hq).2) fun q hq hxy => (hmemN q).2 ⟨?_, hq⟩
    by_contra hno
    exact hxy (mem_nrm_of_not_over hS hx hy hno)
  have key := relIndex_sq_le B W (sUnits F S) hW0 hWB hker hU
  have hrel : W.relIndex (sUnits F S) = 2 ^ (S.card + Fintype.card (InfinitePlace F)) := by
    rw [← relIndex_sqs_sUnits F S]
    have hsub : W.subgroupOf (sUnits F S) = (sqs (sUnits F S)).subgroupOf (sUnits F S) := by
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_subgroupOf]
      rw [mem_sqs_sUnits_iff_isSquare F S x hx, hmemW]
      exact ⟨fun h => isSquare_of_sqr hS hx h, fun h q _ _ => mem_sqr_of_isSquare q h⟩
    unfold Subgroup.relIndex
    rw [hsub]
  obtain ⟨x, hx⟩ := exists_approx S (fun q => if q = p₀ then b else 1)
  have hxW : x ∈ W := (hmemW x).2 fun q hq hql => by
    have hqp : q ≠ p₀ := fun h => hql (h ▸ hlone)
    have h := hx q hq
    rw [if_neg hqp, mul_one] at h
    exact h
  have hxL : x ∉ locSq F S := by
    intro h
    have h1 := (mem_locSq_iff.1 h) p₀ hp₀
    have h2 := hx p₀ hp₀
    rw [if_pos rfl] at h2
    apply hb
    have he : b = x⁻¹ * (x * b) := by group
    rw [he]
    exact mul_mem (inv_mem h1) h2
  have hrl := Subgroup.relIndex_mul_index hle
  have hr1 : (locSq F S).relIndex W ≠ 1 := fun h => hxL (Subgroup.relIndex_eq_one.1 h hxW)
  have hr0 : (locSq F S).relIndex W ≠ 0 := fun h =>
    (index_locSq_le F S).1 (by rw [← hrl, h, zero_mul])
  have h4 := (index_locSq_le F S).2
  rw [hrel] at key
  have hpow : (2 ^ (S.card + Fintype.card (InfinitePlace F))) ^ 2 =
      4 ^ (S.card + Fintype.card (InfinitePlace F)) := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [hpow] at key
  have h4pos : 0 < 4 ^ (S.card + Fintype.card (InfinitePlace F)) := by positivity
  have h2W : 2 * W.index ≤ (locSq F S).index := by
    rw [← hrl]; exact Nat.mul_le_mul_right _ (by omega)
  generalize 4 ^ (S.card + Fintype.card (InfinitePlace F)) = m at *
  omega

theorem prod_hs (a b : Fˣ) (T : Finset (Place F)) (hT : ∀ p, a ∉ nrm p b → p ∈ T) :
    ∏ p ∈ T, hs p a b = 1 := prod_hs_of_not_lone a b T (fun p _ => not_lone p) (fun p _ h => hT p h)

private lemma ringEquivRealOfIsReal_algebraMap {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}
    (hw : w.IsReal) (x : K) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap K w.Completion x) =
      InfinitePlace.embedding_of_isReal hw x := by
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfinitePlace.Completion.algebraMap_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
  first
  | rfl
  | simp
  | rw [← WithAbs.equiv_symm_apply, RingEquiv.apply_symm_apply]

end GlobalTheory.HilbertRecip

namespace GlobalTheory.QuadSymbol

open GlobalTheory.HilbertRecip

theorem eta_infinite_real {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    (e : Module.Basis (Fin 2) K L) (h0 : e 0 = 1) {δ : Kˣ} (h1 : e 1 * e 1 = algebraMap K L δ)
    (t : Kˣ) {w : InfinitePlace K} (hw : w.IsReal) :
    eta K L w.Completion (infDiag K t w) =
      hs (.inr (InfinitePlace.embedding_of_isReal hw)) t δ := by
  obtain ⟨f, hf⟩ : ∃ f : w.Completion ≃+* ℝ, ∀ x : K,
      f (algebraMap K w.Completion x) = InfinitePlace.embedding_of_isReal hw x :=
    ⟨_, ringEquivRealOfIsReal_algebraMap hw⟩
  have key : infDiag K t w ∈ normGroup K L w.Completion ↔
      t ∈ nrm (.inr (InfinitePlace.embedding_of_isReal hw)) δ := by
    rw [mem_normGroup_iff_form e h0 h1]
    have ht : ((infDiag K t w : (w.Completion)ˣ) : w.Completion) = algebraMap K w.Completion t := rfl
    rw [ht]
    show _ ↔ t ∈ normSub (InfinitePlace.embedding_of_isReal hw) (δ : K)
    rw [mem_normSub]
    constructor
    · rintro ⟨a, b, hab⟩
      refine ⟨f a, f b, ?_⟩
      have := congrArg f hab
      simp only [map_sub, map_mul, map_pow, hf] at this
      exact this
    · rintro ⟨a, b, hab⟩
      refine ⟨f.symm a, f.symm b, f.injective ?_⟩
      rw [hf, hab]
      simp only [map_sub, map_mul, map_pow, hf, RingEquiv.apply_symm_apply]
  by_cases h : t ∈ nrm (.inr (InfinitePlace.embedding_of_isReal hw)) δ
  · rw [eta_eq_one_iff.2 (key.2 h), hs_eq_one_iff.2 h]
  · rw [eta_eq_neg_one_iff.2 (fun h' => h (key.1 h')), hs_eq_neg_one_iff.2 h]

private lemma eta_infDiag_eq_one_of_isComplex {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    (e : Module.Basis (Fin 2) K L) (h0 : e 0 = 1) {δ : Kˣ} (h1 : e 1 * e 1 = algebraMap K L δ)
    (t : Kˣ) {w : InfinitePlace K} (hw : w.IsComplex) :
    eta K L w.Completion (infDiag K t w) = 1 := by
  rw [eta_eq_one_iff, mem_normGroup_iff_form e h0 h1]
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      ((infDiag K t w : (w.Completion)ˣ) : w.Completion)) two_pos
  refine ⟨(InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm c, 0, ?_⟩
  have hsq : (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm c ^ 2 =
      ((infDiag K t w : (w.Completion)ˣ) : w.Completion) := by
    rw [← map_pow, hc, RingEquiv.symm_apply_apply]
  rw [hsq]
  simp

theorem prod_eta_infinite {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    (e : Module.Basis (Fin 2) K L) (h0 : e 0 = 1) {δ : Kˣ} (h1 : e 1 * e 1 = algebraMap K L δ)
    (t : Kˣ) [Fintype (K →+* ℝ)] :
    ∏ w : InfinitePlace K, eta K L w.Completion (infDiag K t w) =
      ∏ σ : K →+* ℝ, hs (.inr σ) t δ := by
  classical
  let m : (K →+* ℝ) → InfinitePlace K := fun σ => InfinitePlace.mk (Complex.ofRealHom.comp σ)
  have hr : ∀ σ : K →+* ℝ, ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := fun σ =>
    ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
      simp [ComplexEmbedding.conjugate_coe_eq])
  have hm : ∀ σ, (m σ).IsReal := fun σ => InfinitePlace.isReal_mk_iff.2 (hr σ)
  have hemb : ∀ σ, InfinitePlace.embedding_of_isReal (hm σ) = σ := by
    intro σ
    ext x
    have h2 := InfinitePlace.embedding_of_isReal_apply (hm σ) x
    rw [InfinitePlace.embedding_mk_eq_of_isReal (hr σ)] at h2
    exact Complex.ofReal_injective h2
  have hinj : Function.Injective m := by
    intro σ τ h
    have h2 : InfinitePlace.embedding (m σ) = InfinitePlace.embedding (m τ) := by rw [h]
    simp only [m, InfinitePlace.embedding_mk_eq_of_isReal (hr σ),
      InfinitePlace.embedding_mk_eq_of_isReal (hr τ)] at h2
    ext x
    have h3 := RingHom.congr_fun h2 x
    simpa using h3
  have hsurj : ∀ w : InfinitePlace K, w.IsReal → ∃ σ, m σ = w := by
    intro w hw
    refine ⟨InfinitePlace.embedding_of_isReal hw, ?_⟩
    have h2 : Complex.ofRealHom.comp (InfinitePlace.embedding_of_isReal hw) =
        InfinitePlace.embedding w := by
      ext x
      simp
    show InfinitePlace.mk _ = w
    rw [h2, InfinitePlace.mk_embedding]
  calc ∏ w : InfinitePlace K, eta K L w.Completion (infDiag K t w)
      = ∏ w ∈ Finset.univ.image m, eta K L w.Completion (infDiag K t w) := by
        symm
        apply Finset.prod_subset (Finset.subset_univ _)
        intro w _ hw
        have hc : w.IsComplex := by
          rw [← InfinitePlace.not_isReal_iff_isComplex]
          intro hre
          obtain ⟨σ, rfl⟩ := hsurj w hre
          exact hw (Finset.mem_image_of_mem m (Finset.mem_univ σ))
        exact eta_infDiag_eq_one_of_isComplex e h0 h1 t hc
    _ = ∏ σ : K →+* ℝ, eta K L (m σ).Completion (infDiag K t (m σ)) := by
        apply Finset.prod_image
        intro x _ y _ h
        exact hinj h
    _ = ∏ σ : K →+* ℝ, hs (.inr σ) t δ := by
        refine Finset.prod_congr rfl fun σ _ => ?_
        rw [eta_infinite_real e h0 h1 t (hm σ), hemb σ]

theorem productFormula : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L], ProductFormula K L := by
  intro K L _ _ _ _ _ _ t
  refine ⟨almostNorm_finDiag K L t, ?_⟩
  classical
  obtain ⟨δ₀, e, hns, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ₀ ≠ 0 := by
    rintro rfl
    exact hns ⟨0, by simp⟩
  obtain ⟨δ, rfl⟩ : ∃ δ : Kˣ, (δ : K) = δ₀ := ⟨Units.mk0 δ₀ hδ0, rfl⟩
  have hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      eta K L (v.adicCompletion K) (finDiag K t v) = hs (.inl v) t δ := by
    intro v
    have key : finDiag K t v ∈ normGroup K L (v.adicCompletion K) ↔ t ∈ nrm (.inl v) δ := by
      rw [mem_normGroup_iff_form e h0 h1]
      show _ ↔ t ∈ normSub (algebraMap K (v.adicCompletion K)) (δ : K)
      rw [mem_normSub]
      rfl
    by_cases h : t ∈ nrm (.inl v) δ
    · rw [eta_eq_one_iff.2 (key.2 h), hs_eq_one_iff.2 h]
    · rw [eta_eq_neg_one_iff.2 (fun h' => h (key.1 h')), hs_eq_neg_one_iff.2 h]
  have hF := finite_not_mem_nrm t δ
  have hI : Set.InjOn (Sum.inl : HeightOneSpectrum (𝓞 K) → Place K)
      (Sum.inl ⁻¹' {p : Place K | t ∉ nrm p δ}) := by
    intro a _ b _ h
    exact Sum.inl_injective h
  let Sf : Finset (HeightOneSpectrum (𝓞 K)) := (hF.preimage hI).toFinset
  have hT : ∀ p : Place K, t ∉ nrm p δ → p ∈ Sf.disjSum Finset.univ := by
    rintro (v | σ) hp
    · simp [Sf, hp]
    · simp
  have hprod := prod_hs t δ (Sf.disjSum Finset.univ) hT
  rw [Finset.prod_disjSum] at hprod
  have hfp : (∏ᶠ v : HeightOneSpectrum (𝓞 K), eta K L (v.adicCompletion K) (finDiag K t v)) =
      ∏ v ∈ Sf, hs (.inl v) t δ := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := Sf)]
    · exact Finset.prod_congr rfl fun v _ => hfin v
    · intro v hv
      rw [Function.mem_mulSupport, hfin v] at hv
      simp only [Sf, Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
      intro hm
      exact hv (hs_eq_one_iff.2 hm)
  rw [etaProd, hfp, prod_eta_infinite e h0 h1 t]
  exact hprod

end GlobalTheory.QuadSymbol

end
