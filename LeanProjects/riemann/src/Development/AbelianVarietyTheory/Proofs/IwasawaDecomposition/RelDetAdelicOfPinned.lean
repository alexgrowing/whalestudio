import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.HermitianColumns.HermCols
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitary
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemKDSupUnitIdlIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdFNonnegOfIsInteger
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubDetSubSelfDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowEqSpanNormOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanValuationLe

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open GlobalTheory.Mem.Chr.IdlFact GlobalTheory.Mem.Chr.DetOrd WithZero
open scoped nonZeroDivisors TensorProduct

namespace GlobalTheory.Mem.NormOneIdeal

section Field

variable {L : Type} [Field L] [NumberField L]

def idealExp (n : HeightOneSpectrum (𝓞 L) → ℤ) : FractionalIdeal (𝓞 L)⁰ L :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 L), (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ n v

theorem idealExp_ne_zero (n : HeightOneSpectrum (𝓞 L) → ℤ) : idealExp n ≠ 0 := by
  refine finprod_induction (fun I : FractionalIdeal (𝓞 L)⁰ L => I ≠ 0) one_ne_zero
    (fun _ _ => mul_ne_zero) fun v => zpow_ne_zero _ ?_
  simpa using v.ne_bot

theorem count_idealExp {n : HeightOneSpectrum (𝓞 L) → ℤ} (h : {v | n v ≠ 0}.Finite) (v : HeightOneSpectrum (𝓞 L)) :
    FractionalIdeal.count L v (idealExp n) = n v :=
  FractionalIdeal.count_finprod L v _ (Filter.eventually_cofinite.2 h)

theorem eq_coe_of_val {A : Submodule (𝓞 L) L} {I : FractionalIdeal (𝓞 L)⁰ L} (hI : I ≠ 0)
    (h1 : ∀ x ∈ A, ∀ w : HeightOneSpectrum (𝓞 L), w.valuation L x ≤ exp (-FractionalIdeal.count L w I))
    (h2 : ∀ w : HeightOneSpectrum (𝓞 L), ∃ x ∈ A, w.valuation L x = exp (-FractionalIdeal.count L w I)) :
    A = (I : Submodule (𝓞 L) L) := by
  have hle : A ≤ (I : Submodule (𝓞 L) L) := fun x hx => (GlobalTheory.Idele.mem_iff_valuation_le hI x).2 (h1 x hx)
  let J : FractionalIdeal (𝓞 L)⁰ L := ⟨A, FractionalIdeal.isFractional_of_le hle⟩
  have hJ : J ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 L)
    obtain ⟨x, hx, e⟩ := h2 ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField L)⟩
    have hx' : x ∈ J := hx
    rw [h0, FractionalIdeal.mem_zero_iff] at hx'
    rw [hx', map_zero] at e
    exact exp_ne_zero e.symm
  have : I ≤ J := GlobalTheory.Idele.le_of_count_le hI hJ fun w => by
    obtain ⟨x, hx, e⟩ := h2 w
    have := (GlobalTheory.Idele.mem_iff_valuation_le hJ x).1 hx w
    rw [e, exp_le_exp] at this
    omega
  exact le_antisymm hle this

theorem ordSub_coe {I : FractionalIdeal (𝓞 L)⁰ L} (hI : I ≠ 0) (w : HeightOneSpectrum (𝓞 L)) :
    ordSub w (I : Submodule (𝓞 L) L) = FractionalIdeal.count L w I := by
  obtain ⟨y, hy, e⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI w
  have hy0 : y ≠ 0 := fun h => by rw [h, map_zero] at e; exact exp_ne_zero e.symm
  refine IsLeast.csInf_eq ⟨⟨Units.mk0 y hy0, hy, by simp [ordF, e]⟩, ?_⟩
  rintro n ⟨k, hk, rfl⟩
  have h0 : w.valuation L (k : L) ≠ 0 := by simp
  have := (GlobalTheory.Idele.mem_iff_valuation_le hI _).1 hk w
  rw [← exp_log h0, exp_le_exp] at this
  unfold ordF
  omega

theorem coe_eq_of_pow {𝔞 𝔟 : Submodule (𝓞 L) L} (hb : 𝔞 * 𝔟 = 1) {I : FractionalIdeal (𝓞 L)⁰ L} (hI : I ≠ 0) {z : L}
    (hz : z ≠ 0) {n : ℕ} (hn : 0 < n) (h1 : 𝔞 ^ n = Submodule.span (𝓞 L) {z})
    (h2 : ∀ Q : HeightOneSpectrum (𝓞 L), Q.valuation L z = exp (-FractionalIdeal.count L Q I) ^ n) :
    (I : Submodule (𝓞 L) L) = 𝔞 := by
  have hun : IsUnit 𝔞 := IsUnit.of_mul_eq_one 𝔟 hb
  obtain ⟨J, rfl⟩ : ∃ J : FractionalIdeal (𝓞 L)⁰ L, (J : Submodule (𝓞 L) L) = 𝔞 :=
    ⟨⟨_, FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit hun)⟩, rfl⟩
  have hJz : J ^ n = FractionalIdeal.spanSingleton (𝓞 L)⁰ z := by
    apply FractionalIdeal.coeToSubmodule_injective
    simpa only [FractionalIdeal.coe_pow, FractionalIdeal.coe_spanSingleton] using h1
  have hJ : J ≠ 0 := fun h0 => by
    rw [h0, zero_pow hn.ne', eq_comm, FractionalIdeal.spanSingleton_eq_zero_iff] at hJz
    exact hz hJz
  rw [GlobalTheory.Idele.eq_of_count_eq hI hJ fun Q => ?_]
  have f := h2 Q
  rw [GlobalTheory.Idele.valuation_eq_exp_neg_count Q hz, ← hJz,
    FractionalIdeal.count_pow, ← exp_nsmul, exp_inj, nsmul_eq_mul, mul_neg, neg_inj] at f
  exact (mul_left_cancel₀ (by exact_mod_cast hn.ne') f).symm

theorem val_le_of_span {S : Set L} (w : HeightOneSpectrum (𝓞 L)) {γ : ℤᵐ⁰} (h : ∀ x ∈ S, w.valuation L x ≤ γ) :
    ∀ x ∈ Submodule.span (𝓞 L) S, w.valuation L x ≤ γ := by
  first
  | exact @_root_.GlobalTheory.SpanValuationBound.main
  | exact _root_.GlobalTheory.SpanValuationBound.main
  | (apply _root_.GlobalTheory.SpanValuationBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanValuationBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanValuationBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanValuationBound.main ..)

variable {N : ℕ}

def detFI (M : Submodule (𝓞 L) (Fin N → L)) (h : M.FG) : FractionalIdeal (𝓞 L)⁰ L :=
  ⟨detSub M, isFractional_detSub M h⟩

theorem detFI_ne_zero {M : Submodule (𝓞 L) (Fin N → L)} (h : M.FG)
    (hs : Submodule.span L (M : Set (Fin N → L)) = ⊤) : detFI M h ≠ 0 := by
  obtain ⟨x, hx, hd⟩ := Formalism.L2.LamCM.A2.exists_det_ne M hs
  intro h0
  have : (Matrix.of x).det ∈ detFI M h := det_mem_detSub x hx
  rw [h0, FractionalIdeal.mem_zero_iff] at this
  exact hd this

theorem val_det_le {M : Submodule (𝓞 L) (Fin N → L)} (h : M.FG)
    (hs : Submodule.span L (M : Set (Fin N → L)) = ⊤) (w : HeightOneSpectrum (𝓞 L)) {x : Fin N → Fin N → L}
    (hx : ∀ i, x i ∈ M) : w.valuation L (Matrix.of x).det ≤ exp (-FractionalIdeal.count L w (detFI M h)) :=
  (GlobalTheory.Idele.mem_iff_valuation_le (detFI_ne_zero h hs) _).1 (det_mem_detSub x hx) w

theorem exists_val_det_eq {M : Submodule (𝓞 L) (Fin N → L)} (h : M.FG)
    (hs : Submodule.span L (M : Set (Fin N → L)) = ⊤) (w : HeightOneSpectrum (𝓞 L)) :
    ∃ x : Fin N → Fin N → L, (∀ i, x i ∈ M) ∧
      w.valuation L (Matrix.of x).det = exp (-FractionalIdeal.count L w (detFI M h)) := by
  by_contra hne
  obtain ⟨y, hy, e⟩ := GlobalTheory.Idele.exists_mem_valuation_eq (detFI_ne_zero h hs) w
  have : w.valuation L y ≤ exp (-FractionalIdeal.count L w (detFI M h) - 1) := by
    refine val_le_of_span w ?_ y hy
    rintro _ ⟨x, hx, rfl⟩
    have h1 := lt_of_le_of_ne (val_det_le h hs w hx) fun e => hne ⟨x, hx, e⟩
    rcases eq_or_ne (w.valuation L (Matrix.of x).det) 0 with h0 | h0
    · simp [h0]
    rw [← exp_log h0, exp_lt_exp] at h1
    rw [← exp_log h0, exp_le_exp]
    omega
  rw [e, exp_le_exp] at this
  omega

theorem det_of_mulVec' {A : Type} [CommRing A] (γ : Matrix (Fin N) (Fin N) A) (x : Fin N → Fin N → A) :
    (Matrix.of fun i => γ.mulVec (x i)).det = γ.det * (Matrix.of x).det := by
  have : (Matrix.of fun i => γ.mulVec (x i)) = Matrix.of x * γ.transpose := by
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [this, Matrix.det_mul, Matrix.det_transpose, mul_comm]

theorem span_det_eq {M M' : Submodule (𝓞 L) (Fin N → L)} (h : M.FG)
    (hs : Submodule.span L (M : Set (Fin N → L)) = ⊤) (h' : M'.FG)
    (hs' : Submodule.span L (M' : Set (Fin N → L)) = ⊤) :
    Submodule.span (𝓞 L) {x | ∃ A : Matrix (Fin N) (Fin N) L, (∀ v ∈ M, A.mulVec v ∈ M') ∧ x = A.det} =
      ((detFI M' h' * (detFI M h)⁻¹ : FractionalIdeal (𝓞 L)⁰ L) : Submodule (𝓞 L) L) := by
  have hn := detFI_ne_zero h hs
  have hn' := detFI_ne_zero h' hs'
  have hc : ∀ w, FractionalIdeal.count L w (detFI M' h' * (detFI M h)⁻¹) =
      FractionalIdeal.count L w (detFI M' h') - FractionalIdeal.count L w (detFI M h) := fun w => by
    rw [FractionalIdeal.count_mul L w hn' (inv_ne_zero hn), FractionalIdeal.count_inv, sub_eq_add_neg]
  refine eq_coe_of_val (mul_ne_zero hn' (inv_ne_zero hn)) (fun z hz w => val_le_of_span w ?_ z hz) fun w => ?_
  · rintro _ ⟨A, hA, rfl⟩
    obtain ⟨x, hx, e⟩ := exists_val_det_eq h hs w
    have h1 := val_det_le h' hs' w (x := fun i => A.mulVec (x i)) fun i => hA _ (hx i)
    rw [det_of_mulVec', map_mul, e, ← le_div_iff₀ (zero_lt_iff.2 exp_ne_zero), ← exp_sub] at h1
    rw [hc]
    convert h1 using 2
    ring
  · obtain ⟨x, hx, e⟩ := exists_val_det_eq h hs w
    obtain ⟨y, hy, e'⟩ := exists_val_det_eq h' hs' w
    obtain ⟨s, hsm, es⟩ := GlobalTheory.Idele.exists_mem_valuation_eq (inv_ne_zero hn) w
    rw [FractionalIdeal.count_inv, neg_neg] at es
    have hd : (Matrix.of x).det ≠ 0 := fun h0 => by rw [h0, map_zero] at e; exact exp_ne_zero e.symm
    have hd' : IsUnit (Matrix.of x).transpose.det := by rw [Matrix.det_transpose]; exact hd.isUnit
    refine ⟨_, Submodule.subset_span ⟨(s * (Matrix.of x).det) • ((Matrix.of y).transpose * (Matrix.of x).transpose⁻¹),
      fun v hv => ?_, rfl⟩, ?_⟩
    · have e1 : ((s * (Matrix.of x).det) • ((Matrix.of y).transpose * (Matrix.of x).transpose⁻¹)).mulVec v =
          ∑ i, (s * ((Matrix.of x).updateRow i v).det) • y i := by
        rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, mul_smul, ← Matrix.mulVec_smul, ← Matrix.det_transpose,
          Matrix.det_smul_inv_mulVec_eq_cramer _ _ hd']
        ext j
        simp [Matrix.mulVec, dotProduct, Matrix.cramer_transpose_apply, Finset.mul_sum, mul_comm, mul_left_comm]
      rw [e1]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hm : ((Matrix.of x).updateRow i v).det ∈ detFI M h :=
        det_mem_detSub (Function.update x i v) fun j => by
          rcases eq_or_ne j i with rfl | hj
          · rwa [Function.update_self]
          · rw [Function.update_of_ne hj]; exact hx j
      have h1 := FractionalIdeal.mul_mem_mul hsm hm
      rw [inv_mul_cancel₀ hn, FractionalIdeal.mem_one_iff] at h1
      obtain ⟨r, hr⟩ := h1
      rw [← hr, algebraMap_smul]
      exact M'.smul_mem r (hy i)
    · rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_nonsing_inv, Matrix.det_transpose, Matrix.det_transpose,
        Ring.inverse_eq_inv', map_mul, map_mul, map_pow, map_mul, map_inv₀, es, e, e', hc, ← exp_add, add_neg_cancel,
        exp_zero, one_pow, one_mul, ← exp_neg, ← exp_add]
      congr 1
      ring

end Field

section Adelic

open Formalism.L2.Herm Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem exists_valuation (F : Type) [Field F] [NumberField F] [Algebra F E] (Q : HeightOneSpectrum (𝓞 E)) :
    ∃ ν : Valuation (E ⊗[F] Af F) ℤᵐ⁰, (∀ x : E, ν (inclE (F := F) (Af F) x) = Q.valuation E x) ∧
      ∀ y ∈ intAf F E, ν y ≤ 1 := by
  obtain ⟨ι, h1, h2, -⟩ := GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E
  refine ⟨(Valued.v : Valuation (Q.adicCompletion E) ℤᵐ⁰).comap ((evalV E Q).toRingHom.comp ι.toRingHom),
    fun x => ?_, fun y hy => (h2 y).1 hy Q⟩
  show Valued.v (ι (x ⊗ₜ[F] 1) Q) = _
  rw [h1, GlobalTheory.Idele.adele_algebraMap_apply, GlobalTheory.Idele.valued_algebraMap]

variable {Q : HeightOneSpectrum (𝓞 E)} {ν : Valuation (E ⊗[F] Af F) ℤᵐ⁰}
  (h1 : ∀ x : E, ν (inclE (F := F) (Af F) x) = Q.valuation E x) (h2 : ∀ y ∈ intAf F E, ν y ≤ 1)

theorem det_inclE (x : Fin N → Fin N → E) :
    (Matrix.of fun i j => inclE (F := F) (Af F) (x i j)).det = inclE (F := F) (Af F) (Matrix.of x).det := by
  rw [RingHom.map_det]
  rfl

include h1 h2

theorem val_det_hat_le {M : Submodule (𝓞 E) (Fin N → E)} (h : M.FG)
    (hs : Submodule.span E (M : Set (Fin N → E)) = ⊤) {y : Fin N → Fin N → E ⊗[F] Af F}
    (hy : ∀ i, y i ∈ hatL (F := F) M) : ν (Matrix.of y).det ≤ exp (-FractionalIdeal.count E Q (detFI M h)) := by
  choose n c m e using fun i => Submodule.mem_span_set'.1 (hy i)
  choose x hx ex using fun i k => (m i k).2
  have e1 : (Matrix.of y).det = Matrix.detRowAlternating.toMultilinearMap
      fun i => ∑ k, (c i k : E ⊗[F] Af F) • fun j => inclE (F := F) (Af F) (x i k j) := by
    show Matrix.detRowAlternating.toMultilinearMap y = _
    congr 1
    funext i
    rw [← e i]
    exact Finset.sum_congr rfl fun k _ => by rw [← ex i k]; rfl
  rw [e1, MultilinearMap.map_sum]
  refine ν.map_sum_le fun r _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul, map_mul]
  refine (mul_le_of_le_one_left' (h2 _ (prod_mem fun i _ => (c i (r i)).2))).trans ?_
  have e2 := det_inclE (F := F) fun i => x i (r i)
  have e3 := congrArg ν e2
  rw [h1] at e3
  exact e3.trans_le (val_det_le h hs Q fun i => hx i (r i))

theorem val_det_mul_le {M M' : Submodule (𝓞 E) (Fin N → E)} (h : M.FG)
    (hs : Submodule.span E (M : Set (Fin N → E)) = ⊤) (h' : M'.FG)
    (hs' : Submodule.span E (M' : Set (Fin N → E)) = ⊤) {A : Matrix (Fin N) (Fin N) (E ⊗[F] Af F)}
    (hA : ∀ v ∈ hatL (F := F) M, A.mulVec v ∈ hatL (F := F) M') :
    ν A.det * exp (-FractionalIdeal.count E Q (detFI M h)) ≤ exp (-FractionalIdeal.count E Q (detFI M' h')) := by
  obtain ⟨x, hx, e⟩ := exists_val_det_eq h hs Q
  have h3 := val_det_hat_le h1 h2 h' hs' (y := fun i => A.mulVec fun j => inclE (F := F) (Af F) (x i j))
    fun i => hA _ (Submodule.subset_span ⟨x i, hx i, rfl⟩)
  rwa [det_of_mulVec', map_mul, det_inclE, h1, e] at h3

theorem val_det_of_carries {M M' : Submodule (𝓞 E) (Fin N → E)} (h : M.FG)
    (hs : Submodule.span E (M : Set (Fin N → E)) = ⊤) (h' : M'.FG)
    (hs' : Submodule.span E (M' : Set (Fin N → E)) = ⊤) {g : GL (Fin N) (E ⊗[F] Af F)} (hg : Carries g M M') :
    ν (g : Matrix (Fin N) (Fin N) (E ⊗[F] Af F)).det =
      exp (-FractionalIdeal.count E Q (detFI M' h' * (detFI M h)⁻¹)) := by
  have a := val_det_mul_le h1 h2 h hs h' hs' (A := (g : Matrix (Fin N) (Fin N) (E ⊗[F] Af F))) fun v hv => (hg _).2 (by
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec])
  have b := val_det_mul_le h1 h2 h' hs' h hs (A := ((g⁻¹ : GL (Fin N) (E ⊗[F] Af F)) : Matrix _ _ _))
    fun v hv => (hg _).1 hv
  have c : ν (g : Matrix (Fin N) (Fin N) (E ⊗[F] Af F)).det *
      ν ((g⁻¹ : GL (Fin N) (E ⊗[F] Af F)) : Matrix (Fin N) (Fin N) (E ⊗[F] Af F)).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one]
  have a0 := left_ne_zero_of_mul_eq_one c
  have b0 := right_ne_zero_of_mul_eq_one c
  rw [← exp_log a0, ← exp_add, exp_le_exp] at a
  rw [← exp_log b0, ← exp_add, exp_le_exp] at b
  rw [← exp_log a0, ← exp_log b0, ← exp_add, ← exp_zero, exp_inj] at c
  rw [← exp_log a0, exp_inj, FractionalIdeal.count_mul E Q (detFI_ne_zero h' hs') (inv_ne_zero (detFI_ne_zero h hs)),
    FractionalIdeal.count_inv]
  omega

variable [StarRing E]

theorem val_det_of_mem_int (hc : Formalism.BasicNotions.CMData F E) {u : GL (Fin 1) (E ⊗[F] Af F)} (hu : u ∈ IntegralUnitGroup hc) :
    ν (u : Matrix (Fin 1) (Fin 1) (E ⊗[F] Af F)).det = 1 := by
  have key : ∀ u ∈ IntegralUnitGroup hc, ν (u : Matrix (Fin 1) (Fin 1) (E ⊗[F] Af F)).det ≤ 1 := fun u hu => by
    obtain ⟨r, hr⟩ := (hu.2 fun _ => 1).1 (fun i _ => ⟨1, rfl⟩) 0 trivial
    rw [Matrix.det_fin_one]
    have : (u : Matrix (Fin 1) (Fin 1) (E ⊗[F] Af F)) 0 0 = algebraMap _ (E ⊗[F] Af F) r := by
      simpa [Matrix.mulVec, dotProduct] using hr.symm
    rw [this]
    exact h2 _ r.2
  have c : ν (u : Matrix (Fin 1) (Fin 1) (E ⊗[F] Af F)).det *
      ν ((u⁻¹ : GL (Fin 1) (E ⊗[F] Af F)) : Matrix (Fin 1) (Fin 1) (E ⊗[F] Af F)).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one]
  refine le_antisymm (key u hu) ?_
  rw [← c]
  exact mul_le_of_le_one_right' (key _ (inv_mem hu))

omit h1 h2 in

theorem exists_u1Af (hc : Formalism.BasicNotions.CMData F E) (z : unitary E) : ∃ x : unitaryOneFiniteAdeles hc,
    Matrix.GeneralLinearGroup.det (x : GL (Fin 1) (E ⊗[F] Af F)) = unitaryOneRationalAdele F z := by
  refine ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 1) (unitaryOneRationalAdele F z), ?_⟩, Units.ext ?_⟩
  · show cT _ _ * _ * _ = _
    ext i j
    have hz : star (z : E) * z = 1 := z.2.1
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [cT, Matrix.mul_apply, unitaryOneRationalAdele, inclE, sigR, Formalism.BasicNotions.CMData.sig]
    rw [starRingEnd_apply, hz]
  · simp

omit h1 h2 in

theorem val_eq_pow (hc : Formalism.BasicNotions.CMData F E) {G : Type} [Group G] (dt : unitaryOneFiniteAdeles hc →* G)
    (hker : ∀ x : unitaryOneFiniteAdeles hc, dt x = 1 → (x : GL (Fin 1) (E ⊗[F] Af F)) ∈ IntegralUnitGroup hc) {z : unitary E} {x : unitaryOneFiniteAdeles hc}
    {U : Subgroup G} (hU : U = ((IntegralUnitGroup hc).subgroupOf (unitaryOneFiniteAdeles hc)).map dt) {t k : G} (hk : k ∈ U)
    (ht : ∀ y : unitaryOneFiniteAdeles hc, Matrix.GeneralLinearGroup.det (y : GL (Fin 1) (E ⊗[F] Af F)) = unitaryOneRationalAdele F z → t = dt y) {n : ℕ}
    (e : dt x ^ n = t * k) {M M' : Submodule (𝓞 E) (Fin N → E)} (h : M.FG)
    (hs : Submodule.span E (M : Set (Fin N → E)) = ⊤) (h' : M'.FG)
    (hs' : Submodule.span E (M' : Set (Fin N → E)) = ⊤) {g : GL (Fin N) (E ⊗[F] Af F)} (hg : Carries g M M')
    (hx : IsDetOf hc x g) (Q : HeightOneSpectrum (𝓞 E)) :
    Q.valuation E (z : E) = exp (-FractionalIdeal.count E Q (detFI M' h' * (detFI M h)⁻¹)) ^ n := by
  subst hU
  obtain ⟨u, hu, rfl⟩ := hk
  replace hu : (u : GL (Fin 1) (E ⊗[F] Af F)) ∈ IntegralUnitGroup hc := hu
  obtain ⟨y, hy⟩ := exists_u1Af hc z
  rw [ht y hy] at e
  have hint : ((y⁻¹ * x ^ n : unitaryOneFiniteAdeles hc) : GL (Fin 1) (E ⊗[F] Af F)) ∈ IntegralUnitGroup hc := by
    have h1 := hker (y⁻¹ * x ^ n * u⁻¹) (by
      rw [map_mul, map_mul, map_pow, e, map_inv, map_inv, inv_mul_cancel_left, mul_inv_cancel])
    have h2 := mul_mem h1 hu
    rwa [← Subgroup.coe_mul, inv_mul_cancel_right] at h2
  obtain ⟨ν, h1, h2⟩ := exists_valuation F Q
  have a := val_det_of_carries h1 h2 h hs h' hs' hg
  have b := val_det_of_mem_int h1 h2 hc hint
  have c : ((y : GL (Fin 1) (E ⊗[F] Af F)) : Matrix (Fin 1) (Fin 1) _).det *
      (((y⁻¹ * x ^ n : unitaryOneFiniteAdeles hc) : GL (Fin 1) (E ⊗[F] Af F)) : Matrix (Fin 1) (Fin 1) _).det =
      (g : Matrix (Fin N) (Fin N) (E ⊗[F] Af F)).det ^ n := by
    rw [← Matrix.det_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel_left, Subgroup.coe_pow,
      Units.val_pow_eq_pow_val, Matrix.det_pow]
    exact congrArg (fun t : (E ⊗[F] Af F)ˣ => (t : E ⊗[F] Af F) ^ n) hx
  have d : ((y : GL (Fin 1) (E ⊗[F] Af F)) : Matrix (Fin 1) (Fin 1) _).det =
      inclE (F := F) (Af F) (z : E) := congrArg Units.val hy
  have f := congrArg ν c
  rwa [map_mul, b, mul_one, d, h1, map_pow, a] at f

end Adelic

section Host

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def bar (w : HeightOneSpectrum (𝓞 H.E)) : HeightOneSpectrum (𝓞 H.E) :=
  (existsUnique_conjPl H.conj.toRingEquiv w).choose

theorem val_bar (w : HeightOneSpectrum (𝓞 H.E)) (x : H.E) : (bar H w).valuation H.E (H.conj x) = w.valuation H.E x :=
  (existsUnique_conjPl H.conj.toRingEquiv w).choose_spec.1 x

theorem isConjPl_iff (w w' : HeightOneSpectrum (𝓞 H.E)) : IsConjPl H w w' ↔ w' = bar H w := by
  rw [conjPl_main.2.1 R H w w']
  exact ⟨(existsUnique_conjPl H.conj.toRingEquiv w).choose_spec.2 w', fun h => h ▸ val_bar H w⟩

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  letI := H.cmStar
  have hs : ∀ x : H.E, star x = H.conj x := bridge_star_holds R H
  rw [← hs, ← hs, star_star]

theorem val_conj (w : HeightOneSpectrum (𝓞 H.E)) (x : H.E) : w.valuation H.E (H.conj x) = (bar H w).valuation H.E x := by
  rw [← val_bar H w, conj_conj]

theorem bar_bar (w : HeightOneSpectrum (𝓞 H.E)) : bar H (bar H w) = w :=
  ((existsUnique_conjPl H.conj.toRingEquiv (bar H w)).choose_spec.2 w fun x => val_conj H w x).symm

def expo (a : Ideles H.E) (w : HeightOneSpectrum (𝓞 H.E)) : ℤ := log (valAt (bar H w) a) - log (valAt w a)

theorem expo_finite (a : Ideles H.E) : {w | expo H a w ≠ 0}.Finite := by
  have h := finite_valAt_ne_one a
  refine (h.union (h.image (bar H))).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn
  have h2 : valAt (bar H w) a = 1 := by
    by_contra h3
    exact hn.2 ⟨bar H w, h3, bar_bar H w⟩
  exact hw (by simp [expo, hn.1, h2])

theorem expo_mul (a b : Ideles H.E) (w : HeightOneSpectrum (𝓞 H.E)) : expo H (a * b) w = expo H a w + expo H b w := by
  simp only [expo, map_mul, log_mul (valAt_ne_zero _ _) (valAt_ne_zero _ _)]
  ring

theorem expo_bar (a : Ideles H.E) (w : HeightOneSpectrum (𝓞 H.E)) : expo H a (bar H w) = -expo H a w := by
  simp [expo, bar_bar]

def normIdeal : Ideles H.E →* FractionalIdeal (𝓞 H.E)⁰ H.E where
  toFun a := idealExp (expo H a)
  map_one' := GlobalTheory.Idele.eq_of_count_eq (idealExp_ne_zero _) one_ne_zero fun w => by
    rw [count_idealExp (expo_finite H _), FractionalIdeal.count_one]
    simp [expo]
  map_mul' a b := GlobalTheory.Idele.eq_of_count_eq (idealExp_ne_zero _)
    (mul_ne_zero (idealExp_ne_zero _) (idealExp_ne_zero _)) fun w => by
      rw [FractionalIdeal.count_mul _ w (idealExp_ne_zero _) (idealExp_ne_zero _), count_idealExp (expo_finite H _),
        count_idealExp (expo_finite H _), count_idealExp (expo_finite H _), expo_mul]

theorem normIdeal_ne_zero (a : Ideles H.E) : normIdeal H a ≠ 0 := idealExp_ne_zero _

theorem count_normIdeal (a : Ideles H.E) (w : HeightOneSpectrum (𝓞 H.E)) :
    FractionalIdeal.count H.E w (normIdeal H a) = expo H a w := count_idealExp (expo_finite H a) w

theorem normIdeal_eq_one_iff (a : Ideles H.E) : normIdeal H a = 1 ↔ a ∈ KD H ⊔ unitIdl H.E := by
  rw [mem_KD_sup_unitIdl_iff]
  constructor
  · intro h w w' hw
    obtain rfl := (isConjPl_iff H w w').1 hw
    have := count_normIdeal H a w
    rw [h, FractionalIdeal.count_one, expo, eq_comm, sub_eq_zero] at this
    rw [← valAt_apply, ← valAt_apply, ← exp_log (valAt_ne_zero w a), ← this, exp_log (valAt_ne_zero _ a)]
  · intro h
    refine GlobalTheory.Idele.eq_of_count_eq (normIdeal_ne_zero H a) one_ne_zero fun w => ?_
    have := h w _ ((isConjPl_iff H w _).2 rfl)
    rw [← valAt_apply, ← valAt_apply] at this
    rw [count_normIdeal, FractionalIdeal.count_one, expo, this, sub_self]

def classIdeal : DtT H ⧸ UOT H →* FractionalIdeal (𝓞 H.E)⁰ H.E :=
  QuotientGroup.lift (UOT H)
    (QuotientGroup.lift (KD H) (normIdeal H) fun a ha => (normIdeal_eq_one_iff H a).2 (Subgroup.mem_sup_left ha))
    (by
      rintro _ ⟨a, ha, rfl⟩
      exact (normIdeal_eq_one_iff H a).2 (Subgroup.mem_sup_right ha))

theorem classIdeal_mk (a : Ideles H.E) :
    classIdeal H (QuotientGroup.mk (QuotientGroup.mk a)) = normIdeal H a := rfl

theorem exists_mk_mk (x : DtT H ⧸ UOT H) : ∃ a : Ideles H.E, x = QuotientGroup.mk (QuotientGroup.mk a) := by
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective t
  exact ⟨a, rfl⟩

theorem classIdeal_injective : Function.Injective (classIdeal H) := by
  refine (injective_iff_map_eq_one _).2 fun x hx => ?_
  obtain ⟨a, rfl⟩ := exists_mk_mk H x
  rw [classIdeal_mk, normIdeal_eq_one_iff, ← QuotientGroup.comap_map_mk'] at hx
  exact (QuotientGroup.eq_one_iff _).2 hx

theorem expo_pos_part {n : HeightOneSpectrum (𝓞 H.E) → ℤ} (hf : {w | n w ≠ 0}.Finite) (hn : ∀ w, n (bar H w) = -n w)
    (w : HeightOneSpectrum (𝓞 H.E)) :
    expo H (∏ᶠ w : HeightOneSpectrum (𝓞 H.E), localIdele H.E w (atFin w (unif w)) ^ (n w).toNat) w = n w := by
  classical
  have e : (∏ᶠ w : HeightOneSpectrum (𝓞 H.E), localIdele H.E w (atFin w (unif w)) ^ (n w).toNat) =
      ∏ w ∈ hf.toFinset, localIdele H.E w (atFin w (unif w)) ^ ((n w).toNat : ℤ) := by
    simp only [zpow_natCast]
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    rw [Set.Finite.coe_toFinset]
    intro h0
    exact hv (by simp [h0])
  have h1 : ∀ v, log (valAt v (∏ w ∈ hf.toFinset, localIdele H.E w (atFin w (unif w)) ^ ((n w).toNat : ℤ))) =
      -((n v).toNat : ℤ) := fun v => by
    rw [valAt_prod, log_exp]
    split_ifs with h
    · rfl
    · have : n v = 0 := by simpa using h
      simp [this]
  rw [e, expo, h1, h1, hn]
  omega

theorem normOne_iff (𝔞 : Submodule (𝓞 H.E) H.E) :
    (∃ 𝔟 : Submodule (𝓞 H.E) H.E, (∀ x, x ∈ 𝔟 ↔ H.conj x ∈ 𝔞) ∧ 𝔞 * 𝔟 = 1) ↔
      ∃ x, ((classIdeal H x : FractionalIdeal (𝓞 H.E)⁰ H.E) : Submodule (𝓞 H.E) H.E) = 𝔞 := by
  constructor
  · rintro ⟨𝔟, hb, h⟩
    have hu : IsUnit 𝔞 := IsUnit.of_mul_eq_one 𝔟 h
    have hv : IsUnit 𝔟 := IsUnit.of_mul_eq_one 𝔞 (by rw [mul_comm]; exact h)
    let I : FractionalIdeal (𝓞 H.E)⁰ H.E := ⟨𝔞, FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit hu)⟩
    let J : FractionalIdeal (𝓞 H.E)⁰ H.E := ⟨𝔟, FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit hv)⟩
    have hIJ : I * J = 1 := by
      apply FractionalIdeal.coeToSubmodule_injective
      simp only [FractionalIdeal.coe_mul, FractionalIdeal.coe_one]
      exact h
    have hI := left_ne_zero_of_mul_eq_one hIJ
    have hJ := right_ne_zero_of_mul_eq_one hIJ
    have hn : ∀ w, FractionalIdeal.count H.E (bar H w) I = -FractionalIdeal.count H.E w I := fun w => by
      have h1 := FractionalIdeal.count_mul H.E w hI hJ
      rw [hIJ, FractionalIdeal.count_one] at h1
      obtain ⟨x, hx, ex⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI (bar H w)
      obtain ⟨y, hy, ey⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hJ w
      have hx' : H.conj x ∈ J := (hb _).2 (by rw [conj_conj]; exact hx)
      have hy' : H.conj y ∈ I := (hb _).1 hy
      have h2 := (GlobalTheory.Idele.mem_iff_valuation_le hJ _).1 hx' w
      have h3 := (GlobalTheory.Idele.mem_iff_valuation_le hI _).1 hy' (bar H w)
      rw [val_conj, ex, exp_le_exp] at h2
      rw [val_bar, ey, exp_le_exp] at h3
      omega
    refine ⟨QuotientGroup.mk (QuotientGroup.mk (∏ᶠ w : HeightOneSpectrum (𝓞 H.E),
      localIdele H.E w (atFin w (unif w)) ^ (FractionalIdeal.count H.E w I).toNat)), ?_⟩
    rw [classIdeal_mk, GlobalTheory.Idele.eq_of_count_eq (normIdeal_ne_zero H _) hI fun w => by
      rw [count_normIdeal, expo_pos_part H (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I)) hn]]
    rfl
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := exists_mk_mk H x
    rw [classIdeal_mk]
    have h0 := normIdeal_ne_zero H a
    refine ⟨((normIdeal H a)⁻¹ : FractionalIdeal (𝓞 H.E)⁰ H.E), fun x => ?_, ?_⟩
    · rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_coe, GlobalTheory.Idele.mem_iff_valuation_le h0,
        GlobalTheory.Idele.mem_iff_valuation_le (inv_ne_zero h0)]
      simp only [FractionalIdeal.count_inv, count_normIdeal, val_conj]
      refine ⟨fun h w => ?_, fun h w => ?_⟩
      · simpa [expo_bar] using h (bar H w)
      · simpa [expo_bar, bar_bar] using h (bar H w)
    · rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ h0, FractionalIdeal.coe_one]

theorem classIdeal_e1T : letI := H.cmStar
    ∀ z : unitary H.E, classIdeal H (QuotientGroup.mk (e1T H z)) = FractionalIdeal.spanSingleton (𝓞 H.E)⁰ (z : H.E) := by
  letI := H.cmStar
  intro z
  obtain ⟨k, hk⟩ := GlobalTheory.Mem.Col2.exists_eq_div_conj H z
  have hz : (z : H.E) ≠ 0 := fun h => k.ne_zero (by rw [← hk, h, zero_mul])
  rw [← GlobalTheory.Mem.Col2.isRationalUnitaryDeterminantMap_rationalUnitary H k z hk, classIdeal_mk]
  refine GlobalTheory.Idele.eq_of_count_eq (normIdeal_ne_zero H _) (FractionalIdeal.spanSingleton_ne_zero_iff.2 hz) fun w => ?_
  have hv : ∀ v : HeightOneSpectrum (𝓞 H.E), valAt v (diagUnits H.E k) = v.valuation H.E (k : H.E) := fun v =>
    GlobalTheory.Idele.valued_algebraMap v (k : H.E)
  have h1 := congrArg (fun x => log (w.valuation H.E x)) hk
  simp only [map_mul, val_conj] at h1
  rw [log_mul (by simpa using hz) (by simp), GlobalTheory.Idele.valuation_eq_exp_neg_count w hz, log_exp] at h1
  rw [count_normIdeal, expo, hv, hv]
  omega

theorem classIdeal_relDetT (N : ℕ) : letI := H.cmStar
    ∀ L L' : SDLat H.E N, classIdeal H (relDetT H N L.1 L'.1) = detFI L'.1 L'.2.1 * (detFI L.1 L.2.1)⁻¹ := by
  letI := H.cmStar
  intro L L'
  have hn := detFI_ne_zero L.2.1 L.2.2.1
  have hn' := detFI_ne_zero L'.2.1 L'.2.2.1
  rw [relDetT, classIdeal_mk]
  refine GlobalTheory.Idele.eq_of_count_eq (normIdeal_ne_zero H _) (mul_ne_zero hn' (inv_ne_zero hn)) fun w => ?_
  rw [count_normIdeal, expo_pos_part H (n := fun w => ordSub w (detSub L'.1) - ordSub w (detSub L.1)),
    FractionalIdeal.count_mul _ w hn' (inv_ne_zero hn), FractionalIdeal.count_inv, ← ordSub_coe hn, ← ordSub_coe hn',
    sub_eq_add_neg]
  · rfl
  · refine ((ordSub_detSub_lattice _ N L.1 L.2.1 L.2.2.1).1.union
      (ordSub_detSub_lattice _ N L'.1 L'.2.1 L'.2.2.1).1).subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at h
    exact hv (by simp [h.1, h.2])
  · intro v
    have h1 := ordSub_detSub_selfDual R H N L v _ ((isConjPl_iff H v _).2 rfl)
    have h2 := ordSub_detSub_selfDual R H N L' v _ ((isConjPl_iff H v _).2 rfl)
    omega

end Host

section Record

open Formalism.MainNotions.TaylorLogMetric Formalism.L2.Herm Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem detId_eq (D : D7) {N : ℕ} (L L' : SDLat D.host.E N) : detId D L.1 L'.1 =
    ((detFI L'.1 L'.2.1 * (detFI L.1 L.2.1)⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : IdE D) :=
  span_det_eq L.2.1 L.2.2.1 L'.2.1 L'.2.2.1

theorem pinned_of_equiv (D : D7) (e : DtT D.host ⧸ UOT D.host ≃* D.Dt ⧸ D.UO)
    (h1 : ∀ z, QuotientGroup.mk (D.e1Dt z) = e (QuotientGroup.mk (e1T D.host z)))
    (h2 : ∀ N (L L' : SDLat D.host.E N), D.relDet N L L' = e (relDetT D.host N L.1 L'.1)) :
    RelDetPinned D fun x => (classIdeal D.host (e.symm x) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  refine ⟨fun x y h => e.symm.injective (classIdeal_injective _ (FractionalIdeal.coeToSubmodule_injective h)),
    fun 𝔞 => (normOne_iff D.host 𝔞).trans ⟨fun ⟨x, hx⟩ => ⟨e x, by simpa using hx⟩, fun ⟨x, hx⟩ => ⟨_, hx⟩⟩,
    fun x y => ?_, fun z => ?_, fun N L L' => ?_⟩
  · simp only [map_mul, FractionalIdeal.coe_mul]
  · simp only [h1, e.symm_apply_apply, classIdeal_e1T D.host z, FractionalIdeal.coe_spanSingleton]
  · simp only [h2, e.symm_apply_apply, classIdeal_relDetT D.host N L L', detId_eq]

theorem relDet_eq_of_pinned (D : D7) (idl : D.Dt ⧸ D.UO → IdE D) (hp : RelDetPinned D idl)
    (hc : Formalism.BasicNotions.CMData D.host.F D.host.E) (dt : unitaryOneFiniteAdeles hc →* D.Dt)
    (hker : ∀ x : unitaryOneFiniteAdeles hc, dt x = 1 → (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Af D.host.F)) ∈ IntegralUnitGroup hc)
    (hUO : D.UO = ((IntegralUnitGroup hc).subgroupOf (unitaryOneFiniteAdeles hc)).map dt)
    (hrat : ∀ (z : unitary D.host.E) (x : unitaryOneFiniteAdeles hc),
      Matrix.GeneralLinearGroup.det (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Af D.host.F)) = unitaryOneRationalAdele D.host.F z →
      D.e1Dt z = dt x)
    {N : ℕ} (L L' : SDLat D.host.E N) (g : GL (Fin N) (D.host.E ⊗[D.host.F] Af D.host.F)) (x : unitaryOneFiniteAdeles hc)
    (hg : Carries g L.1 L'.1) (hx : IsDetOf hc x g) : D.relDet N L L' = QuotientGroup.mk (dt x) := by
  obtain ⟨h, z, hh, k, hk, e⟩ := Formalism.MainNotions.GL3Theta.powRatAll_of D idl hp (GlobalTheory.KernelScalarUnit.normOne_pow D) (dt x)
  obtain ⟨hinj, hN, hmul, hz, hdet⟩ := hp
  have e' : (QuotientGroup.mk (dt x) : D.Dt ⧸ D.UO) ^ h = QuotientGroup.mk (D.e1Dt z) := by
    rw [← QuotientGroup.mk_pow, e, QuotientGroup.mk_mul_of_mem _ hk]
  obtain ⟨𝔟, -, hb⟩ := (hN _).2 ⟨QuotientGroup.mk (dt x), rfl⟩
  have hJz : idl (QuotientGroup.mk (dt x)) ^ h = Submodule.span (𝓞 D.host.E) {(z : D.host.E)} := by
    obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
    rw [← hz, ← e', Formalism.MainNotions.GL3Theta.idl_pow hmul]
  have hz0 : (z : D.host.E) ≠ 0 := right_ne_zero_of_mul_eq_one z.2.1
  refine hinj ((hdet N L L').trans ((detId_eq D L L').trans ?_))
  exact coe_eq_of_pow hb
    (mul_ne_zero (detFI_ne_zero L'.2.1 L'.2.2.1) (inv_ne_zero (detFI_ne_zero L.2.1 L.2.2.1))) hz0 hh hJz
    (val_eq_pow hc dt hker hUO hk (hrat z) e L.2.1 L.2.2.1 L'.2.1 L'.2.2.1 hg hx)

open GlobalTheory.Mem.Col2 in

theorem pinned_of_finer (D : D7) (SQ : Finset (HeightOneSpectrum (𝓞 D.host.E))) (ε : DtQ D.host SQ ≃* D.Dt)
    (hU : D.UO = (UOQ D.host SQ).map ε.toMonoidHom) (h1 : ∀ z, D.e1Dt z = ε (e1Q D.host SQ z))
    (h2 : ∀ (N : ℕ) (L L' : SDLat D.host.E N) (t : DtQ D.host SQ), relDetQ D.host SQ N L.1 L'.1 = QuotientGroup.mk t →
      D.relDet N L L' = QuotientGroup.mk (ε t)) : ∃ idl : D.Dt ⧸ D.UO → IdE D, RelDetPinned D idl := by
  let e : DtQ D.host SQ ⧸ UOQ D.host SQ ≃* D.Dt ⧸ D.UO := QuotientGroup.congr _ _ ε hU.symm
  have he : ∀ t, e (QuotientGroup.mk t) = QuotientGroup.mk (ε t) := fun _ => rfl
  have hm : ∀ t, (modEquiv D.host SQ).symm (toDtTMod D.host SQ t) = t := (modEquiv D.host SQ).symm_apply_apply
  refine ⟨_, pinned_of_equiv D ((modEquiv D.host SQ).symm.trans e) (fun z => ?_) fun N L L' => ?_⟩
  · rw [MulEquiv.trans_apply, ← toDtT_e1Q D.host SQ z, ← toDtTMod_mk, hm, he, h1]
  · obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective (relDetQ D.host SQ N L.1 L'.1)
    rw [MulEquiv.trans_apply, ← toDtTMod_relDetQ D.host SQ, hm, h2 N L L' t ht.symm, ← ht, he]

end Record

end GlobalTheory.Mem.NormOneIdeal
