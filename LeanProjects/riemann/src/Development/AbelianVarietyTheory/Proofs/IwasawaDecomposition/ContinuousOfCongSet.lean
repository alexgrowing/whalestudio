import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdInfMulFinPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqOfMapEq

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
open Formalism.L2.DIV (AfE RInt congN congU intU suppAt inertAt wildAt ratId idF GoodPl)
open scoped TensorProduct

namespace GlobalTheory.Mem.ReadEx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

def toIdl : (AfE F E)ˣ →* Ideles E :=
  Units.map ((MonoidHom.inr (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)).comp
    (afIso F E : AfE F E →* FiniteAdeleRing (𝓞 E) E))

theorem toIdl_fst (y : (AfE F E)ˣ) : (toIdl F E y : AdeleRing (𝓞 E) E).1 = 1 := rfl

theorem toIdl_snd (y : (AfE F E)ˣ) : (toIdl F E y : AdeleRing (𝓞 E) E).2 = afIso F E y := rfl

theorem toIdl_finAf (a : Ideles E) : toIdl F E (finAf F E a) = finPartI E a :=
  Units.ext (Prod.ext rfl (afIso_finAf F E a))

theorem mem_intU_iff (y : (AfE F E)ˣ) : y ∈ intU F E ↔ toIdl F E y ∈ unitIdl E := by
  constructor
  · rintro ⟨h1, h2⟩ P
    have k1 : Valued.v (afIso F E (y : AfE F E) P) ≤ 1 := (mem_rInt_iff F E _).1 h1 P
    have k2 : Valued.v (afIso F E ((y⁻¹ : (AfE F E)ˣ) : AfE F E) P) ≤ 1 := (mem_rInt_iff F E _).1 h2 P
    have h : afIso F E (y : AfE F E) P * afIso F E ((y⁻¹ : (AfE F E)ˣ) : AfE F E) P = 1 := by
      have := congrArg (fun z => afIso F E z P) y.mul_inv
      simp only [map_mul, map_one] at this
      exact this
    have h3 := congrArg (Valued.v : Valuation (P.adicCompletion E) _) h
    rw [map_mul, map_one] at h3
    refine le_antisymm k1 ?_
    rw [← h3]
    exact mul_le_of_le_one_right' k2
  · intro h
    refine ⟨(mem_rInt_iff F E _).2 fun P => (h P).le, (mem_rInt_iff F E _).2 fun P => ?_⟩
    have h' := (unitIdl E).inv_mem h
    rw [← map_inv] at h'
    exact (h' P).le

theorem mem_congU_iff (I : Ideal (RInt F E)) (y : (AfE F E)ˣ) :
    y ∈ congU F E I ↔ y ∈ intU F E ∧ ∃ z ∈ I, (z : AfE F E) = y - 1 := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨(u : RInt F E).2, ((u⁻¹ : (RInt F E)ˣ) : RInt F E).2⟩, _, (Formalism.L2.DIV.mem_kerRed I u).1 hu, rfl⟩
  · rintro ⟨⟨h1, h2⟩, z, hz, e⟩
    refine ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext y.mul_inv, Subtype.ext y.inv_mul⟩,
      (Formalism.L2.DIV.mem_kerRed I _).2 ?_, Units.ext rfl⟩
    convert hz using 1
    exact Subtype.ext e.symm

theorem mem_congN_iff (N : ℕ) (y : (AfE F E)ˣ) :
    y ∈ congN F E N ↔ y ∈ intU F E ∧ ∃ c ∈ RInt F E, c * N = y - 1 := by
  unfold congN
  rw [mem_congU_iff]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨z, hz, e⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨c, c.2, by simpa using e⟩
  · rintro ⟨c, hc, e⟩
    exact ⟨⟨c, hc⟩ * N, Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, by simpa using e⟩

def congSet (L : Type) [Field L] [NumberField L] (N : ℕ) : Set (Ideles L) :=
  {a | a ∈ unitIdl L ∧ ∀ v, (algebraMap L (FiniteAdeleRing (𝓞 L) L) (N : L)⁻¹ * ((a : AdeleRing (𝓞 L) L).2 - 1)) v ∈
    v.adicCompletionIntegers L}

theorem isOpen_congSet (L : Type) [Field L] [NumberField L] (N : ℕ) : IsOpen (congSet L N) := by
  have hV : IsOpen {a : FiniteAdeleRing (𝓞 L) L | ∀ v, a v ∈ v.adicCompletionIntegers L} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have c1 : Continuous fun a : Ideles L => (a : AdeleRing (𝓞 L) L).2 := continuous_snd.comp Units.continuous_val
  exact UnitOpen.isOpen_unitIdl.inter (hV.preimage (continuous_const.mul (c1.sub continuous_const)))

theorem one_mem_congSet (L : Type) [Field L] [NumberField L] (N : ℕ) : (1 : Ideles L) ∈ congSet L N := by
  refine ⟨one_mem _, fun v => ?_⟩
  have h : ((1 : Ideles L) : AdeleRing (𝓞 L) L).2 = 1 := rfl
  rw [h, sub_self, mul_zero]
  exact zero_mem _

theorem continuous_of_congSet {L : Type} [Field L] [NumberField L] (ψ : Ideles L →* ℂˣ) (N : ℕ)
    (h : ∀ a ∈ congSet L N, ψ a = 1) : Continuous ψ := by
  refine continuous_of_continuousAt_one ψ ?_
  refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
  filter_upwards [(isOpen_congSet L N).mem_nhds (one_mem_congSet L N)] with a ha
  exact (h a ha).symm

theorem inv_mul_mul_nat {L : Type} [Field L] [NumberField L] {N : ℕ} (hN : 0 < N) (z : FiniteAdeleRing (𝓞 L) L) :
    algebraMap L (FiniteAdeleRing (𝓞 L) L) (N : L)⁻¹ * z * N = z := by
  rw [mul_right_comm, ← map_natCast (algebraMap L (FiniteAdeleRing (𝓞 L) L)), ← map_mul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one, one_mul]

theorem finAf_mem_congN {N : ℕ} (hN : 0 < N) {a : Ideles E} (ha : a ∈ congSet E N) : finAf F E a ∈ congN F E N := by
  rw [mem_congN_iff, mem_intU_iff, toIdl_finAf]
  refine ⟨ha.1, (afIso F E).symm (algebraMap E _ (N : E)⁻¹ * ((a : AdeleRing (𝓞 E) E).2 - 1)), ?_, ?_⟩
  · rw [mem_rInt_iff, RingEquiv.apply_symm_apply]
    exact ha.2
  · apply (afIso F E).injective
    rw [map_mul, RingEquiv.apply_symm_apply, map_natCast, inv_mul_mul_nat hN, map_sub, map_one, afIso_finAf]

theorem finAf_diag (k : Eˣ) : finAf F E (diagUnits E k) = ratId F E k :=
  Units.ext ((afIso F E).injective ((afIso_finAf F E _).trans (afIso_tmul_one F E k).symm))

theorem exists_reads {K : Type} [Field K] (σ : K →+* ℂ) (μ : Formalism.L2.DIV.Chr F E K) (h1 : (ratId F E).range ≤ μ.ker)
    (h2 : μ ∈ Formalism.L2.DIV.openChr F E K) : ∃ ξ : HChar E, Reads σ μ ξ := by
  obtain ⟨N, hN, h2⟩ := h2
  refine ⟨⟨(Units.map (σ : K →* ℂ)).comp (μ.comp (finAf F E)), continuous_of_congSet _ N fun a ha => ?_, fun k => ?_⟩,
    fun a => rfl⟩
  · have h : μ (finAf F E a) = 1 := h2 (finAf_mem_congN hN ha)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h, map_one]
  · have h : μ (ratId F E k) = 1 := h1 ⟨k, rfl⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, finAf_diag, h, map_one]

theorem map_finPartI [IsTotallyComplex E] {ξ : HChar E} {n : ℕ} (hn : 0 < n) (h : ξ.OrderDvd n) (a : Ideles E) :
    ξ.1 (finPartI E a) = ξ.1 a := by
  obtain ⟨y, hy⟩ := Determ.exists_prod_inf_mul_finPart a
  have key : ∀ (w : InfinitePlace E) (x : (w.Completion)ˣ), ξ.1 (infIdele E w x) = 1 := fun w x => by
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e x) hn
    have hz' : (e.symm z) ^ n = x := by rw [← map_pow, hz, e.symm_apply_apply]
    have h0 : e.symm z ≠ 0 := fun h0 => x.ne_zero (by rw [← hz', h0, zero_pow hn.ne'])
    have hx : x = Units.mk0 _ h0 ^ n := Units.ext hz'.symm
    rw [hx, map_pow, map_pow]
    exact congrArg (fun χ : HChar E => χ.1 (infIdele E w (Units.mk0 _ h0))) h
  conv_rhs => rw [← hy, map_mul, map_prod, Finset.prod_eq_one fun w _ => key w _, one_mul]

theorem exists_read {K : Type} [Field K] (σ : K →+* ℂ) (ξ : HChar E) (h1 : ∀ a, ξ.1 (finPartI E a) = ξ.1 a)
    (h2 : ∀ a, ((ξ.1 a : ℂˣ) : ℂ) ∈ σ.range) : ∃ μ : Formalism.L2.DIV.Chr F E K, Reads σ μ ξ := by
  have hi : Function.Injective (Units.map (σ : K →* ℂ)) := Units.map_injective σ.injective
  have h3 : ∀ y, ∃ k : Kˣ, Units.map (σ : K →* ℂ) k = ξ.1 (toIdl F E y) := fun y => by
    obtain ⟨k, hk⟩ := h2 (toIdl F E y)
    have h0 : k ≠ 0 := by
      rintro rfl
      exact Units.ne_zero _ (hk.symm.trans (map_zero σ))
    exact ⟨Units.mk0 k h0, Units.ext hk⟩
  choose f hf using h3
  refine ⟨MonoidHom.mk' f fun y z => hi ?_, fun a => ?_⟩
  · rw [map_mul, hf, hf, hf, map_mul, map_mul]
  · rw [← h1, ← toIdl_finAf (F := F), ← hf]
    rfl

theorem ker_of_reads {K : Type} [Field K] {σ : K →+* ℂ} {μ : Formalism.L2.DIV.Chr F E K} {ξ : HChar E} (h : Reads σ μ ξ)
    {y : (AfE F E)ˣ} (hy : ξ.1 (toIdl F E y) = 1) : y ∈ μ.ker := by
  have h1 := h.apply (toIdl F E y) y rfl
  rw [hy] at h1
  exact Units.ext (σ.injective (h1.symm.trans (map_one σ).symm))

variable (F) in

def evP (P : HeightOneSpectrum (𝓞 E)) : AfE F E →+* P.adicCompletion E where
  toFun z := afIso F E z P
  map_one' := by rw [map_one]; rfl
  map_mul' a b := by rw [map_mul]; rfl
  map_zero' := by rw [map_zero]; rfl
  map_add' a b := by rw [map_add]; rfl

theorem le_exp_neg_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem valued_le_of_pow {P : HeightOneSpectrum (𝓞 E)} {z c : AfE F E} (hc : c ∈ RInt F E) {m N : ℕ}
    (hN : (N : 𝓞 E) ∈ P.asIdeal) (h : c * N = z ^ m) : Valued.v (evP F P z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  have h1 : Valued.v (N : P.adicCompletion E) < 1 := by
    rw [← map_natCast (algebraMap E (P.adicCompletion E)), Formalism.UG.P.levelaf_valued_algebraMap,
      ← map_natCast (algebraMap (𝓞 E) E), HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hN
  have h2 : Valued.v (evP F P c) ≤ 1 := (mem_rInt_iff F E c).1 hc P
  have h3 := congrArg (fun t => Valued.v (evP F P t)) h
  simp only [map_mul, map_pow, map_natCast] at h3
  refine le_exp_neg_one (lt_of_not_ge fun h4 => ?_)
  have h5 := one_le_pow_of_one_le' h4 m
  rw [← h3] at h5
  exact absurd (h5.trans (mul_le_of_le_one_left' h2)) h1.not_ge

theorem map_toIdl_eq_one {ξ : HChar E} (ht : ∀ P, ξ.TameAt P) {y : (AfE F E)ˣ} (hy : y ∈ intU F E)
    (h : ∀ P, ¬ ξ.UnrAt P → Valued.v (evP F P (y - 1)) ≤ WithZero.exp (-((1 : ℕ) : ℤ))) : ξ.1 (toIdl F E y) = 1 := by
  have hu := (mem_intU_iff y).1 hy
  refine LocTriv.eq_one_of_local E ξ.1 ξ.2.1 _ hu (fun _ => rfl) fun P x hx => ?_
  have hx1 : IsUnitAt P x := by
    unfold IsUnitAt
    rw [hx]
    exact hu P
  by_cases hP : ξ.UnrAt P
  · exact hP x hx1
  · refine ht P x hx1 ?_
    have h1 := h P hP
    rw [map_sub, map_one] at h1
    rw [hx]
    exact h1

theorem valued_le_of_supp {v : HeightOneSpectrum (𝓞 F)} {y : (AfE F E)ˣ} (hy : y ∈ suppAt E v)
    {P : HeightOneSpectrum (𝓞 E)} (hP : P.under (𝓞 F) ≠ v) :
    Valued.v (evP F P (y - 1)) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  have h : evP F P y = 1 := (mem_suppAt_iff F E v y).1 hy P hP
  rw [map_sub, h, map_one, sub_self, map_zero]
  exact zero_le'

theorem exists_congN {ξ : HChar E} (ht : ∀ P, ξ.TameAt P) :
    ∃ N : ℕ, 0 < N ∧ ∀ y ∈ congN F E N, ξ.1 (toIdl F E y) = 1 := by
  classical
  have hf := UnrAe.finite_ramified ξ
  refine ⟨∏ P ∈ hf.toFinset, Ideal.absNorm P.asIdeal, Finset.prod_pos fun P _ =>
    Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), fun y hy => ?_⟩
  obtain ⟨h1, c, hc, e⟩ := (mem_congN_iff _ y).1 hy
  refine map_toIdl_eq_one ht h1 fun P hP => valued_le_of_pow hc (m := 1) ?_ (by rw [e, pow_one])
  rw [← Finset.mul_prod_erase _ _ (hf.mem_toFinset.2 hP), Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem map_wildAt {ξ : HChar E} (ht : ∀ P, ξ.TameAt P) {v : HeightOneSpectrum (𝓞 F)} {y : (AfE F E)ˣ}
    (hy : y ∈ wildAt E v) : ξ.1 (toIdl F E y) = 1 := by
  obtain ⟨⟨h1, z, ⟨m, hz⟩, e⟩, h2⟩ := And.intro ((mem_congU_iff _ y).1 hy.1) hy.2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hz
  refine map_toIdl_eq_one ht h1 fun P _ => ?_
  by_cases hP : P.under (𝓞 F) = v
  · refine valued_le_of_pow c.2 (m := m) (N := Formalism.EigenvalueLevelCeiling.plc v) ?_ ?_
    · have h3 : ((Formalism.EigenvalueLevelCeiling.plc v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
        exact ringChar.Nat.cast_ringChar
      subst hP
      rw [← map_natCast (algebraMap (𝓞 F) (𝓞 E))]
      exact h3
    · rw [← e]
      simpa using congrArg (RInt F E).subtype hc
  · exact valued_le_of_supp h2 hP

theorem map_inertAt {ξ : HChar E} (ht : ∀ P, ξ.TameAt P) {v : HeightOneSpectrum (𝓞 F)}
    (hv : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → ξ.UnrAt P) {y : (AfE F E)ˣ}
    (hy : y ∈ inertAt E v) : ξ.1 (toIdl F E y) = 1 :=
  map_toIdl_eq_one ht hy.1 fun P hP => valued_le_of_supp hy.2 fun e => hP (hv P e)

theorem afIso_one_tmul {a : FiniteAdeleRing (𝓞 F) F} {k : F} {P : HeightOneSpectrum (𝓞 E)}
    (h : a (P.under (𝓞 F)) = algebraMap F _ k) : afIso F E (1 ⊗ₜ[F] a) P = algebraMap E _ (algebraMap F E k) := by
  have h1 : ∀ n : ℕ, Valued.v (afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) ≤ WithZero.exp (-(n : ℤ)) :=
    fun n => (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2 a k P n
      (by rw [h, sub_self, map_zero]; exact zero_le')
  by_contra hne
  have h0 : Valued.v (afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact sub_ne_zero.2 hne
  have h2 := h1 (1 - WithZero.log (Valued.v (afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)))).toNat
  conv_lhs at h2 => rw [← WithZero.exp_log h0]
  rw [WithZero.exp_le_exp] at h2
  omega

variable (F E) in

def finF : Ideles F →* (AfE F E)ˣ :=
  (idF F E).comp (Units.map (MonoidHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))

theorem coe_finF (a : Ideles F) : (finF F E a : AfE F E) = 1 ⊗ₜ[F] (a : AdeleRing (𝓞 F) F).2 := rfl

theorem one_tmul_mem {a : FiniteAdeleRing (𝓞 F) F} (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) :
    (1 : E) ⊗ₜ[F] a ∈ RInt F E :=
  Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

theorem finF_mem_congN {N : ℕ} (hN : 0 < N) {a : Ideles F} (ha : a ∈ congSet F N) : finF F E a ∈ congN F E N := by
  rw [mem_congN_iff]
  refine ⟨⟨one_tmul_mem fun v => (ha.1 v).le, one_tmul_mem fun v => ((unitIdl F).inv_mem ha.1 v).le⟩, _,
    one_tmul_mem ha.2, ?_⟩
  rw [coe_finF, ← map_natCast (Algebra.TensorProduct.includeRight : FiniteAdeleRing (𝓞 F) F →ₐ[F] AfE F E),
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_mul_nat hN, one_mul,
    TensorProduct.tmul_sub, Algebra.TensorProduct.one_def]

theorem toIdl_finF_local (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    toIdl F E (finF F E (localIdele F v (atFin v k))) = locF F v k := by
  have hm : ∀ Q, Q ∈ aboveF (L := E) F v ↔ Q.under (𝓞 F) = v := fun Q => (finite_aboveF F v).mem_toFinset
  have h1 : toIdl F E (finF F E (localIdele F v (atFin v k))) =
      LocTriv.part (toIdl F E (finF F E (localIdele F v (atFin v k)))) (aboveF F v) := by
    refine Units.ext (Prod.ext (LocTriv.part_fst _ _).symm (FiniteAdeleRing.ext _ fun P => ?_))
    by_cases hP : P ∈ aboveF (L := E) F v
    · exact (LocTriv.ev_part_mem _ hP).symm
    · refine Eq.trans ?_ (LocTriv.ev_part_not_mem _ hP).symm
      have h2 := afIso_one_tmul (P := P) (k := (1 : F)) (a := (localIdele F v (atFin v k) : AdeleRing (𝓞 F) F).2)
        ((LocTriv.ev_local_ne (fun e => hP ((hm P).2 e)) (atFin v k)).trans (map_one (algebraMap F _)).symm)
      rw [map_one, map_one] at h2
      exact h2
  rw [h1]
  refine Finset.prod_congr rfl fun P hP => congrArg _ (Units.ext ?_)
  obtain rfl := (hm P).1 hP
  exact afIso_one_tmul (P := P) (k := (k : F)) (LocTriv.ev_local_self _ (atFin _ k))

theorem map_idF {ξ : HChar E} (ht : ∀ P, ξ.TameAt P) (hF : ξ.TrivOn F) (b : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ξ.1 (toIdl F E (idF F E b)) = 1 := by
  obtain ⟨N, hN, h⟩ := exists_congN (F := F) ht
  let ψ : Ideles F →* ℂˣ := ξ.1.comp ((toIdl F E).comp (finF F E))
  have hψ : Continuous ψ := continuous_of_congSet ψ N fun a ha => h _ (finF_mem_congN hN ha)
  refine Determ.eq_one_of_components hψ (fun v k => ?_) (fun k => ?_)
    (Units.map (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) b)
  · have h1 := hF.1 v k
    rw [HChar.resFin, MonoidHom.finsetProd_apply] at h1
    show ξ.1 (toIdl F E (finF F E (localIdele F v (atFin v k)))) = 1
    rw [toIdl_finF_local, locF, map_prod]
    exact h1
  · rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
    refine Finset.prod_eq_one fun w _ => ?_
    have h1 : finF F E (((infIdele F w).comp (atInf w)) k) = 1 := Units.ext rfl
    show ξ.1 (toIdl F E (finF F E (((infIdele F w).comp (atInf w)) k))) = 1
    rw [h1, map_one, map_one]

theorem exists_reads_tup : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (K : Type) [Field K] (σ : K →+* ℂ) (S : Set ℕ), (∀ μ : Formalism.L2.DIV.Tup H.F H.E K S, ∃ ξ : HChar H.E, Reads σ (μ.1 : Formalism.L2.DIV.Chr H.F H.E K) ξ) ∧ ∀ ξ : HChar H.E, IsTwist H S ξ → (∀ a, ((ξ.1 a : ℂˣ) : ℂ) ∈ σ.range) → ∃ μ : Formalism.L2.DIV.Tup H.F H.E K S, Reads σ (μ.1 : Formalism.L2.DIV.Chr H.F H.E K) ξ := by
  intro R H K _ σ S
  refine ⟨fun μ => exists_reads σ μ.1 μ.2.1.1.1.1.1 μ.2.1.1.1.1.2, ?_⟩
  rintro ξ ⟨⟨n, hn, hord⟩, hF, ht, hr⟩ hσ
  obtain ⟨c, -, hcm, -⟩ := HostCM.host_cm R H
  have := hcm.cplx
  have hfin := map_finPartI hn hord
  obtain ⟨μ, hμ⟩ := exists_read (F := H.F) σ ξ hfin hσ
  refine ⟨⟨μ, ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩⟩, hμ⟩
  · rintro _ ⟨k, rfl⟩
    refine ker_of_reads hμ ?_
    rw [← finAf_diag, toIdl_finAf, hfin]
    exact ξ.2.2 k
  · obtain ⟨N, hN, h⟩ := exists_congN (F := H.F) ht
    exact ⟨N, hN, fun y hy => ker_of_reads hμ (h y hy)⟩
  · refine isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, MonoidHom.ext fun y => ?_⟩
    have h1 : y ^ n ∈ μ.ker := ker_of_reads hμ (by
      rw [map_pow, map_pow]
      exact congrArg (fun χ : HChar H.E => χ.1 (toIdl H.F H.E y)) hord)
    rw [MonoidHom.mem_ker, map_pow] at h1
    exact h1
  · rintro _ ⟨b, rfl⟩
    exact ker_of_reads hμ (map_idF ht hF b)
  · exact Subgroup.mem_iInf.2 fun v y hy => ker_of_reads hμ (map_wildAt ht hy)
  · refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv y hy =>
      ker_of_reads hμ (map_inertAt ht (fun P hP => by_contra fun hn => hv ?_) hy)
    subst hP
    exact (GoodPlace.goodPl_under_iff R H S P).2 (hr P hn)

end GlobalTheory.Mem.ReadEx

end
