import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProof

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open IsDedekindDomain NumberField HeightOneSpectrum Filter
open scoped WithZero Topology

namespace LocFldPf

lemma lt_one_iff_le (g : ℤᵐ⁰) : g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
  induction g using WithZero.expRecOn with
  | zero => simp
  | exp a => rw [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]; omega

section Compl

variable {R : Type} [CommRing R] [IsDedekindDomain R] {L : Type} [Field L] [Algebra R L]
  [IsFractionRing R L] (w : HeightOneSpectrum R)

local notation "Lw" => adicCompletion L w
local notation "Ow" => adicCompletionIntegers L w

lemma v_algebraMap (l : L) : Valued.v (algebraMap L Lw l) = w.valuation L l :=
  valuedAdicCompletion_eq_valuation' w l

lemma exists_unif : ∃ π : Ow, Valued.v (π : Lw) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer L
  have h : Valued.v (algebraMap L Lw π) = WithZero.exp (-1 : ℤ) := by
    rw [v_algebraMap, hπ]
  refine ⟨⟨algebraMap L Lw π, ?_⟩, h⟩
  rw [mem_adicCompletionIntegers, h]
  exact ((lt_one_iff_le _).2 le_rfl).le

lemma mem_max_iff (x : Ow) :
    x ∈ IsLocalRing.maximalIdeal Ow ↔ Valued.v (x : Lw) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have : Valued.v (x : Lw) ≤ 1 := (mem_adicCompletionIntegers R L w).1 x.2
  exact ⟨fun h => lt_of_le_of_ne this h, fun h => h.ne⟩

lemma max_eq_span {π : Ow} (hπ : Valued.v (π : Lw) = WithZero.exp (-1 : ℤ)) :
    IsLocalRing.maximalIdeal Ow = Ideal.span {π} := by
  ext x
  rw [mem_max_iff, Ideal.mem_span_singleton, lt_one_iff_le, ← hπ]
  exact (adicCompletionIntegers.integers L w).le_iff_dvd

lemma mem_max_pow_iff {π : Ow} (hπ : Valued.v (π : Lw) = WithZero.exp (-1 : ℤ)) (x : Ow) (n : ℕ) :
    x ∈ IsLocalRing.maximalIdeal Ow ^ n ↔ Valued.v (x : Lw) ≤ Valued.v (π : Lw) ^ n := by
  rw [max_eq_span w hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have := (adicCompletionIntegers.integers L w).le_iff_dvd (x := x) (y := π ^ n)
  rw [map_pow, map_pow] at this
  exact this.symm

theorem isPrecomplete : IsPrecomplete (IsLocalRing.maximalIdeal Ow) Ow := by
  obtain ⟨π, hπ⟩ := exists_unif (L := L) w
  have hπ1 : Valued.v (π : Lw) < 1 := (lt_one_iff_le _).2 hπ.le
  have hπ0 : (π : Lw) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨fun f hf => ?_⟩
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, mem_max_pow_iff w hπ] at hf ⊢
  let g : ℕ → Lw := fun n => (f n : Lw)
  have hc : Cauchy (map g atTop) := by
    rw [Valued.cauchy_iff]
    refine ⟨map_neBot, fun γ => ?_⟩
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hπ1 (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := (.ofClass (Valued.v : Valuation Lw ℤᵐ⁰)))) γ)
    refine ⟨g '' Set.Ici n, image_mem_map (Ici_mem_atTop n), ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [Valuation.restrict_lt_iff_lt_embedding]
    refine lt_of_le_of_lt ?_ hn
    have h1 := hf (m := n) (n := a) ha
    have h2 := hf (m := n) (n := b) hb
    have e : g b - g a = ((f n - f a : Ow) : Lw) - ((f n - f b : Ow) : Lw) := by
      simp only [g]; push_cast; ring
    rw [e]
    exact Valuation.map_sub_le _ h1 h2
  obtain ⟨l, hl⟩ := CompleteSpace.complete hc
  have key : ∀ n, Valued.v (g n - l) ≤ Valued.v (π : Lw) ^ n := by
    intro n
    have hU : {y : Lw | (Valued.v : Valuation Lw ℤᵐ⁰).restrict (y - l) <
        (Valued.v : Valuation Lw ℤᵐ⁰).restrict ((π : Lw) ^ n)} ∈ 𝓝 l := by
      rw [Valued.mem_nhds]
      exact ⟨Units.mk0 ((Valued.v : Valuation Lw ℤᵐ⁰).restrict ((π : Lw) ^ n)) (by simp [hπ0]),
        subset_rfl⟩
    have hm := hl hU
    rw [mem_map, mem_atTop_sets] at hm
    obtain ⟨N, hN⟩ := hm
    have h1 : (Valued.v : Valuation Lw ℤᵐ⁰).restrict (g (max N n) - l) <
        (Valued.v : Valuation Lw ℤᵐ⁰).restrict ((π : Lw) ^ n) := hN (max N n) (le_max_left _ _)
    rw [Valuation.restrict_lt_iff, map_pow] at h1
    have h2 := hf (m := n) (n := max N n) (le_max_right N n)
    have e : g n - l = ((f n - f (max N n) : Ow) : Lw) + (g (max N n) - l) := by
      simp only [g]; push_cast; ring
    rw [e]
    exact Valuation.map_add_le _ h2 h1.le
  have hl1 : l ∈ Ow := by
    have e : l = g 0 - (g 0 - l) := by ring
    rw [e]
    exact sub_mem (f 0).2 ((mem_adicCompletionIntegers R L w).2 (by simpa using key 0))
  exact ⟨⟨l, hl1⟩, fun n => key n⟩

theorem isAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal Ow) Ow :=
  { toIsHausdorff := inferInstance, toIsPrecomplete := isPrecomplete w }

lemma finite_res [Finite (R ⧸ w.asIdeal)] : Finite (IsLocalRing.ResidueField Ow) := by
  let φ : R →+* IsLocalRing.ResidueField Ow := (IsLocalRing.residue Ow).comp (algebraMap R Ow)
  have h0 : ∀ a ∈ w.asIdeal, φ a = 0 := by
    intro a ha
    show IsLocalRing.residue Ow (algebraMap R Ow a) = 0
    rw [IsLocalRing.residue_eq_zero_iff, mem_max_iff, algebraMap_adicCompletionIntegers_apply,
      valuedAdicCompletion_eq_valuation', valuation_lt_one_iff_mem]
    exact ha
  refine Finite.of_surjective (Ideal.Quotient.lift w.asIdeal φ h0) ?_
  apply Ideal.Quotient.lift_surjective_of_surjective
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hU : {y : Lw | (Valued.v : Valuation Lw ℤᵐ⁰).restrict (y - (x : Lw)) < 1} ∈ 𝓝 (x : Lw) := by
    rw [Valued.mem_nhds]
    exact ⟨1, subset_rfl⟩
  obtain ⟨l, hl⟩ := (denseRange_algebraMap L w).mem_nhds hU
  have hl' : Valued.v (algebraMap L Lw l - (x : Lw)) < 1 := by
    have : (Valued.v : Valuation Lw ℤᵐ⁰).restrict (algebraMap L Lw l - (x : Lw)) < 1 := hl
    rwa [Valuation.restrict_lt_iff_lt_embedding, map_one] at this
  have hl1 : w.valuation L l ≤ 1 := by
    rw [← v_algebraMap]
    have e : algebraMap L Lw l = (algebraMap L Lw l - (x : Lw)) + (x : Lw) := by ring
    rw [e]
    exact Valuation.map_add_le _ hl'.le ((mem_adicCompletionIntegers R L w).1 x.2)
  obtain ⟨a, ha⟩ := w.exists_valuation_sub_lt_of_integer hl1 1
  refine ⟨a, ?_⟩
  show IsLocalRing.residue Ow (algebraMap R Ow a) = IsLocalRing.residue Ow x
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_max_iff]
  have e : ((algebraMap R Ow a - x : Ow) : Lw) =
      algebraMap L Lw (algebraMap R L a - l) + (algebraMap L Lw l - (x : Lw)) := by
    have h1 : ((algebraMap R Ow a : Ow) : Lw) = algebraMap L Lw (algebraMap R L a) := by
      rw [algebraMap_adicCompletionIntegers_apply]
      rfl
    rw [AddSubgroupClass.coe_sub, h1, map_sub]
    ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ hl'
  rw [v_algebraMap]
  simpa using ha

def kMap : L →+* FractionRing Ow :=
  ((FractionRing.algEquiv Ow Lw).symm : Lw →+* FractionRing Ow).comp (algebraMap L Lw)

lemma exists_e : ∃ e : ℕ, 0 < e ∧ ∀ x : L, valV Ow (kMap w x) = w.valuation L x ^ e := by
  let : Algebra L (FractionRing Ow) := (kMap w).toAlgebra
  have : IsScalarTower R L (FractionRing Ow) := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R Ow (FractionRing Ow)]
    show _ = (FractionRing.algEquiv Ow Lw).symm (algebraMap L Lw (algebraMap R L r))
    have : algebraMap L Lw (algebraMap R L r) = algebraMap Ow Lw (algebraMap R Ow r) := by
      show _ = ((algebraMap R Ow r : Ow) : Lw)
      rw [algebraMap_adicCompletionIntegers_apply]
      rfl
    rw [this, AlgEquiv.commutes]
  let m : HeightOneSpectrum Ow := IsDiscreteValuationRing.maximalIdeal Ow
  have : m.asIdeal.LiesOver w.asIdeal := ⟨by
    ext a
    rw [Ideal.mem_comap]
    show _ ↔ algebraMap R Ow a ∈ IsLocalRing.maximalIdeal Ow
    rw [mem_max_iff, algebraMap_adicCompletionIntegers_apply,
      valuedAdicCompletion_eq_valuation', valuation_lt_one_iff_mem]⟩
  exact ⟨w.asIdeal.ramificationIdx' m.asIdeal,
    Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver m.asIdeal w.ne_bot),
    fun x => (valuation_liesOver (FractionRing Ow) w m x).symm⟩

end Compl

end LocFldPf

open LocFldPf in

theorem locFld : LocFld := by
  intro K L _ _ _ _ j la
  let : Algebra K L := j.toAlgebra
  have := la.isMaximal
  obtain ⟨Q, hQ, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) la.asIdeal
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot la.ne_bot Q
  let w : HeightOneSpectrum (𝓞 L) := ⟨Q, hQ.isPrime, hQ0⟩
  have : w.asIdeal.LiesOver la.asIdeal := hQl
  have : Finite (𝓞 L ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  have : CharZero (adicCompletionIntegers L w) :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective (𝓞 L) (adicCompletionIntegers L w))
  obtain ⟨e1, he1, h1⟩ := exists_e (L := L) w
  let T : CDVR := { V := adicCompletionIntegers L w, cpl := isAdicComplete w }
  have he2 : la.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal la.ne_bot
  refine ⟨T, kMap w, la.asIdeal.ramificationIdx' w.asIdeal * e1,
    ⟨Nat.mul_pos (Nat.pos_of_ne_zero he2) he1, fun a => ?_⟩, finite_res w⟩
  show vV (adicCompletionIntegers L w) (kMap w (j a)) = _
  simp only [vV, vLa]
  rw [h1, show j a = algebraMap K L a from rfl, ← valuation_liesOver L la w a, ← pow_mul,
    WithZero.log_pow]
  push_cast
  simp

section Cor

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem algPtLa_of_numPt (hN : XoNumPt Xo c) : AlgPtLa Xo c := algPtLa_of hN locFld

theorem intFrNe_of_numPt (hN : XoNumPt Xo c) (hE : IntFrExt Xo c) : IntFrNe Xo c (algCls Xo c) :=
  intFrNe_of' hN locFld hE

end Cor

end Formalism.L2.Pj
