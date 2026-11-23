import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveTuplesWithGramMatrixHenselCountStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimitiveTuplesGramModNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianMatricesDvdSqStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimitiveTuplesWithGramMatrixResidueRingStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.GramCount

section Abstract

variable {O : Type} [CommRing O]

def quotInv (c : O →+* O) (p : O) (hp : c p = p) :
    O ⧸ Ideal.span {p} →+* O ⧸ Ideal.span {p} :=
  Ideal.quotientMap _ c (by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, hp]
    exact Ideal.mem_span_singleton_self p)

theorem quotInv_mk (c : O →+* O) (p : O) (hp : c p = p) (u : O) :
    quotInv c p hp (Ideal.Quotient.mk _ u) = Ideal.Quotient.mk _ (c u) := rfl

theorem quotInv_quotInv (c : O →+* O) (hc : ∀ u, c (c u) = u) (p : O) (hp : c p = p) (u) :
    quotInv c p hp (quotInv c p hp u) = u := by
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [quotInv_mk, quotInv_mk, hc]

private lemma quotient_mk_dvd_mk_iff_dvd (p : O) (j : ℕ) (hj : 1 ≤ j) (u : O) :
    Ideal.Quotient.mk (Ideal.span {p ^ j}) p ∣ Ideal.Quotient.mk (Ideal.span {p ^ j}) u ↔
      p ∣ u := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hv
    obtain ⟨k, hk⟩ := hv
    have hpj : p ^ j = p * p ^ (j - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    exact ⟨w + p ^ (j - 1) * k, by linear_combination hk + k * hpj⟩
  · rintro ⟨w, rfl⟩
    exact ⟨Ideal.Quotient.mk _ w, map_mul _ _ _⟩

theorem count_quot (c : O →+* O) (hc : ∀ u, c (c u) = u) (ω : O) (hω : IsUnit (ω - c ω))
    (p : O) (hp : c p = p) (hK : ∀ t, c t = t → ¬ p ∣ t → IsUnit t) (q : ℕ) (hq : 2 ≤ q)
    (j : ℕ) (hj : 1 ≤ j) (h1 : Nat.card (O ⧸ Ideal.span {p}) = q ^ 2)
    (h2 : Nat.card (O ⧸ Ideal.span {p ^ j}) = q ^ (2 * j)) (hpj : c (p ^ j) = p ^ j)
    (m n : ℕ) (hmn : 2 * m + 3 ≤ n) (G : Matrix (Fin m) (Fin m) O)
    (hG : ∀ a b, c (G b a) = G a b) (N : ℕ)
    (hN : N = Set.ncard (sols (quotInv c (p ^ j) hpj) n (G.map (Ideal.Quotient.mk _)))) :
    (q : ℝ) ^ (j * (2 * n * m - m ^ 2)) ≤ 2 * N ∧
      (N : ℝ) ≤ 2 * (q : ℝ) ^ (j * (2 * n * m - m ^ 2)) := by
  classical
  have hq0 : 0 < q := by omega

  have hfinA : Finite (O ⧸ Ideal.span {p ^ j}) :=
    Nat.finite_of_card_ne_zero (by rw [h2]; exact pow_ne_zero _ hq0.ne')
  have hfinB : Finite (O ⧸ Ideal.span {p}) :=
    Nat.finite_of_card_ne_zero (by rw [h1]; exact pow_ne_zero _ hq0.ne')
  let _ : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _

  have hle : Ideal.span {p ^ j} ≤ (Ideal.span {p}).comap (RingHom.id O) := by
    rw [Ideal.comap_id, Ideal.span_singleton_le_span_singleton]
    exact dvd_pow_self p (by omega)
  set φ := Ideal.quotientMap (Ideal.span {p}) (RingHom.id O) hle with hφdef
  have hφmk : ∀ u, φ (Ideal.Quotient.mk _ u) = Ideal.Quotient.mk _ u := fun u =>
    Ideal.quotientMap_mk
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨_, hφmk u⟩
  set cA := quotInv c (p ^ j) hpj with hcAdef
  set cB := quotInv c p hp with hcBdef
  have hφc : ∀ u, φ (cA u) = cB (φ u) := by
    intro u
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective u
    rw [hcAdef, hcBdef, quotInv_mk, hφmk, hφmk, quotInv_mk]
  set pA : O ⧸ Ideal.span {p ^ j} := Ideal.Quotient.mk _ p with hpAdef
  have hker : ∀ u, φ u = 0 ↔ pA ∣ u := by
    intro u
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective u
    rw [hφmk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hpAdef,
      quotient_mk_dvd_mk_iff_dvd p j hj v]
  have hnil : IsNilpotent pA :=
    ⟨j, by rw [hpAdef, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
           exact Ideal.mem_span_singleton_self _⟩
  have hcA : ∀ u, cA (cA u) = u := quotInv_quotInv c hc _ hpj
  have hcB : ∀ u, cB (cB u) = u := quotInv_quotInv c hc _ hp
  have hωA : IsUnit (Ideal.Quotient.mk (Ideal.span {p ^ j}) ω - cA (Ideal.Quotient.mk _ ω)) := by
    rw [hcAdef, quotInv_mk, ← map_sub]
    exact hω.map _
  have hωB : IsUnit (Ideal.Quotient.mk (Ideal.span {p}) ω - cB (Ideal.Quotient.mk _ ω)) := by
    rw [hcBdef, quotInv_mk, ← map_sub]
    exact hω.map _
  have hpA : cA pA = pA := by rw [hcAdef, hpAdef, quotInv_mk, hp]
  set GA := G.map (Ideal.Quotient.mk (Ideal.span {p ^ j})) with hGAdef
  have hGA : ∀ a b, cA (GA b a) = GA a b := by
    intro a b
    simp only [hGAdef, Matrix.map_apply]
    rw [hcAdef, quotInv_mk, hG]
  have hGB : ∀ a b, cB ((GA.map φ) b a) = (GA.map φ) a b := by
    intro a b
    simp only [Matrix.map_apply]
    rw [← hφc, hGA]

  have hKB : ∀ t, cB t = t → t ≠ 0 → IsUnit t := by
    intro t ht ht0
    obtain ⟨θ, -, hθ, -, -⟩ := exists_trace_one c hc hω
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective t
    have h' : Ideal.Quotient.mk (Ideal.span {p}) (c u) = Ideal.Quotient.mk _ u := by
      rw [hcBdef, quotInv_mk] at ht
      exact ht
    have hv : c (θ * u + c (θ * u)) = θ * u + c (θ * u) := by
      rw [map_add, hc, add_comm]
    have hmk : Ideal.Quotient.mk (Ideal.span {p}) (θ * u + c (θ * u)) =
        Ideal.Quotient.mk _ u := by
      rw [map_mul c, map_add, map_mul, map_mul, h', ← add_mul, ← map_add, hθ, map_one, one_mul]
    have hnd : ¬ p ∣ θ * u + c (θ * u) := by
      intro hd
      apply ht0
      rw [← hmk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact hd
    rw [← hmk]
    exact (hK _ hv hnd).map _
  have hcardB : Fintype.card (O ⧸ Ideal.span {p}) = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact h1

  have h29 := GlobalTheory.T.primitiveTuplesWithGramMatrix_hensel_count cA hcA _ hωA pA hpA hnil m n GA hGA
  have h31 := GlobalTheory.T.ncard_primitive_tuples_gram_mod_nilpotent cA cB hcA pA hnil φ hsurj hφc hker m n GA
  have h33 := GlobalTheory.T.card_hermitian_matrices_dvd_sq cA hcA _ hωA pA hpA m
  have h62 := GlobalTheory.T.ncard_primitiveTuplesWithGramMatrix_residueRing cB hcB _ hωB hKB q hq hcardB m n hmn (GA.map φ) hGB

  have hD : Nat.card {u : O ⧸ Ideal.span {p ^ j} // pA ∣ u} = q ^ (2 * (j - 1)) := by
    have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      (φ : (O ⧸ Ideal.span {p ^ j}) →+ (O ⧸ Ideal.span {p})).ker
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective
      (φ : (O ⧸ Ideal.span {p ^ j}) →+ (O ⧸ Ideal.span {p})) hsurj).toEquiv, h1, h2] at hcard
    have hsub : Nat.card ((φ : (O ⧸ Ideal.span {p ^ j}) →+ (O ⧸ Ideal.span {p})).ker) =
        Nat.card {u : O ⧸ Ideal.span {p ^ j} // pA ∣ u} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun u => by
        rw [AddMonoidHom.mem_ker]
        exact hker u)
    rw [hsub] at hcard
    have h2j : q ^ (2 * j) = q ^ 2 * q ^ (2 * (j - 1)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h2j] at hcard
    exact (Nat.eq_of_mul_eq_mul_left (pow_pos hq0 2) hcard).symm
  rw [hD] at h31 h33

  have hH : Nat.card {H : Matrix (Fin m) (Fin m) (O ⧸ Ideal.span {p ^ j}) //
      (∀ a b, cA (H b a) = H a b) ∧ ∀ a b, pA ∣ H a b} = q ^ ((j - 1) * (m * m)) := by
    apply Nat.pow_left_injective (n := 2) (by norm_num)
    simp only
    rw [h33, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hH, h31] at h29
  have hle2 : m * m ≤ 2 * n * m := by nlinarith
  have hK2 : 2 * n * m - m ^ 2 + m * m = 2 * n * m := by
    rw [sq]
    exact Nat.sub_add_cancel hle2
  have hexp : 2 * (j - 1) * (n * m) =
      (j - 1) * (2 * n * m - m ^ 2) + (j - 1) * (m * m) := by
    rw [← Nat.mul_add, hK2]
    ring
  rw [← pow_mul, hexp, pow_add] at h29
  have hS : Set.ncard (sols cA n GA) =
      q ^ ((j - 1) * (2 * n * m - m ^ 2)) * Set.ncard (sols cB n (GA.map φ)) := by
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hq0 ((j - 1) * (m * m)))
    rw [h29]
    ring
  have hjK : j * (2 * n * m - m ^ 2) = (j - 1) * (2 * n * m - m ^ 2) + (2 * n * m - m ^ 2) := by
    conv_lhs => rw [← Nat.sub_add_cancel hj]
    ring
  rw [hN, hS, hjK]
  push_cast
  rw [pow_add]
  have hX : (0 : ℝ) ≤ (q : ℝ) ^ ((j - 1) * (2 * n * m - m ^ 2)) := by positivity
  obtain ⟨hlo, hhi⟩ := h62
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo hX]
  · nlinarith [mul_le_mul_of_nonneg_left hhi hX]

end Abstract

theorem primitive_gram_count : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (n m j : ℕ), 2 * m + 3 ≤ n → 1 ≤ j → ∀ (Gm : Matrix (Fin m) (Fin m) E), IsHerm L Gm → IsIntM L Gm → ∀ (R : Finset E), (∀ u ∈ R, u ∈ L.O) → (∀ u ∈ L.O, ∃! w, w ∈ R ∧ ∃ c ∈ L.O, u - w = algebraMap F E ((ϖ : F) ^ j) * c) → ∀ N : ℕ, N = Set.ncard {x : Fin m → Fin n → E | (∀ a i, x a i ∈ R) ∧ (∃ y : Fin m → Fin n → E, (∀ a i, y a i ∈ L.O) ∧ ∀ a b, hf L 1 (x a) (y b) = if a = b then 1 else 0) ∧ ∀ a b, ∃ c ∈ L.O, hf L 1 (x b) (x a) - Gm a b = algebraMap F E ((ϖ : F) ^ j) * c} → (resQ ϖ : ℝ) ^ (j * (2 * n * m - m ^ 2)) ≤ 2 * N ∧ (N : ℝ) ≤ 2 * (resQ ϖ : ℝ) ^ (j * (2 * n * m - m ^ 2)) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n m j hmn hj Gm hHm hIm R hR hrep N hN
  classical
  obtain ⟨-, -, -, -, hmemF, hcardj, hq2, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ

  let c : L.O →+* L.O :=
    (L.cj : E →+* E).restrict L.O L.O (fun x hx => GlobalTheory.UnramOrder.cj_mem L hx)
  have hcv : ∀ u : L.O, (c u : E) = L.cj u := fun u => rfl
  have hc : ∀ u, c (c u) = u := fun u => Subtype.ext (L.cj_cj u)
  obtain ⟨ω0, hω0, e0, he0, hωe⟩ := GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  have hω : IsUnit ((⟨ω0, hω0⟩ : L.O) - c ⟨ω0, hω0⟩) :=
    IsUnit.of_mul_eq_one (⟨e0, he0⟩ : L.O) (Subtype.ext hωe)

  let p : L.O := ⟨algebraMap F E (ϖ : F), (hmemF _).2 ϖ.2⟩
  have hpv : ∀ k : ℕ, ((p ^ k : L.O) : E) = algebraMap F E ((ϖ : F) ^ k) := by
    intro k
    rw [SubmonoidClass.coe_pow, map_pow]
  have hp : c p = p := Subtype.ext (L.cj.commutes _)
  have hpj : c (p ^ j) = p ^ j := by rw [map_pow, hp]
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hpnu : ¬ IsUnit p := by
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hv1 : algebraMap F E (ϖ : F) * v = 1 := congrArg Subtype.val hv
    have hv2 : algebraMap F E (ϖ : F)⁻¹ * algebraMap F E (ϖ : F) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hϖ0, map_one]
    have hvE : (v : E) = algebraMap F E (ϖ : F)⁻¹ := by
      calc (v : E) = algebraMap F E (ϖ : F)⁻¹ * (algebraMap F E (ϖ : F) * v) := by
            rw [← mul_assoc, hv2, one_mul]
        _ = algebraMap F E (ϖ : F)⁻¹ := by rw [hv1, mul_one]
    have hmem : (ϖ : F)⁻¹ ∈ 𝒪[F] := by
      rw [← hmemF, ← hvE]
      exact v.2
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one (a := ϖ) (⟨_, hmem⟩ : 𝒪[F]) (Subtype.ext (mul_inv_cancel₀ hϖ0)))

  have hK : ∀ t : L.O, c t = t → ¬ p ∣ t → IsUnit t := by
    intro t ht hnd
    obtain ⟨a, ha⟩ := GlobalTheory.UnramOrder.exists_int_of_fixed L t.2 (congrArg Subtype.val ht)
    have hau : IsUnit a := by
      by_contra hna
      have hmax : a ∈ IsLocalRing.maximalIdeal 𝒪[F] :=
        (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hna)
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
        Ideal.mem_span_singleton] at hmax
      obtain ⟨b, rfl⟩ := hmax
      exact hnd ⟨⟨algebraMap F E (b : F), (hmemF _).2 b.2⟩,
        Subtype.ext (ha.trans (map_mul (algebraMap F E) (ϖ : F) (b : F)))⟩
    obtain ⟨u, rfl⟩ := hau
    have huw : ((u : 𝒪[F]) : F) * (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) = 1 :=
      congrArg Subtype.val u.mul_inv
    refine IsUnit.of_mul_eq_one (a := t) (M := L.O) ⟨algebraMap F E (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F),
      (hmemF _).2 ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]).2⟩ (Subtype.ext ?_)
    show (t : E) * algebraMap F E (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) = 1
    rw [ha, ← map_mul, huw, map_one]

  have hjac : ∀ u : L.O, u ∈ Ideal.span {p ^ j} → IsUnit (1 + u) := by
    intro u hu
    rw [Ideal.mem_span_singleton] at hu
    obtain ⟨v, rfl⟩ := hu
    have hfix : c ((1 + p ^ j * v) * c (1 + p ^ j * v)) = (1 + p ^ j * v) * c (1 + p ^ j * v) := by
      rw [map_mul, hc, mul_comm]
    have hcv' : c (1 + p ^ j * v) = 1 + p ^ j * c v := by
      rw [map_add, map_one, map_mul, map_pow, hp]
    have hnd : ¬ p ∣ (1 + p ^ j * v) * c (1 + p ^ j * v) := by
      rintro ⟨s, hs⟩
      rw [hcv'] at hs
      have hpj' : p ^ j = p * p ^ (j - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      apply hpnu
      refine IsUnit.of_mul_eq_one (a := p) (s - p ^ (j - 1) * (v + c v + p ^ j * v * c v)) ?_
      linear_combination (-1 : L.O) * hs + (v + c v + p ^ j * v * c v) * hpj'
    exact isUnit_of_mul_isUnit_left (hK _ hfix hnd)

  have hsetj : ∀ k : ℕ, {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ k)} = {p ^ k} := by
    intro k
    ext y
    rw [Set.mem_ofPred_eq, Set.mem_singleton_iff, ← hpv k]
    exact ⟨fun h => Subtype.ext h, fun h => h ▸ rfl⟩
  have h2 : Nat.card (L.O ⧸ Ideal.span {p ^ j}) = resQ ϖ ^ (2 * j) := by
    have := hcardj j
    rwa [hsetj j] at this
  have h1 : Nat.card (L.O ⧸ Ideal.span {p}) = resQ ϖ ^ 2 := by
    have := hcardj 1
    rwa [hsetj 1, pow_one, mul_one] at this
  have hmkeq : ∀ u v : L.O, Ideal.Quotient.mk (Ideal.span {p ^ j}) u = Ideal.Quotient.mk _ v ↔
      ∃ c0 ∈ L.O, (u : E) - v = algebraMap F E ((ϖ : F) ^ j) * c0 := by
    intro u v
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, k.2, ?_⟩
      rw [← hpv j]
      exact congrArg Subtype.val hk
    · rintro ⟨c0, hc0, h⟩
      refine ⟨⟨c0, hc0⟩, Subtype.ext ?_⟩
      rw [← hpv j] at h
      exact h

  have hrepQ : ∀ z : L.O ⧸ Ideal.span {p ^ j}, ∃ w : E, ∃ hw : w ∈ L.O,
      w ∈ R ∧ Ideal.Quotient.mk _ (⟨w, hw⟩ : L.O) = z := by
    intro z
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨w, ⟨hwR, c0, hc0, hw⟩, -⟩ := hrep u u.2
    refine ⟨w, hR w hwR, hwR, (hmkeq _ _).2 ⟨-c0, neg_mem hc0, ?_⟩⟩
    show w - (u : E) = _
    rw [mul_neg, ← hw]
    ring
  choose rp hrpO hrpR hrpmk using hrepQ
  have hrp_eq : ∀ w (hw : w ∈ R),
      rp (Ideal.Quotient.mk (Ideal.span {p ^ j}) (⟨w, hR w hw⟩ : L.O)) = w := by
    intro w hw
    obtain ⟨c0, hc0, hc⟩ := (hmkeq _ _).1 (hrpmk (Ideal.Quotient.mk (Ideal.span {p ^ j})
      (⟨w, hR w hw⟩ : L.O)))
    have hc' : rp (Ideal.Quotient.mk (Ideal.span {p ^ j}) (⟨w, hR w hw⟩ : L.O)) - w =
        algebraMap F E ((ϖ : F) ^ j) * c0 := hc
    obtain ⟨w', -, huniq⟩ := hrep w (hR w hw)
    have ea := huniq _ ⟨hrpR _, -c0, neg_mem hc0, by rw [mul_neg, ← hc']; ring⟩
    have eb := huniq w ⟨hw, 0, zero_mem _, by rw [sub_self, mul_zero]⟩
    exact ea.trans eb.symm

  have hfv : ∀ u v : Fin n → L.O,
      hf L 1 (fun i => (u i : E)) (fun i => (v i : E)) = ((ip c u v : L.O) : E) := by
    intro u v
    simp [hf, ip, Matrix.one_apply, hcv]
  let cA := quotInv c (p ^ j) hpj
  have hφc' : ∀ u, Ideal.Quotient.mk (Ideal.span {p ^ j}) (c u) = cA (Ideal.Quotient.mk _ u) :=
    fun u => (quotInv_mk c (p ^ j) hpj u).symm
  have hk : ∀ u, Ideal.Quotient.mk (Ideal.span {p ^ j}) u = 0 → IsUnit (1 + u) :=
    fun u hu => hjac u (Ideal.Quotient.eq_zero_iff_mem.1 hu)
  have hEprim : ∀ u : Fin m → Fin n → L.O,
      (∃ y : Fin m → Fin n → E, (∀ a i, y a i ∈ L.O) ∧
        ∀ a b, hf L 1 (fun i => (u a i : E)) (y b) = if a = b then 1 else 0) ↔ Prim c u := by
    intro u
    constructor
    · rintro ⟨y, hyO, hy⟩
      refine ⟨fun b i => ⟨y b i, hyO b i⟩, fun a b => Subtype.ext ?_⟩
      have e : hf L 1 (fun i => (u a i : E)) (fun i => ((⟨y b i, hyO b i⟩ : L.O) : E)) =
          if a = b then 1 else 0 := hy a b
      rw [hfv] at e
      exact e.trans (by split_ifs <;> rfl)
    · rintro ⟨y, hy⟩
      refine ⟨fun b i => (y b i : E), fun b i => (y b i).2, fun a b => ?_⟩
      have e := congrArg Subtype.val (hy a b)
      rw [← hfv] at e
      exact e.trans (by split_ifs <;> rfl)
  let GO : Matrix (Fin m) (Fin m) L.O := fun a b => ⟨Gm a b, hIm a b⟩
  have hGO : ∀ a b, c (GO b a) = GO a b := fun a b => Subtype.ext (congrFun (congrFun hHm a) b)
  have hgram : ∀ u : Fin m → Fin n → L.O,
      (∀ a b, ∃ c0 ∈ L.O, hf L 1 (fun i => (u b i : E)) (fun i => (u a i : E)) - Gm a b =
        algebraMap F E ((ϖ : F) ^ j) * c0) ↔
      ∀ a b, ip cA (fun i => Ideal.Quotient.mk (Ideal.span {p ^ j}) (u b i))
        (fun i => Ideal.Quotient.mk (Ideal.span {p ^ j}) (u a i)) =
          Ideal.Quotient.mk (Ideal.span {p ^ j}) (GO a b) := by
    intro u
    refine forall_congr' fun a => forall_congr' fun b => ?_
    rw [← map_ip c cA _ hφc', hmkeq, hfv]

  have hset : {x : Fin m → Fin n → E | (∀ a i, x a i ∈ R) ∧ (∃ y : Fin m → Fin n → E,
      (∀ a i, y a i ∈ L.O) ∧ ∀ a b, hf L 1 (x a) (y b) = if a = b then 1 else 0) ∧
      ∀ a b, ∃ c ∈ L.O, hf L 1 (x b) (x a) - Gm a b = algebraMap F E ((ϖ : F) ^ j) * c} =
      (fun z a i => rp (z a i)) '' sols cA n (GO.map (Ideal.Quotient.mk _)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hx, hprim, hgr⟩
      let u : Fin m → Fin n → L.O := fun a i => ⟨x a i, hR _ (hx a i)⟩
      refine ⟨fun a i => Ideal.Quotient.mk _ (u a i), And.intro ?_ ?_, ?_⟩
      · exact Prim.map c cA _ hφc' ((hEprim u).1 hprim)
      · exact (hgram u).1 hgr
      · funext a i
        exact hrp_eq (x a i) (hx a i)
    · rintro ⟨z, ⟨hzp, hzg⟩, rfl⟩
      let u : Fin m → Fin n → L.O := fun a i => ⟨rp (z a i), hrpO (z a i)⟩
      have hu : (fun a i => Ideal.Quotient.mk (Ideal.span {p ^ j}) (u a i)) = z :=
        funext fun a => funext fun i => hrpmk (z a i)
      refine ⟨fun a i => hrpR (z a i), (hEprim u).2 ?_, (hgram u).2 ?_⟩
      · apply prim_of_map c hc cA _ hφc' Ideal.Quotient.mk_surjective hk
        rw [hu]
        exact hzp
      · intro a b
        have e := hzg a b
        rw [← hu] at e
        exact e
  have hinj : Function.Injective
      (fun (z : Fin m → Fin n → L.O ⧸ Ideal.span {p ^ j}) (a : Fin m) (i : Fin n) => rp (z a i)) := by
    intro z z' h
    funext a i
    have e : rp (z a i) = rp (z' a i) := congrFun (congrFun h a) i
    calc z a i = Ideal.Quotient.mk _ ⟨rp (z a i), hrpO _⟩ := (hrpmk _).symm
      _ = Ideal.Quotient.mk _ ⟨rp (z' a i), hrpO _⟩ := congrArg _ (Subtype.ext e)
      _ = z' a i := hrpmk _
  have hN' : N = Set.ncard (sols cA n (GO.map (Ideal.Quotient.mk _))) :=
    hN.trans ((congrArg Set.ncard hset).trans (Set.ncard_image_of_injective _ hinj))
  exact count_quot c hc _ hω p hp hK (resQ ϖ) hq2 j hj h1 h2 hpj m n hmn GO hGO N hN'

end GlobalTheory.GramCount
