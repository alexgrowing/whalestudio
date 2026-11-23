import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TorsionIsotropicCommutatorPairing
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsAdaptedSimilitudeDataAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueChainRuleNormalizedPullbackStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SumHvPrimaryKernelStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CardPrimaryTorsionTuplesKilledByMatrixStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslateMulOfCoprimeOrdersStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueSymmetricTranslateOddLevel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueNormalisedPullbackRationalNorm
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslations
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MemRangeOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslatesMultiplicationPullbackDescrip
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsotropicGroupPrimaryDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.InZhIffKillsAdapted
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

set_option autoImplicit false

namespace GlobalTheory.ShortPrime

section Val
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

def Un (V : Type) {K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] (x : K) : Prop := valV V x = 1

theorem Un.mul {x y : K} (hx : Un V x) (hy : Un V y) : Un V (x * y) := by
  unfold Un at *; rw [map_mul, hx, hy, _root_.one_mul]

theorem Un.inv {x : K} (hx : Un V x) : Un V x⁻¹ := by
  unfold Un at *; rw [map_inv₀, hx, inv_one]

theorem Un.pow {x : K} (hx : Un V x) (n : ℕ) : Un V (x ^ n) := by
  unfold Un at *; rw [map_pow, hx, one_pow]

theorem Un.ne {x : K} (hx : Un V x) : x ≠ 0 := by
  rintro rfl; simp [Un] at hx

theorem Un.nval {x : K} (hx : Un V x) (e : ℕ) (z : K) : nval V e (x * z) = nval V e z :=
  nval_mul_unit e hx.ne (by unfold Un at hx; simp [vV, hx]) z

theorem un_of_vV {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (h : vV V x = vV V y) : Un V (x * y⁻¹) := by
  unfold Un
  have h1 : WithZero.log (valV V x) = WithZero.log (valV V y) := neg_injective h
  have h2 : valV V x = valV V y := by
    rw [← WithZero.exp_log (valV_ne_zero (V := V) hx), h1, WithZero.exp_log (valV_ne_zero (V := V) hy)]
  rw [map_mul, map_inv₀, h2, mul_inv_cancel₀ (valV_ne_zero hy)]

theorem isUnit_of_coprime {ℓ k : ℕ} (hl : ¬ IsUnit (ℓ : V)) (h : Nat.Coprime k ℓ) : IsUnit (k : V) := by
  obtain ⟨a, b, hab⟩ : IsCoprime (k : V) (ℓ : V) := h.cast
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h1 | h1
  · exact isUnit_of_mul_isUnit_right h1
  · exact absurd (isUnit_of_mul_isUnit_right h1) hl

theorem un_of_coprime {ℓ k : ℕ} (hl : ¬ IsUnit (ℓ : V)) (h : Nat.Coprime k ℓ) : Un V (k : K) := by
  unfold Un valV
  rw [← map_natCast (algebraMap V K), IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
  exact fun hm => (IsLocalRing.mem_maximalIdeal _).1 hm (isUnit_of_coprime hl h)

theorem un_ordProj [CharZero K] {ℓ m : ℕ} (hp : ℓ.Prime) (hl : ¬ IsUnit (ℓ : V)) (hm : m ≠ 0) :
    Un V (((ℓ ^ m.factorization ℓ : ℕ) : K) * (m : K)⁻¹) := by
  have h := (un_of_coprime (K := K) hl (Nat.coprime_ordCompl hp hm).symm).inv
  convert h using 1
  have h1 : (m : K) = ((ℓ ^ m.factorization ℓ : ℕ) : K) * ((m / ℓ ^ m.factorization ℓ : ℕ) : K) := by
    rw [← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  have h2 : ((ℓ ^ m.factorization ℓ : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne_zero)
  generalize ((m / ℓ ^ m.factorization ℓ : ℕ) : K) = t at *
  rw [h1, mul_inv, ← _root_.mul_assoc, mul_inv_cancel₀ h2, _root_.one_mul]

theorem le_nval_sum {J : Type} (s : Finset J) (e : ℕ) (r : EReal) (f : J → K) (h : ∀ i ∈ s, r ≤ nval V e (f i)) :
    r ≤ nval V e (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, nval_zero]; exact le_top
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (le_min (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).trans
      (nval_add e _ _)
end Val

theorem eq_one_of_coprime {G : Type} [Monoid G] {u : G} {k ℓ : ℕ} (h : Nat.Coprime k ℓ) (h1 : u ^ k = 1)
    (h2 : ∃ j : ℕ, u ^ (ℓ ^ j) = 1) : u = 1 := by
  obtain ⟨j, hj⟩ := h2
  rw [← orderOf_eq_one_iff]
  exact Nat.eq_one_of_dvd_coprimes (h.pow_right j) (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hj)

section Pts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l)

theorem comp_act_nat {T : Over Xo.X} (u : T ⟶ Xo.univ.t.G) (k : ℕ) : u ≫ Xo.univ.t.act.act (k : 𝓞 E) = u ^ k := by
  rw [ZhStable.act_natCast, MonObj.comp_pow, Category.comp_id]

theorem kills_pow {T : Over Xo.X} {n : ℕ} {mu : Matrix (Fin n) (Fin n) (𝓞 E)} {u : Fin n → (T ⟶ Xo.univ.t.G)}
    (h : Kills Xo mu u) (k : ℕ) : Kills Xo mu (fun b => u b ^ k) := by
  letI := ZPart.ptMod Xo T
  rw [ZPart.kills_iff] at h ⊢
  intro i
  simp only [ofMul_pow, smul_comm (mu i _) k]
  rw [← Finset.smul_sum, h i, smul_zero]

theorem kills_mul {T : Over Xo.X} {n : ℕ} {mu : Matrix (Fin n) (Fin n) (𝓞 E)} {u : Fin n → (T ⟶ Xo.univ.t.G)}
    (h : Kills Xo mu u) (nu : Matrix (Fin n) (Fin n) (𝓞 E)) : Kills Xo (nu * mu) u := by
  letI := ZPart.ptMod Xo T
  rw [ZPart.kills_iff] at h ⊢
  exact h.mul nu

theorem nat_mul_bar (k : ℕ) : (k : 𝓞 E) * H.bar (k : 𝓞 E) = ((k ^ 2 : ℕ) : 𝓞 E) := by
  rw [map_natCast]; push_cast; ring

variable {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}

theorem moves_comm {k : ℕ} (hk : Odd k) {u t : ptO Xo x ⟶ Xo.univ.t.G} {m ℓ : ℕ} (hu : u ^ k = 1) (ht : t ^ k = 1)
    (hc : Nat.Coprime m ℓ) (hul : ∃ j : ℕ, u ^ (ℓ ^ j) = 1) (htm : t ^ m = 1) {A A' B B' : SecN Xo x k}
    (h1 : Moves Xo u A A') (h2 : Moves Xo t A B) (h3 : Moves Xo t A' B') : Moves Xo u B B' := by
  obtain ⟨j, hj⟩ := hul
  have h4 := (GlobalTheory.T.symmetricTranslate_mul_of_coprime_orders E H Dw l Xo S x k hk t u m (ℓ ^ j) ht hu (hc.pow_right j) htm hj A A' B' h1).1 h3
  rw [_root_.mul_comm] at h4
  exact (GlobalTheory.T.symmetricTranslate_mul_of_coprime_orders E H Dw l Xo S x k hk u t (ℓ ^ j) m hu ht (hc.pow_right j).symm hj htm A B B' h2).2 h4
end Pts

section Base
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}

theorem exists_base {N ℓ m m' : ℕ} (hN : Odd N) (s : SecN Xo x 1) (a' t : ptO Xo x ⟶ Xo.univ.t.G)
    (ha' : a' ^ (N ^ 2) = 1) (ht : t ^ (N ^ 2) = 1) (hm : Nat.Coprime m ℓ) (hm' : Nat.Coprime m' ℓ)
    (ham : a' ^ m = 1) (htm : t ^ m' = 1) :
    ∃ F₀ : SecN Xo x (N ^ 2), Reach Xo s (N ^ 2) F₀ ∧
      (∀ u : ptO Xo x ⟶ Xo.univ.t.G, (∃ j : ℕ, u ^ (ℓ ^ j) = 1) → u ^ N = 1 → Moves Xo u F₀ F₀) ∧
      ∀ (a : ptO Xo x ⟶ Xo.univ.t.G) F, (∃ j : ℕ, a ^ (ℓ ^ j) = 1) → a ^ (N ^ 2) = 1 →
        IsUUOver Xo.univ.t.G Xo.univ.t.PP N s (a * a') t F → Moves Xo a F₀ (sqN Xo N F) := by
  have hN2 : Odd (N ^ 2) := hN.pow
  obtain ⟨G₀, hG₀, hG₀u⟩ := GlobalTheory.existsUnique_pulls E H Dw l Xo S x (N : 𝓞 E) (N ^ 2) 1 (N ^ 2) (nat_mul_bar N)
    (Nat.one_mul _).symm s
  obtain ⟨F₁, hF₁, -⟩ := (GlobalTheory.existsUnique_moves E H Dw l Xo S x (N ^ 2) hN2 a' ha' G₀).1
  obtain ⟨F₀, hF₀, -⟩ := (GlobalTheory.existsUnique_moves E H Dw l Xo S x (N ^ 2) hN2 t ht F₁).1
  refine ⟨F₀, ?_, fun u hu huN => ?_, fun a F ha haN hF => ?_⟩
  · exact .move _ _ _ _ (.move _ _ _ _ (.pull 1 (N ^ 2) (N ^ 2) (N : 𝓞 E) s G₀ .base (Or.inl rfl) hN2
      (nat_mul_bar N) (Nat.one_mul _).symm hG₀) hF₁) hF₀
  · have hu2 : u ^ (N ^ 2) = 1 := by rw [pow_two, pow_mul, huN, one_pow]
    have h0 : Moves Xo u G₀ G₀ := moves_of_pulls E H Dw l Xo S x (N : 𝓞 E) (N ^ 2) 1 (N ^ 2) (nat_mul_bar N)
      (Nat.one_mul _).symm hN2 1 u ((comp_act_nat Xo u N).trans huN) hu2 s s G₀ G₀
      (GlobalTheory.existsUnique_moves E H Dw l Xo S x 1 odd_one 1 (one_pow _) s).2 hG₀ hG₀
    exact moves_comm Xo hN2 hu2 ht hm' hu htm (moves_comm Xo hN2 hu2 ha' hm hu ham h0 hF₁ hF₁) hF₀ hF₀
  · obtain ⟨G, F₂, hG, h2, h3⟩ := ((uu_through_moves E H Dw l Xo S x N hN s).1 (a * a') t F
      (by rw [mul_pow, haN, ha', _root_.one_mul]) ht).1 hF
    obtain rfl := hG₀u G hG
    obtain ⟨j, hj⟩ := ha
    have h4 := (GlobalTheory.T.symmetricTranslate_mul_of_coprime_orders E H Dw l Xo S x _ hN2 a a' (ℓ ^ j) m haN ha' (hm.pow_right j).symm hj ham
      G F₁ F₂ hF₁).2 h2
    exact moves_comm Xo hN2 haN ht hm' ⟨j, hj⟩ htm h4 hF₀ h3

theorem exists_perm {T : Over Xo.X} {n k ℓ : ℕ} (hk : Nat.Coprime k ℓ) (mu : Matrix (Fin n) (Fin n) (𝓞 E))
    {J : Type} [Fintype J] (a : J → Fin n → (T ⟶ Xo.univ.t.G)) (hinj : Function.Injective a)
    (ha : ∀ u, (∃ i, a i = u) ↔ (Kills Xo mu u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1)) :
    ∃ π : J ≃ J, ∀ i b, a (π i) b = a i b ^ k := by
  have h1 : ∀ i, ∃ i', a i' = fun b => a i b ^ k := fun i => by
    obtain ⟨h1, h2⟩ := (ha _).1 ⟨i, rfl⟩
    exact (ha _).2 ⟨kills_pow Xo h1 k, fun b => (h2 b).imp fun j hj => by rw [pow_right_comm, hj, one_pow]⟩
  choose π hπ using h1
  have h2 : Function.Injective π := fun i i' h => hinj <| funext fun b => by
    have h3 : a i b ^ k = a i' b ^ k := by
      have := hπ i
      rw [h, hπ i'] at this
      exact (congrFun this b).symm
    obtain ⟨j, hj⟩ := ((ha _).1 ⟨i, rfl⟩).2 b
    obtain ⟨j', hj'⟩ := ((ha _).1 ⟨i', rfl⟩).2 b
    refine div_eq_one.1 (eq_one_of_coprime hk (by rw [div_pow, h3, div_self']) ⟨j + j', ?_⟩)
    rw [div_pow, pow_add, pow_mul, hj, one_pow, _root_.mul_comm, pow_mul, hj', one_pow, div_self']
  exact ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.1 h2), fun i b => congrFun (hπ i) b⟩

theorem card_kills {T : Over Xo.X} {n ℓ : ℕ} (p q : Matrix (Fin n) (Fin n) (𝓞 E))
    {J : Type} (a : J → Fin n → (T ⟶ Xo.univ.t.G)) (hinj : Function.Injective a)
    (ha : ∀ u, (∃ i, a i = u) ↔ (Kills Xo (p * q) u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1)) :
    Nat.card {i : J // Kills Xo q (a i)} =
      Nat.card {u : Fin n → (T ⟶ Xo.univ.t.G) // Kills Xo q u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1} := by
  refine Nat.card_eq_of_bijective (fun i => ⟨a i.1, i.2, ((ha _).1 ⟨i.1, rfl⟩).2⟩) ⟨fun i i' h => ?_, fun u => ?_⟩
  · exact Subtype.ext (hinj (congrArg Subtype.val h))
  · obtain ⟨i, hi⟩ := (ha u.1).2 ⟨kills_mul Xo u.2.1 p, u.2.2⟩
    exact ⟨⟨i, hi ▸ u.2.1⟩, Subtype.ext hi⟩
end Base

section Core
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem one_or_four_le {N : ℕ} (hN : Odd N) : N ^ 2 = 1 ∨ 4 ≤ N ^ 2 := by
  obtain ⟨r, rfl⟩ := hN
  rcases r with _ | r
  · exact Or.inl rfl
  · exact Or.inr (le_trans (by norm_num : 4 ≤ 3 ^ 2) (Nat.pow_le_pow_left (by omega) 2))

theorem un_nrm (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) {k ℓ : ℕ} (hl : ¬ IsUnit (ℓ : T.V)) (hk : Nat.Coprime k ℓ)
    (w : (E →+* ℂ) × ℕ → ℕ) : Un T.V (io (nrm Dw c w (k : 𝓞 E))) := by
  simp only [nrm, map_natCast, Finset.prod_pow_eq_pow_sum, map_pow]
  exact (un_of_coprime hl hk).pow _

theorem ell_part (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hst : ∀ a : 𝓞 E, star a = H.bar a) (T : CDVR)
    (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (hC : Good3 C) (nab : NabV Xo c)
    (hnab : IsNab Xo c nab) (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (he : 0 < e) (hB : ChBound C e ρ w n)
    (ℓ : ℕ) (hp : ℓ.Prime) (hl : ¬ IsUnit (ℓ : T.V)) (Λ : GenLat E n) (N M : ℕ) (hU : Λ.Unimod) (hL : Λ.LevOK N M)
    (β : c.F) (hβ0 : β ≠ 0) (hβ : BetaIs (Dw := Dw) c Λ β) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w)
    (hR : AllRat Xo (xOf y) (N ^ 2)) (J : Type) [Fintype J] (a : J → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (hinj : Function.Injective a) (ha : ∀ u, (∃ i, a i = u) ↔ (InZh Xo Λ N u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1))
    (F₀ : Fin n → SecN Xo (xOf y) (N ^ 2)) (F : J → Fin n → SecN Xo (xOf y) (N ^ 2))
    (hre : ∀ b, Reach Xo (sOf1 y) (N ^ 2) (F₀ b))
    (hfix : ∀ b (u : ptO Xo (xOf y) ⟶ Xo.univ.t.G), (∃ j : ℕ, u ^ (ℓ ^ j) = 1) → u ^ N = 1 → Moves Xo u (F₀ b) (F₀ b))
    (hF : ∀ i b, Moves Xo (a i b) (F₀ b) (F i b)) :
    letI := io.toAlgebra
    ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
      ∑ i, hv Xo c nab y.1 (N ^ 2) (F i) P) := by
  letI := io.toAlgebra
  obtain ⟨A, hsim⟩ := GlobalTheory.T.exists_adapted_similitude_data_at_prime E H n Λ N M ℓ hU hL hp
  have hN : Odd N := hL.1
  have hkN : Odd (A.k * N) := A.odd.mul hN
  have hlev : (A.k * N) ^ 2 = N ^ 2 * A.k ^ 2 := by ring
  have hz := fun u hu => GlobalTheory.inZh_iff_kills_adapted E H Dw l Xo n Λ N ℓ hp hN.pos A (ptO Xo (xOf y)) u hu
  have ha' : ∀ u, (∃ i, a i = u) ↔ (Kills Xo (A.p * A.q) u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1) := fun u =>
    (ha u).trans (and_congr_left fun hu => (hz u hu).1)
  have hZ : ∀ i, InZh Xo Λ (A.k * N) (a i) := fun i =>
    have h := (ha' _).1 ⟨i, rfl⟩
    (hz _ h.2).2.2 h.1
  obtain ⟨π, hπ⟩ := exists_perm Xo A.cop _ a hinj ha'
  have hpull := fun G => (GlobalTheory.existsUnique_pulls E H Dw l Xo _ (xOf y) (A.k : 𝓞 E) (A.k ^ 2) (N ^ 2) ((A.k * N) ^ 2)
    (nat_mul_bar A.k) hlev G).exists
  choose pl hpl using hpull
  have hmv : ∀ (u : ptO Xo (xOf y) ⟶ Xo.univ.t.G) G G', u ^ ((A.k * N) ^ 2) = 1 → Moves Xo (u ^ A.k) G G' →
      Moves Xo u (pl G) (pl G') := fun u G G' hu h =>
    moves_of_pulls E H Dw l Xo _ (xOf y) (A.k : 𝓞 E) (A.k ^ 2) (N ^ 2) ((A.k * N) ^ 2) (nat_mul_bar A.k) hlev
      hkN.pow _ u (comp_act_nat Xo u A.k) hu G G' _ _ h (hpl G) (hpl G')
  have hsub : Ideal.span {((A.k * N : ℕ) : 𝓞 E)} • stdLat E n ≤ Λ.La := by
    refine le_trans (Submodule.smul_mono_left ?_) (hL.2.2.trans inf_le_left)
    rw [Nat.cast_mul]
    exact Ideal.span_singleton_le_span_singleton.2 (dvd_mul_left _ _)
  have hiso := (GlobalTheory.zh_isotropic_and_half_isotropic GlobalTheory.firstFiveLaws.1 E H Dw l Xo _ (xOf y) n Λ (A.k * N) hU
    hkN.pos hsub).1
  obtain ⟨hff, -, hhom⟩ := GlobalTheory.PushIntegral.map_pushL_mem_FFV E H Dw l c n Λ w P hP T io A.k A.ga
    (isUnit_of_coprime hl A.cop) A.unitary A.into
  have hkN0 : ((A.k * N : ℕ) : c.F) ^ P.totalDegree ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hkN.pos.ne')
  obtain ⟨z, hz1, hz2⟩ := GlobalTheory.T.sum_hv_primary_kernel_alt E H Dw l Xo c hst T io y C hC nab hnab e ρ w n he hB ℓ hp hl (A.k * N)
    (A.k ^ 2) (N ^ 2) A.k₁ A.p A.q ((A.k : 𝓞 E) • A.g) hkN hsim (mul_pow _ _ _) (A.cop.pow_left 2) hR A.cop₁
    (by rw [Matrix.smul_mul, A.gq, smul_smul]; congr 1; push_cast; ring) J a hinj ha'
    (fun i i' ε hε => hiso (a i) (a i') ε (hZ i) (hZ i') fun b => by rw [← Nat.cast_pow]; exact hε b)
    (fun b => pl (F₀ b)) (fun i b => pl (F (π i) b))
    (fun b => .pull (N ^ 2) (A.k ^ 2) _ (A.k : 𝓞 E) (F₀ b) _ (hre b)
      (one_or_four_le hN)
      A.odd.pow (nat_mul_bar A.k) hlev (hpl _))
    (fun b u hu huN => hmv u _ _ (by rw [pow_two, pow_mul, huN, one_pow]) (hfix b _
      (hu.imp fun j hj => by rw [pow_right_comm, hj, one_pow]) (by rw [← pow_mul, huN])))
    (fun i b => hmv _ _ _ ((hZ i).1 b) (by rw [← hπ]; exact hF _ _))
    P (((A.k * N : ℕ) : c.F) ^ P.totalDegree)⁻¹ hP.1
    (by rw [A.prod, hhom, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ hkN0, map_one, _root_.one_mul]; exact hff)
  have hch : ∀ i, hv Xo c nab y.1 ((A.k * N) ^ 2) (fun b => pl (F (π i) b)) P =
      io (nrm Dw c w (A.k : 𝓞 E)) * hv Xo c nab y.1 (N ^ 2) (F (π i)) P := fun i =>
    GlobalTheory.T.harmonic_value_chain_rule_normalized_pullback E H Dw l Xo c hst nab hnab T.Fr y.1 (A.k : 𝓞 E) (A.k ^ 2) (N ^ 2) _ (nat_mul_bar A.k) hlev n
      (F (π i)) _ (fun b => hpl _) w P hP.1
  obtain ⟨hi1, hi2, hi3⟩ := GlobalTheory.LatticeIndex.latidx E H Dw l c n Λ N M ℓ hU hL hp A
  obtain ⟨hi4, hi5⟩ := hi3 β hβ0 hβ T io hl
  have hcnt := GlobalTheory.T.card_primaryTorsionTuples_killed_by_matrix E H Dw l Xo T.Fr (xOf y) ℓ hp n A.q ((N : 𝓞 E) • A.g) A.k₁ (N ^ 2) A.cop₁
    (pow_pos hN.pos 2) (by rw [Matrix.smul_mul, A.gq, smul_smul]; congr 1; push_cast; ring) hR
  rw [card_kills Xo A.p A.q a hinj ha', hcnt, hi1, Finset.sum_congr rfl fun i _ => hch i, ← Finset.mul_sum,
    Equiv.sum_comp π fun i => hv Xo c nab y.1 (N ^ 2) (F i) P] at hz2
  have hδ : io (∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ) ≠ 0 := by
    refine (map_ne_zero io).2 (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_)
    exact (map_ne_zero (embF c τ)).2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).2 hi5)
  have u1 := un_of_vV hδ ((map_ne_zero io).2 hβ0) hi4
  have u2 := un_ordProj (K := T.Fr) hp hl hi2
  have u3 := un_nrm (Dw := Dw) c T io hl A.cop w
  have u4 := (un_of_coprime (K := T.Fr) hl A.cop).pow P.totalDegree
  rw [← (((u1.mul u2).mul u3.inv).mul u4).nval e z] at hz1
  convert hz1 using 2
  have h3 := u3.ne
  have h4 := u4.ne
  have h5 : (N : T.Fr) ^ P.totalDegree ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hN.pos.ne')
  simp only [map_mul, map_inv₀, map_pow io, map_natCast, Nat.cast_mul, mul_pow] at hz2 ⊢
  generalize (∑ i, hv Xo c nab y.1 (N ^ 2) (F i) P) = Sm at *
  generalize io (nrm Dw c w (A.k : 𝓞 E)) = ν at *
  generalize (A.k : T.Fr) ^ P.totalDegree = κ at *
  generalize (N : T.Fr) ^ P.totalDegree = ξ at *
  have h6 : Sm = κ * ξ * ν⁻¹ * ((κ * ξ)⁻¹ * (ν * Sm)) := by field_simp
  rw [h6, hz2]
  field_simp
end Core

end GlobalTheory.ShortPrime

theorem GlobalTheory.short_value_bound_of_coprime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ChBound C e ρ w n → ∀ (ℓ : ℕ), ℓ.Prime → ¬ IsUnit (ℓ : T.V) → ∀ (Λ : GenLat E n) (N M : ℕ), Λ.Unimod → Λ.LevOK N M → ∀ (β : c.F), β ≠ 0 → BetaIs (Dw := Dw) c Λ β → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmL c Λ w → ∀ (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo (xOf y) z → (∀ b, tp b ^ (N ^ 2) = 1) → (∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b)) → AllRat Xo (xOf y) (N ^ 2) → (∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ b, tp b ^ m = 1) → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) * ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
  intro E _ _ _ H Dw l Xo c _ hst T io y C hC nab hnab e ρ w n he hB ℓ hp hl Λ N M hU hL β hβ0 hβ P hP z tp F hz hg
    htp hF hR ⟨m', hm', htm⟩
  letI := io.toAlgebra
  obtain ⟨J, J', _, _, a, a', σ, hinj, ha, ⟨m, hm, ham⟩, hσ, -⟩ :=
    GlobalTheory.T.isotropic_group_primary_decomposition E H Dw l Xo T.Fr (xOf y) n Λ N M ℓ hU hL hp z hz hg
  rw [← Equiv.sum_comp σ, Fintype.sum_prod_type_right, Finset.mul_sum]
  refine GlobalTheory.ShortPrime.le_nval_sum _ _ _ _ fun i' _ => ?_
  choose F₀ h1 h2 h3 using fun b => GlobalTheory.ShortPrime.exists_base Xo hL.1 (sOf1 y) (a' i' b) (tp b) (ham i' b).2 (htp b)
    hm hm' (ham i' b).1 (htm b)
  refine GlobalTheory.ShortPrime.ell_part Xo c hst T io y C hC nab hnab e ρ w n he hB ℓ hp hl Λ N M hU hL β hβ0 hβ P hP hR J a
    hinj ha F₀ (fun i b => sqN Xo N (F (σ (i, i')) b)) h1 h2 fun i b => ?_
  obtain ⟨h4, h5⟩ := (ha _).1 ⟨i, rfl⟩
  exact h3 b _ _ (h5 b) (h4.1 b) (hσ i i' b ▸ hF _ b)
