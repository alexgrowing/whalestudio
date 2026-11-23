import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InZhGeoInjStable
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueNormalisedPullbackRationalNorm
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueSymmetricTranslateOddLevel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslateMulOfCoprimeOrders
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslations
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslatesMultiplicationPullbackDescrip
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueTranslatedProductValuationBoundStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsotropicGroupPrimaryDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LatticeTrivialAtPrimeIndicesAndUnitsStatement

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.ShortTriv

section Pts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l)

theorem comp_act_natCast {T : Over Xo.X} (a : T ⟶ Xo.univ.t.G) (m : ℕ) :
    a ≫ Xo.univ.t.act.act (m : 𝓞 E) = a ^ m := by
  rw [GlobalTheory.ZhStable.act_natCast, MonObj.comp_pow, Category.comp_id]

theorem pow_eq_one_of_trivAt {n : ℕ} {Λ : GenLat E n} {N ℓ : ℕ} (hΛ : Λ.TrivAt ℓ) {T : Over Xo.X}
    {a : Fin n → (T ⟶ Xo.univ.t.G)} (ha : InZh Xo Λ N a) (b : Fin n) {j : ℕ} (hj : a b ^ (ℓ ^ j) = 1) :
    a b ^ N = 1 := by
  unfold InZh GenLat.TrivAt at *
  obtain ⟨k, hk, h1, -⟩ := hΛ
  have hrow := ha.2 ((k : E) • (1 : Matrix (Fin n) (Fin n) E)) ?_
    (fun i j => if i = j then ((N * k : ℕ) : 𝓞 E) else 0) ?_ b
  · beta_reduce at hrow
    have hf : (fun j => a j ≫ Xo.univ.t.act.act (if b = j then ((N * k : ℕ) : 𝓞 E) else 0)) =
        fun j => if b = j then a b ^ (N * k) else 1 := by
      funext j
      split_ifs with hj
      · subst hj; exact comp_act_natCast Xo (a b) (N * k)
      · simpa using comp_act_natCast Xo (a j) 0
    rw [hf, List.prod_ofFn, Fintype.prod_ite_eq] at hrow
    have hg := pow_gcd_eq_one.2 ⟨hrow, hj⟩
    rw [Nat.Coprime.gcd_mul_right_cancel N (Nat.Coprime.pow_right j hk)] at hg
    obtain ⟨c, hc⟩ := Nat.gcd_dvd_left N (ℓ ^ j)
    rw [hc, pow_mul, hg, one_pow]
  · intro v hv
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact h1 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hv)
  · intro i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]

variable {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}

theorem moves_self {N : ℕ} (hN : Odd N) (s : SecN Xo x 1) (F₀ : SecN Xo x (N ^ 2)) (hF : Pulls Xo (N : 𝓞 E) s F₀)
    (a : ptO Xo x ⟶ Xo.univ.t.G) (ha : a ^ N = 1) : Moves Xo a F₀ F₀ := by
  have hN2 : Odd (N ^ 2) := hN.pow
  have h1 := (GlobalTheory.existsUnique_moves E H Dw l Xo S x 1 odd_one 1 (_root_.one_pow 1) s).2
  have hb : a ≫ Xo.univ.t.act.act (N : 𝓞 E) = 1 := by rw [comp_act_natCast Xo a N, ha]
  have hbar : (N : 𝓞 E) * H.bar (N : 𝓞 E) = ((N ^ 2 : ℕ) : 𝓞 E) := by
    rw [map_natCast, Nat.cast_pow, sq]
  exact GlobalTheory.PlaceInt.moves_of_pulls E H Dw l Xo S x (N : 𝓞 E) (N ^ 2) 1 (N ^ 2) hbar (by ring) hN2 1 a hb
    (by rw [_root_.pow_two, _root_.pow_mul, ha, _root_.one_pow]) s s F₀ F₀ h1 hF hF

theorem isUUOver_of_mul {N : ℕ} (hN : Odd N) (s : SecN Xo x 1) (a a' t : ptO Xo x ⟶ Xo.univ.t.G) (ha : a ^ N = 1)
    (ha' : a' ^ (N ^ 2) = 1) (ht : t ^ (N ^ 2) = 1) {m m' : ℕ} (hc : Nat.Coprime m' m) (ham : a ^ m = 1)
    (ham' : a' ^ m' = 1) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo x)))
    (hF : IsUUOver Xo.univ.t.G Xo.univ.t.PP N s (a * a') t F) : IsUUOver Xo.univ.t.G Xo.univ.t.PP N s a' t F := by
  have hN2 : Odd (N ^ 2) := hN.pow
  have haN2 : a ^ (N ^ 2) = 1 := by rw [_root_.pow_two, _root_.pow_mul, ha, _root_.one_pow]
  have hprod : (a * a') ^ (N ^ 2) = 1 := by rw [_root_.mul_pow, haN2, ha', _root_.one_mul]
  have huu := (GlobalTheory.PlaceInt.uu_through_moves E H Dw l Xo S x N hN s).1
  obtain ⟨F₀, F₁, hP, hM, hT⟩ := (huu (a * a') t F hprod ht).1 hF
  obtain ⟨⟨G₁, hG₁, -⟩, -⟩ := GlobalTheory.existsUnique_moves E H Dw l Xo S x (N ^ 2) hN2 a' ha' F₀
  have hfix : Moves Xo a F₀ F₀ := moves_self Xo hN s F₀ hP a ha
  have hG : Moves Xo (a' * a) F₀ G₁ :=
    (GlobalTheory.PlaceInt.moves_mul_of_coprime E H Dw l Xo S x (N ^ 2) hN2 a' a m' m ha' haN2 hc ham' ham F₀ F₀ G₁ hfix).1 hG₁
  rw [_root_.mul_comm a' a] at hG
  have hEq : G₁ = F₁ :=
    (GlobalTheory.existsUnique_moves E H Dw l Xo S x (N ^ 2) hN2 (a * a') hprod F₀).1.unique hG hM
  subst hEq
  exact (huu a' t F ha' ht).2 ⟨F₀, G₁, hP, hG₁, hT⟩

theorem sqN_eq_of_isUUOver {N : ℕ} (hN : Odd N) (s : SecN Xo x 1) (a t : ptO Xo x ⟶ Xo.univ.t.G)
    (ha : a ^ (N ^ 2) = 1) (ht : t ^ (N ^ 2) = 1)
    (F F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo x)))
    (hF : IsUUOver Xo.univ.t.G Xo.univ.t.PP N s a t F) (hF' : IsUUOver Xo.univ.t.G Xo.univ.t.PP N s a t F') :
    sqN Xo N F = sqN Xo N F' := by
  have hN2 : Odd (N ^ 2) := hN.pow
  have huu := (GlobalTheory.PlaceInt.uu_through_moves E H Dw l Xo S x N hN s).1
  obtain ⟨F₀, F₁, hP, hM, hT⟩ := (huu a t F ha ht).1 hF
  obtain ⟨G₀, G₁, hP', hM', hT'⟩ := (huu a t F' ha ht).1 hF'
  have hbar : (N : 𝓞 E) * H.bar (N : 𝓞 E) = ((N ^ 2 : ℕ) : 𝓞 E) := by
    rw [map_natCast, Nat.cast_pow, sq]
  have h0 : F₀ = G₀ :=
    (GlobalTheory.existsUnique_pulls E H Dw l Xo S x (N : 𝓞 E) (N ^ 2) 1 (N ^ 2) hbar (by ring) s).unique hP hP'
  subst h0
  have h1 : F₁ = G₁ := (GlobalTheory.existsUnique_moves E H Dw l Xo S x (N ^ 2) hN2 a ha F₀).1.unique hM hM'
  subst h1
  exact (GlobalTheory.existsUnique_moves E H Dw l Xo S x (N ^ 2) hN2 t ht F₁).1.unique hT hT'
end Pts

section Val
variable (T : CDVR)

theorem isUnit_of_coprime {m ℓ : ℕ} (hc : Nat.Coprime m ℓ) (hl : ¬ IsUnit (ℓ : T.V)) : IsUnit (m : T.V) := by
  by_contra h
  have h1 : ((m : ℕ) : T.V) ∈ IsLocalRing.maximalIdeal T.V := (IsLocalRing.mem_maximalIdeal _).2 h
  have h2 : ((ℓ : ℕ) : T.V) ∈ IsLocalRing.maximalIdeal T.V := (IsLocalRing.mem_maximalIdeal _).2 hl
  have key : ((Nat.gcd m ℓ : ℤ) : T.V) =
      ((m : ℤ) : T.V) * (Nat.gcdA m ℓ : T.V) + ((ℓ : ℤ) : T.V) * (Nat.gcdB m ℓ : T.V) := by
    rw [Nat.gcd_eq_gcd_ab]; push_cast; ring
  rw [Nat.Coprime.gcd_eq_one hc] at key
  push_cast at key
  have h3 : (1 : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
    rw [key]; exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_right _ _ h2)
  exact (IsLocalRing.maximalIdeal T.V).ne_top_iff_one.1 (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top h3

theorem vV_natCast {m : ℕ} (hm : IsUnit (m : T.V)) : vV T.V (m : T.Fr) = 0 := by
  have h1 : ((m : ℕ) : T.Fr) = algebraMap T.V T.Fr (m : T.V) := (map_natCast _ _).symm
  unfold vV valV
  rw [h1, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2]
  · simp
  · exact fun hmem => (IsLocalRing.mem_maximalIdeal _).1 hmem hm

theorem vV_inv_eq_zero {u : T.Fr} (hu : vV T.V u = 0) : vV T.V u⁻¹ = 0 := by
  unfold vV at *
  rw [map_inv₀, WithZero.log_inv]
  simpa using hu

theorem le_nval_sum {J : Type} (s : Finset J) (e : ℕ) (r : EReal) (f : J → T.Fr) (hf : ∀ j ∈ s, r ≤ nval T.V e (f j)) :
    r ≤ nval T.V e (∑ j ∈ s, f j) := by
  unfold nval at *
  split_ifs with h0
  · exact le_top
  · have hne : s.Nonempty := by
      by_contra hs
      rw [Finset.not_nonempty_iff_eq_empty] at hs
      exact h0 (by simp [hs])
    obtain ⟨j₀, hj₀, hmax⟩ := Finset.exists_max_image s (fun j => valV T.V (f j)) hne
    have hsum : valV T.V (∑ j ∈ s, f j) ≤ valV T.V (f j₀) := Valuation.map_sum_le _ hmax
    have hs0 : valV T.V (∑ j ∈ s, f j) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    have hf0 : f j₀ ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hsum
      exact hs0 (le_antisymm hsum zero_le)
    have h1 := hf j₀ hj₀
    rw [if_neg hf0] at h1
    refine h1.trans (EReal.coe_le_coe_iff.2 (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg e)))
    have hv : vV T.V (f j₀) ≤ vV T.V (∑ j ∈ s, f j) := by
      unfold vV
      exact neg_le_neg ((WithZero.log_le_log hs0 ((Valuation.ne_zero_iff _).2 hf0)).2 hsum)
    exact_mod_cast hv
end Val

theorem short_bound_of_trivAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ChBound C e ρ w n → ∀ (ℓ : ℕ), ℓ.Prime → ¬ IsUnit (ℓ : T.V) → ∀ (Λ : GenLat E n) (N M : ℕ), Λ.Unimod → Λ.LevOK N M → ∀ (β : c.F), β ≠ 0 → BetaIs (Dw := Dw) c Λ β → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmL c Λ w → ∀ (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo (xOf y) z → (∀ b, tp b ^ (N ^ 2) = 1) → (∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b)) → Λ.TrivAt ℓ → ∀ (n' A Bn j : ℕ) (α β₀ : 𝓞 E), Nat.Coprime n' ℓ → (N : 𝓞 E) = β₀ * α * n' → α * H.bar α = (A : 𝓞 E) → β₀ * H.bar β₀ = (Bn : 𝓞 E) → A * Bn = ℓ ^ j → (∀ b, (tp b ≫ Xo.univ.t.act.act β₀) ^ (n' ^ 2 * A) = 1) → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w α * (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹)) * ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
  intro E iF iN iC H Dw l Xo c iS hst T io y C hC nab hnab e ρ w n he hCB ℓ hℓ hl Λ N M hU hL β hβ0 hβ P hP z tp F hz hgi htp hF hΛ n' A Bn j α β₀ hn' hN hA hBn hAB htpβ
  letI := io.toAlgebra
  have vV_mul : ∀ {u z : T.Fr}, u ≠ 0 → z ≠ 0 → vV T.V u = 0 → vV T.V (u * z) = vV T.V z := by
    intro u z hu0 hz hu
    unfold vV at hu ⊢
    rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hu0) ((Valuation.ne_zero_iff _).2 hz)]
    linarith
  have nval_mul : ∀ {u : T.Fr} (z : T.Fr), u ≠ 0 → vV T.V u = 0 → nval T.V e (u * z) = nval T.V e z := by
    intro u z hu0 hu
    by_cases hz : z = 0
    · rw [hz, mul_zero]
    · unfold nval
      rw [if_neg (mul_ne_zero hu0 hz), if_neg hz, vV_mul hu0 hz hu]
  have hNodd : Odd N := hL.1
  obtain ⟨J, J', iJ, iJ', a, a', σ, hinj, ha, ⟨m, hm, ha'⟩, hz', hcard⟩ :=
    GlobalTheory.T.isotropic_group_primary_decomposition E H Dw l Xo T.Fr (xOf y) n Λ N M ℓ hU hL hℓ z hz hgi
  obtain ⟨hfac, hmne, hrest⟩ := GlobalTheory.T.lattice_trivial_at_prime_indices_and_units E H Dw l c n Λ N M ℓ hU hL hℓ hΛ
  obtain ⟨hβv, hFFV⟩ := hrest T io hl
  obtain ⟨j₀⟩ : Nonempty J := Fintype.card_pos_iff.1 (by rw [hcard]; exact pow_pos hℓ.pos _)
  have hell : ∀ i b, ∃ k : ℕ, a i b ^ (ℓ ^ k) = 1 := fun i => ((ha (a i)).1 ⟨i, rfl⟩).2
  have haN : ∀ i b, a i b ^ N = 1 := by
    intro i b
    obtain ⟨k, hk⟩ := hell i b
    exact pow_eq_one_of_trivAt Xo hΛ ((ha (a i)).1 ⟨i, rfl⟩).1 b hk
  have hUU : ∀ i i' b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (a' i' b) (tp b) (F (σ (i, i')) b) := by
    intro i i' b
    obtain ⟨k, hk⟩ := hell i b
    have h := hF (σ (i, i')) b
    rw [hz' i i' b] at h
    exact isUUOver_of_mul Xo hNodd (sOf1 y) (a i b) (a' i' b) (tp b) (haN i b) (ha' i' b).2 (htp b)
      (Nat.Coprime.pow_right k hm) hk (ha' i' b).1 _ h
  have hG : ∀ i i', hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F (σ (i, i')) b)) P =
      hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F (σ (j₀, i')) b)) P := by
    intro i i'
    rw [show (fun b => sqN Xo N (F (σ (i, i')) b)) = (fun b => sqN Xo N (F (σ (j₀, i')) b)) from
      funext fun b => sqN_eq_of_isUUOver Xo hNodd (sOf1 y) (a' i' b) (tp b) (ha' i' b).2 (htp b) _ _
        (hUU i i' b) (hUU j₀ i' b)]
  have hsum : (∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) =
      (Fintype.card J : T.Fr) * ∑ i', hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F (σ (j₀, i')) b)) P := by
    rw [← Equiv.sum_comp σ, Fintype.sum_prod_type]
    simp only [hG]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hN2 : N ^ 2 = ℓ ^ j * n' ^ 2 := by
    have hb : ∀ k : ℕ, H.bar (k : 𝓞 E) = k := fun k => map_natCast _ k
    have h2 : ((N ^ 2 : ℕ) : 𝓞 E) = ((ℓ ^ j * n' ^ 2 : ℕ) : 𝓞 E) := by
      calc ((N ^ 2 : ℕ) : 𝓞 E) = (N : 𝓞 E) * H.bar (N : 𝓞 E) := by rw [hb]; push_cast; ring
        _ = (β₀ * H.bar β₀) * (α * H.bar α) * ((n' : 𝓞 E) * H.bar (n' : 𝓞 E)) := by
          rw [hN]; simp only [map_mul]; ring
        _ = ((ℓ ^ j * n' ^ 2 : ℕ) : 𝓞 E) := by
          rw [hA, hBn, hb, ← hAB]; push_cast; ring
    exact_mod_cast h2
  have ha'n : ∀ i' b, a' i' b ^ (n' ^ 2) = 1 := by
    intro i' b
    have h1 : a' i' b ^ (n' ^ 2 * ℓ ^ j) = 1 := by
      rw [show n' ^ 2 * ℓ ^ j = N ^ 2 by rw [hN2]; ring]; exact (ha' i' b).2
    have hg := pow_gcd_eq_one.2 ⟨h1, (ha' i' b).1⟩
    rw [Nat.Coprime.gcd_mul_right_cancel (n' ^ 2) (Nat.Coprime.pow_left j hm.symm)] at hg
    obtain ⟨d, hd⟩ := Nat.gcd_dvd_left (n' ^ 2) m
    rw [hd, pow_mul, hg, one_pow]
  have hterm : ∀ i', ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w α * ((N : c.F) ^ P.totalDegree)⁻¹) *
      hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F (σ (j₀, i')) b)) P) := by
    intro i'
    refine GlobalTheory.T.harmonicValue_translated_product_valuation_bound E H Dw l Xo c hst T io y C hC nab hnab e ρ w n he hCB N n' A Bn α β₀ hNodd hN hA hBn
      (isUnit_of_coprime T hn' hl) (a' i') tp (fun b => F (σ (j₀, i')) b) ?_ P hP.1 (hFFV w P hP)
    intro b
    refine ⟨(ha' i' b).2, htp b, ?_, htpβ b, hUU j₀ i' b⟩
    have := Xo.univ.t.act.hom (α * β₀)
    rw [← MonObj.pow_comp, ha'n i' b]
    have h0 := MonObj.pow_comp (a' i' b) 0 (Xo.univ.t.act.act (α * β₀))
    simpa using h0
  obtain ⟨v, hvd⟩ : ∃ v, v = (Λ.mIdx N (Dw.p + Dw.q)).factorization ℓ := ⟨_, rfl⟩
  obtain ⟨mc, hmc⟩ : ∃ mc, mc = Λ.mIdx N (Dw.p + Dw.q) / ℓ ^ v := ⟨_, rfl⟩
  have hsplit : ℓ ^ v * mc = Λ.mIdx N (Dw.p + Dw.q) := by
    rw [hmc, hvd]; exact Nat.ordProj_mul_ordCompl_eq_self _ _
  have hcop : Nat.Coprime mc ℓ := by rw [hmc, hvd]; exact (Nat.coprime_ordCompl hℓ hmne).symm
  have hmc0 : mc ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hsplit; exact hmne hsplit.symm
  have hcardJ : Fintype.card J = ℓ ^ v := by rw [hcard, hfac, hvd]
  have hkey : io (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((Fintype.card J : ℕ) : c.F)) =
      (io β)⁻¹ * ((mc : ℕ) : T.Fr)⁻¹ := by
    have : β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((Fintype.card J : ℕ) : c.F) = β⁻¹ * ((mc : ℕ) : c.F)⁻¹ := by
      rw [hcardJ, ← hsplit]
      push_cast
      have h1 : ((ℓ : ℕ) : c.F) ^ v ≠ 0 := pow_ne_zero v (Nat.cast_ne_zero.2 hℓ.ne_zero)
      rw [mul_inv, _root_.mul_assoc β⁻¹]
      congr 1
      rw [_root_.mul_assoc, _root_.mul_comm ((mc : c.F))⁻¹, ← _root_.mul_assoc, inv_mul_cancel₀ h1, _root_.one_mul]
    rw [this, map_mul, map_inv₀, map_inv₀, map_natCast]
  have hprod : io (nrm Dw c w α * (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹)) *
      ((Fintype.card J : T.Fr) * ∑ i', hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F (σ (j₀, i')) b)) P) =
      io (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((Fintype.card J : ℕ) : c.F)) *
        ∑ i', io (nrm Dw c w α * ((N : c.F) ^ P.totalDegree)⁻¹) *
          hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F (σ (j₀, i')) b)) P := by
    rw [← Finset.mul_sum]; simp only [map_mul, map_natCast]; ring
  have hu0 : (io β)⁻¹ * ((mc : ℕ) : T.Fr)⁻¹ ≠ 0 := by
    refine mul_ne_zero (inv_ne_zero ((map_ne_zero io).2 hβ0)) (inv_ne_zero ?_)
    rw [← map_natCast io]; exact (map_ne_zero io).2 (Nat.cast_ne_zero.2 hmc0)
  have hu : vV T.V ((io β)⁻¹ * ((mc : ℕ) : T.Fr)⁻¹) = 0 := by
    have h1 : vV T.V (io β)⁻¹ = 0 := vV_inv_eq_zero T (hβv β hβ0 hβ)
    have h2 : vV T.V ((mc : ℕ) : T.Fr)⁻¹ = 0 := vV_inv_eq_zero T (vV_natCast T (isUnit_of_coprime T hcop hl))
    rw [vV_mul (inv_ne_zero ((map_ne_zero io).2 hβ0)) (right_ne_zero_of_mul hu0) h1, h2]
  rw [hsum, hprod, hkey, nval_mul _ hu0 hu]
  exact le_nval_sum T Finset.univ e _ _ (fun i' _ => hterm i')

end GlobalTheory.PlaceInt.ShortTriv
