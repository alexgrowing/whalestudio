import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOfNormResultantEqStatement
open Polynomial

namespace GlobalTheory.PolyNorm

noncomputable def ev {r : ℕ} (Φ : MvPolynomial (Fin r) ℚ) {K : Type} [CommRing K] [Algebra ℚ K]
    (F : K[X]) : K :=
  MvPolynomial.aeval (fun i : Fin r => F.coeff i) Φ

noncomputable def gen {r : ℕ} {K : Type} [CommRing K] (f : Fin r → K) : K[X] :=
  ∑ i : Fin r, monomial (i : ℕ) (f i)

theorem ev_map {r : ℕ} (Φ : MvPolynomial (Fin r) ℚ) {K L : Type} [CommRing K] [Algebra ℚ K]
    [CommRing L] [Algebra ℚ L] (φ : K →+* L) (F : K[X]) : φ (ev Φ F) = ev Φ (F.map φ) := by
  unfold ev
  rw [MvPolynomial.map_aeval, MvPolynomial.aeval_def, MvPolynomial.coe_eval₂Hom]
  congr 1
  · exact RingHom.ext_rat _ _
  · ext i; simp

theorem gen_map {r : ℕ} {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) (f : Fin r → K) :
    (gen f).map φ = gen (fun i => φ (f i)) := by
  simp [gen, Polynomial.map_sum]

theorem gen_coeff {r : ℕ} {K : Type} [CommRing K] (F : K[X]) (h : F.natDegree < r) :
    gen (fun i : Fin r => F.coeff i) = F := by
  unfold gen
  rw [Fin.sum_univ_eq_sum_range (fun i => monomial i (F.coeff i)) r]
  exact (as_sum_range' F r h).symm

theorem natDegree_gen {r : ℕ} {K : Type} [CommRing K] (f : Fin (r + 1) → K) :
    (gen f).natDegree ≤ r := by
  unfold gen
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => (natDegree_monomial_le _).trans ?_
  exact Nat.lt_succ_iff.mp i.2

theorem ev_homog {r m : ℕ} {Φ : MvPolynomial (Fin r) ℚ} (h : Φ.IsHomogeneous m)
    {K : Type} [CommRing K] [Algebra ℚ K] (c : K) (F : K[X]) :
    ev Φ (C c * F) = c ^ m * ev Φ F := by
  unfold ev
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : ∑ i, d i = m := by
    have := h.degree_eq_sum_deg_support hd
    rw [this]
    exact (Finset.sum_subset (Finset.subset_univ _) (by simp)).symm
  simp only [coeff_C_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd']
  ring

section
variable (N : ℤ[X] → ℚ) (Φ : (r : ℕ) → MvPolynomial (Fin r) ℚ)
  (hN : ∀ r (F : ℤ[X]), F.natDegree < r → N F = ev (Φ r) (F.map (Int.castRingHom ℚ)))
include hN

theorem shift_poly (F : ℤ[X]) : ∃ p : ℚ[X], ∀ t : ℕ, N (F + t) = p.eval (t : ℚ) := by
  refine ⟨ev (Φ (F.natDegree + 1)) (F.map (Int.castRingHom ℚ[X]) + C X), fun t => ?_⟩
  rw [hN (F.natDegree + 1), ← coe_evalRingHom, ev_map]
  · congr 1
    simp [Polynomial.map_map, RingHom.ext_int ((evalRingHom (t:ℚ)).comp _) (Int.castRingHom ℚ)]
  · rw [← C_eq_natCast, natDegree_add_C]; omega

theorem shift_poly₂ (F G : ℤ[X]) :
    ∃ p : ℚ[X], ∀ t : ℕ, N ((F + t) * (G + t)) = p.eval (t : ℚ) := by
  refine ⟨ev (Φ (F.natDegree + G.natDegree + 1)) ((F.map (Int.castRingHom ℚ[X]) + C X) *
    (G.map (Int.castRingHom ℚ[X]) + C X)), fun t => ?_⟩
  rw [hN (F.natDegree + G.natDegree + 1), ← coe_evalRingHom, ev_map]
  · congr 1
    simp [Polynomial.map_map, RingHom.ext_int ((evalRingHom (t:ℚ)).comp _) (Int.castRingHom ℚ)]
  · refine lt_of_le_of_lt natDegree_mul_le ?_
    rw [← C_eq_natCast, natDegree_add_C, natDegree_add_C]; omega

theorem mul_all (Good : ℤ[X] → Prop) (hG : ∀ F, ∀ᶠ t : ℕ in Filter.atTop, Good (F + t))
    (hm : ∀ F G, Good F → Good G → N (F * G) = N F * N G) (F G : ℤ[X]) :
    N (F * G) = N F * N G := by
  obtain ⟨p, hp⟩ := shift_poly N Φ hN F
  obtain ⟨q, hq⟩ := shift_poly N Φ hN G
  obtain ⟨s, hs⟩ := shift_poly₂ N Φ hN F G
  have : s = p * q := by
    apply eq_of_infinite_eval_eq
    obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp ((hG F).and (hG G))
    refine Set.Infinite.mono (s := (fun t : ℕ => (t : ℚ)) '' Set.Ici a) ?_
      ((Set.Ici_infinite a).image Nat.cast_injective.injOn)
    rintro _ ⟨t, ht, rfl⟩
    simp only [Set.mem_setOf_eq, eval_mul]
    rw [← hp, ← hq, ← hs, hm _ _ (ha t ht).1 (ha t ht).2]
  have h0 := hs 0
  rw [this, eval_mul, ← hp, ← hq] at h0
  simpa using h0

theorem ev_mul (hm : ∀ F G, N (F * G) = N F * N G) {K : Type} [CommRing K] [Algebra ℚ K]
    (r₁ r₂ s : ℕ) (hs : r₁ + r₂ < s) (F G : K[X]) (hF : F.natDegree ≤ r₁)
    (hG : G.natDegree ≤ r₂) :
    ev (Φ s) (F * G) = ev (Φ (r₁ + 1)) F * ev (Φ (r₂ + 1)) G := by
  let R := MvPolynomial (Fin (r₁ + 1) ⊕ Fin (r₂ + 1)) ℚ
  let A : R[X] := gen fun i => MvPolynomial.X (Sum.inl i)
  let B : R[X] := gen fun i => MvPolynomial.X (Sum.inr i)
  have key : ev (Φ s) (A * B) = ev (Φ (r₁ + 1)) A * ev (Φ (r₂ + 1)) B := by
    apply MvPolynomial.funext_set (s := fun _ => Set.range (Int.cast : ℤ → ℚ))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective)
    intro x hx
    choose y hy using fun i => hx i (Set.mem_univ i)
    have hA : A.map (MvPolynomial.eval x) =
        (gen fun i => y (Sum.inl i)).map (Int.castRingHom ℚ) := by
      simp [A, gen_map, hy]
    have hB : B.map (MvPolynomial.eval x) =
        (gen fun i => y (Sum.inr i)).map (Int.castRingHom ℚ) := by
      simp [B, gen_map, hy]
    have h1 := natDegree_gen fun i => y (Sum.inl i)
    have h2 := natDegree_gen fun i => y (Sum.inr i)
    rw [map_mul, ev_map, ev_map, ev_map, Polynomial.map_mul, hA, hB, ← Polynomial.map_mul,
      ← hN, ← hN, ← hN, hm]
    · omega
    · omega
    · exact lt_of_le_of_lt natDegree_mul_le (by omega)
  let φ : R →+* K := (MvPolynomial.aeval
    (Sum.elim (fun i : Fin (r₁ + 1) => F.coeff i) (fun i : Fin (r₂ + 1) => G.coeff i))).toRingHom
  have hA : A.map φ = F := by
    refine (gen_map _ _).trans (Eq.trans ?_ (gen_coeff F (Nat.lt_succ_of_le hF)))
    congr 1
    exact funext fun i => MvPolynomial.aeval_X _ _
  have hB : B.map φ = G := by
    refine (gen_map _ _).trans (Eq.trans ?_ (gen_coeff G (Nat.lt_succ_of_le hG)))
    congr 1
    exact funext fun i => MvPolynomial.aeval_X _ _
  have := congrArg φ key
  rwa [map_mul, ev_map, ev_map, ev_map, Polynomial.map_mul, hA, hB] at this

theorem ev_one (h1 : N 1 = 1) {K : Type} [CommRing K] [Algebra ℚ K] (r : ℕ) :
    ev (Φ (r + 1)) (1 : K[X]) = 1 := by
  have := ev_map (Φ (r + 1)) (algebraMap ℚ K) ((1 : ℤ[X]).map (Int.castRingHom ℚ))
  rw [← hN _ _ (by simp), h1] at this
  simpa using this.symm

theorem ev_compat (h1 : N 1 = 1) (hm : ∀ F G, N (F * G) = N F * N G) {K : Type} [CommRing K]
    [Algebra ℚ K] (s : ℕ) (F : K[X]) (hF : F.natDegree < s) :
    ev (Φ s) F = ev (Φ (F.natDegree + 1)) F := by
  have := ev_mul N Φ hN hm F.natDegree 0 s hF F 1 le_rfl (by simp)
  rwa [ev_one N Φ hN h1, mul_one, mul_one] at this

theorem exists_ext (h1 : N 1 = 1) (hm : ∀ F G, N (F * G) = N F * N G) (K : Type) [CommRing K]
    [Algebra ℚ K] : ∃ M : K[X] →* K, ∀ s (F : K[X]), F.natDegree < s → M F = ev (Φ s) F := by
  refine ⟨⟨⟨fun F => ev (Φ (F.natDegree + 1)) F, ev_one N Φ hN h1 _⟩, fun F G => ?_⟩,
    fun s F h => (ev_compat N Φ hN h1 hm s F h).symm⟩
  dsimp only
  rw [← ev_mul N Φ hN hm F.natDegree G.natDegree _ (Nat.lt_succ_self _) F G le_rfl le_rfl,
    ← ev_compat N Φ hN h1 hm]
  exact Nat.lt_succ_of_le natDegree_mul_le

end

theorem monic_ev {m : ℕ} {Φ : MvPolynomial (Fin 2) ℚ} (h : Φ.IsHomogeneous m)
    (h1 : ev Φ (1 : ℚ[X]) = 1) :
    (ev Φ (C X - X : ℚ[X][X])).Monic ∧ (ev Φ (C X - X : ℚ[X][X])).natDegree = m := by
  have hd : ∀ d ∈ Φ.support, d 0 + d 1 = m := fun d hd => by
    have := h.degree_eq_sum_deg_support hd
    rw [this, ← Fin.sum_univ_two (fun i => d i)]
    exact (Finset.sum_subset (Finset.subset_univ _) (by simp)).symm
  have e : ev Φ (C X - X : ℚ[X][X]) =
      ∑ d ∈ Φ.support, monomial (d 0) (Φ.coeff d * (-1) ^ d 1) := by
    unfold ev
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [← C_mul_X_pow_eq_monomial, coeff_X, coeff_C]
    ring
  have hle : (ev Φ (C X - X : ℚ[X][X])).natDegree ≤ m := by
    rw [e]
    refine natDegree_sum_le_of_forall_le _ _ fun d hd' => (natDegree_monomial_le _).trans ?_
    have := hd d hd'; omega
  have hc : (ev Φ (C X - X : ℚ[X][X])).coeff m = 1 := by
    rw [e, ← h1, finset_sum_coeff]
    unfold ev
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    refine Finset.sum_congr rfl fun d hd' => ?_
    have := hd d hd'
    by_cases h0 : d 1 = 0
    · have : d 0 = m := by omega
      simp [coeff_monomial, h0, this]
    · have : d 0 ≠ m := by omega
      simp [coeff_monomial, h0, this, coeff_one]
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one m hle hc,
    natDegree_eq_of_le_of_coeff_ne_zero hle (by simp [hc])⟩

theorem eq_prod_of_mul {K : Type} [Field K] [IsAlgClosed K] (M : K[X] →* K) (a : Multiset K)
    (hc : ∀ c, M (C c) = c ^ Multiset.card a)
    (hl : ∀ β, M (C β - X) = (a.map fun x => β - x).prod) (F : K[X]) :
    M F = (a.map fun x => F.eval x).prod := by
  let M' : K[X] →* K :=
    { toFun := fun F => (a.map fun x => F.eval x).prod
      map_one' := by simp
      map_mul' := by simp [Multiset.prod_map_mul] }
  have hc' : ∀ c, M (C c) = M' (C c) := fun c => by simp [hc, M']
  have hl' : ∀ β, M (X - C β) = M' (X - C β) := fun β => by
    have : (X - C β : K[X]) = C (-1) * (C β - X) := by simp
    rw [this, map_mul, map_mul, hc', hl]
    simp [M']
  change M F = M' F
  rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (p := F) IsAlgClosed.card_roots_eq_natDegree,
    map_mul, map_mul, hc', map_multiset_prod, map_multiset_prod, Multiset.map_map,
    Multiset.map_map]
  simp [hl']

theorem norm_all {l : ℕ} [hl : Fact l.Prime] {m : ℕ} (U : Matrix (Fin m) (Fin m) ℤ_[l])
    (N : ℤ[X] → ℚ) (Good : ℤ[X] → Prop)
    (hp : ∀ F : ℤ[X], ∃ p : ℚ[X], ∀ t : ℕ, N (F + t) = p.eval (t : ℚ))
    (hG : ∀ F, ∀ᶠ t : ℕ in Filter.atTop, Good (F + t))
    (hn : ∀ F, Good F → ‖((N F : ℚ) : ℚ_[l])‖ = ‖(Polynomial.aeval U F).det‖) (F : ℤ[X]) :
    ‖((N F : ℚ) : ℚ_[l])‖ = ‖(Polynomial.aeval U F).det‖ := by
  obtain ⟨p, hp⟩ := hp F
  have t0 : Filter.Tendsto (fun k : ℕ => (l : ℤ_[l]) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt))
  have c1 : Continuous fun x : ℤ_[l] => ‖(p.map (Rat.castHom ℚ_[l])).eval (x : ℚ_[l])‖ :=
    ((p.map (Rat.castHom ℚ_[l])).continuous.comp continuous_subtype_val).norm
  have c2 : Continuous fun x : ℤ_[l] =>
      ‖(Polynomial.aeval U F + x • (1 : Matrix (Fin m) (Fin m) ℤ_[l])).det‖ :=
    ((continuous_const.add (continuous_id.smul continuous_const)).matrix_det).norm
  have e1 : ∀ t : ℕ, ((N (F + t) : ℚ) : ℚ_[l]) =
      (p.map (Rat.castHom ℚ_[l])).eval (((t : ℤ_[l])) : ℚ_[l]) := fun t => by
    rw [hp, PadicInt.coe_natCast, ← map_natCast (Rat.castHom ℚ_[l]), eval_map, eval₂_at_apply]
    rfl
  have e2 : ∀ t : ℕ, Polynomial.aeval U (F + (t : ℤ[X])) =
      Polynomial.aeval U F + (t : ℤ_[l]) • (1 : Matrix (Fin m) (Fin m) ℤ_[l]) := fun t => by
    rw [map_add, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_one]
  have h := tendsto_nhds_unique_of_eventuallyEq ((c1.tendsto 0).comp t0) ((c2.tendsto 0).comp t0)
    (((tendsto_pow_atTop_atTop_of_one_lt hl.out.one_lt).eventually (hG F)).mono fun k hk => by
      have := hn _ hk
      rw [e1, e2] at this
      simpa using this)
  have := e1 0
  simp only [Nat.cast_zero, add_zero] at this
  rw [this, h]
  simp

theorem det_eq_prod {K : Type} [Field K] [IsAlgClosed K] {m : ℕ} (V : Matrix (Fin m) (Fin m) K)
    (b : Multiset K) (hb : V.charpoly = (b.map fun x => X - C x).prod) (F : K[X]) :
    (aeval V F).det = (b.map fun x => F.eval x).prod := by
  have hc : Multiset.card b = m := by
    rw [← natDegree_multiset_prod_X_sub_C_eq_card b, ← hb]; simp
  refine eq_prod_of_mul (Matrix.detMonoidHom.comp (aeval V : K[X] →ₐ[K] _).toMonoidHom) b
    (fun c => ?_) (fun β => ?_) F
  · simp [hc, Algebra.algebraMap_eq_smul_one]
  · have := congrArg (eval β) hb
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at this
    simpa [Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def] using this

theorem eq_det : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (U : Matrix (Fin m) (Fin m) ℤ_[l]) (N : Polynomial ℤ → ℚ) (Good : Polynomial ℤ → Prop), (∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous m ∧ ∀ a : Fin r → ℤ, N (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ) → N 1 = 1 → (∀ F, ∀ᶠ t : ℕ in Filter.atTop, Good (F + t)) → (∀ F G, Good F → Good G → N (F * G) = N F * N G) → (∀ F, Good F → ‖((N F : ℚ) : ℚ_[l])‖ = ‖(Polynomial.aeval U F).det‖) → ∀ F, ((N F : ℚ) : ℚ_[l]) = ((Polynomial.aeval U F).det : ℤ_[l]) := by
  intro l _ m U N Good hΦ h1 hG hm hn
  choose Φ hh hΦ using hΦ
  have hN : ∀ r (F : ℤ[X]), F.natDegree < r → N F = ev (Φ r) (F.map (Int.castRingHom ℚ)) := by
    intro r F hF
    have := hΦ r fun i => F.coeff i
    rw [show ∑ i : Fin r, monomial (i : ℕ) (F.coeff i) = F from gen_coeff F hF] at this
    rw [this]
    simp [ev, MvPolynomial.aeval_eq_eval]
  have hm' := mul_all N Φ hN Good hG hm
  have hn' := norm_all U N Good (shift_poly N Φ hN) hG hn
  obtain ⟨E, _, _, _, _⟩ : ∃ (E : Type) (_ : Field E) (_ : Algebra ℚ_[l] E),
      IsAlgClosed E ∧ Algebra.IsAlgebraic ℚ_[l] E :=
    ⟨AlgebraicClosure ℚ_[l], inferInstance, inferInstance, inferInstance, inferInstance⟩
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
  have inj : Function.Injective (algebraMap ℚ_[l] E) := (algebraMap ℚ_[l] E).injective
  obtain ⟨M, hM⟩ := exists_ext N Φ hN h1 hm' E
  obtain ⟨hP, hPd⟩ := monic_ev (hh 2) (ev_one N Φ hN h1 1)
  set P := ev (Φ 2) (C X - X : ℚ[X][X]) with hPdef
  let ψ : ℤ_[l] →+* E := (algebraMap ℚ_[l] E).comp PadicInt.Coe.ringHom
  let V : Matrix (Fin m) (Fin m) E := U.map ψ
  have roots : ∀ S : E[X], S.Monic → S = (S.roots.map fun x => X - C x).prod := fun S hS =>
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hS IsAlgClosed.card_roots_eq_natDegree).symm
  let a := (P.map (algebraMap ℚ E)).roots
  have ha : P.map (algebraMap ℚ E) = (a.map fun x => X - C x).prod := roots _ (hP.map _)
  have hac : Multiset.card a = m := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hP.natDegree_map, hPd]
  have hMa : ∀ F, M F = (a.map fun x => F.eval x).prod := by
    refine eq_prod_of_mul M a (fun c => ?_) (fun β => ?_)
    · rw [hM 1 _ (by simp), ← mul_one (C c), ev_homog (hh 1), ev_one N Φ hN h1, mul_one, hac]
    · have := congrArg (eval β) ha
      rw [eval_multiset_prod, Multiset.map_map, eval_map, ← coe_eval₂RingHom, hPdef,
        ev_map] at this
      rw [hM 2]
      · simpa using this
      · exact lt_of_le_of_lt (natDegree_sub_le _ _) (by simp)
  have hNa : ∀ F : ℤ[X], algebraMap ℚ_[l] E (N F : ℚ_[l]) = (a.map fun x => aeval x F).prod := by
    intro F
    have := hMa (F.map (algebraMap ℤ E))
    simp only [eval_map_algebraMap] at this
    rw [← this, hM (F.natDegree + 1) _ (Nat.lt_succ_of_le natDegree_map_le), map_ratCast,
      ← eq_ratCast (algebraMap ℚ E), hN _ F (Nat.lt_succ_self _), ev_map, Polynomial.map_map]
    congr 2
    all_goals exact RingHom.ext_int _ _
  have hDb : ∀ b : Multiset E, V.charpoly = (b.map fun x => X - C x).prod → ∀ F : ℤ[X],
      algebraMap ℚ_[l] E ((aeval U F).det : ℤ_[l]) = (b.map fun x => aeval x F).prod := by
    intro b hb F
    have := det_eq_prod V b hb (F.map (algebraMap ℤ E))
    simp only [eval_map_algebraMap, aeval_map_algebraMap] at this
    rw [← this]
    change ψ _ = _
    rw [RingHom.map_det]
    congr 1
    exact (aeval_algHom_apply ψ.mapMatrix.toIntAlgHom U F).symm
  have hPm : (P.map (Rat.castHom ℚ_[l])).map (algebraMap ℚ_[l] E) = P.map (algebraMap ℚ E) := by
    rw [Polynomial.map_map]; congr 1 <;> exact RingHom.ext_rat _ _
  have hQm : (U.charpoly.map PadicInt.Coe.ringHom).map (algebraMap ℚ_[l] E) = V.charpoly := by
    rw [Polynomial.map_map, ← Matrix.charpoly_map]
  have hb := roots _ V.charpoly_monic
  have key := GlobalTheory.T.eq_of_norm_prod_aeval_eq_moduli l E a V.charpoly.roots (P.map (Rat.castHom ℚ_[l]))
    (U.charpoly.map PadicInt.Coe.ringHom) (hPm.trans ha) (hQm.trans hb) (fun F u v hu hv => by
      rw [← hNa] at hu
      rw [← hDb _ hb] at hv
      rw [inj hu, inj hv, hn']
      rfl)
  intro F
  apply inj
  rw [hNa, hDb a]
  rw [← hQm, ← key, hPm, ha]

end GlobalTheory.PolyNorm
