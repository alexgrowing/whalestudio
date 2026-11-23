import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFundCycleBaseChange

set_option autoImplicit false

noncomputable section

open MvPolynomial
open GroundTheory.Heights₂.Heights (IsProjPrime IsHomogIdeal localMult linForm)

namespace ChowFormHeightComparison₂.CF.A

variable {R A : Type} [CommRing R] [CommRing A] {m : ℕ} (c : R →+* A) (t : Fin m → A)

def cone : MvPolynomial (Fin m) R →+* Polynomial A :=
  eval₂Hom (Polynomial.C.comp c) fun k => Polynomial.X * Polynomial.C (t k)

theorem cone_of_homog {d : ℕ} {g : MvPolynomial (Fin m) R} (hg : g.IsHomogeneous d) :
    cone c t g = Polynomial.X ^ d * Polynomial.C (eval₂Hom c t g) := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  simp only [cone, map_sum, eval₂Hom_monomial, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  have : a.degree = d := by rw [Finsupp.degree_eq_weight_one]; exact hg (mem_support_iff.1 ha)
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_prod, map_pow]
  rw [← this, Finsupp.degree_apply, mul_left_comm, RingHom.comp_apply]

theorem coeff_cone (g : MvPolynomial (Fin m) R) (d : ℕ) :
    (cone c t g).coeff d = eval₂Hom c t (homogeneousComponent d g) := by
  conv_lhs => rw [← g.sum_homogeneousComponent, map_sum]
  simp only [cone_of_homog c t (homogeneousComponent_isHomogeneous _ g), Polynomial.finsetSum_coeff,
    Polynomial.X_pow_mul_C, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]

theorem eval₂Hom_mul {d : ℕ} {g : MvPolynomial (Fin m) R} (hg : g.IsHomogeneous d) (a : A) :
    eval₂Hom c (fun j => t j * a) g = eval₂Hom c t g * a ^ d := by
  have e : (Polynomial.evalRingHom a).comp (cone c t) = eval₂Hom c fun j => t j * a :=
    MvPolynomial.ringHom_ext (fun r => by simp [cone]) fun j => by simp [cone]
  rw [← e, RingHom.comp_apply, cone_of_homog c t hg]
  simp

def pr (q : Ideal A) : Ideal (MvPolynomial (Fin m) R) := (q.map Polynomial.C).comap (cone c t)

variable {c t}

theorem mem_pr {q : Ideal A} {g : MvPolynomial (Fin m) R} :
    g ∈ pr c t q ↔ ∀ d, eval₂Hom c t (homogeneousComponent d g) ∈ q := by
  simp only [pr, Ideal.mem_comap, Ideal.mem_map_C_iff, coeff_cone]

theorem mem_pr_homog {q : Ideal A} {d : ℕ} {g : MvPolynomial (Fin m) R} (hg : g.IsHomogeneous d) :
    g ∈ pr c t q ↔ eval₂Hom c t g ∈ q := by
  rw [mem_pr]
  refine ⟨fun h => by simpa [homogeneousComponent_of_mem hg] using h d, fun h e => ?_⟩
  rw [homogeneousComponent_of_mem hg]
  split_ifs
  · exact h
  · simp

theorem isHomog_pr (q : Ideal A) : IsHomogIdeal (pr c t q) := fun _ hg d =>
  (mem_pr_homog (homogeneousComponent_isHomogeneous d _)).2 (mem_pr.1 hg d)

instance isPrime_pr (q : Ideal A) [q.IsPrime] : (pr c t q).IsPrime :=
  have : (q.map (Polynomial.C : A →+* Polynomial A)).IsPrime := Ideal.isPrime_map_C_of_isPrime
  Ideal.comap_isPrime _ _

theorem pr_mono {q q' : Ideal A} (h : q ≤ q') : pr c t q ≤ pr c t q' := Ideal.comap_mono (Ideal.map_mono h)

theorem isHomog_linForm (u : Fin m → R) : (linForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X R j).C_mul _

variable {k : Fin m}

theorem X_notMem_pr (hk : t k = 1) (q : Ideal A) [hq : q.IsPrime] : X k ∉ pr c t q := by
  rw [mem_pr_homog (isHomogeneous_X R k), eval₂Hom_X', hk]
  exact (Ideal.ne_top_iff_one q).1 hq.ne_top

theorem isProjPrime_pr (hk : t k = 1) (q : Ideal A) [q.IsPrime] : IsProjPrime (pr c t q) :=
  ⟨inferInstance, isHomog_pr q, k, X_notMem_pr hk q⟩

theorem exists_homog (hk : t k = 1) (g : MvPolynomial (Fin m) R) {N : ℕ} (hN : g.totalDegree ≤ N) :
    ∃ G : MvPolynomial (Fin m) R, G.IsHomogeneous N ∧ eval₂Hom c t G = eval₂Hom c t g ∧
      ∀ W : Ideal (MvPolynomial (Fin m) R), IsHomogIdeal W → g ∈ W → G ∈ W := by
  refine ⟨∑ d ∈ Finset.range (g.totalDegree + 1), homogeneousComponent d g * X k ^ (N - d),
    IsHomogeneous.sum _ _ _ fun d hd => ?_, ?_, fun W hW hg =>
      W.sum_mem fun d _ => W.mul_mem_right _ (hW g hg d)⟩
  · have h := (homogeneousComponent_isHomogeneous d g).mul ((isHomogeneous_X R k).pow (N - d))
    have hd' := Finset.mem_range.1 hd
    rwa [one_mul, show d + (N - d) = N by omega] at h
  · conv_rhs => rw [← g.sum_homogeneousComponent]
    simp only [map_sum, map_mul, map_pow, eval₂Hom_X', hk, one_pow, mul_one]

theorem exists_homog' (hs : Function.Surjective (eval₂Hom c t)) (hk : t k = 1) (a : A) :
    ∃ (N : ℕ) (G : MvPolynomial (Fin m) R), G.IsHomogeneous N ∧ eval₂Hom c t G = a := by
  obtain ⟨g, rfl⟩ := hs a
  obtain ⟨G, h1, h2, -⟩ := exists_homog (c := c) hk g le_rfl
  exact ⟨_, G, h1, h2⟩

theorem pr_le_iff (hs : Function.Surjective (eval₂Hom c t)) (hk : t k = 1) {q q' : Ideal A} :
    pr c t q ≤ pr c t q' ↔ q ≤ q' := by
  refine ⟨fun h a ha => ?_, pr_mono⟩
  obtain ⟨N, G, h1, rfl⟩ := exists_homog' hs hk a
  exact (mem_pr_homog h1).1 (h ((mem_pr_homog h1).2 ha))

theorem exists_eq_pr (hs : Function.Surjective (eval₂Hom c t)) (hk : t k = 1) {W : Ideal (MvPolynomial (Fin m) R)}
    (hp : W.IsPrime) (hh : IsHomogIdeal W) (hX : X k ∉ W) (hle : pr c t ⊥ ≤ W) :
    ∃ q : Ideal A, q.IsPrime ∧ pr c t q = W := by
  have key {d : ℕ} {G : MvPolynomial (Fin m) R} (hG : G.IsHomogeneous d) :
      eval₂Hom c t G ∈ W.map (eval₂Hom c t) ↔ G ∈ W := by
    refine ⟨fun h => ?_, Ideal.mem_map_of_mem _⟩
    obtain ⟨w, hw, e⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 h
    obtain ⟨w', h1, h2, h3⟩ := exists_homog (c := c) hk w (N := d + w.totalDegree) (Nat.le_add_left _ _)
    have h4 : (G * X k ^ w.totalDegree).IsHomogeneous (d + w.totalDegree) := by
      simpa using hG.mul ((isHomogeneous_X R k).pow w.totalDegree)
    have h5 : G * X k ^ w.totalDegree - w' ∈ W := hle ((mem_pr_homog (h4.sub h1)).2 (by
      rw [map_sub, h2, e, map_mul, map_pow, eval₂Hom_X', hk, one_pow, mul_one, sub_self]; exact Ideal.zero_mem _))
    have h6 := W.add_mem h5 (h3 W hh hw)
    rw [sub_add_cancel] at h6
    exact (hp.mem_or_mem h6).resolve_right fun h => hX (hp.mem_of_pow_mem _ h)
  refine ⟨W.map (eval₂Hom c t), ⟨fun h => hX ?_, fun {a b} hab => ?_⟩, ?_⟩
  · exact (key (isHomogeneous_X R k)).1 (h ▸ Submodule.mem_top)
  · obtain ⟨N, G, h1, rfl⟩ := exists_homog' hs hk a
    obtain ⟨N', G', h1', rfl⟩ := exists_homog' hs hk b
    rw [← map_mul, key (h1.mul h1')] at hab
    rw [key h1, key h1']
    exact hp.mem_or_mem hab
  · ext g
    rw [mem_pr]
    simp only [key (homogeneousComponent_isHomogeneous _ g)]
    refine ⟨fun h => ?_, hh g⟩
    rw [← g.sum_homogeneousComponent]
    exact W.sum_mem fun d _ => h d

theorem exists_core (W : Ideal (MvPolynomial (Fin m) R)) [W.IsPrime] :
    ∃ W' : Ideal (MvPolynomial (Fin m) R), W'.IsPrime ∧ IsHomogIdeal W' ∧ W' ≤ W ∧
      ∀ g, (∀ d, homogeneousComponent d g ∈ W) → g ∈ W' := by
  have e (g : MvPolynomial (Fin m) R) :
      eval₂Hom ((Ideal.Quotient.mk W).comp C) (fun j => Ideal.Quotient.mk W (X j)) g = Ideal.Quotient.mk W g := by
    refine RingHom.congr_fun (f := eval₂Hom _ _) (MvPolynomial.ringHom_ext (fun r => ?_) fun j => ?_) g
    · simp
    · simp
  have h (g : MvPolynomial (Fin m) R) :
      g ∈ pr ((Ideal.Quotient.mk W).comp C) (fun j => Ideal.Quotient.mk W (X j)) ⊥ ↔
        ∀ d, homogeneousComponent d g ∈ W := by
    simp only [mem_pr, e, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨_, isPrime_pr ⊥, isHomog_pr _, fun g hg => ?_, fun g => (h g).2⟩
  rw [← g.sum_homogeneousComponent]
  exact W.sum_mem fun d _ => (h g).1 hg d

theorem mem_minimalPrimes_iff (hs : Function.Surjective (eval₂Hom c t)) (hk : t k = 1) (u : Fin m → R)
    (q : Ideal A) [hq : q.IsPrime] :
    pr c t q ∈ (pr c t ⊥ ⊔ Ideal.span {linForm u}).minimalPrimes ↔
      q ∈ (Ideal.span {eval₂Hom c t (linForm u)}).minimalPrimes := by
  have hJ (q' : Ideal A) : pr c t ⊥ ⊔ Ideal.span {linForm u} ≤ pr c t q' ↔
      Ideal.span {eval₂Hom c t (linForm u)} ≤ q' := by
    rw [sup_le_iff, Ideal.span_singleton_le_iff_mem, Ideal.span_singleton_le_iff_mem,
      mem_pr_homog (isHomog_linForm u), and_iff_right (pr_mono bot_le)]
  refine ⟨fun h => ⟨⟨hq, (hJ q).1 h.1.2⟩, fun q' hq' hle => ?_⟩, fun h => ⟨⟨inferInstance, (hJ q).2 h.1.2⟩,
    fun W hW hle => ?_⟩⟩
  · have := hq'.1
    exact (pr_le_iff hs hk).1 (h.2 ⟨inferInstance, (hJ q').2 hq'.2⟩ (pr_mono hle))
  · have := hW.1
    obtain ⟨W', h1, h2, h3, h4⟩ := exists_core W
    have h5 : pr c t ⊥ ≤ W' := fun g hg => h4 g fun d => hW.2 (Ideal.mem_sup_left (isHomog_pr _ g hg d))
    have h6 : linForm u ∈ W' := h4 _ fun d => by
      rw [homogeneousComponent_of_mem (isHomog_linForm u)]
      split_ifs
      · exact hW.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      · exact W.zero_mem
    obtain ⟨q', hq', rfl⟩ := exists_eq_pr hs hk h1 h2 (fun hX => X_notMem_pr hk q (hle (h3 hX))) h5
    exact (pr_mono (h.2 ⟨hq', (hJ q').1 (sup_le h5 ((Ideal.span_singleton_le_iff_mem _).2 h6))⟩
      ((pr_le_iff hs hk).1 (h3.trans hle)))).trans h3

theorem localMult_map {S L : Type} [CommRing S] [CommRing L] (φ : S →+* L) (W' : Ideal L) [W'.IsPrime] (J : Ideal S)
    (hs : ∀ b, ∃ a s, φ s ∉ W' ∧ b * φ s = φ a) (hJ : RingHom.ker φ ≤ J) :
    localMult (J.map φ) W' = localMult J (W'.comap φ) := by
  have hW : (W'.comap φ).IsPrime := Ideal.comap_isPrime _ _
  rw [localMult, localMult, dif_pos hW, dif_pos ‹W'.IsPrime›]
  congr 1
  set SW := Localization.AtPrime (W'.comap φ)
  set LW := Localization.AtPrime W'
  let ψ : SW →+* LW := Localization.localRingHom (W'.comap φ) W' φ rfl
  have hψ (a : S) : ψ (algebraMap S SW a) = algebraMap L LW (φ a) := Localization.localRingHom_to_map _ _ _ _ a
  have hu (s : S) (h : φ s ∉ W') : IsUnit (algebraMap S SW s) :=
    IsLocalization.map_units SW (⟨s, h⟩ : (W'.comap φ).primeCompl)
  have h1 (b : L) : algebraMap L LW b ∈ ψ.range := by
    obtain ⟨a, s, h, e⟩ := hs b
    obtain ⟨v, hv⟩ := (hu s h).exists_right_inv
    refine ⟨algebraMap S SW a * v, ?_⟩
    rw [map_mul, hψ, ← e, map_mul, ← hψ, mul_assoc, ← map_mul, hv, map_one, mul_one]
  have hsurj : Function.Surjective ψ := fun x => by
    obtain ⟨⟨b, b'⟩, e⟩ := IsLocalization.surj W'.primeCompl x
    obtain ⟨a, s, h, e'⟩ := hs b'
    have ha : φ a ∉ W' := e' ▸ fun hm => (‹W'.IsPrime›.mem_or_mem hm).elim b'.2 h
    obtain ⟨v, hv⟩ := (hu a ha).exists_right_inv
    obtain ⟨y, hy⟩ := h1 b
    refine ⟨y * algebraMap S SW s * v, ?_⟩
    have hv' := congrArg ψ hv
    rw [map_mul, hψ, ← e', map_mul, map_one] at hv'
    rw [map_mul, map_mul, hy, hψ, ← e]
    linear_combination x * hv'
  let := ψ.toAlgebra
  have hJ' : (J.map φ).map (algebraMap L LW) = (J.map (algebraMap S SW)).map ψ := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    exact RingHom.ext fun a => (hψ a).symm
  have hker : RingHom.ker ψ ≤ J.map (algebraMap S SW) := fun x hx => by
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj (W'.comap φ).primeCompl x
    have h0 : algebraMap L LW (φ a) = 0 := by
      rw [← hψ, ← e, map_mul, (RingHom.mem_ker).1 hx, zero_mul]
    obtain ⟨b, hb⟩ := (IsLocalization.map_eq_zero_iff W'.primeCompl LW _).1 h0
    obtain ⟨a', s', h, e'⟩ := hs b
    have ha : φ a' ∉ W' := e' ▸ fun hm => (‹W'.IsPrime›.mem_or_mem hm).elim b.2 h
    have h2 : a' * a ∈ J := hJ ((RingHom.mem_ker).2 (by
      rw [map_mul, ← e']; linear_combination φ s' * hb))
    have h3 := Ideal.mem_map_of_mem (algebraMap S SW) h2
    rw [map_mul, ← e] at h3
    exact (Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units SW s)).1
      ((Ideal.unit_mul_mem_iff_mem _ (hu a' ha)).1 h3)
  rw [hJ', ← Module.length_eq_of_surjective (S := SW) (R := LW) hsurj]
  let χ : SW →ₗ[SW] LW ⧸ (J.map (algebraMap S SW)).map ψ :=
    (Ideal.Quotient.mkₐ SW _).toLinearMap ∘ₗ Algebra.linearMap SW LW
  have hχ : Function.Surjective χ := Ideal.Quotient.mk_surjective.comp hsurj
  have hk : LinearMap.ker χ = J.map (algebraMap S SW) := by
    ext x
    change Ideal.Quotient.mk _ (ψ x) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ hsurj,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.2 hker]
  rw [← (χ.quotKerEquivOfSurjective hχ).length_eq, hk]

theorem localMult_pr (hs : Function.Surjective (eval₂Hom c t)) (hk : t k = 1) (u : Fin m → R)
    (q : Ideal A) [hq : q.IsPrime] :
    localMult (pr c t ⊥ ⊔ Ideal.span {linForm u}) (pr c t q) =
      localMult (Ideal.span {eval₂Hom c t (linForm u)}) q := by
  have hp : (q.map (Polynomial.C : A →+* Polynomial A)).IsPrime := Ideal.isPrime_map_C_of_isPrime
  have hX : (Polynomial.X : Polynomial A) ∉ q.map (Polynomial.C : A →+* Polynomial A) := fun h => by
    have := Ideal.mem_map_C_iff.1 h 1
    rw [Polynomial.coeff_X_one] at this
    exact (Ideal.ne_top_iff_one q).1 hq.ne_top this
  have hXk : cone c t (X k) = Polynomial.X := by simp [cone, hk]
  have hker : pr c t ⊥ = RingHom.ker (cone c t) := by rw [pr, Ideal.map_bot]; rfl
  have h1 := localMult_map (cone c t) (q.map Polynomial.C) (pr c t ⊥ ⊔ Ideal.span {linForm u}) (fun b => by
    suffices h : ∃ (n : ℕ) (a : MvPolynomial (Fin m) R), b * Polynomial.X ^ n = cone c t a by
      obtain ⟨n, a, h⟩ := h
      exact ⟨a, X k ^ n, by rw [map_pow, hXk]; exact fun h => hX (hp.mem_of_pow_mem _ h), by rw [map_pow, hXk, h]⟩
    induction b using Polynomial.induction_on' with
    | add b b' h h' =>
      obtain ⟨n, a, h⟩ := h
      obtain ⟨n', a', h'⟩ := h'
      exact ⟨n + n', a * X k ^ n' + a' * X k ^ n, by
        simp only [map_add, map_mul, map_pow, hXk, ← h, ← h']; ring⟩
    | monomial n a =>
      obtain ⟨N, G, h1, rfl⟩ := exists_homog' hs hk a
      exact ⟨N, G * X k ^ n, by
        rw [map_mul, map_pow, hXk, cone_of_homog c t h1, ← Polynomial.C_mul_X_pow_eq_monomial]; ring⟩)
    (hker ▸ le_sup_left)
  refine h1.symm.trans ?_
  rw [Ideal.map_sup, hker, (Ideal.map_eq_bot_iff_le_ker _).2 le_rfl, bot_sup_eq, Ideal.map_span,
    Set.image_singleton, cone_of_homog c t (isHomog_linForm u), pow_one]
  have : (q.map (Polynomial.C : A →+* Polynomial A)).LiesOver q := ⟨by
    ext a
    rw [Ideal.mem_comap, Polynomial.algebraMap_eq, Ideal.mem_map_C_iff]
    refine ⟨fun h n => ?_, fun h => by simpa using h 0⟩
    rw [Polynomial.coeff_C]
    split_ifs
    · exact h
    · exact q.zero_mem⟩
  have h2 := GroundTheory.Heights₂.Heights.localMult_map_of_flat (B := Polynomial A)
    (Ideal.span {eval₂Hom c t (linForm u)}) q (q.map Polynomial.C) Localization.AtPrime.map_eq_maximalIdeal
  rw [← h2, Ideal.map_span, Set.image_singleton, Polynomial.algebraMap_eq, localMult, localMult, dif_pos hp, dif_pos hp]
  refine congrArg (fun I : Ideal (Localization.AtPrime (q.map (Polynomial.C : A →+* Polynomial A))) =>
    (Module.length (Localization.AtPrime (q.map (Polynomial.C : A →+* Polynomial A))) (_ ⧸ I)).toNat) ?_
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_mul,
    Ideal.span_singleton_mul_left_unit (IsLocalization.map_units _ (⟨_, hX⟩ : (q.map Polynomial.C).primeCompl))]

end ChowFormHeightComparison₂.CF.A
