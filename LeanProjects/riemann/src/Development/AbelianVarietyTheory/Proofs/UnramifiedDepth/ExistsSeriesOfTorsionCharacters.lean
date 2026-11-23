import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitOfBijectiveMulNatural
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace CharGerm

section Series

variable {R₀ κ : Type} [CommRing R₀]

noncomputable abbrev truncI (R₀ κ : Type) [CommRing R₀] (p N : ℕ) : Ideal (MvPolynomial κ R₀) :=
  Ideal.span (insert ((p : MvPolynomial κ R₀) ^ N)
    (Set.range fun j : κ => (MvPolynomial.X j : MvPolynomial κ R₀) ^ N))

lemma coeff_mem_of_mem_truncI [DecidableEq κ] {p N : ℕ}
    {q : MvPolynomial κ R₀} (hq : q ∈ truncI R₀ κ p N) :
    ∀ m : κ →₀ ℕ, (∀ j, m j < N) → MvPolynomial.coeff m q ∈ Ideal.span {(p : R₀) ^ N} := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
  · rintro _ (rfl | ⟨j, rfl⟩) m hm
    · have : (p : MvPolynomial κ R₀) ^ N = MvPolynomial.C ((p : R₀) ^ N) := by simp
      rw [this, MvPolynomial.coeff_C]
      split_ifs
      · exact Ideal.mem_span_singleton_self _
      · exact zero_mem _
    · simp only [MvPolynomial.coeff_X_pow]
      rw [if_neg]
      · exact zero_mem _
      rintro rfl
      simpa using hm j
  · intro m _; simp
  · intro x y _ _ hx hy m hm
    rw [MvPolynomial.coeff_add]
    exact add_mem (hx m hm) (hy m hm)
  · intro r x _ hx m hm
    rw [smul_eq_mul, MvPolynomial.coeff_mul]
    refine Ideal.sum_mem _ fun e he => Ideal.mul_mem_left _ _ (hx e.2 ?_)
    intro j
    have : e.1 + e.2 = m := by simpa using he
    have h2 := hm j
    rw [← this, Finsupp.add_apply] at h2
    omega

lemma truncI_X (p N : ℕ) (j : κ) :
    (Ideal.Quotient.mk (truncI R₀ κ p N) (MvPolynomial.X j)) ^ N = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Or.inr ⟨j, rfl⟩)

lemma truncI_p (p N : ℕ) : (p : MvPolynomial κ R₀ ⧸ truncI R₀ κ p N) ^ N = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (truncI R₀ κ p N)), ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Or.inl rfl)

lemma aeval_eq_sum [Fintype κ] [DecidableEq κ]
    {S : Type} [CommRing S] [Algebra R₀ S] {N : ℕ} {a : κ → S} (ha : ∀ i, a i ^ N = 0)
    (q : MvPolynomial κ R₀) :
    MvPolynomial.aeval a q = ∑ e : κ → Fin N, algebraMap R₀ S (MvPolynomial.coeff
      (Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)) q) * ∏ i, a i ^ (e i : ℕ) := by
  induction q using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, MvPolynomial.coeff_add, add_mul, Finset.sum_add_distrib, hp, hq]
  | monomial m r =>
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    by_cases hm : ∀ j, m j < N
    · rw [Finset.sum_eq_single (fun j => (⟨m j, hm j⟩ : Fin N))]
      · rw [MvPolynomial.coeff_monomial, if_pos]
        ext j; simp
      · intro e _ he
        rw [MvPolynomial.coeff_monomial, if_neg, map_zero, zero_mul]
        intro h
        apply he
        funext j
        apply Fin.ext
        simp [h]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_zero]
      · push Not at hm
        obtain ⟨j, hj⟩ := hm
        rw [Finset.prod_eq_zero (f := fun i => a i ^ m i) (Finset.mem_univ j)
          (pow_eq_zero_of_le hj (ha j)), mul_zero]
      · intro e _
        rw [MvPolynomial.coeff_monomial, if_neg, map_zero, zero_mul]
        intro h
        apply hm
        intro j
        simp [h]

theorem exists_series [Fintype κ] [DecidableEq κ] (p : ℕ)
    [IsPrecomplete (Ideal.span {(p : R₀)}) R₀]
    (c : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (κ → S) → S)
    (hc : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
      (φ : S →ₐ[R₀] S') (a : κ → S), IsNilpotent (p : S) →
      (∀ i, IsNilpotent (a i)) → φ (c S a) = c S' (fun i => φ (a i))) :
    ∃ f : MvPowerSeries κ R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S) (N : ℕ),
      (p : S) ^ N = 0 → (∀ i, a i ^ N = 0) → c S a = tEval N f a := by
  choose P hP using fun N : ℕ => Ideal.Quotient.mk_surjective (I := truncI R₀ κ p N)
    (c (MvPolynomial κ R₀ ⧸ truncI R₀ κ p N)
      (fun j => Ideal.Quotient.mk (truncI R₀ κ p N) (MvPolynomial.X j)))
  have key : ∀ (N : ℕ) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (p : S) ^ N = 0 →
      (∀ i, a i ^ N = 0) → c S a = MvPolynomial.aeval a (P N) := by
    intro N S _ _ a hp ha
    let φ : (MvPolynomial κ R₀ ⧸ truncI R₀ κ p N) →ₐ[R₀] S :=
      Ideal.Quotient.liftₐ (truncI R₀ κ p N) (MvPolynomial.aeval a) (by
        intro x hx
        have : truncI R₀ κ p N ≤ RingHom.ker (MvPolynomial.aeval (R := R₀) a) := by
          refine Ideal.span_le.2 ?_
          rintro _ (rfl | ⟨j, rfl⟩)
          · simp [RingHom.mem_ker, hp]
          · simp [RingHom.mem_ker, ha j]
        exact this hx)
    have hφ : ∀ x, φ (Ideal.Quotient.mk (truncI R₀ κ p N) x) = MvPolynomial.aeval a x :=
      fun x => rfl
    have h := hc _ S φ (fun j => Ideal.Quotient.mk (truncI R₀ κ p N) (MvPolynomial.X j))
      ⟨N, truncI_p p N⟩ (fun j => ⟨N, truncI_X p N j⟩)
    rw [← hP N, hφ] at h
    simp only [hφ, MvPolynomial.aeval_X] at h
    exact h.symm
  have compat : ∀ N M : ℕ, N ≤ M → ∀ m : κ →₀ ℕ, (∀ j, m j < N) →
      MvPolynomial.coeff m (P N) - MvPolynomial.coeff m (P M) ∈ Ideal.span {(p : R₀) ^ N} := by
    intro N M h m hm
    have h1 := key M _ (fun j => Ideal.Quotient.mk (truncI R₀ κ p N) (MvPolynomial.X j))
      (pow_eq_zero_of_le h (truncI_p p N))
      (fun j => pow_eq_zero_of_le h (truncI_X p N j))
    have h2 : MvPolynomial.aeval (R := R₀)
        (fun j => Ideal.Quotient.mk (truncI R₀ κ p N) (MvPolynomial.X j))
        = Ideal.Quotient.mkₐ R₀ (truncI R₀ κ p N) := by
      ext j; simp
    rw [← hP N, h2, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at h1
    have h3 := coeff_mem_of_mem_truncI h1 m hm
    rwa [MvPolynomial.coeff_sub] at h3
  have hI : ∀ n : ℕ, (Ideal.span {(p : R₀)} ^ n • ⊤ : Submodule R₀ R₀) =
      Ideal.span {(p : R₀) ^ n} := fun n => by
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  have hle : ∀ {n n' : ℕ}, n ≤ n' → Ideal.span {(p : R₀) ^ n'} ≤ Ideal.span {(p : R₀) ^ n} :=
    fun h => Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h)
  have lim : ∀ m : κ →₀ ℕ, ∃ L : R₀, ∀ n,
      MvPolynomial.coeff m (P (n + (Finset.univ.sup m + 1))) - L ∈ Ideal.span {(p : R₀) ^ n} := by
    intro m
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {(p : R₀)}) (M := R₀) inferInstance
      (f := fun n => MvPolynomial.coeff m (P (n + (Finset.univ.sup m + 1)))) (by
        intro n n' h
        rw [hI, SModEq.sub_mem]
        refine hle (Nat.le_add_right _ _) (compat _ _ (by omega) m fun j => ?_)
        have := Finset.le_sup (f := m) (Finset.mem_univ j)
        omega)
    refine ⟨L, fun n => ?_⟩
    have := hL n
    rwa [hI, SModEq.sub_mem] at this
  choose L hL using lim
  refine ⟨L, ?_⟩
  intro S _ _ a N hp hN
  rw [key N S a hp hN, aeval_eq_sum hN]
  unfold tEval
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 1
  set m : κ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ) with hm
  change _ = algebraMap R₀ S (L m)
  have h1 := add_mem (compat N _ (Nat.le_add_right N (Finset.univ.sup m + 1)) m
    (fun j => by simp [hm])) (hL m N)
  rw [sub_add_sub_cancel] at h1
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h1
  rw [← sub_eq_zero, ← map_sub, ← hr, map_mul, map_pow, map_natCast, hp, mul_zero]

end Series

section Torsion

variable {R₀ : Type} [CommRing R₀] {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {g : ℕ}
  {x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)}
  (h0 : ∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1)
  (hnat : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (φ : S →ₐ[R₀] S') (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
      spMap φ ≫ x S a = x S' (fun i => φ (a i)))
  (hinj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
    (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b)
  (hsurj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (ρ : S →ₐ[R₀] S'), Function.Surjective ρ → (∀ a ∈ RingHom.ker ρ, IsNilpotent a) →
      ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)

include h0 hnat hsurj in

lemma exists_linear : ∃ d : Fin g → (Fin g ⊕ Fin g → R₀),
    ∀ (S : Type) [CommRing S] [Algebra R₀ S] (c : Fin g ⊕ Fin g → S), (∀ k l, c k * c l = 0) →
      x S (fun i => c (Sum.inl i)) * x S (fun i => c (Sum.inr i)) =
        x S (fun i => ∑ k, d i k • c k) := by
  let T := TrivSqZeroExt R₀ (Fin g ⊕ Fin g → R₀)
  let e : Fin g ⊕ Fin g → T := fun k => TrivSqZeroExt.inr (Pi.single k 1)
  have hnil : ∀ v : Fin g ⊕ Fin g → R₀, IsNilpotent (TrivSqZeroExt.inr v : T) := fun v =>
    ⟨2, by rw [pow_two, TrivSqZeroExt.inr_mul_inr]⟩
  have hker : ∀ a ∈ RingHom.ker (TrivSqZeroExt.fstHom R₀ R₀ (Fin g ⊕ Fin g → R₀)),
      a = TrivSqZeroExt.inr a.snd := fun a ha => by
    ext1
    · exact ha
    · rfl
  obtain ⟨d, hd, hx⟩ := hsurj T R₀ (TrivSqZeroExt.fstHom R₀ R₀ (Fin g ⊕ Fin g → R₀))
    (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩) (fun a ha => by rw [hker a ha]; exact hnil _)
    (x T (fun i => e (Sum.inl i)) * x T (fun i => e (Sum.inr i))) (by
      rw [MonObj.comp_mul, hnat _ _ _ _ (fun i => hnil _), hnat _ _ _ _ (fun i => hnil _)]
      exact (congrArg₂ (· * ·) (h0 R₀) (h0 R₀)).trans (_root_.mul_one _))
  refine ⟨fun i => (d i).snd, fun S _ _ c hc => ?_⟩
  let φ : T →ₐ[R₀] S := TrivSqZeroExt.liftEquivOfComm
    ⟨Fintype.linearCombination R₀ c, fun v w => by
      simp only [Fintype.linearCombination_apply, Finset.sum_mul_sum, smul_mul_smul_comm, hc,
        smul_zero, Finset.sum_const_zero]⟩
  have hφ : ∀ v, φ (TrivSqZeroExt.inr v) = ∑ k, v k • c k := fun v => by
    simp only [φ]
    rw [TrivSqZeroExt.liftEquivOfComm_apply, TrivSqZeroExt.lift_apply_inr,
      Fintype.linearCombination_apply]
  have hφe : ∀ k, φ (e k) = c k := fun k => by
    rw [hφ]
    simp [Pi.single_apply]
  have h := congrArg (spMap φ ≫ ·) hx
  simp only [MonObj.comp_mul] at h
  rw [hnat _ _ _ _ (fun i => hnil _), hnat _ _ _ _ (fun i => hnil _),
    hnat _ _ _ _ (fun i => by rw [hker _ (hd i)]; exact hnil _)] at h
  simp only [show ∀ k, φ (TrivSqZeroExt.inr (Pi.single k 1)) = c k from hφe] at h
  rw [h]
  congr 1
  funext i
  exact (congrArg φ (hker _ (hd i))).trans (hφ _)

include h0 hnat hinj hsurj in

lemma mul_eq_add {S : Type} [CommRing S] [Algebra R₀ S] {I : Ideal S} (hI : I ^ 2 = ⊥)
    {a b : Fin g → S} (ha : ∀ i, a i ∈ I) (hb : ∀ i, b i ∈ I) :
    x S a * x S b = x S (a + b) := by
  obtain ⟨d, hd⟩ := exists_linear h0 hnat hsurj
  have hmul : ∀ u ∈ I, ∀ v ∈ I, u * v = 0 := fun u hu v hv => by
    have := Ideal.mul_mem_mul hu hv
    rwa [← pow_two, hI, Ideal.mem_bot] at this
  have hnil : ∀ u ∈ I, IsNilpotent u := fun u hu => ⟨2, by rw [pow_two, hmul u hu u hu]⟩
  have key : ∀ u v : Fin g → S, (∀ i, u i ∈ I) → (∀ i, v i ∈ I) → x S u * x S v =
      x S (fun i => ∑ k, d i (Sum.inl k) • u k + ∑ k, d i (Sum.inr k) • v k) := by
    intro u v hu hv
    have hm : ∀ k, Sum.elim u v k ∈ I := by
      rintro (k | k)
      exacts [hu k, hv k]
    have := hd S (Sum.elim u v) (fun k l => hmul _ (hm k) _ (hm l))
    simpa only [Sum.elim_inl, Sum.elim_inr, Fintype.sum_sum_type] using this
  have hsum : ∀ (r : Fin g → R₀) (u : Fin g → S), (∀ i, u i ∈ I) → ∑ k, r k • u k ∈ I :=
    fun r u hu => Ideal.sum_mem _ fun k _ => Submodule.smul_of_tower_mem _ _ (hu k)
  have h1 := key a 0 ha (fun _ => zero_mem _)
  have h2 := key 0 b (fun _ => zero_mem _) hb
  simp only [h0, _root_.mul_one, _root_.one_mul, Pi.zero_apply, smul_zero, Finset.sum_const_zero,
    add_zero, zero_add] at h1 h2
  have h1' := hinj S _ _ (fun i => hnil _ (ha i)) (fun i => hnil _ (hsum _ _ ha)) h1
  have h2' := hinj S _ _ (fun i => hnil _ (hb i)) (fun i => hnil _ (hsum _ _ hb)) h2
  rw [key a b ha hb]
  congr 1
  funext i
  rw [Pi.add_apply, congrFun h1' i, congrFun h2' i]

include h0 hnat hinj hsurj in
lemma pow_eq_smul {S : Type} [CommRing S] [Algebra R₀ S] {I : Ideal S} (hI : I ^ 2 = ⊥)
    {a : Fin g → S} (ha : ∀ i, a i ∈ I) (n : ℕ) : x S a ^ n = x S (fun i => (n : S) * a i) := by
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact (h0 S).symm
  | succ n ih =>
    rw [pow_succ, ih, mul_eq_add h0 hnat hinj hsurj hI (fun i => Ideal.mul_mem_left _ _ (ha i)) ha]
    congr 1
    funext i
    simp [add_mul]

include h0 hnat hinj hsurj in

lemma exists_pow_eq_one (p : ℕ) {S : Type} [CommRing S] [Algebra R₀ S] (hp : IsNilpotent (p : S))
    {a : Fin g → S} (ha : ∀ i, IsNilpotent (a i)) : ∃ N : ℕ, x S a ^ (p ^ N) = 1 := by
  have hle : Ideal.span (Set.range a) ≤ nilradical S := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact ha i
  have hI : IsNilpotent (Ideal.span (Set.range a)) :=
    (Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.finite_range a))).2 hle
  refine Ideal.IsNilpotent.induction_on
    (P := fun S _ I => ∀ [Algebra R₀ S], IsNilpotent (p : S) → (∀ u ∈ I, IsNilpotent u) →
      ∀ a : Fin g → S, (∀ i, a i ∈ I) → ∃ N : ℕ, x S a ^ (p ^ N) = 1) _ hI ?_ ?_ hp hle a
      (fun i => Ideal.subset_span ⟨i, rfl⟩)
  · intro S _ I hI _ ⟨N, hN⟩ _ a ha
    refine ⟨N, ?_⟩
    rw [pow_eq_smul h0 hnat hinj hsurj hI ha, Nat.cast_pow, hN]
    simp only [zero_mul]
    exact h0 S
  · intro S _ I J hIJ h₁ h₂ _ hp hJ a ha
    obtain ⟨N, hN⟩ := h₂ (by simpa using hp.map (Ideal.Quotient.mk I)) (fun u hu => by
        obtain ⟨v, hv, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hu
        exact (hJ v hv).map _)
      (fun i => Ideal.Quotient.mk I (a i)) (fun i => Ideal.mem_map_of_mem _ (ha i))
    have hk : ∀ u ∈ RingHom.ker (Ideal.Quotient.mkₐ R₀ I), u ∈ I := fun u hu =>
      Ideal.Quotient.eq_zero_iff_mem.1 hu
    obtain ⟨c, hc, hx⟩ := hsurj S _ (Ideal.Quotient.mkₐ R₀ I) Ideal.Quotient.mk_surjective
      (fun u hu => hJ u (hIJ (hk u hu))) (x S a ^ (p ^ N)) (by
        rw [MonObj.comp_pow, hnat _ _ _ _ (fun i => hJ _ (ha i))]
        exact hN)
    obtain ⟨M, hM⟩ := h₁ hp (fun u hu => hJ u (hIJ hu)) c (fun i => hk _ (hc i))
    exact ⟨N + M, by rw [pow_add, pow_mul, hx, hM]⟩

end Torsion

section Value

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.KernelNoTorsion GlobalTheory.GmPoints

variable {R₀ : Type} [CommRing R₀] {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {p : ℕ}
  (χ : Tv G p)

lemma comp_χ_of_le {T : Over (Spec (CommRingCat.of R₀))} {m n : ℕ} (h : m ≤ n)
    (u : T ⟶ torsion G (p ^ m)) (v : T ⟶ torsion G (p ^ n))
    (huv : u ≫ torsion.ι G (p ^ m) = v ≫ torsion.ι G (p ^ n)) : u ≫ χ.χ m = v ≫ χ.χ n := by
  induction n, h using Nat.le_induction with
  | base => rw [torsion_hom_ext huv]
  | succ n hmn ih =>
    have h1 : (u ≫ torsion.ι G (p ^ m)) ^ (p ^ n) = 1 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [pow_add, pow_mul, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one, one_pow]
    rw [ih (torsionLift _ h1) (torsionLift_ι _ _).symm]
    exact χ.compat n _ _ _ (by rw [torsionLift_ι, huv])

lemma comp_χ_eq {T : Over (Spec (CommRingCat.of R₀))} {m n : ℕ}
    (u : T ⟶ torsion G (p ^ m)) (v : T ⟶ torsion G (p ^ n))
    (huv : u ≫ torsion.ι G (p ^ m) = v ≫ torsion.ι G (p ^ n)) : u ≫ χ.χ m = v ≫ χ.χ n := by
  rcases le_total m n with h | h
  · exact comp_χ_of_le χ h u v huv
  · exact (comp_χ_of_le χ h v u huv.symm).symm

open Classical in

noncomputable def val {S : Type} [CommRing S] [Algebra R₀ S] (z : sp (R₀ := R₀) S ⟶ G) : S :=
  if h : ∃ N : ℕ, z ^ (p ^ N) = 1 then
    (unitOf (O := R₀) (torsionLift z h.choose_spec ≫ χ.χ h.choose) : S) else 0

lemma unitOf_eq_val {S : Type} [CommRing S] [Algebra R₀ S] {z : sp (R₀ := R₀) S ⟶ G} {N : ℕ}
    (w : sp (R₀ := R₀) S ⟶ torsion G (p ^ N)) (hw : w ≫ torsion.ι G (p ^ N) = z) :
    (unitOf (O := R₀) (w ≫ χ.χ N) : S) = val χ z := by
  have h : ∃ N : ℕ, z ^ (p ^ N) = 1 :=
    ⟨N, by rw [← hw, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one]⟩
  rw [val, dif_pos h, comp_χ_eq χ w (torsionLift z h.choose_spec) (by rw [hw, torsionLift_ι])]

lemma map_val {S S' : Type} [CommRing S] [Algebra R₀ S] [CommRing S'] [Algebra R₀ S']
    (φ : S →ₐ[R₀] S') {z : sp (R₀ := R₀) S ⟶ G} (h : ∃ N : ℕ, z ^ (p ^ N) = 1) :
    φ (val χ z) = val χ (spMap φ ≫ z) := by
  obtain ⟨N, hN⟩ := h
  rw [← unitOf_eq_val χ (torsionLift z hN) (torsionLift_ι _ _),
    ← unitOf_eq_val χ (spMap φ ≫ torsionLift z hN) (by rw [Category.assoc, torsionLift_ι]),
    Category.assoc]
  exact (unitOf_ptMap φ _).symm

lemma val_one {S : Type} [CommRing S] [Algebra R₀ S] : val χ (1 : sp (R₀ := R₀) S ⟶ G) = 1 := by
  let z : sp (R₀ := R₀) S ⟶ torsion G (p ^ 0) := torsionLift 1 (one_pow _)
  have h1 : z ≫ torsion.ι G (p ^ 0) = 1 := torsionLift_ι _ _
  have h2 := χ.isChar 0 _ z z z (by rw [h1, _root_.mul_one])
  have h3 : unitOf (O := R₀) (z ≫ χ.χ 0) = 1 := by
    have := congrArg (unitOf (O := R₀)) h2
    rw [unitOf_mul] at this
    exact left_eq_mul.mp this
  rw [← unitOf_eq_val χ z h1, h3, Units.val_one]

end Value

end CharGerm

theorem exists_series_of_torsion_characters :
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (c : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (κ → S) → S),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : κ → S),
      (∀ i, IsNilpotent (a i)) → φ (c S a) = c S' (fun i => φ (a i))) →
    ∃ f : MvPowerSeries κ R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (∀ i, IsNilpotent (a i)) → c S a = nEval f a) →
  (∀ (p : ℕ) [Fact p.Prime] {R₀ : Type} [CommRing R₀] [IsAdicComplete (Ideal.span {(p : R₀)}) R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G]
    (g : ℕ) (x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)),
    ((∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : Fin g → S),
        (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i))) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
        (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)) →
    ∀ χ : ReciprocityTheory.ChartRestriction.G.Pdiv.Tv G p, ∃ s : MvPowerSeries (Fin g) R₀, MvPowerSeries.coeff 0 s = 1 ∧
      ∀ (S : Type) [CommRing S] [Algebra R₀ S], IsNilpotent (p : S) → ∀ a : Fin g → S, (∀ i, IsNilpotent (a i)) →
        (∃ N : ℕ, x S a ^ (p ^ N) = 1) ∧
        ∀ (N : ℕ) (w : sp (R₀ := R₀) S ⟶ ReciprocityTheory.ChartRestriction.G.Semi.torsion G (p ^ N)), w ≫ ReciprocityTheory.ChartRestriction.G.Semi.torsion.ι G (p ^ N) = x S a →
          (ReciprocityTheory.ChartRestriction.G.Pdiv.unitOf (O := R₀) (w ≫ χ.χ N) : S) = nEval s a) := by
  intro hE _ p _ R₀ _ _ G _ _ g x ⟨h0, hnat, hinj, hsurj⟩ χ
  obtain ⟨s, hs⟩ := CharGerm.exists_series (R₀ := R₀) (κ := Fin g) p
    (fun S _ _ a => CharGerm.val χ (x S a)) (fun S _ _ S' _ _ φ a hp ha => by
      rw [CharGerm.map_val χ φ (CharGerm.exists_pow_eq_one h0 hnat hinj hsurj p hp ha),
        hnat _ _ _ _ ha])
  have hs' : ∀ (S : Type) [CommRing S] [Algebra R₀ S], IsNilpotent (p : S) → ∀ a : Fin g → S,
      (∀ i, IsNilpotent (a i)) → CharGerm.val χ (x S a) = nEval s a := by
    intro S _ _ ⟨n, hn⟩ a ha
    choose k hk using ha
    have hN : ∀ i, a i ^ (n + Finset.univ.sup k) = 0 := fun i =>
      pow_eq_zero_of_le ((Finset.le_sup (f := k) (Finset.mem_univ i)).trans (Nat.le_add_left _ _))
        (hk i)
    rw [(hE s S a).1 _ hN]
    exact hs S a _ (pow_eq_zero_of_le (Nat.le_add_right _ _) hn) hN
  refine ⟨s, ?_, fun S _ _ hp a ha => ⟨CharGerm.exists_pow_eq_one h0 hnat hinj hsurj p hp ha,
    fun N w hw => (CharGerm.unitOf_eq_val χ w hw).trans (hs' S hp a ha)⟩⟩
  refine sub_eq_zero.mp (IsHausdorff.haus' (I := Ideal.span {(p : R₀)}) _ fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
  have hp : IsNilpotent (p : R₀ ⧸ Ideal.span {(p : R₀)} ^ n) := ⟨n, by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : R₀)} ^ n)), ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n⟩
  have h1 := hs' _ hp 0 (fun _ => IsNilpotent.zero)
  have h2 := ((hE s (R₀ ⧸ Ideal.span {(p : R₀)} ^ n) 0).2 (fun _ => IsNilpotent.zero)).2
  rw [h0, CharGerm.val_one] at h1
  have h3 : Ideal.span (Set.range (0 : Fin g → R₀ ⧸ Ideal.span {(p : R₀)} ^ n)) = ⊥ := by
    rw [Ideal.span_eq_bot]
    rintro _ ⟨i, rfl⟩
    rfl
  rw [h3, ← h1, Ideal.mem_bot, sub_eq_zero] at h2
  rw [map_one]
  exact h2.symm

end GlobalTheory
