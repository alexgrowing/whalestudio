import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam

section Mat

variable {O k : Type} [CommRing O] [CommRing k] {d : ℕ}

def actD (M : O →+* Matrix (Fin d) (Fin d) k) {n : ℕ} (b : Fin n → O) (c : Fin n → k) :
    Matrix (Fin d) (Fin d) k :=
  ∑ i, c i • M (b i)

def evD (χ : O →+* k) {n : ℕ} (b : Fin n → O) (c : Fin n → k) : k := ∑ i, c i * χ (b i)

def IsEqv (χ : O →+* k) {n : ℕ} (b : Fin n → O) (c : Fin n → k) : Prop :=
  ∀ a : O, ∃ m : Fin n → Fin n → ℤ, (∀ i, a * b i = ∑ j, m i j • b j) ∧
    ∀ j, ∑ i, (m i j : k) * c i = χ a * c j

private theorem smul_mulVec_lemma {S : Type} [CommRing S] {m : ℕ} (e : S)
    (A : Matrix (Fin m) (Fin m) S) (v : Fin m → S) : (e • A).mulVec v = e • A.mulVec v := by
  funext i
  show ∑ j, (e • A) i j * v j = e * ∑ j, A i j * v j
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show e * A i j * v j = e * (A i j * v j)
  ring

theorem actD_mulVec_eig (M : O →+* Matrix (Fin d) (Fin d) k) (χ : O →+* k) {n : ℕ} (b : Fin n → O) (c : Fin n → k)
    (v : Fin d → k) (hv : ∀ a, (M a).mulVec v = χ a • v) : (actD M b c).mulVec v = evD χ b c • v := by
  have key : ∀ s : Finset (Fin n),
      (∑ i ∈ s, c i • M (b i)).mulVec v = ∑ i ∈ s, (c i * χ (b i)) • v := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro j s hj ih
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Matrix.add_mulVec, ih,
        smul_mulVec_lemma, hv, smul_smul]
  unfold actD evD
  rw [key, Finset.sum_smul]

theorem eig_actD (M : O →+* Matrix (Fin d) (Fin d) k) (χ : O →+* k) {n : ℕ} (b : Fin n → O) (c : Fin n → k)
    (h : IsEqv χ b c) (a : O) : M a * actD M b c = χ a • actD M b c := by
  obtain ⟨m, hm1, hm2⟩ := h a
  unfold actD
  rw [Finset.mul_sum, Finset.smul_sum]
  calc ∑ i, M a * (c i • M (b i)) = ∑ i, c i • M (a * b i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, Matrix.mul_smul]
    _ = ∑ i, c i • ∑ j, ((m i j : ℤ) : k) • M (b j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hm1 i, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_zsmul, Int.cast_smul_eq_zsmul]
    _ = ∑ j, (∑ i, ((m i j : ℤ) : k) * c i) • M (b j) := by
        simp_rw [Finset.smul_sum, Finset.sum_smul, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm]
    _ = ∑ j, χ a • (c j • M (b j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hm2 j, smul_smul]

theorem evD_eqv (χ χ' : O →+* k) {n : ℕ} (b : Fin n → O) (c : Fin n → k) (h : IsEqv χ b c) (a : O) :
    χ' a * evD χ' b c = χ a * evD χ' b c := by
  obtain ⟨m, hm1, hm2⟩ := h a
  unfold evD
  rw [Finset.mul_sum, Finset.mul_sum]
  calc ∑ i, χ' a * (c i * χ' (b i)) = ∑ i, c i * χ' (a * b i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        ring
    _ = ∑ i, c i * ∑ j, ((m i j : ℤ) : k) * χ' (b j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hm1 i, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_zsmul, zsmul_eq_mul]
    _ = ∑ j, (∑ i, ((m i j : ℤ) : k) * c i) * χ' (b j) := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ∑ j, χ a * (c j * χ' (b j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hm2 j]
        ring

theorem evD_orth {K : Type} [Field K] (χ χ' : O →+* K) {n : ℕ} (b : Fin n → O) (c : Fin n → K)
    (h : IsEqv χ b c) (a : O) (ha : χ' a ≠ χ a) : evD χ' b c = 0 := by
  have h1 := evD_eqv χ χ' b c h a
  have h2 : (χ' a - χ a) * evD χ' b c = 0 := by
    rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr ha)

theorem M_comm (M : O →+* Matrix (Fin d) (Fin d) k) (a b : O) : M a * M b = M b * M a := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem actD_mul_eig (M : O →+* Matrix (Fin d) (Fin d) k) (χ : O →+* k) {n n' : ℕ} (b : Fin n → O) (c : Fin n → k)
    (h : IsEqv χ b c) (b' : Fin n' → O) (c' : Fin n' → k) :
    actD M b c * actD M b' c' = evD χ b' c' • actD M b c := by
  have hc : ∀ x, actD M b c * M x = M x * actD M b c := by
    intro x
    unfold actD
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, M_comm]
  show actD M b c * ∑ j, c' j • M (b' j) = _
  rw [Finset.mul_sum, evD, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_smul, hc, eig_actD M χ b c h, smul_smul]

end Mat

section Pair

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [Field k] [Algebra ℚ k] [Algebra R k]

def actP (B : FB R d O) {n : ℕ} (b : Fin n → O) (c : Fin n → k) (ξ : (Fin d → k) × (Fin d → k)) :
    (Fin d → k) × (Fin d → k) :=
  ((actD (EigA.dActH k B) b c).mulVec ξ.1, (actD (EigA.dActS k B) b c).mulVec ξ.2)

theorem actP_eig (B : FB R d O) (χ : O →+* k) {n : ℕ} (b : Fin n → O) (c : Fin n → k) (h : IsEqv χ b c)
    (ξ : (Fin d → k) × (Fin d → k)) (a : O) : OactH k B a (actP B b c ξ) = χ a • actP B b c ξ := by
  have e1 := eig_actD (EigA.dActH k B) χ b c h a
  have e2 := eig_actD (EigA.dActS k B) χ b c h a
  show ((EigA.dActH k B a).mulVec ((actD (EigA.dActH k B) b c).mulVec ξ.1),
      (EigA.dActS k B a).mulVec ((actD (EigA.dActS k B) b c).mulVec ξ.2)) = _
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e1, e2, smul_mulVec_lemma,
    smul_mulVec_lemma]
  rfl

theorem actP_actP_eig (B : FB R d O) (χ : O →+* k) {n n' : ℕ} (b : Fin n → O) (c : Fin n → k) (h : IsEqv χ b c)
    (b' : Fin n' → O) (c' : Fin n' → k) (ξ : (Fin d → k) × (Fin d → k)) :
    actP B b c (actP B b' c' ξ) = evD χ b' c' • actP B b c ξ := by
  show ((actD (EigA.dActH k B) b c).mulVec ((actD (EigA.dActH k B) b' c').mulVec ξ.1),
      (actD (EigA.dActS k B) b c).mulVec ((actD (EigA.dActS k B) b' c').mulVec ξ.2)) = _
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, actD_mul_eig (EigA.dActH k B) χ b c h b' c',
    actD_mul_eig (EigA.dActS k B) χ b c h b' c', smul_mulVec_lemma,
    smul_mulVec_lemma]
  rfl

theorem betaH_sum_left {ι : Type} (s : Finset ι) (f : ι → (Fin d → k) × (Fin d → k)) (η : (Fin d → k) × (Fin d → k)) :
    betaH k (∑ i ∈ s, f i) η = ∑ i ∈ s, betaH k (f i) η := by
  simp only [betaH, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Finset.mul_sum,
    Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_comm

theorem betaH_sum_right {ι : Type} (s : Finset ι) (ξ : (Fin d → k) × (Fin d → k)) (f : ι → (Fin d → k) × (Fin d → k)) :
    betaH k ξ (∑ i ∈ s, f i) = ∑ i ∈ s, betaH k ξ (f i) := by
  simp only [betaH, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Finset.mul_sum,
    Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_comm

theorem beta_vanish (B : FB R d O) {Ty : Type} [Fintype Ty] (χ : Ty → O →+* k) (nt : Ty → ℕ)
    (bt : ∀ t, Fin (nt t) → O) (ct : ∀ t, Fin (nt t) → k) (heq : ∀ t, IsEqv (χ t) (bt t) (ct t))
    (hcompH : ∑ t, actD (EigA.dActH k B) (bt t) (ct t) = 1) (hcompS : ∑ t, actD (EigA.dActS k B) (bt t) (ct t) = 1)
    {n n' : ℕ} (bz : Fin n → O) (cz : Fin n → k) (bw : Fin n' → O) (cw : Fin n' → k) (ξ0 η0 : (Fin d → k) × (Fin d → k))
    (hsep : ∀ t t', evD (χ t) bz cz ≠ 0 → evD (χ t') bw cw ≠ 0 → ∃ a, χ t a ≠ χ t' (star a)) :
    betaH k (actP B bz cz ξ0) (actP B bw cw η0) = 0 := by
  classical
  have hsmulL : ∀ (e : k) (x y : (Fin d → k) × (Fin d → k)),
      betaH k (e • x) y = e * betaH k x y := by
    intro e x y
    simp only [betaH, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hsmulR : ∀ (e : k) (x y : (Fin d → k) × (Fin d → k)),
      betaH k x (e • y) = e * betaH k x y := by
    intro e x y
    simp only [betaH, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hmv : ∀ (A : Matrix (Fin d) (Fin d) k) (v : Fin d → k) (i : Fin d),
      A.mulVec v i = ∑ j, A i j * v j := fun A v i => rfl
  have hadj : ∀ (a : O) (x y : (Fin d → k) × (Fin d → k)),
      betaH k (OactH k B a x) y = betaH k x (OactH k B (star a) y) := by
    intro a x y
    simp only [betaH, OactH, star_star, hmv, Matrix.transpose_apply, Finset.mul_sum,
      Finset.sum_mul, ← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have horth : ∀ (t t' : Ty) (x y : (Fin d → k) × (Fin d → k)), (∃ a, χ t a ≠ χ t' (star a)) →
      betaH k (actP B (bt t) (ct t) x) (actP B (bt t') (ct t') y) = 0 := by
    intro t t' x y ⟨a, ha⟩
    have h1 : betaH k (OactH k B a (actP B (bt t) (ct t) x)) (actP B (bt t') (ct t') y) =
        χ t a * betaH k (actP B (bt t) (ct t) x) (actP B (bt t') (ct t') y) := by
      rw [actP_eig B (χ t) (bt t) (ct t) (heq t) x a, hsmulL]
    have h2 : betaH k (actP B (bt t) (ct t) x) (OactH k B (star a) (actP B (bt t') (ct t') y)) =
        χ t' (star a) * betaH k (actP B (bt t) (ct t) x) (actP B (bt t') (ct t') y) := by
      rw [actP_eig B (χ t') (bt t') (ct t') (heq t') y (star a), hsmulR]
    rw [hadj] at h1
    rw [h1] at h2
    have h3 : (χ t a - χ t' (star a)) *
        betaH k (actP B (bt t) (ct t) x) (actP B (bt t') (ct t') y) = 0 := by
      rw [sub_mul, h2, sub_self]
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr ha)
  have hs : ∀ (s : Finset Ty) (N : Ty → Matrix (Fin d) (Fin d) k) (v : Fin d → k),
      (∑ t ∈ s, N t).mulVec v = ∑ t ∈ s, (N t).mulVec v := by
    intro s N v
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro j s hj ih
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Matrix.add_mulVec, ih]
  have hdec : ∀ x : (Fin d → k) × (Fin d → k), x = ∑ t, actP B (bt t) (ct t) x := by
    intro x
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      exact calc x.1 = (1 : Matrix (Fin d) (Fin d) k).mulVec x.1 := (Matrix.one_mulVec _).symm
        _ = (∑ t, actD (EigA.dActH k B) (bt t) (ct t)).mulVec x.1 := by rw [hcompH]
        _ = ∑ t, (actD (EigA.dActH k B) (bt t) (ct t)).mulVec x.1 := hs _ _ _
    · rw [Prod.snd_sum]
      exact calc x.2 = (1 : Matrix (Fin d) (Fin d) k).mulVec x.2 := (Matrix.one_mulVec _).symm
        _ = (∑ t, actD (EigA.dActS k B) (bt t) (ct t)).mulVec x.2 := by rw [hcompS]
        _ = ∑ t, (actD (EigA.dActS k B) (bt t) (ct t)).mulVec x.2 := hs _ _ _
  rw [hdec (actP B bz cz ξ0), hdec (actP B bw cw η0), betaH_sum_left]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [betaH_sum_right]
  refine Finset.sum_eq_zero fun t' _ => ?_
  rw [actP_actP_eig B (χ t) (bt t) (ct t) (heq t) bz cz ξ0,
    actP_actP_eig B (χ t') (bt t') (ct t') (heq t') bw cw η0, hsmulL, hsmulR]
  by_cases hz : evD (χ t) bz cz = 0
  · rw [hz, zero_mul]
  by_cases hw : evD (χ t') bw cw = 0
  · rw [hw, zero_mul, mul_zero]
  rw [horth t t' ξ0 η0 (hsep t t' hz hw), mul_zero, mul_zero]

end Pair

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
