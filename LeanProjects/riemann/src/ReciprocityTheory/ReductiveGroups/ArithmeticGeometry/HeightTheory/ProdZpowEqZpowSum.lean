import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.BlockDegOfScale
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GoodPrimesProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.KTFiniteDimensional

theorem ReciprocityTheory.ChartRestriction.G.T0.prod_zpow_eq_zpow_sum_height {M : Type*} [CommGroupWithZero M] {α : Type*}
    (s : Finset α) (f : α → ℤ) (a : M) (ha : a ≠ 0) :
    ∏ i ∈ s, a ^ f i = a ^ (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ ha]

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

private theorem tauFG_sH_X (c : ι) (b : Fin (d.D + 1)) (u : Kˣ) (v : TVar d.D d.N) :
    tauFG (Ω := Ω c) b u (d.sH c (X v)) = d.sH c (sigP b u (X v)) := by
  have hKC : ∀ r : K, algebraMap K (OmS (Ω c) d.D d.N) r =
      algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (C (algebraMap K (Ω c) r)) := by
    intro r
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)]
    rfl
  have hTC : ∀ a : Ω c, tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u (C a) = C a :=
    fun a => (tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u).commutes a
  have hconst : ∀ r : K, tauFG (Ω := Ω c) (D := d.D) (N := d.N) b u
      (algebraMap K (OmS (Ω c) d.D d.N) r) = algebraMap K (OmS (Ω c) d.D d.N) r := by
    intro r
    rw [hKC]
    unfold tauFG
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    congr 1
    exact hTC _
  have hTin : ∀ w : SVar d.D d.N, IsBaseBlockVar b w →
      tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u (X w) = C (algebraMap K (Ω c) u) * X w := by
    intro w hw
    show (aeval (R := Ω c) (S₁ := MvPolynomial (SVar d.D d.N) (Ω c)) _) (X w) = _
    rw [aeval_X]
    try dsimp only
    rw [if_pos hw]
    rfl
  have hTout : ∀ w : SVar d.D d.N, ¬ IsBaseBlockVar b w →
      tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u (X w) = X w := by
    intro w hw
    show (aeval (R := Ω c) (S₁ := MvPolynomial (SVar d.D d.N) (Ω c)) _) (X w) = _
    rw [aeval_X]
    try dsimp only
    rw [if_neg hw]
  have hsX : ∀ w : TVar d.D d.N, d.sH c (X w) = sImg (d.jc c) (d.x c) w := fun w => by
    show aeval (sImg (d.jc c) (d.x c)) (X w) = _
    exact aeval_X _ _
  have hsC : d.sH c (C (u : K)) = algebraMap K _ (u : K) := (d.sH c).commutes _
  have hX : ∀ v : TVar d.D d.N, tauFG (Ω := Ω c) b u (d.sH c (X v)) = d.sH c (sigP b u (X v)) := by
    rintro ⟨i, j⟩
    by_cases hib : i = b
    · have hs : sigP (K := K) (N := d.N) b u (X (i, j)) = C (u : K) * X (i, j) := by
        show (aeval (R := K) (S₁ := KTp K d.D d.N) _) (X (i, j)) = _
        rw [aeval_X]
        try dsimp only
        rw [if_pos hib]
      rw [hs, map_mul, hsC, hsX, hKC]
      unfold sImg tauFG
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, ← map_mul]
      congr 1
      show tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u _ = _
      rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
      · rw [show ∀ (A : MvPolynomial (SVar d.D d.N) (Ω c)) (F : Fin d.N → MvPolynomial (SVar d.D d.N) (Ω c)),
            Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) A F (d.jc c) = A
            from fun A F => Fin.insertNth_apply_same _ _ _]
        split_ifs with hi0
        · exact hTin _ (hib.symm.trans hi0)
        · simp only [map_neg, map_sum, map_mul, hTC, fun k => hTin (Sum.inr (i, k)) hib, mul_neg,
            Finset.mul_sum, mul_assoc]
      · rw [show ∀ (A : MvPolynomial (SVar d.D d.N) (Ω c)) (F : Fin d.N → MvPolynomial (SVar d.D d.N) (Ω c)),
            Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) A F
              ((d.jc c).succAbove k) = F k
            from fun A F => Fin.insertNth_apply_succAbove _ _ _ _]
        exact hTin _ hib
    · have hs : sigP (K := K) (N := d.N) b u (X (i, j)) = X (i, j) := by
        show (aeval (R := K) (S₁ := KTp K d.D d.N) _) (X (i, j)) = _
        rw [aeval_X]
        try dsimp only
        rw [if_neg hib]
      rw [hs, hsX]
      unfold sImg tauFG
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
      congr 1
      show tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u _ = _
      rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
      · rw [show ∀ (A : MvPolynomial (SVar d.D d.N) (Ω c)) (F : Fin d.N → MvPolynomial (SVar d.D d.N) (Ω c)),
            Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) A F (d.jc c) = A
            from fun A F => Fin.insertNth_apply_same _ _ _]
        split_ifs with hi0
        · exact hTout _ (fun hb0 => hib (hi0.trans hb0.symm))
        · simp only [map_neg, map_sum, map_mul, hTC, fun k => hTout (Sum.inr (i, k)) hib]
      · rw [show ∀ (A : MvPolynomial (SVar d.D d.N) (Ω c)) (F : Fin d.N → MvPolynomial (SVar d.D d.N) (Ω c)),
            Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) A F
              ((d.jc c).succAbove k) = F k
            from fun A F => Fin.insertNth_apply_succAbove _ _ _ _]
        exact hTout _ hib
  exact hX v

theorem tauFG_KTtoS (h : d.S1) (c : ι) (b : Fin (d.D + 1)) (u : Kˣ) (z : KTf K d.D d.N) :
    tauFG (Ω := Ω c) b u (d.KTtoS h c z) = d.KTtoS h c (sigF b u z) := by
  have hsH : ∀ q : KTp K d.D d.N, d.KTtoS h c (algebraMap _ (KTf K d.D d.N) q) = d.sH c q := by
    intro q
    unfold KTtoS
    exact IsFractionRing.lift_algebraMap _ _
  have hKC : ∀ r : K, algebraMap K (OmS (Ω c) d.D d.N) r =
      algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (C (algebraMap K (Ω c) r)) := by
    intro r
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)]
    rfl
  have hTC : ∀ a : Ω c, tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u (C a) = C a :=
    fun a => (tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u).commutes a
  have hconst : ∀ r : K, tauFG (Ω := Ω c) (D := d.D) (N := d.N) b u
      (algebraMap K (OmS (Ω c) d.D d.N) r) = algebraMap K (OmS (Ω c) d.D d.N) r := by
    intro r
    rw [hKC]
    unfold tauFG
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    congr 1
    exact hTC _
  have hTin : ∀ w : SVar d.D d.N, IsBaseBlockVar b w →
      tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u (X w) = C (algebraMap K (Ω c) u) * X w := by
    intro w hw
    show (aeval (R := Ω c) (S₁ := MvPolynomial (SVar d.D d.N) (Ω c)) _) (X w) = _
    rw [aeval_X]
    try dsimp only
    rw [if_pos hw]
    rfl
  have hTout : ∀ w : SVar d.D d.N, ¬ IsBaseBlockVar b w →
      tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u (X w) = X w := by
    intro w hw
    show (aeval (R := Ω c) (S₁ := MvPolynomial (SVar d.D d.N) (Ω c)) _) (X w) = _
    rw [aeval_X]
    try dsimp only
    rw [if_neg hw]
  have hsX : ∀ w : TVar d.D d.N, d.sH c (X w) = sImg (d.jc c) (d.x c) w := fun w => by
    show aeval (sImg (d.jc c) (d.x c)) (X w) = _
    exact aeval_X _ _
  have hsC : d.sH c (C (u : K)) = algebraMap K _ (u : K) := (d.sH c).commutes _
  have hX : ∀ v : TVar d.D d.N, tauFG (Ω := Ω c) b u (d.sH c (X v)) = d.sH c (sigP b u (X v)) :=
    fun v => tauFG_sH_X d c b u v
  have hpoly : ∀ q : KTp K d.D d.N, tauFG (Ω := Ω c) b u (d.sH c q) = d.sH c (sigP b u q) := by
    intro q
    have e := MvPolynomial.ringHom_ext
      (f := (tauFG (Ω := Ω c) (D := d.D) (N := d.N) b u).toRingHom.comp (d.sH c).toRingHom)
      (g := (d.sH c).toRingHom.comp (sigP (K := K) (N := d.N) b u).toRingEquiv.toRingHom)
      (fun r => by
        show tauFG (Ω := Ω c) b u (d.sH c (C r)) = d.sH c (sigP b u (C r))
        rw [show sigP (K := K) (N := d.N) b u (C r) = C r from (sigP (K := K) (N := d.N) b u).commutes r,
          show d.sH c (C r) = algebraMap K _ r from (d.sH c).commutes r, hconst])
      (fun v => hX v)
    exact RingHom.congr_fun e q
  have hsig : ∀ g : KTp K d.D d.N, sigF (K := K) (D := d.D) (N := d.N) b u
      (algebraMap _ (KTf K d.D d.N) g) = algebraMap _ (KTf K d.D d.N) (sigP b u g) := fun g => by
    unfold sigF
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ g
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := KTp K d.D d.N) z
  simp only [map_div₀, hsH, hsig, hpoly]

theorem sigF_normG (h : d.S1) (c : ι) (b : Fin (d.D + 1)) (u : Kˣ) (z : OmS (Ω c) d.D d.N) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    sigF b u (Algebra.norm (KTf K d.D d.N) z) =
      Algebra.norm (KTf K d.D d.N) (tauFG (Ω := Ω c) b u z) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  have he : (algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)).comp
      (sigF (K := K) (D := d.D) (N := d.N) b u : KTf K d.D d.N →+* KTf K d.D d.N) =
      (tauFG (Ω := Ω c) (K := K) (D := d.D) (N := d.N) b u :
        OmS (Ω c) d.D d.N →+* OmS (Ω c) d.D d.N).comp
        (algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)) := by
    ext1 z
    exact (d.tauFG_KTtoS h c b u z).symm
  rw [Algebra.norm_eq_of_equiv_equiv (sigF (K := K) (D := d.D) (N := d.N) b u)
    (tauFG (Ω := Ω c) (K := K) (D := d.D) (N := d.N) b u) he z]
  exact RingEquiv.apply_symm_apply _ _

theorem sigF_algebraMap (b : Fin (d.D + 1)) (u : Kˣ) (g : KTp K d.D d.N) :
    sigF (K := K) (D := d.D) (N := d.N) b u (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) g) =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (sigP b u g) := by
  unfold sigF
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ g

theorem algebraMap_K_KTf (t : K) :
    algebraMap K (KTf K d.D d.N) t = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (C t) := by
  rw [IsScalarTower.algebraMap_apply K (KTp K d.D d.N) (KTf K d.D d.N), MvPolynomial.algebraMap_eq]

theorem KTtoS_algebraMap_K (h : d.S1) (c : ι) (t : K) :
    d.KTtoS h c (algebraMap K (KTf K d.D d.N) t) = algebraMap K (OmS (Ω c) d.D d.N) t := by
  rw [algebraMap_K_KTf d t]
  unfold KTtoS
  rw [IsFractionRing.lift_algebraMap]
  exact (d.sH c).commutes t

theorem tauFG_w0rat (c : ι) (b : Fin (d.D + 1)) (u : Kˣ) :
    tauFG (Ω := Ω c) b u (d.rationalBaseRow c) =
      algebraMap K (OmS (Ω c) d.D d.N) (if b = 0 then (u : K) else 1) * d.rationalBaseRow c := by
  have hΩ : ∀ a : Ω c, tauFG (Ω := Ω c) (D := d.D) (N := d.N) b u
      (algebraMap (Ω c) (OmS (Ω c) d.D d.N) a) = algebraMap (Ω c) (OmS (Ω c) d.D d.N) a := by
    intro a
    rw [IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)]
    unfold tauFG
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    congr 1
    exact (tauPG (Ω := Ω c) (D := d.D) (N := d.N) b u).commutes a
  have hsC : d.sH c (C (u : K)) = algebraMap K _ (u : K) := (d.sH c).commutes _
  unfold rationalBaseRow
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, tauFG_sH_X d c b u (0, j), hΩ]
  by_cases hb : b = 0
  · have hs : sigP (K := K) (N := d.N) b u (X (0, j)) = C (u : K) * X (0, j) := by
      show (aeval (R := K) (S₁ := KTp K d.D d.N) _) (X (0, j)) = _
      rw [aeval_X]
      try dsimp only
      rw [if_pos hb.symm]
    rw [hs, map_mul, hsC, if_pos hb]
    ring
  · have hs : sigP (K := K) (N := d.N) b u (X (0, j)) = X (0, j) := by
      show (aeval (R := K) (S₁ := KTp K d.D d.N) _) (X (0, j)) = _
      rw [aeval_X]
      try dsimp only
      rw [if_neg (fun h0 => hb h0.symm)]
    rw [hs, if_neg hb, map_one, one_mul]

theorem sigF_norm_w0rat (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (b : Fin (d.D + 1)) (u : Kˣ) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    sigF b u (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)) =
      algebraMap K (KTf K d.D d.N) ((if b = 0 then (u : K) else 1) ^ d.delc c) *
        Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  rw [d.sigF_normG h c b u, d.tauFG_w0rat c b u]
  have e : algebraMap K (OmS (Ω c) d.D d.N) (if b = 0 then (u : K) else 1) =
      algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
        (algebraMap K (KTf K d.D d.N) (if b = 0 then (u : K) else 1)) :=
    (d.KTtoS_algebraMap_K h c _).symm
  rw [e, map_mul, Algebra.norm_algebraMap, (d.omS_finite hd h c).2, map_pow]

noncomputable def cMM (h : d.S1) (c : ι) : KTf K d.D d.N :=
  ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p

noncomputable def aMM (h : d.S1) (c : ι) : ℤ :=
  ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
    d.nPMM h c (d.w (d.jc c) c) p * (d.dg (d.gen p) : ℤ)

theorem ordMM_base_nonneg (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) :
    0 ≤ d.ordMM c v (d.w (d.jc c) c) := by
  unfold ordMM
  exact sub_nonneg.mpr
    (ciInf_le (Set.finite_range _).bddBelow (⟨d.jc c, hd.w_base c⟩ : {j // d.w j c ≠ 0}))

theorem aMM_nonneg (hd : d.AxH 𝒜) (h : d.S1) (c : ι) : 0 ≤ d.aMM h c := by
  unfold aMM
  refine finsum_nonneg fun p => finsum_nonneg fun _ => mul_nonneg ?_ (Nat.cast_nonneg _)
  unfold nPMM
  exact finsum_nonneg fun w => finsum_nonneg fun _ =>
    mul_nonneg (Nat.cast_nonneg _) (ordMM_base_nonneg d hd c _)

theorem sigF_cMM (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (b : Fin (d.D + 1)) (u : Kˣ) :
    sigF b u (d.cMM h c) =
      algebraMap K (KTf K d.D d.N) ((u : K) ^ (if b = 0 then (0 : ℤ) else d.aMM h c)) * d.cMM h c := by
  classical
  have x2 := d.good_primes_properties hd h c
  have hfin := x2.2.2.2 _ (hd.w_mem (d.jc c) c) (hd.w_base c)
  set S := hfin.toFinset
  have hS : ∀ p ∈ S, p ∈ d.HtOne := fun p hp => ((Set.Finite.mem_toFinset _).1 hp).1
  have hsub : ∀ p, p ∈ d.HtOne → d.nPMM h c (d.w (d.jc c) c) p ≠ 0 → p ∈ S := fun p hp h1 =>
    (Set.Finite.mem_toFinset _).2 ⟨hp, h1⟩
  have eC : d.cMM h c = ∏ p ∈ S,
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p := by
    unfold cMM
    refine finprod_mem_eq_prod_of_subset _ ?_ (fun p hp => hS p hp)
    rintro p ⟨hp, hne⟩
    by_contra hpS
    have : d.nPMM h c (d.w (d.jc c) c) p = 0 := by
      by_contra h1; exact hpS (hsub p hp h1)
    exact hne (by simp [this])
  have eA : d.aMM h c = ∑ p ∈ S, d.nPMM h c (d.w (d.jc c) c) p * (d.dg (d.gen p) : ℤ) := by
    unfold aMM
    refine finsum_mem_eq_sum_of_subset _ ?_ (fun p hp => hS p hp)
    rintro p ⟨hp, hne⟩
    by_contra hpS
    have : d.nPMM h c (d.w (d.jc c) c) p = 0 := by
      by_contra h1; exact hpS (hsub p hp h1)
    exact hne (by simp [this])
  have hfac : ∀ p ∈ S, sigF b u (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
        d.nPMM h c (d.w (d.jc c) c) p) =
      algebraMap K (KTf K d.D d.N) ((u : K) ^ (if b = 0 then (0 : ℤ) else
        d.nPMM h c (d.w (d.jc c) c) p * (d.dg (d.gen p) : ℤ))) *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p := by
    intro p hp
    have hpH := hS p hp
    have hne : d.nPMM h c (d.w (d.jc c) c) p ≠ 0 := ((Set.Finite.mem_toFinset _).1 hp).2
    have hg : ∃ w, w ∈ d.GoodP c p := by
      by_contra hno
      push_neg at hno
      have hG : d.GoodP c p = ∅ := Set.eq_empty_iff_forall_notMem.mpr hno
      apply hne
      unfold nPMM
      rw [hG]
      simp
    have hm := x2.2.1 p hpH hg
    rw [map_zpow₀, d.sigF_algebraMap, sigP, scale_multiHomogeneous b u _ _ hm, map_mul, mul_zpow,
      ← d.algebraMap_K_KTf]
    congr 1
    by_cases hb : b = 0
    · simp [hb]
    · simp only [hb, if_false]
      rw [← map_zpow₀, ← zpow_natCast, ← zpow_mul, mul_comm]
  rw [eC, map_prod, Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, ← map_prod,
    prod_zpow_eq_zpow_sum_height _ _ _ (Units.ne_zero u)]
  congr 2
  by_cases hb : b = 0
  · simp [hb]
  · simp [hb, eA]

theorem sigF_fZ (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (b : Fin (d.D + 1)) (u : Kˣ) :
    sigF b u (d.fZ h c) = algebraMap K (KTf K d.D d.N)
      ((u : K) ^ (if b = 0 then (d.delc c : ℤ) else d.aMM h c)) * d.fZ h c := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  show sigF b u (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) * d.cMM h c) = _
  rw [map_mul, sigF_norm_w0rat d hd h c b u, sigF_cMM d hd h c b u]
  show _ = _ * (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) * d.cMM h c)
  split_ifs with hb
  · simp only [zpow_zero, map_one, mul_one, zpow_natCast]
    ring
  · simp only [one_pow, map_one, one_mul]
    ring

theorem sigP_F (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) (b : Fin (d.D + 1)) (u : Kˣ) :
    sigP b u F = C ((u : K) ^ (if b = 0 then (d.delc c : ℤ) else d.aMM h c)) * F := by
  apply IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  rw [← sigF_algebraMap d b u F, hF, sigF_fZ d hd h c b u, map_mul, ← hF, algebraMap_K_KTf d]

private theorem sigP_monomial {D N : ℕ} (b : Fin (D + 1)) (u : Kˣ) (s : TVar D N →₀ ℕ) (a : K) :
    sigP (K := K) (N := N) b u (monomial s a) = monomial s (a * (u : K) ^ (∑ j, s (b, j))) := by
  show aeval (fun v : TVar D N => if v.1 = b then C (u : K) * X v else X v) (monomial s a) = _
  have e1 : (s.prod fun v e => (if v.1 = b then C (u : K) * X v else X v) ^ e) =
      ∏ v, (if v.1 = b then C (u : K) * X v else X v) ^ s v :=
    Finsupp.prod_fintype _ _ (fun v => pow_zero _)
  have e2 : (s.prod fun v e => (X v : MvPolynomial (TVar D N) K) ^ e) = ∏ v, X v ^ s v :=
    Finsupp.prod_fintype _ _ (fun v => pow_zero _)
  have hfac : ∀ v : TVar D N, (if v.1 = b then C (u : K) * X v else X v) ^ s v =
      C (u : K) ^ (if v.1 = b then s v else 0) * X v ^ s v := by
    intro v
    split_ifs <;> simp [mul_pow]
  have hsum : ∑ v : TVar D N, (if v.1 = b then s v else 0) = ∑ j, s (b, j) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  rw [aeval_monomial, monomial_eq, e1, e2, Finset.prod_congr rfl (fun v _ => hfac v),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum, algebraMap_eq, C_mul, C_pow]
  ring

theorem F_degrees (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    (∀ s ∈ F.support, ∑ j, s (0, j) = d.delc c) ∧
      ∀ b : Fin (d.D + 1), b ≠ 0 → ∀ s ∈ F.support, ∑ j, s (b, j) = (d.aMM h c).toNat := by
  have hco : ∀ (b : Fin (d.D + 1)) (u : Kˣ) (s : TVar d.D d.N →₀ ℕ),
      coeff s F * (u : K) ^ (∑ j, s (b, j)) =
        (u : K) ^ (if b = 0 then (d.delc c : ℤ) else d.aMM h c) * coeff s F := by
    intro b u s
    have e := congrArg (coeff s) (sigP_F d hd h c F hF b u)
    rw [coeff_C_mul] at e
    rw [← e]
    conv_rhs => rw [F.as_sum]
    rw [map_sum, coeff_sum]
    simp only [sigP_monomial, coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hs
    · rfl
    · rw [mem_support_iff, not_not] at hs
      rw [hs, zero_mul]
  have hdeg : ∀ (b : Fin (d.D + 1)) (s : TVar d.D d.N →₀ ℕ), s ∈ F.support →
      (2 : K) ^ (∑ j, s (b, j)) = (2 : K) ^ (if b = 0 then (d.delc c : ℤ) else d.aMM h c) := by
    intro b s hs
    have h2 := hco b (Units.mk0 2 two_ne_zero) s
    simp only [Units.val_mk0] at h2
    rw [mul_comm] at h2
    exact mul_right_cancel₀ (mem_support_iff.mp hs) h2
  have inj : ∀ m n : ℕ, (2 : K) ^ m = (2 : K) ^ n → m = n := by
    intro m n hmn
    have h' : ((2 ^ m : ℕ) : K) = ((2 ^ n : ℕ) : K) := by
      push_cast
      exact hmn
    exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h')
  refine ⟨fun s hs => ?_, fun b hb s hs => ?_⟩
  · have h0 := hdeg 0 s hs
    rw [if_pos rfl, zpow_natCast] at h0
    exact inj _ _ h0
  · have h1 := hdeg b s hs
    rw [if_neg hb, ← Int.toNat_of_nonneg (aMM_nonneg d hd h c), zpow_natCast] at h1
    exact inj _ _ h1

end Data

end ReciprocityTheory.ChartRestriction.G.T0
