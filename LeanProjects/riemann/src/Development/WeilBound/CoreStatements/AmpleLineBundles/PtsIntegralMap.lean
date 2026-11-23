import Development.WeilBound.CoreStatements.AmpleLineBundles.HeightRecRFull

noncomputable section

namespace CoverDenseAlt.Rename₂

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights

variable {K : Type} [Fintype K] {ι ι' : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  (e : ∀ k, ι k ≃ ι' k)

def ren : MRing ι ≃+* MRing ι' := (renameEquiv ℤ (Equiv.sigmaCongrRight e)).toRingEquiv

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem ren_apply (f : MRing ι) : ren e f = rename (Equiv.sigmaCongrRight e) f := rfl

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem ren_X (k : K) (i : ι k) : ren e (X ⟨k, i⟩) = X ⟨k, e k i⟩ := by
  rw [ren_apply, rename_X]
  rfl

omit [Fintype K] in
theorem homog_ren {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) : IsMultiHomog (ren e g) a := by
  classical
  intro m hm k
  rw [ren_apply, support_rename_of_injective (Equiv.sigmaCongrRight e).injective, Finset.mem_image] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  have h1 : ∀ i : ι' k, Finsupp.mapDomain (Equiv.sigmaCongrRight e) m0 ⟨k, i⟩ = m0 ⟨k, (e k).symm i⟩ := by
    intro i
    have : (⟨k, i⟩ : Σ k, ι' k) = Equiv.sigmaCongrRight e ⟨k, (e k).symm i⟩ := by simp
    rw [this, Finsupp.mapDomain_apply (Equiv.sigmaCongrRight e).injective]
  simp only [h1]
  rw [Equiv.sum_comp (e k).symm (fun j => m0 ⟨k, j⟩)]
  exact hg m0 hm0 k

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem relevant_iff (V : Ideal (MRing ι)) : IsRelevant (V.map (ren e)) ↔ IsRelevant V := by
  refine forall_congr' fun k => ⟨?_, ?_⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := (e k).surjective i
    exact ⟨j, by rwa [← ren_X, mem_map_ringEquiv_iff] at hi⟩
  · rintro ⟨j, hj⟩
    exact ⟨e k j, by rwa [← ren_X, mem_map_ringEquiv_iff]⟩

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem comap_C (V : Ideal (MRing ι)) :
    (V.map (ren e)).comap (C : ℤ →+* MRing ι') = V.comap (C : ℤ →+* MRing ι) := by
  ext n
  rw [Ideal.mem_comap, Ideal.mem_comap, ← mem_map_ringEquiv_iff (ren e) V, ren_apply, rename_C]

omit [Fintype K] in
theorem homogIdeal_map {V : Ideal (MRing ι)} (h : IsMultiHomogIdeal V) : IsMultiHomogIdeal (V.map (ren e)) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine ⟨ren e '' S, ?_, Ideal.map_span _ _⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, homog_ren e ha⟩

theorem arithVar_map {V : Ideal (MRing ι)} {d : ℕ} (h : IsArithVar V d) : IsArithVar (V.map (ren e)) d := by
  obtain ⟨hne, ⟨hp, hh, hr⟩, hhor, hdim⟩ := h
  refine ⟨hne, ⟨(isPrime_map_ringEquiv_iff _ V).2 hp, homogIdeal_map e hh, (relevant_iff e V).2 hr⟩, ?_, ?_⟩
  · unfold IsHorizontal
    rw [comap_C]
    exact hhor
  · rw [ringKrullDim_quotient_map, hdim]

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem sup_map (V : Ideal (MRing ι)) (s : MRing ι) :
    V.map (ren e) ⊔ Ideal.span {ren e s} = (V ⊔ Ideal.span {s}).map (ren e) := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem divSupp_map (V : Ideal (MRing ι)) (s : MRing ι) :
    divSupp (V.map (ren e)) (ren e s) = Ideal.map (ren e) '' divSupp V s := by
  ext W'
  simp only [divSupp, Set.mem_setOf_eq, Set.mem_image, sup_map, minimalPrimes_map_ringEquiv]
  constructor
  · rintro ⟨⟨W, hW, rfl⟩, hrel⟩
    exact ⟨W, ⟨hW, (relevant_iff e W).1 hrel⟩, rfl⟩
  · rintro ⟨W, ⟨hW, hrel⟩, rfl⟩
    exact ⟨⟨W, hW, rfl⟩, (relevant_iff e W).2 hrel⟩

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem multAt_map (J V : Ideal (MRing ι)) : multAt (J.map (ren e)) (V.map (ren e)) = multAt J V := by
  unfold multAt
  by_cases hV : V.IsPrime
  · have hV' : (V.map (ren e)).IsPrime := (isPrime_map_ringEquiv_iff (ren e) V).2 hV
    rw [dif_pos hV, dif_pos hV']
    exact congrArg ENat.toNat (length_localizedModule_quotient_map (ren e) J V)
  · have hV' : ¬ (V.map (ren e)).IsPrime := fun h' => hV ((isPrime_map_ringEquiv_iff (ren e) V).1 h')
    rw [dif_neg hV, dif_neg hV']

def chartId (V : Ideal (MRing ι)) (c : ∀ k, ι k) : Ideal (MRing ι) :=
  V ⊔ Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing ι) - 1)

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem chartId_map (V : Ideal (MRing ι)) (c : ∀ k, ι k) :
    (chartId V c).map (ren e) = chartId (V.map (ren e)) fun k => e k (c k) := by
  unfold chartId
  rw [Ideal.map_sup, Ideal.map_span, ← Set.range_comp]
  congr 3
  funext k
  simp [ren_X]

theorem geoNum_map (V : Ideal (MRing ι)) (hV : IsRelevant V) (a b : Fin 0 → K → ℤ)
    (hc : ∀ c c' : ∀ k, ι' k, (∀ k, (X ⟨k, c k⟩ : MRing ι') ∉ V.map (ren e)) →
      (∀ k, (X ⟨k, c' k⟩ : MRing ι') ∉ V.map (ren e)) →
      Nonempty ((MRing ι' ⧸ chartId (V.map (ren e)) c) ≃+* (MRing ι' ⧸ chartId (V.map (ren e)) c'))) :
    geoNum 0 (V.map (ren e)) a = geoNum 0 V b := by
  have hV' := (relevant_iff e V).2 hV
  have h1 : geoNum 0 V b = ((Module.length ℤ (MRing ι ⧸ chartId V fun k => (hV k).choose)).toNat : ℤ) := by
    simp only [geoNum]
    rw [dif_pos hV]
    rfl
  have h2 : geoNum 0 (V.map (ren e)) a =
      ((Module.length ℤ (MRing ι' ⧸ chartId (V.map (ren e)) fun k => (hV' k).choose)).toNat : ℤ) := by
    simp only [geoNum]
    rw [dif_pos hV']
    rfl
  obtain ⟨φ⟩ := hc (fun k => (hV' k).choose) (fun k => e k (hV k).choose) (fun k => (hV' k).choose_spec)
    (fun k => by
      rw [← ren_X, mem_map_ringEquiv_iff]
      exact (hV k).choose_spec)
  rw [h1, h2, φ.toAddEquiv.toIntLinearEquiv.length_eq, ← chartId_map, length_int_quotient_map]

def pull {F : Type} (z : (Σ k, ι' k) → F) : (Σ k, ι k) → F := fun p => z ⟨p.1, e p.1 p.2⟩

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem eval_ren (z : (Σ k, ι' k) → ℂ) (f : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (ren e f)) = eval (pull e z) (map (Int.castRingHom ℂ) f) := by
  rw [ren_apply, map_rename, eval_rename]
  rfl

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem nz_pull {F : Type} [Zero F] (z : (Σ k, ι' k) → F) :
    (∀ k, ∃ i, pull e z ⟨k, i⟩ ≠ 0) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  refine forall_congr' fun k => ⟨?_, ?_⟩
  · rintro ⟨i, hi⟩
    exact ⟨e k i, hi⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := (e k).surjective i
    exact ⟨j, hi⟩

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem mem_mcPts (V : Ideal (MRing ι)) (z : (Σ k, ι' k) → ℂ) :
    z ∈ mcPts (V.map (ren e)) ↔ pull e z ∈ mcPts V := by
  refine and_congr (nz_pull e z).symm ⟨fun h f hf => ?_, fun h f hf => ?_⟩
  · rw [← eval_ren]
    exact h _ ((mem_map_ringEquiv_iff _ V f).2 hf)
  · obtain ⟨g, rfl⟩ := (ren e).surjective f
    rw [eval_ren]
    exact h _ ((mem_map_ringEquiv_iff _ V g).1 hf)

def ptsEquiv (V : Ideal (MRing ι)) : mcPts (V.map (ren e)) ≃ mcPts V where
  toFun z := ⟨pull e z.1, (mem_mcPts e V z.1).1 z.2⟩
  invFun z := ⟨fun p => z.1 ⟨p.1, (e p.1).symm p.2⟩, (mem_mcPts e V _).2 (by
    have : pull e (fun p : Σ k, ι' k => z.1 ⟨p.1, (e p.1).symm p.2⟩) = z.1 := by
      funext p
      simp [pull]
    rw [this]
    exact z.2)⟩
  left_inv z := by
    apply Subtype.ext
    funext p
    simp [pull]
  right_inv z := by
    apply Subtype.ext
    funext p
    simp [pull]

def projEquiv (V : Ideal (MRing ι)) : projPts (V.map (ren e)) ≃ projPts V :=
  Quot.congr (ptsEquiv e V) fun z z' => by
    refine exists_congr fun c => and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
    · funext p
      exact congrFun h ⟨p.1, e p.1 p.2⟩
    · funext ⟨k, i⟩
      obtain ⟨j, rfl⟩ := (e k).surjective i
      exact congrFun h ⟨k, j⟩

theorem degC_map (V : Ideal (MRing ι)) : degC (V.map (ren e)) = degC V :=
  Nat.card_congr (projEquiv e V)

theorem out_eq (V : Ideal (MRing ι)) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (hg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → z ∈ mcPts V → g (fun p => c p.1 * z p) = g z)
    (z : mcPts V) : g (Quot.out (Quot.mk _ z : projPts V) : mcPts V) = g z := by
  let G : projPts V → ℝ := Quot.lift (fun z : mcPts V => g z) (by
    rintro z z' ⟨c, hc, h⟩
    rw [h, hg c z hc z.2])
  have h1 : ∀ w : mcPts V, g w = G (Quot.mk _ w) := fun _ => rfl
  rw [h1, h1, Quot.out_eq]

theorem ptsIntegral_map [Nonempty K] (V : Ideal (MRing ι)) (hV : IsMultiHomogIdeal V)
    (hfin : Finite (projPts V)) (g : ((Σ k, ι k) → ℂ) → ℝ) (g' : ((Σ k, ι' k) → ℂ) → ℝ)
    (hg : ∀ (c : K → ℂ) (z : (Σ k, ι' k) → ℂ), (∀ k, c k ≠ 0) → z ∈ mcPts (V.map (ren e)) →
      g' (fun p => c p.1 * z p) = g' z)
    (hgg : ∀ z ∈ mcPts (V.map (ren e)), g' z = g (pull e z)) :
    ptsIntegral (V.map (ren e)) (Fin.elim0 : Fin 0 → ((Σ k, ι' k) → ℂ) → ℝ) g' =
      ptsIntegral V (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) g := by
  have hg0 : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → z ∈ mcPts V →
      g (fun p => c p.1 * z p) = g z := by
    intro c z hc hz
    obtain ⟨z', hz'⟩ := (ptsEquiv e V).surjective ⟨z, hz⟩
    have hz'' : pull e z'.1 = z := congrArg Subtype.val hz'
    have hmem : (fun p : Σ k, ι' k => c p.1 * z'.1 p) ∈ mcPts (V.map (ren e)) := by
      obtain ⟨S, hS, hVS⟩ := homogIdeal_map e hV
      refine ⟨fun k => ?_, fun f hf => ?_⟩
      · obtain ⟨i, hi⟩ := z'.2.1 k
        exact ⟨i, mul_ne_zero (hc k) hi⟩
      · have hle : Ideal.span S ≤ RingHom.ker ((eval fun p : Σ k, ι' k => c p.1 * z'.1 p).comp
            (map (Int.castRingHom ℂ))) := by
          refine Ideal.span_le.2 fun t ht => ?_
          obtain ⟨a, ha⟩ := hS t ht
          have h0 := z'.2.2 t (hVS ▸ Ideal.subset_span ht)
          change eval _ (map _ t) = 0
          rw [eval_map, eval₂_eq'] at h0 ⊢
          have : ∀ m ∈ t.support, (Int.castRingHom ℂ) (coeff m t) * ∏ p : Σ k, ι' k, (c p.1 * z'.1 p) ^ m p =
              (∏ k, c k ^ a k) * ((Int.castRingHom ℂ) (coeff m t) * ∏ p, z'.1 p ^ m p) := by
            intro m hm
            have h1 : ∏ p : Σ k, ι' k, c p.1 ^ m p = ∏ k, c k ^ a k := by
              rw [Fintype.prod_sigma]
              refine Finset.prod_congr rfl fun k _ => ?_
              show ∏ i, c k ^ m ⟨k, i⟩ = _
              rw [Finset.prod_pow_eq_pow_sum, ha m hm k]
            simp only [mul_pow, Finset.prod_mul_distrib, h1]
            ring
          rw [Finset.sum_congr rfl this, ← Finset.mul_sum, h0, mul_zero]
        exact hle (hVS ▸ hf)
    rw [← hz'', ← hgg _ z'.2, ← hg c _ hc z'.2, hgg _ hmem]
    rfl
  haveI := hfin
  rw [PtsIntegralPoints.homogProof K ι V g hV hfin hg0,
    PtsIntegralPoints.homogProof K ι' _ g' (homogIdeal_map e hV) (Finite.of_equiv _ (projEquiv e V).symm) hg,
    ← finsum_comp_equiv (projEquiv e V)]
  refine finsum_congr fun q => ?_
  induction q using Quot.ind with
  | mk z =>
    rw [out_eq _ g' hg z, hgg _ z.2]
    exact (out_eq V g hg0 (ptsEquiv e V z)).symm

theorem recR_map [Nonempty K] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (I' : Ideal (MRing ι') → (n : ℕ) → (Fin n → HermLine ι') → ℝ)
    (W : Ideal (MRing ι)) (hW : IsMultiHomogIdeal W) (hfin : Finite (projPts W))
    (A : HermLine ι) (A' : HermLine ι') (s : MRing ι)
    (hinv : ∀ (c : K → ℂ) (z : (Σ k, ι' k) → ℂ), (∀ k, c k ≠ 0) → z ∈ mcPts (W.map (ren e)) →
      logNorm A' (ren e s) (fun p => c p.1 * z p) = logNorm A' (ren e s) z)
    (hA : ∀ z, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A'.h z = A.h (pull e z))
    (hvert : ∀ V ∈ divSupp (W.map (ren e)) (ren e s), ¬ IsHorizontal V)
    (hc : ∀ V ∈ divSupp (W.map (ren e)) (ren e s), ∀ c c' : ∀ k, ι' k, (∀ k, (X ⟨k, c k⟩ : MRing ι') ∉ V) →
      (∀ k, (X ⟨k, c' k⟩ : MRing ι') ∉ V) → Nonempty ((MRing ι' ⧸ chartId V c) ≃+* (MRing ι' ⧸ chartId V c'))) :
    recR I' (W.map (ren e)) (Fin.elim0 : Fin 0 → HermLine ι') A' (ren e s) =
      recR I W (Fin.elim0 : Fin 0 → HermLine ι) A s := by
  unfold recR
  congr 1
  · rw [divSupp_map] at hvert hc ⊢
    rw [finsum_mem_image (map_ringEquiv_injective (ren e)).injOn]
    refine finsum_mem_congr rfl fun V hV => ?_
    have h1 := hvert _ ⟨V, hV, rfl⟩
    have h2 : ¬ IsHorizontal V := by
      intro h
      apply h1
      unfold IsHorizontal
      rw [comap_C]
      exact h
    have h3 : charOf (V.map (ren e)) = charOf V := by simp only [charOf, comap_C]
    rw [if_neg h1, if_neg h2, sup_map, multAt_map, h3, geoNum_map e V hV.2 _ _ (hc _ ⟨V, hV, rfl⟩)]
  · have e0 : (fun j z => Real.log (((Fin.elim0 : Fin 0 → HermLine ι) j).h z)) =
        (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) := funext fun j => j.elim0
    have e1 : (fun j z => Real.log (((Fin.elim0 : Fin 0 → HermLine ι') j).h z)) =
        (Fin.elim0 : Fin 0 → ((Σ k, ι' k) → ℂ) → ℝ) := funext fun j => j.elim0
    rw [arInt, arInt, e0, e1]
    refine ptsIntegral_map e W hW hfin _ _ hinv fun z hz => ?_
    rw [logNorm, logNorm, eval_ren, hA z hz.1]

end CoverDenseAlt.Rename₂
