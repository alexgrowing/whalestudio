import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SInternal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresMaximalIdealGrZeroEqSupSpanMonomials
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PresNew
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PresIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem spanMono_prec_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  have key : ∀ (n : ℕ) (x : Fin r → R), x ∈ (I ^ n • ⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ I ^ n := by
    intro n x
    constructor
    · intro hx i
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro a ha m _
        simpa using (I ^ n).mul_mem_right (m i) ha
      · intro y z hy hz
        simpa using add_mem hy hz
    · intro hx
      have hx' : x = ∑ i, x i • Pi.single i (1 : R) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hx']
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top
  have hR : ∀ (n : ℕ) (a : R), a ∈ (I ^ n • ⊤ : Submodule R R) ↔ a ∈ I ^ n := by
    intro n a
    simp [smul_eq_mul, Ideal.mul_top]
  refine ⟨fun f hf => ?_⟩
  choose L hL using fun i : Fin r => IsPrecomplete.prec' (I := I) (M := R) (fun n => f n i)
    (fun {m n} hmn => by
      have h := hf hmn
      rw [SModEq.sub_mem] at h ⊢
      rw [hR]
      simpa using (key m _).1 h i)
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, key]
  intro i
  have h := hL i n
  rw [SModEq.sub_mem, hR] at h
  simpa using h

private theorem spanMono_prec {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  haveI := spanMono_prec_pi I n
  have hmap : ∀ k, (I ^ k • ⊤ : Submodule R (Fin n → R)).map π = I ^ k • ⊤ := by
    intro k
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hπ]
  refine ⟨fun f hf => ?_⟩
  have hd : ∀ k, f (k + 1) - f k ∈ (I ^ k • ⊤ : Submodule R M) := by
    intro k
    have h := (hf (Nat.le_succ k)).symm
    rw [SModEq.sub_mem] at h
    exact h
  have hlift : ∀ k, ∃ e, e ∈ (I ^ k • ⊤ : Submodule R (Fin n → R)) ∧ π e = f (k + 1) - f k := by
    intro k
    have h := hd k
    rw [← hmap k] at h
    obtain ⟨e, he, hpe⟩ := h
    exact ⟨e, he, hpe⟩
  choose e he hpe using hlift
  obtain ⟨g0, hg0⟩ := hπ (f 0)
  let g : ℕ → (Fin n → R) := fun m => g0 + ∑ k ∈ Finset.range m, e k
  have hg : ∀ m, π (g m) = f m := by
    intro m
    induction m with
    | zero => simp [g, hg0]
    | succ m ih =>
      simp only [g, Finset.sum_range_succ, map_add] at ih ⊢
      rw [← add_assoc, ih, hpe]
      abel
  have hcau : ∀ {a b : ℕ}, a ≤ b → g a ≡ g b [SMOD (I ^ a • ⊤ : Submodule R (Fin n → R))] := by
    intro a b hab
    rw [SModEq.sub_mem]
    have hs : g a - g b = -∑ k ∈ Finset.Ico a b, e k := by
      simp only [g]
      rw [← Finset.sum_range_add_sum_Ico _ hab]
      abel
    rw [hs, neg_mem_iff]
    exact Submodule.sum_mem _ fun k hk => Submodule.pow_smul_top_le I _ (Finset.mem_Ico.1 hk).1 (he k)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) g hcau
  refine ⟨π L, fun m => ?_⟩
  have h := hL m
  rw [SModEq.sub_mem] at h ⊢
  rw [← hmap m]
  exact ⟨_, h, by rw [map_sub, hg]⟩

private theorem exists_pow_mem_map_maxIdeal_of_monic_aeval_mem {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [IsLocalRing B]
    [Algebra O B] (x : B) (hx : x ∈ maximalIdeal B)
    (hJ : (maximalIdeal O).map (algebraMap O B) ≤ maximalIdeal B) :
    ∀ (d m : ℕ) (p : Polynomial O), p.Monic → p.natDegree = d →
      x ^ m * Polynomial.aeval x p ∈ (maximalIdeal O).map (algebraMap O B) →
      ∃ n : ℕ, x ^ n ∈ (maximalIdeal O).map (algebraMap O B) := by
  intro d
  induction d with
  | zero =>
    intro m p hp hd h
    refine ⟨m, ?_⟩
    rw [Polynomial.eq_one_of_monic_natDegree_zero hp hd] at h
    simpa using h
  | succ d ih =>
    intro m p hp hd h
    have hq : p.divX.Monic := by
      unfold Polynomial.Monic Polynomial.leadingCoeff
      rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, Polynomial.coeff_divX, hd]
      have h1 := hp.coeff_natDegree
      rw [hd] at h1
      simpa using h1
    have hqd : p.divX.natDegree = d := by
      rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hd]
      simp
    have hsplit : Polynomial.aeval x p =
        x * Polynomial.aeval x p.divX + algebraMap O B (p.coeff 0) := by
      have h0 := congrArg (Polynomial.aeval x) (Polynomial.X_mul_divX_add p)
      simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h0
      exact h0.symm
    by_cases hc : p.coeff 0 ∈ maximalIdeal O
    · apply ih (m + 1) p.divX hq hqd
      have h2 : x ^ m * algebraMap O B (p.coeff 0) ∈ (maximalIdeal O).map (algebraMap O B) :=
        Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hc)
      have h3 := Ideal.sub_mem _ h h2
      rw [hsplit] at h3
      convert h3 using 1
      ring
    · have hc0 : IsUnit (p.coeff 0) := by
        by_contra h'
        exact hc ((IsLocalRing.mem_maximalIdeal _).2 h')
      have hcu : IsUnit (algebraMap O B (p.coeff 0)) := hc0.map _
      have hu : IsUnit (x * Polynomial.aeval x p.divX + algebraMap O B (p.coeff 0)) := by
        by_contra h'
        have hm1 : x * Polynomial.aeval x p.divX + algebraMap O B (p.coeff 0) ∈ maximalIdeal B :=
          (IsLocalRing.mem_maximalIdeal _).2 h'
        have hm2 : x * Polynomial.aeval x p.divX ∈ maximalIdeal B := Ideal.mul_mem_right _ _ hx
        have hm3 := Ideal.sub_mem _ hm1 hm2
        rw [add_sub_cancel_left] at hm3
        exact (IsLocalRing.mem_maximalIdeal _).1 hm3 hcu
      refine ⟨m, ?_⟩
      rw [hsplit] at h
      exact (Ideal.mul_unit_mem_iff_mem _ hu).1 h

private theorem spanMono_top {O B : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [CommRing B] [Algebra O B] [IsCO O B] (A : Subalgebra O B) [Module.Finite O A] (u : Set B) (hu : u ⊆ A)
    (hm : maximalIdeal B = (maximalIdeal O).map (algebraMap O B) ⊔ Ideal.span u) : ∀ b, b ∈ A := by
  classical
  have hJm : (maximalIdeal O).map (algebraMap O B) ≤ maximalIdeal B := by
    rw [hm]
    exact le_sup_left
  have hum : ∀ x ∈ u, x ∈ maximalIdeal B := by
    intro x hx
    rw [hm]
    exact Ideal.mem_sup_right (Ideal.subset_span hx)
  have hnil : ∀ x ∈ u, ∃ n : ℕ, x ^ n ∈ (maximalIdeal O).map (algebraMap O B) := by
    intro x hx
    have hint : IsIntegral O (⟨x, hu hx⟩ : A) := Algebra.IsIntegral.isIntegral _
    obtain ⟨p, hp, hpx⟩ := hint
    have h0 : Polynomial.aeval (⟨x, hu hx⟩ : A) p = 0 := hpx
    have h1 : Polynomial.aeval x p = 0 := by
      have h2 := congrArg A.val h0
      rw [← Polynomial.aeval_algHom_apply] at h2
      simpa using h2
    refine exists_pow_mem_map_maxIdeal_of_monic_aeval_mem x (hum x hx) hJm _ 0 p hp rfl ?_
    rw [h1, mul_zero]
    exact Ideal.zero_mem _
  have hrad : Ideal.span u ≤ ((maximalIdeal O).map (algebraMap O B)).radical := by
    rw [Ideal.span_le]
    intro x hx
    obtain ⟨n, hn⟩ := hnil x hx
    exact ⟨n, hn⟩
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  let Q : ℕ → Submodule O B := fun k =>
    Subalgebra.toSubmodule A ⊔ (((maximalIdeal O).map (algebraMap O B)) ⊔ Ideal.span u ^ k).restrictScalars O
  have hQ : ∀ k, ∀ b : B, b ∈ Q k := by
    intro k
    induction k with
    | zero =>
      intro b
      apply Submodule.mem_sup_right
      simp
    | succ k ih =>
      have hP : ∀ y ∈ Ideal.span u, ∀ b : B, b * y ∈ Q (k + 1) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem x hx =>
          intro b
          obtain ⟨a, ha, t, ht, rfl⟩ := Submodule.mem_sup.1 (ih b)
          rw [add_mul]
          refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
          · exact A.mul_mem ha (hu hx)
          · have hmul : t * x ∈ (((maximalIdeal O).map (algebraMap O B)) ⊔ Ideal.span u ^ k) * Ideal.span u :=
              Ideal.mul_mem_mul ht (Ideal.subset_span hx)
            rw [Ideal.sup_mul] at hmul
            have hle : ((maximalIdeal O).map (algebraMap O B)) * Ideal.span u ⊔ Ideal.span u ^ k * Ideal.span u ≤
                ((maximalIdeal O).map (algebraMap O B)) ⊔ Ideal.span u ^ (k + 1) :=
              sup_le_sup (by first | exact Ideal.mul_le_right | exact Ideal.mul_le_left) (le_of_eq (pow_succ _ _).symm)
            exact hle hmul
        | zero =>
          intro b
          rw [mul_zero]
          exact Submodule.zero_mem _
        | add y z _ _ hy hz =>
          intro b
          rw [mul_add]
          exact Submodule.add_mem _ (hy b) (hz b)
        | smul c y _ hy =>
          intro b
          rw [smul_eq_mul, ← mul_assoc]
          exact hy (b * c)
      intro b
      obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) b
      rw [hm] at hc
      obtain ⟨j, hj, s, hs, hjs⟩ := Submodule.mem_sup.1 hc
      have hb : b = algebraMap O B c + j + s := by
        rw [add_assoc, hjs]
        ring
      rw [hb]
      refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
      · exact Submodule.mem_sup_left (A.algebraMap_mem c)
      · exact Submodule.mem_sup_right (Ideal.mem_sup_left hj)
      · simpa using hP s hs 1
  haveI : IsPrecomplete (maximalIdeal O) A := spanMono_prec (maximalIdeal O)
  haveI : IsAdicComplete (maximalIdeal B) B := IsCO.complete (O := O)
  haveI : IsHausdorff (maximalIdeal O) B := by
    refine ⟨fun x hx => IsHausdorff.haus' (I := maximalIdeal B) x fun n => ?_⟩
    have h := hx n
    rw [SModEq.zero] at h ⊢
    rw [Ideal.smul_top_eq_map] at h
    have h' : x ∈ (maximalIdeal O ^ n).map (algebraMap O B) := h
    rw [Ideal.map_pow] at h'
    have h'' : x ∈ maximalIdeal B ^ n := Ideal.pow_right_mono hJm n h'
    simpa [smul_eq_mul, Ideal.mul_top] using h''
  have hsurj : Function.Surjective (A.val.toLinearMap : A →ₗ[O] B) := by
    apply surjective_of_mkQ_comp_surjective (I := maximalIdeal O)
    intro y
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨a, ha, t, ht, hat⟩ := Submodule.mem_sup.1 (hQ N b)
    have ht' : t ∈ (maximalIdeal O).map (algebraMap O B) := by
      have ht2 : t ∈ ((maximalIdeal O).map (algebraMap O B)) ⊔ Ideal.span u ^ N := ht
      exact (sup_le le_rfl hN) ht2
    refine ⟨⟨a, ha⟩, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, AlgHom.toLinearMap_apply,
      Subalgebra.coe_val]
    rw [Submodule.Quotient.eq, Ideal.smul_top_eq_map]
    have : a - b = -t := by rw [← hat]; ring
    rw [this]
    exact Submodule.neg_mem _ ht'
  intro b
  obtain ⟨a, ha⟩ := hsurj b
  rw [← ha]
  exact a.2

private theorem spanMono_parts {O X R : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X]
    [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R) (hz : ∀ s, W.z s ∈ maximalIdeal R)
    (N : X → Submodule O R) [SetLike.GradedMonoid N] (hN : ∀ s, W.z s ∈ N (W.wt s))
    (A : Subalgebra O R) [Module.Finite O A] (hA : ∀ x, x ∈ A ↔ x ∈ N 0) (w : X) : W.part w ≤ N w := by
  classical
  haveI := wPres_gr_zero_isCO_of_mem_maximalIdeal O X R W hz
  obtain ⟨-, u, hu, hmu⟩ := wPres_maximalIdeal_gr_zero_eq_sup_span_monomials O X R W hz
  have hmono : ∀ n : W.σ →₀ ℕ, W.π (MvPowerSeries.monomial n 1) ∈ N (Finsupp.weight W.wt n) := by
    intro n
    induction n using Finsupp.induction with
    | zero =>
      rw [MvPowerSeries.monomial_zero_one, map_one, map_zero]
      exact SetLike.one_mem_graded N
    | single_add a b f _ _ ih =>
      have hw : Finsupp.weight W.wt (Finsupp.single a b + f) = b • W.wt a + Finsupp.weight W.wt f := by
        rw [map_add, Finsupp.weight_apply, Finsupp.sum_single_index (by simp)]
      rw [hw, ← one_mul (1 : O), ← MvPowerSeries.monomial_mul_monomial, ← MvPowerSeries.X_pow_eq,
        map_mul, map_pow]
      exact SetLike.mul_mem_graded (SetLike.pow_mem_graded b (hN a)) ih
  have hprod : ∀ n : W.σ →₀ ℕ, (n.prod fun s k => W.z s ^ k) ∈ N (Finsupp.weight W.wt n) := by
    intro n
    rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.prod]
    exact SetLike.prod_mem_graded _ _ _ fun s _ => SetLike.pow_mem_graded _ (hN s)
  let A' : Subalgebra O ↥(W.gr 0) :=
    { carrier := {b | ((b : W.A) : R) ∈ A}
      mul_mem' := fun {a b} ha hb => A.mul_mem ha hb
      one_mem' := A.one_mem
      add_mem' := fun {a b} ha hb => A.add_mem ha hb
      zero_mem' := A.zero_mem
      algebraMap_mem' := fun c => A.algebraMap_mem c }
  let φ : A' →ₗ[O] A :=
    { toFun := fun x => ⟨(((x : ↥(W.gr 0)) : W.A) : R), x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : Module.Finite O A' := Module.Finite.of_injective φ (by
    intro x y h
    have h' := congrArg (fun t : A => (t : R)) h
    exact Subtype.ext (Subtype.ext (Subtype.ext h')))
  have hall := spanMono_top (O := O) (B := ↥(W.gr 0)) A' (↑u) (by
    intro b hb
    obtain ⟨n, -, hn0, hbn⟩ := hu b hb
    show ((b : W.A) : R) ∈ A
    rw [hA, hbn]
    have h1 := hprod n
    rwa [hn0] at h1) hmu
  have h0 : ∀ x ∈ W.part 0, x ∈ N 0 := by
    intro x hx
    have hxA := W.part_le_A hx
    have h1 := hall ⟨⟨x, hxA⟩, (show (⟨x, hxA⟩ : W.A) ∈ W.gr 0 from hx)⟩
    exact (hA x).1 h1
  intro x hx
  obtain ⟨f, hf, rfl⟩ := hx
  obtain ⟨μ, hμS, hμ⟩ := part_span O R X W {n | Finsupp.weight W.wt n = w} w (fun n hn => hn)
  obtain ⟨b, hb, rfl⟩ := hμ f (fun n hn => hf n hn)
  rw [AlgHom.toLinearMap_apply, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [map_mul]
  have hw : Finsupp.weight W.wt m = w := hμS hm
  have h2 := SetLike.mul_mem_graded (h0 _ ⟨b m, hb m, rfl⟩) (hmono m)
  rwa [zero_add, hw] at h2

private theorem spanMono_lift {O R H : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing R] [Algebra O R] [IsCO O R] [Group H] [TopologicalSpace H]
    (W : WPres O (ℤ × ℤ) R) (hz : ∀ s, W.z s ∈ maximalIdeal R) {rbar : H →* M4 (ResidueField O)}
    (hbar : ∀ g i j, i ≠ j → rbar g i j = 0) (r : Lift O rbar R) (hgen : r.Generates)
    (hr : ∀ g i j, r.hom g i j ∈ W.part (wt i j))
    (hfin : Module.Finite O (Algebra.adjoin O (mono r.hom 0))) (w : ℤ × ℤ) :
    W.part w = Submodule.span O (mono r.hom w) := by
  classical
  have hm1 : ∀ {v1 v2 : ℤ × ℤ} {x y : R}, x ∈ mono r.hom v1 → y ∈ mono r.hom v2 →
      x * y ∈ mono r.hom (v1 + v2) := by
    rintro v1 v2 x y ⟨L1, hL1, rfl⟩ ⟨L2, hL2, rfl⟩
    exact ⟨L1 ++ L2, by simp [List.sum_append, hL1, hL2], by simp [List.prod_append]⟩
  have hm2 : (1 : R) ∈ mono r.hom 0 := ⟨[], by simp, by simp⟩
  have hm3 : ∀ g a b, r.hom g a b ∈ mono r.hom (wt a b) := fun g a b => ⟨[(g, a, b)], by simp, by simp⟩
  have hmulN : ∀ {v1 v2 : ℤ × ℤ} {x y : R}, x ∈ Submodule.span O (mono r.hom v1) →
      y ∈ Submodule.span O (mono r.hom v2) → x * y ∈ Submodule.span O (mono r.hom (v1 + v2)) := by
    intro v1 v2 x y hx hy
    have hxy := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at hxy
    refine Submodule.span_mono ?_ hxy
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact hm1 ha hb
  haveI : SetLike.GradedMonoid (fun v => Submodule.span O (mono r.hom v)) :=
    { one_mem := Submodule.subset_span hm2
      mul_mem := fun v1 v2 x y hx hy => hmulN hx hy }
  have hlist : ∀ L : List (H × Fin 4 × Fin 4), (L.map (fun a => r.hom a.1 a.2.1 a.2.2)).prod ∈
      W.part (L.map (fun a => wt a.2.1 a.2.2)).sum := by
    intro L
    induction L with
    | nil => simpa using SetLike.one_mem_graded W.part
    | cons a L ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact SetLike.mul_mem_graded (hr a.1 a.2.1 a.2.2) ih
  have h1W : (1 : R) ∈ W.part 0 := SetLike.one_mem_graded W.part
  choose c hc using fun t : H × Fin 4 × Fin 4 => IsCO.res_surj (O := O) (r.hom t.1 t.2.1 t.2.2)
  let z' : H × Fin 4 × Fin 4 → R := fun t =>
    if t.2.1 = t.2.2 then r.hom t.1 t.2.1 t.2.2 - algebraMap O R (c t) else r.hom t.1 t.2.1 t.2.2
  have hz'max : ∀ t, z' t ∈ maximalIdeal R := by
    rintro ⟨g, a, b⟩
    by_cases hab : a = b
    · subst hab
      dsimp only [z']
      rw [if_pos rfl]
      exact hc (g, a, a)
    · dsimp only [z']
      rw [if_neg hab, ← res_eq_zero_iff O R, r.red, hbar g a b hab]
  have hz'part : ∀ t, z' t ∈ W.part (wt t.2.1 t.2.2) := by
    rintro ⟨g, a, b⟩
    by_cases hab : a = b
    · subst hab
      dsimp only [z']
      rw [if_pos rfl]
      refine Submodule.sub_mem _ (hr g a a) ?_
      rw [(wt_eq_zero a a).2 rfl, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ h1W
    · dsimp only [z']
      rw [if_neg hab]
      exact hr g a b
  have hz'N : ∀ t, z' t ∈ Submodule.span O (mono r.hom (wt t.2.1 t.2.2)) := by
    rintro ⟨g, a, b⟩
    by_cases hab : a = b
    · subst hab
      dsimp only [z']
      rw [if_pos rfl]
      refine Submodule.sub_mem _ (Submodule.subset_span (hm3 g a a)) ?_
      rw [(wt_eq_zero a a).2 rfl, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hm2)
    · dsimp only [z']
      rw [if_neg hab]
      exact Submodule.subset_span (hm3 g a b)
  haveI : IsCO O (DualNumber (ResidueField O)) := (co_res O).2
  have hcot : maximalIdeal R ≤ Ideal.span (Set.range z') ⊔ Ideal.map (Algebra.ofId O R) (maximalIdeal O) ⊔
      maximalIdeal R ^ 2 := by
    refine co_span O R O (Algebra.ofId O R) (Set.range z') ?_ ?_
    · rintro _ ⟨t, rfl⟩
      exact hz'max t
    · intro f f' _ hs
      apply hgen _ f f'
      apply Lift.ext
      refine MonoidHom.ext fun g => Matrix.ext fun a b => ?_
      have hfs := hs _ ⟨(g, a, b), rfl⟩
      show f (r.hom g a b) = f' (r.hom g a b)
      by_cases hab : a = b
      · subst hab
        dsimp only [z'] at hfs
        rw [if_pos rfl, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes] at hfs
        exact sub_left_inj.1 hfs
      · dsimp only [z'] at hfs
        rwa [if_neg hab] at hfs
  have hcot' : maximalIdeal R ≤ Ideal.span (Set.range z') ⊔ Ideal.map (algebraMap O R) (maximalIdeal O) ⊔
      maximalIdeal R ^ 2 := hcot
  obtain ⟨U, hUsub, hUspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := R) (Set.range z')).1
      (IsNoetherian.noetherian (Submodule.span R (Set.range z')))
  have hidx : ∀ s : U, ∃ t, z' t = s := fun s => hUsub s.2
  choose idx hidx' using hidx
  let z'' : U → R := fun s => z' (idx s)
  let wt'' : U → ℤ × ℤ := fun s => wt (idx s).2.1 (idx s).2.2
  have h2 : maximalIdeal R ≤ Ideal.span (Set.range z'') ⊔ Ideal.map (algebraMap O R) (maximalIdeal O) ⊔
      maximalIdeal R ^ 2 := by
    refine hcot'.trans (sup_le_sup_right (sup_le_sup_right ?_ _) _)
    change Submodule.span R (Set.range z') ≤ Submodule.span R (Set.range z'')
    rw [hUspan]
    refine Submodule.span_mono ?_
    intro x hx
    exact ⟨⟨x, hx⟩, hidx' ⟨x, hx⟩⟩
  obtain ⟨W', e, he⟩ := pres_new O (ℤ × ℤ) R W hz U wt'' z'' (fun s => ⟨hz'max _, hz'part _⟩) h2
  have hzW' : ∀ s, W'.z s ∈ maximalIdeal R := by
    intro s
    obtain ⟨t, rfl⟩ := e.surjective s
    rw [(he t).1]
    exact hz'max _
  have hpW' : ∀ s, W'.z s ∈ W.part (W'.wt s) := by
    intro s
    obtain ⟨t, rfl⟩ := e.surjective s
    rw [(he t).1, (he t).2]
    exact hz'part _
  have hNW' : ∀ s, W'.z s ∈ Submodule.span O (mono r.hom (W'.wt s)) := by
    intro s
    obtain ⟨t, rfl⟩ := e.surjective s
    rw [(he t).1, (he t).2]
    exact hz'N _
  haveI := hfin
  have hAeq : ∀ x, x ∈ Algebra.adjoin O (mono r.hom 0) ↔ x ∈ Submodule.span O (mono r.hom 0) := by
    intro x
    constructor
    · intro hx
      induction hx using Algebra.adjoin_induction with
      | mem y hy => exact Submodule.subset_span hy
      | algebraMap d =>
        rw [Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hm2)
      | add y y' _ _ hy hy' => exact Submodule.add_mem _ hy hy'
      | mul y y' _ _ hy hy' => simpa using hmulN hy hy'
    · intro hx
      exact (Submodule.span_le.2 Algebra.subset_adjoin :
        Submodule.span O (mono r.hom 0) ≤ Subalgebra.toSubmodule (Algebra.adjoin O (mono r.hom 0))) hx
  have hle := spanMono_parts W' hzW' (fun v => Submodule.span O (mono r.hom v)) hNW'
    (Algebra.adjoin O (mono r.hom 0)) hAeq w
  rw [pres_indep O (ℤ × ℤ) R W hz W' hzW' hpW' w] at hle
  refine le_antisymm hle ?_
  rw [Submodule.span_le]
  rintro x ⟨L, rfl, rfl⟩
  exact hlist L

theorem UpperTheory.V.GradeZeroInterpolatingElement.spanMono :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, D.Fin0 → ∀ w, M.sPart w = Submodule.span c.O (mono M.ru.hom w) := by
  intro Ω _ _ _ l _ c D hD M hF w
  obtain ⟨-, -, WS, hW, hz⟩ := sInternal D hD M
  rw [← hW]
  refine spanMono_lift WS hz (fun g i j h => ?_) M.ru M.gen (fun g i j => ?_) (hF M.S M.ru M.pt) w
  · show residue c.O (Matrix.diagonal _ i j) = 0
    rw [Matrix.diagonal_apply_ne _ h, map_zero]
  · rw [hW]
    exact M.entry_mem g i j
