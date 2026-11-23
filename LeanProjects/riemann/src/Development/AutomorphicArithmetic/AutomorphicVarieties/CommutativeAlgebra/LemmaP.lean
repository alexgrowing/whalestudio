import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedUniv
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedGrading
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTangent
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.RelPres
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ObsClass
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.MapPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerGen

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem lp_wcomp_mul {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X) {c : X}
    {a : MvPowerSeries σ O} (ha : a ∈ wtPart O wt c) (j : X) (b : MvPowerSeries σ O) :
    wcomp O wt j (b * a) = wcomp O wt (j - c) b * a := by
  classical
  ext n
  rw [coeff_wcomp, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = c
    · rw [coeff_wcomp, if_pos]
      rw [← h, ← hp', map_add, h2, add_sub_cancel_right]
    · rw [ha _ h2, mul_zero, mul_zero]
  · refine (Finset.sum_eq_zero fun p hp => ?_).symm
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = c
    · rw [coeff_wcomp, if_neg, zero_mul]
      intro h1
      exact h (by rw [← hp', map_add, h1, h2, sub_add_cancel])
    · rw [ha _ h2, mul_zero]

private theorem lp_homog_mul {O σ X κ : Type} [CommRing O] [AddCommGroup X] [Fintype κ] (wt : σ → X)
    (I : Ideal (MvPowerSeries σ O)) (hI : IsHomog O wt I) (f : κ → MvPowerSeries σ O) (c : κ → X)
    (hf : ∀ u, f u ∈ wtPart O wt (c u)) : IsHomog O wt (I * Ideal.span (Set.range f)) := by
  intro x hx j
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · obtain ⟨d, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hb
    rw [Finset.mul_sum, map_sum]
    refine Ideal.sum_mem _ fun u _ => ?_
    rw [← mul_assoc, lp_wcomp_mul wt (hf u)]
    exact Ideal.mul_mem_mul (hI _ (I.mul_mem_right _ ha) _) (Ideal.subset_span ⟨u, rfl⟩)
  · rw [map_add]; exact add_mem ha hb

private theorem lp_homog_sup {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X)
    (I J : Ideal (MvPowerSeries σ O)) (hI : IsHomog O wt I) (hJ : IsHomog O wt J) : IsHomog O wt (I ⊔ J) := by
  intro x hx j
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  exact Submodule.add_mem_sup (hI a ha j) (hJ b hb j)

private theorem lp_mem_max {O σ : Type} [CommRing O] [IsLocalRing O] (x : MvPowerSeries σ O) :
    x ∈ maximalIdeal (MvPowerSeries σ O) ↔ constantCoeff x ∈ maximalIdeal O := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_iff_constantCoeff]

private theorem lp_homog_max {O σ X : Type} [CommRing O] [IsLocalRing O] [AddCommGroup X] (wt : σ → X) :
    IsHomog O wt (maximalIdeal (MvPowerSeries σ O)) := by
  intro x hx j
  rw [lp_mem_max] at hx ⊢
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_wcomp]
  split_ifs
  · exact hx
  · exact zero_mem _

private theorem lp_loc {O R R' : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (x : R) :
    f x ∈ maximalIdeal R' ↔ x ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem lp_loc_sq {O R R' : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {x : R} (hx : x ∈ maximalIdeal R ^ 2) :
    f x ∈ maximalIdeal R' ^ 2 := by
  have h : (maximalIdeal R).map f ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 fun y hy => (lp_loc f y).2 hy
  have := Ideal.mem_map_of_mem f hx
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono h 2 this

private theorem lp_taylor {O σ : Type} [CommRing O] [IsLocalRing O] [Fintype σ] (g : MvPowerSeries σ O) :
    ∃ c : σ → O, g - algebraMap O _ (constantCoeff g) - ∑ s, c s • X s ∈ maximalIdeal (MvPowerSeries σ O) ^ 2 := by
  obtain ⟨k, -, hk⟩ := GlobalTheory.exists_eq_sum_X_mul (n := 0) (g := g - C (constantCoeff g)) fun d hd => by
    have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by simpa using hd)
    subst this
    simp
  refine ⟨fun s => constantCoeff (k s), ?_⟩
  rw [show algebraMap O (MvPowerSeries σ O) (constantCoeff g) = C (constantCoeff g) from rfl, hk,
    ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun s _ => ?_
  have : X s * k s - constantCoeff (k s) • X s = X s * (k s - C (constantCoeff (k s))) := by
    rw [smul_eq_C_mul]; ring
  rw [this, pow_two]
  refine Ideal.mul_mem_mul ?_ ?_ <;> rw [lp_mem_max] <;> simp

private theorem lp_pad {X κ : Type} [Fintype κ] (wf : κ → X) (n : X → ℕ) (S : Finset X)
    (hS : ∀ j, j ∉ S → n j = 0) (h : ∀ j, Nat.card {u // wf u = j} ≤ n j) :
    ∃ (κ' : Type) (_ : Fintype κ') (wf' : κ' → X), ∀ j, Nat.card {u : κ ⊕ κ' // Sum.elim wf wf' u = j} = n j := by
  classical
  refine ⟨Σ j : S, Fin (n j - Nat.card {u // wf u = j}), inferInstance, fun x => x.1, fun j => ?_⟩
  rw [Nat.card_congr (Equiv.subtypeSum), Nat.card_sum]
  simp only [Sum.elim_inl, Sum.elim_inr]
  by_cases hj : j ∈ S
  · have e : {x : (Σ j : S, Fin (n j - Nat.card {u // wf u = j})) // (x.1 : X) = j} ≃
        Fin (n j - Nat.card {u // wf u = j}) :=
      (Equiv.subtypeEquivRight (fun x => by
        rw [← Subtype.ext_iff (a2 := (⟨j, hj⟩ : S))])).trans
        (Equiv.sigmaSubtype (β := fun j : S => Fin (n j - Nat.card {u // wf u = j})) ⟨j, hj⟩)
    rw [Nat.card_congr e, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]
    have := h j
    omega
  · haveI : IsEmpty {x : (Σ j : S, Fin (n j - Nat.card {u // wf u = j})) // (x.1 : X) = j} :=
      ⟨fun x => hj (x.2 ▸ x.1.1.2)⟩
    have := h j
    rw [hS j hj] at this ⊢
    have h0 : Nat.card {x : (Σ j : S, Fin (n j - Nat.card {u // wf u = j})) // (x.1 : X) = j} = 0 :=
      Nat.card_of_isEmpty
    omega

private theorem lp_detect {O B A R κ : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B] [IsCO O B]
    [CommRing A] [Algebra O A] [IsCO O A] [CommRing R] [Algebra O R] [IsCO O R] [Fintype κ]
    (i : B →ₐ[O] A) (p : A →ₐ[O] R) (hm : maximalIdeal A * RingHom.ker p = ⊥)
    (hker : RingHom.ker p ≤ (maximalIdeal B).map i ⊔ maximalIdeal A ^ 2)
    (ε : κ → A) (hε : ∀ u, p (ε u) = 0) (hind : ∀ c : κ → O, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal O)
    (c : κ → O)
    (H : ∀ (A' : Type) [CommRing A'] [Algebra O A'] [IsCO O A'] (p' : A →ₐ[O] A') (p'' : A' →ₐ[O] R) (η : A'),
      Function.Surjective p' → p''.comp p' = p → (∀ x ∈ maximalIdeal A', x * η = 0) → p'' η = 0 →
      (∀ u, p' (ε u) = c u • η) → ∃ s : R →ₐ[O] A', p''.comp s = AlgHom.id O R ∧ s.comp (p.comp i) = p'.comp i) :
    ∀ u, c u ∈ maximalIdeal O := by
  classical
  intro u0
  by_contra h0
  obtain ⟨d, hd⟩ := (notMem_maximalIdeal.1 h0).exists_right_inv
  have hz : ∀ x ∈ maximalIdeal A, ∀ y, p y = 0 → x * y = 0 := fun x hx y hy => by
    have := Ideal.mul_mem_mul hx (show y ∈ RingHom.ker p from hy)
    rwa [hm] at this
  let δ : κ → A := fun u => ε u - (c u * d) • ε u0
  have hδ : ∀ u, p (δ u) = 0 := fun u => by simp [δ, hε]
  let I : Ideal A := Ideal.span (Set.range δ)
  have hI : I ≤ RingHom.ker p := Ideal.span_le.2 (by rintro _ ⟨u, rfl⟩; exact hδ u)
  let p'' : (A ⧸ I) →ₐ[O] R := Ideal.Quotient.liftₐ I p hI
  let p' : A →ₐ[O] A ⧸ I := Ideal.Quotient.mkₐ O I
  have hp' : Function.Surjective p' := Ideal.Quotient.mk_surjective
  have hpp : ∀ x, p'' (p' x) = p x := fun x => rfl
  haveI : Nontrivial (A ⧸ I) := p''.toRingHom.domain_nontrivial
  haveI : IsCO O (A ⧸ I) := co_quot O A _ p' hp'
  obtain ⟨s, hs1, hs2⟩ := H (A ⧸ I) p' p'' (p' (d • ε u0)) hp' (AlgHom.ext hpp)
    (fun x hx => by
      obtain ⟨x, rfl⟩ := hp' x
      rw [← map_mul, hz x ((lp_loc p' x).1 hx) _ (by simp [hε]), map_zero])
    (by rw [hpp]; simp [hε])
    (fun u => by
      rw [← map_smul, smul_smul]
      exact Ideal.Quotient.eq.2 (Ideal.subset_span ⟨u, rfl⟩))
  have hs1' : ∀ x, p'' (s x) = x := fun x => DFunLike.congr_fun hs1 x
  have hs : Function.Surjective s := by
    refine co_surj O R _ s fun x hx => ?_
    obtain ⟨y, hy⟩ := hp' (x - s (p'' x))
    have h1 : y ∈ RingHom.ker p := by
      show p y = 0
      rw [← hpp, hy, map_sub, hs1', sub_self]
    have h2 : x = s (p'' x) + p' y := by rw [hy]; ring
    rw [h2]
    refine add_mem (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ((lp_loc p'' x).2 hx))) ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hker h1)
    rw [map_add]
    refine Submodule.add_mem_sup ?_ (lp_loc_sq p' hb)
    have h3 : (maximalIdeal B).map i ≤ ((maximalIdeal R).map s).comap p' :=
      Ideal.map_le_iff_le_comap.2 fun t ht => by
        show p' (i t) ∈ (maximalIdeal R).map s
        have h4 : s (p (i t)) = p' (i t) := DFunLike.congr_fun hs2 t
        rw [← h4]
        exact Ideal.mem_map_of_mem _ ((lp_loc p _).2 ((lp_loc i _).2 ht))
    exact h3 ha
  have h5 : ε u0 ∈ I := by
    obtain ⟨y, hy⟩ := hs (p' (ε u0))
    have : y = 0 := by rw [← hs1' y, hy, hpp, hε]
    rw [this, map_zero] at hy
    exact Ideal.Quotient.eq_zero_iff_mem.1 hy.symm
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 h5
  choose b hb using fun u => IsCO.res_surj (O := O) (a u)
  have h6 : ∑ u, b u • δ u = ε u0 := by
    rw [← ha]
    refine Finset.sum_congr rfl fun u _ => ?_
    have := hz _ (hb u) _ (hδ u)
    rw [sub_mul, sub_eq_zero] at this
    rw [this, Algebra.smul_def]
  have h7 := hind (fun u => b u - if u = u0 then 1 + ∑ v, b v * (c v * d) else 0) (by
    simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      add_smul, one_smul, Finset.sum_smul]
    simp only [δ, smul_sub, Finset.sum_sub_distrib, smul_smul] at h6
    linear_combination h6)
  have h8 : ∑ u, (b u - if u = u0 then 1 + ∑ v, b v * (c v * d) else 0) * (c u * d) ∈ maximalIdeal O :=
    Ideal.sum_mem _ fun u _ => Ideal.mul_mem_right _ _ (h7 u)
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    hd, mul_one] at h8
  rw [sub_add_cancel_right, neg_mem_iff] at h8
  exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h8)

private theorem lp_ker {O B A R σ σB τ : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing B] [Algebra O B] [IsCO O B]
    [CommRing A] [Algebra O A] [IsCO O A] [CommRing R] [Algebra O R] [IsCO O R] [Fintype σ] [Fintype σB] [Fintype τ]
    (e : σB ⊕ τ ≃ σ) (i : B →ₐ[O] A) (p : A →ₐ[O] R) (π : MvPowerSeries σ O →ₐ[O] A) (hπ : Function.Surjective π)
    (h1 : ∀ s, ∃ b ∈ maximalIdeal B, π (X (e (.inl s))) = i b)
    (h2 : ∀ c : τ → O, ∑ t, c t • p (π (X (e (.inr t)))) ∈ (maximalIdeal B).map (p.comp i) ⊔ maximalIdeal R ^ 2 →
      ∀ t, c t ∈ maximalIdeal O) :
    RingHom.ker p ≤ (maximalIdeal B).map i ⊔ maximalIdeal A ^ 2 := by
  haveI : IsCO O (MvPowerSeries σ O) := co_mvps O O σ
  intro x hx
  obtain ⟨g, rfl⟩ := hπ x
  have hx' : p (π g) = 0 := hx
  have hg : constantCoeff g ∈ maximalIdeal O := by
    rw [← lp_mem_max, ← lp_loc π, ← lp_loc p, hx']
    exact zero_mem _
  obtain ⟨c, hc⟩ := lp_taylor g
  have key : ∀ (T : Type) [CommRing T] [Algebra O T] [IsCO O T] (q : A →ₐ[O] T),
      q (π g) - ∑ t, c (e (.inr t)) • q (π (X (e (.inr t)))) ∈
        (maximalIdeal B).map (q.comp i) ⊔ maximalIdeal T ^ 2 := by
    intro T _ _ _ q
    have k1 := lp_loc_sq (q.comp π) hc
    rw [map_sub, map_sub, AlgHom.commutes, map_sum, ← e.sum_comp, Fintype.sum_sum_type] at k1
    simp only [map_smul, AlgHom.comp_apply] at k1
    have k2 : algebraMap O T (constantCoeff g) ∈ (maximalIdeal B).map (q.comp i) := by
      rw [← (q.comp i).commutes]
      exact Ideal.mem_map_of_mem _ ((lp_loc (Algebra.ofId O B) _).2 hg)
    have k3 : ∑ s, c (e (.inl s)) • q (π (X (e (.inl s)))) ∈ (maximalIdeal B).map (q.comp i) := by
      refine Ideal.sum_mem _ fun s _ => ?_
      obtain ⟨b, hb, hb'⟩ := h1 s
      rw [hb', Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem (q.comp i) hb)
    have := Submodule.add_mem_sup (add_mem k2 k3) k1
    convert this using 1
    ring
  have k4 := key R p
  rw [hx', zero_sub, neg_mem_iff] at k4
  have k5 := h2 _ k4
  have k6 := key A (AlgHom.id O A)
  simp only [AlgHom.id_apply, AlgHom.id_comp] at k6
  have k7 : ∑ t, c (e (.inr t)) • π (X (e (.inr t))) ∈ maximalIdeal A ^ 2 := by
    refine Ideal.sum_mem _ fun t _ => ?_
    rw [Algebra.smul_def, pow_two]
    refine Ideal.mul_mem_mul ((lp_loc (Algebra.ofId O A) _).2 (k5 t)) ((lp_loc π _).2 ?_)
    rw [lp_mem_max]; simp
  simpa using add_mem k6 (Ideal.mem_sup_right k7)

private theorem lp_ob_zero {O ι X Γ : Type} [CommRing O] [IsLocalRing O] [Fintype ι] [DecidableEq ι] [AddCommGroup X]
    {w : ι → X} (Φ : FormData O w) [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    (hbar : Φ.Normalises rbar) (F : Frame Γ) (j : X) (hj : ∀ a b, w a - w b ≠ j) :
    Module.finrank (ResidueField O) (F.Ob (FormData.adRep hbar j)) = 0 := by
  haveI : Subsingleton (Φ.gw (ResidueField O) j) :=
    ⟨fun x y => Subtype.ext (Matrix.ext fun a b => (x.2.2 a b (hj a b)).trans (y.2.2 a b (hj a b)).symm)⟩
  haveI : Subsingleton (F.Ob (FormData.adRep hbar j)) := (Submodule.mkQ_surjective _).subsingleton
  exact Module.finrank_zero_of_subsingleton

theorem UpperTheory.V.Alg.lemmaP :
    LemmaP := by
  intro l _ O _ _ _ _ _ _ hl ι X _ _ _ _ _ w Φ Γ _ _ _ _ _ _ hΦ rbar r0 hbar h0 F L hN hL hL0 hfin B _ _ _ WB ρ hWB hρ hρw
  classical
  have h2 : IsUnit (2 : O) := by
    rw [← residue_ne_zero_iff_isUnit, map_ofNat]
    intro h
    have h' := (CharP.cast_eq_zero_iff (ResidueField O) l 2).1 (by exact_mod_cast h)
    exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h')
  obtain ⟨R, _, _, _, i, r, α, hU⟩ := framed_univ l O ι X w Φ h2 Γ rbar r0 hbar h0 hΦ F L hN hL hL0 B ρ hρ ()
  obtain ⟨W₀, g1, g2, g3, g4⟩ := framed_grading O ι X w Φ h2 Γ rbar r0 hbar h0 F L hN hL hL0 B ρ hρ WB hWB hρw R i r α hU
  obtain ⟨τ, _, z, wt, t1, t2, t3, t4⟩ := framed_tangent O ι X w Φ h2 Γ rbar r0 hbar h0 F L hN hL hL0 B ρ hρ R i r α hU
  have hone : ∀ c : O, algebraMap O R c ∈ W₀.part 0 := fun c => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ SetLike.GradedOne.one_mem
  have hz : ∀ t, z t ∈ maximalIdeal R ∧ z t ∈ W₀.part (wt t) := by
    intro t
    obtain ⟨a, b, hab, ⟨s, hs⟩ | ⟨v, hv⟩⟩ := t1 t
    · rw [hs, hab]
      refine ⟨?_, sub_mem (g3 s a b) ?_⟩
      · rw [← res_eq_zero_iff O, map_sub, r.red, ← r0.red, sub_eq_zero]
        exact (res_map (Algebra.ofId O R) _).symm
      · by_cases e : w a = w b
        · rw [e, sub_self]; exact hone _
        · rw [h0.2.2 s a b e, map_zero]; exact zero_mem _
    · rw [hv, hab, Matrix.sub_apply]
      refine ⟨?_, sub_mem (g4 v a b) ?_⟩
      · have := congrFun (congrFun (hU.1.2.2.1 v).2.2 a) b
        rw [Matrix.map_apply] at this
        rw [← res_eq_zero_iff O, map_sub, this, sub_eq_zero, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      · rw [Matrix.one_apply]
        split_ifs with e
        · rw [e, sub_self]; exact SetLike.GradedOne.one_mem
        · exact zero_mem _
  obtain ⟨W, κ, _, e, f, wf, hrel, p1, p2, p3⟩ := rel_pres O X B R WB W₀ i hWB g1 g2 τ z wt hz t2
  obtain ⟨q1, q2, q3, q4⟩ := hrel
  have bound : ∀ j, Nat.card {u // wf u = j} ≤ Module.finrank (ResidueField O) (F.Ob (FormData.adRep hbar j)) := by
    haveI : IsCO O (MvPowerSeries W.σ O) := co_mvps O O _
    haveI : IsCO O (MvPowerSeries WB.σ O) := co_mvps O O _
    have hX : ∀ (σ : Type) (s : σ), (MvPowerSeries.X s : MvPowerSeries σ O) ∈ maximalIdeal _ := fun σ s => by
      rw [lp_mem_max]; simp
    set ren : MvPowerSeries WB.σ O →ₐ[O] MvPowerSeries W.σ O := MvPowerSeries.rename fun s => e (.inl s) with hren
    set N : Ideal (MvPowerSeries W.σ O) := (RingHom.ker WB.π).map ren ⊔ maximalIdeal _ * RingHom.ker W.π with hNdef
    have hrp : ∀ j, ∀ x ∈ wtPart O WB.wt j, ren x ∈ wtPart O W.wt j := fun j x hx => by
      obtain ⟨y, hy, hy'⟩ := map_part O X _ (WPres.free O WB.wt) (fun s => hX _ s) _ (WPres.free O W.wt)
        (fun s => hX _ s) ren (fun (s : WB.σ) => ⟨MvPowerSeries.X (e (.inl s)),
          (show _ ∈ wtPart O W.wt (WB.wt s) from q1 s ▸ X_mem_wtPart O W.wt (e (.inl s))),
          (show MvPowerSeries.X (e (.inl s)) = ren (MvPowerSeries.X s) by rw [hren, rename_X])⟩) j x ⟨x, hx, rfl⟩
      have : y = ren x := hy'
      exact this ▸ hy
    have hNh : IsHomog O W.wt N := by
      obtain ⟨n, a, c, ha, ha'⟩ := ker_gen O X _ WB.wt _ WB.homog
      obtain ⟨n', a', c', hb, hb'⟩ := ker_gen O X _ W.wt _ W.homog
      refine lp_homog_sup _ _ _ ?_ ?_
      · rw [ha', Ideal.map_span, ← Set.range_comp, ← Ideal.top_mul (Ideal.span _)]
        exact lp_homog_mul _ _ (fun _ _ _ => Submodule.mem_top) _ c fun u => hrp _ _ (ha u)
      · rw [hb']
        exact lp_homog_mul _ _ (lp_homog_max _) _ c' hb
    have hNK : N ≤ RingHom.ker W.π := sup_le (q4 ▸ le_sup_left) Ideal.mul_le_right
    let π : MvPowerSeries W.σ O →ₐ[O] MvPowerSeries W.σ O ⧸ N := Ideal.Quotient.mkₐ O N
    have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
    have hπ0 : ∀ x, π x = 0 ↔ x ∈ N := fun x => Ideal.Quotient.eq_zero_iff_mem
    let p : (MvPowerSeries W.σ O ⧸ N) →ₐ[O] R := Ideal.Quotient.liftₐ N W.π hNK
    have hpπ : ∀ x, p (π x) = W.π x := fun x => rfl
    haveI : Nontrivial (MvPowerSeries W.σ O ⧸ N) := p.toRingHom.domain_nontrivial
    haveI : IsCO O (MvPowerSeries W.σ O ⧸ N) := co_quot O _ _ π hπ
    let WA : WPres O X (MvPowerSeries W.σ O ⧸ N) :=
      { σ := W.σ, wt := W.wt, π := π, surj := hπ
        homog := fun x hx j => (hπ0 _).2 (hNh x ((hπ0 _).1 hx) j) }
    let iA : B →ₐ[O] (MvPowerSeries W.σ O ⧸ N) := AlgHom.liftOfSurjective WB.π WB.surj (π.comp ren) fun x hx =>
      (hπ0 _).2 (Ideal.mem_sup_left (Ideal.mem_map_of_mem ren hx))
    have hiA : ∀ x, iA (WB.π x) = π (ren x) := fun x => AlgHom.liftOfSurjective_apply _ _ _ _ x
    have hpi : p.comp iA = i := AlgHom.ext fun x => by
      obtain ⟨x, rfl⟩ := WB.surj x
      rw [AlgHom.comp_apply, hiA, hpπ, q2]
    have hp : Function.Surjective p := fun x => by
      obtain ⟨y, rfl⟩ := W.surj x
      exact ⟨π y, rfl⟩
    have hm : maximalIdeal _ * RingHom.ker p = ⊥ := by
      rw [eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      obtain ⟨x, rfl⟩ := hπ x
      obtain ⟨y, rfl⟩ := hπ y
      rw [Ideal.mem_bot, ← map_mul, hπ0]
      exact Ideal.mem_sup_right (Ideal.mul_mem_mul ((lp_loc π x).1 hx) hy)
    have hε0 : ∀ u, p (π (f u)) = 0 := fun u => by
      have : f u ∈ RingHom.ker W.π := q4 ▸ Ideal.mem_sup_right (Ideal.subset_span ⟨u, rfl⟩)
      exact this
    have hkp : RingHom.ker p = Ideal.span (Set.range fun u => π (f u)) := by
      refine le_antisymm (fun y hy => ?_) (Ideal.span_le.2 (by rintro _ ⟨u, rfl⟩; exact hε0 u))
      obtain ⟨y, rfl⟩ := hπ y
      have hy' : y ∈ RingHom.ker W.π := hy
      rw [q4] at hy'
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy'
      rw [map_add, (hπ0 a).2 (Ideal.mem_sup_left ha), zero_add]
      obtain ⟨d, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hb
      rw [map_sum]
      refine Ideal.sum_mem _ fun u _ => ?_
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨u, rfl⟩)
    have hind : ∀ c : κ → O, ∑ u, c u • π (f u) = 0 → ∀ u, c u ∈ maximalIdeal O := fun c hc => by
      refine p3 c ((hπ0 _).1 ?_)
      rw [map_sum]
      simpa only [map_smul] using hc
    have hpart : ∀ j, ∀ x ∈ W₀.part j, x ∈ (WA.part j).map p.toLinearMap := fun j x hx => by
      rw [← p2] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨π y, ⟨y, hy, rfl⟩, rfl⟩
    have hker : RingHom.ker p ≤ (maximalIdeal B).map iA ⊔ maximalIdeal _ ^ 2 := by
      refine lp_ker e iA p π hπ (fun s => ⟨WB.z s, hWB s, ?_⟩) fun c hc => t3 c ?_
      · rw [WPres.z, hiA, rename_X]
      · rw [hpi] at hc
        have : ∀ t, p (π (MvPowerSeries.X (e (.inr t)))) = z t := fun t => (p1 t).1
        simpa only [this] using hc
    obtain ⟨o, ho⟩ := obs_class O ι X w Φ h2 Γ rbar r0 hbar h0 F L hN hL hL0 B ρ hρ _ R p hp hm WA
      (fun s => (lp_loc π _).2 (hX _ s)) κ (fun u => π (f u)) wf (fun u => ⟨f u, q3 u, rfl⟩) hkp hind iA r α
      (hpi ▸ hU.1) (fun v s a b => by
        obtain ⟨y, hy, hy'⟩ := hρw v s a b
        have hy'' : WB.π y = (ρ v).hom s a b := hy'
        rw [← hy'', hiA]
        exact ⟨_, hrp _ _ hy, rfl⟩)
      (fun s a b => hpart _ _ (g3 s a b)) (fun v a b => hpart _ _ (g4 v a b))
    intro j
    haveI := hfin j
    have hli : LinearIndependent (ResidueField O) (o j) := by
      rw [Fintype.linearIndependent_iff]
      intro cb hcb
      choose c hc using fun u => residue_surjective (cb u)
      have h3 := lp_detect iA p hm hker (fun u => π (f u)) hε0 hind
        (fun u => if h : wf u = j then c ⟨u, h⟩ else 0) (by
          intro A' _ _ _ p' p'' η k1 k2 k3 k4 k5
          obtain ⟨r', α', m1, m2, m3⟩ := ho j c (by simpa only [hc] using hcb) A' p' p'' η k1 k2 k3 k4
            (fun u => by rw [k5, dif_pos u.2]) (fun u hu => by rw [k5, dif_neg hu, zero_smul])
          obtain ⟨s, ⟨s1, s2, s3⟩, -⟩ := hU.2 A' _ r' α' m1
          refine ⟨s, ?_, by rw [hpi, s1]⟩
          refine (hU.2 R i r α hU.1).unique ⟨?_, ?_, fun v => ?_⟩ ⟨rfl, rfl, fun v => rfl⟩
          · rw [AlgHom.comp_assoc, s1, ← AlgHom.comp_assoc, k2, hpi]
          · rw [← s2] at m2; exact m2
          · have m4 := m3 v
            rw [← s3 v] at m4; exact m4)
      intro u
      have h4 := h3 u
      rw [dif_pos u.2] at h4
      rw [← hc, residue_eq_zero_iff]
      exact h4
    rw [Nat.card_eq_fintype_card]
    exact hli.fintype_card_le_finrank
  obtain ⟨κ', _, wf', hpad⟩ := lp_pad wf (fun j => Module.finrank (ResidueField O) (F.Ob (FormData.adRep hbar j)))
    (Finset.univ.image fun x : ι × ι => w x.1 - w x.2)
    (fun j hj => lp_ob_zero Φ hbar F j fun a b h => hj (Finset.mem_image.2 ⟨(a, b), Finset.mem_univ _, h⟩)) bound
  refine ⟨R, _, _, inferInstance, i, r, α, W, τ, κ ⊕ κ', inferInstance, inferInstance, e, Sum.elim f fun _ => 0,
    Sum.elim wf wf', hU, ⟨q1, q2, ?_, ?_⟩, fun s a b => p2 _ ▸ g3 s a b, fun v a b => p2 _ ▸ g4 v a b, fun t => ?_,
    fun j => ?_, hpad⟩
  · rintro (u | u)
    · exact q3 u
    · exact zero_mem _
  · rw [q4]
    congr 1
    refine le_antisymm (Ideal.span_mono ?_) (Ideal.span_le.2 ?_)
    · rintro _ ⟨u, rfl⟩
      exact ⟨.inl u, rfl⟩
    · rintro _ ⟨u | u, rfl⟩
      · exact Ideal.subset_span ⟨u, rfl⟩
      · exact zero_mem _
  · rw [(p1 t).1, (p1 t).2]
    exact t1 t
  · simp only [(p1 _).2]
    exact t4 j
