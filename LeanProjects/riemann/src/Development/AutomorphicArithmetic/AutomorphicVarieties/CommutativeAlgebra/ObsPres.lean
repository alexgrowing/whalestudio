import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem op_min {A ι : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Fintype ι]
    (K K0 : Ideal A) (f : ι → A) (h : K = K0 ⊔ Ideal.span (Set.range f)) :
    ∃ s : Finset ι, K = K0 ⊔ Ideal.span (Set.range fun u : s => f u) ∧
      ∀ c : s → A, ∑ u, c u * f u ∈ K0 ⊔ maximalIdeal A * K → ∀ u, c u ∈ maximalIdeal A := by
  classical
  have hex : ∃ n, ∃ s : Finset ι, s.card = n ∧ K = K0 ⊔ Ideal.span (Set.range fun u : s => f u) := by
    refine ⟨_, Finset.univ, rfl, ?_⟩
    rw [h]
    congr 2
    ext x
    simp
  obtain ⟨s, hs, hK⟩ := Nat.find_spec hex
  refine ⟨s, hK, fun c hc u => ?_⟩
  by_contra hu
  have hun : IsUnit (c u) := by
    by_contra h'
    exact hu h'
  obtain ⟨v, hv⟩ := hun
  refine Nat.find_min hex (m := (s.erase u).card) (by rw [← hs]; exact Finset.card_erase_lt_of_mem u.2)
    ⟨s.erase u, rfl, ?_⟩
  set N : Ideal A := K0 ⊔ Ideal.span (Set.range fun w : s.erase u => f w) with hN
  have hmem : ∀ w : s, w ≠ u → f w ∈ N := fun w hw =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨⟨w, Finset.mem_erase.2 ⟨fun e => hw (Subtype.ext e), w.2⟩⟩, rfl⟩)
  have hNK : N ≤ K := by
    rw [hK]
    refine sup_le_sup_left (Ideal.span_mono ?_) _
    rintro _ ⟨w, rfl⟩
    exact ⟨⟨w, Finset.mem_of_mem_erase w.2⟩, rfl⟩
  refine le_antisymm ?_ hNK
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A) (IsNoetherian.noetherian K)
    (maximalIdeal_le_jacobson _) ?_
  have h1 : f u ∈ N ⊔ maximalIdeal A • K := by
    have h2 : ∑ w, c w * f w ∈ N ⊔ maximalIdeal A • K :=
      (sup_le_sup_right (le_sup_left : K0 ≤ N) (maximalIdeal A * K)) hc
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u)] at h2
    have h3 : ∑ w ∈ Finset.univ.erase u, c w * f w ∈ N ⊔ maximalIdeal A • K :=
      Ideal.mem_sup_left (Ideal.sum_mem _ fun w hw =>
        Ideal.mul_mem_left _ _ (hmem w (Finset.mem_erase.1 hw).1))
    have h4 := Ideal.mul_mem_left _ (↑v⁻¹ : A) (sub_mem h2 h3)
    rwa [add_sub_cancel_right, ← hv, Units.inv_mul_cancel_left] at h4
  conv_lhs => rw [hK]
  refine sup_le (le_sup_of_le_left le_sup_left) (Ideal.span_le.2 ?_)
  rintro _ ⟨w, rfl⟩
  by_cases hw : w = u
  · subst hw; exact h1
  · exact Ideal.mem_sup_left (hmem w hw)

private theorem op_mem_max {O σ : Type} [CommRing O] [IsLocalRing O] (x : MvPowerSeries σ O) :
    x ∈ maximalIdeal (MvPowerSeries σ O) ↔ constantCoeff x ∈ maximalIdeal O := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_iff_constantCoeff]

private theorem op_loc {O R R' : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (x : R) :
    f x ∈ maximalIdeal R' ↔ x ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem op_loc_sq {O R R' : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {x : R} (hx : x ∈ maximalIdeal R ^ 2) :
    f x ∈ maximalIdeal R' ^ 2 := by
  have h : (maximalIdeal R).map f ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 fun y hy => (op_loc f y).2 hy
  have := Ideal.mem_map_of_mem f hx
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono h 2 this

private theorem op_taylor {O σ : Type} [CommRing O] [IsLocalRing O] [Fintype σ] (g : MvPowerSeries σ O) :
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
  refine Ideal.mul_mem_mul ?_ ?_ <;> rw [op_mem_max] <;> simp

private theorem op_detect {O B A R κ : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B] [IsCO O B]
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
      rw [← map_mul, hz x ((op_loc p' x).1 hx) _ (by simp [hε]), map_zero])
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
    refine add_mem (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ((op_loc p'' x).2 hx))) ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hker h1)
    rw [map_add]
    refine Submodule.add_mem_sup ?_ (op_loc_sq p' hb)
    have h3 : (maximalIdeal B).map i ≤ ((maximalIdeal R).map s).comap p' :=
      Ideal.map_le_iff_le_comap.2 fun t ht => by
        show p' (i t) ∈ (maximalIdeal R).map s
        have h4 : s (p (i t)) = p' (i t) := DFunLike.congr_fun hs2 t
        rw [← h4]
        exact Ideal.mem_map_of_mem _ ((op_loc p _).2 ((op_loc i _).2 ht))
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

private theorem op_ker {O B A R σ σB τ : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
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
    rw [← op_mem_max, ← op_loc π, ← op_loc p, hx']
    exact zero_mem _
  obtain ⟨c, hc⟩ := op_taylor g
  have key : ∀ (T : Type) [CommRing T] [Algebra O T] [IsCO O T] (q : A →ₐ[O] T),
      q (π g) - ∑ t, c (e (.inr t)) • q (π (X (e (.inr t)))) ∈
        (maximalIdeal B).map (q.comp i) ⊔ maximalIdeal T ^ 2 := by
    intro T _ _ _ q
    have k1 := op_loc_sq (q.comp π) hc
    rw [map_sub, map_sub, AlgHom.commutes, map_sum, ← e.sum_comp, Fintype.sum_sum_type] at k1
    simp only [map_smul, AlgHom.comp_apply] at k1
    have k2 : algebraMap O T (constantCoeff g) ∈ (maximalIdeal B).map (q.comp i) := by
      rw [← (q.comp i).commutes]
      exact Ideal.mem_map_of_mem _ ((op_loc (Algebra.ofId O B) _).2 hg)
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
    refine Ideal.mul_mem_mul ((op_loc (Algebra.ofId O A) _).2 (k5 t)) ((op_loc π _).2 ?_)
    rw [op_mem_max]; simp
  simpa using add_mem k6 (Ideal.mem_sup_right k7)

private theorem op_min_fin {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (K K0 : Ideal A) (h : K0 ≤ K) :
    ∃ (n : ℕ) (f : Fin n → A), K = K0 ⊔ Ideal.span (Set.range f) ∧
      ∀ c : Fin n → A, ∑ u, c u * f u ∈ K0 ⊔ maximalIdeal A * K → ∀ u, c u ∈ maximalIdeal A := by
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian K)
  have hg' : Ideal.span (Set.range g) = K := hg
  obtain ⟨s, hs, hmin⟩ := op_min K K0 g (by rw [hg', sup_eq_right.2 h])
  let e := (Fintype.equivFin s).symm
  refine ⟨_, fun u => g (e u), ?_, fun c hc u => ?_⟩
  · rw [hs]
    congr 2
    exact (e.surjective.range_comp fun u : s => g u).symm
  · have := hmin (fun v => c (e.symm v)) (by
      rw [← e.sum_comp]
      simpa using hc) (e u)
    simpa using this

private theorem op_min_pres (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] :
    ∃ (a : ℕ) (π : MvPowerSeries (Fin a) O →ₐ[O] R), Function.Surjective π ∧
      RingHom.ker π ≤ (maximalIdeal O).map (Algebra.ofId O (MvPowerSeries (Fin a) O)) ⊔ maximalIdeal _ ^ 2 := by
  obtain ⟨a, z, hz, hmin⟩ := op_min_fin (maximalIdeal R) ((maximalIdeal O).map (Algebra.ofId O R))
    (Ideal.map_le_iff_le_comap.2 fun x hx => (op_loc (Algebra.ofId O R) x).2 hx)
  haveI : IsCO O (MvPowerSeries (Fin a) O) := co_mvps O O _
  have hzm : ∀ s, z s ∈ maximalIdeal R := fun s => hz ▸ Ideal.mem_sup_right (Ideal.subset_span ⟨s, rfl⟩)
  obtain ⟨π, ⟨-, hX⟩, -⟩ := co_ev O O R (Fin a) (Algebra.ofId O R) z hzm
  refine ⟨a, π, co_surj O _ R π (le_sup_of_le_left ?_), ?_⟩
  · rw [hz]
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun x hx => ?_) (Ideal.span_le.2 ?_)
    · show algebraMap O R x ∈ (maximalIdeal _).map π
      rw [← π.commutes]
      exact Ideal.mem_map_of_mem _ ((op_loc (Algebra.ofId O _) x).2 hx)
    · rintro _ ⟨s, rfl⟩
      rw [← hX]
      exact Ideal.mem_map_of_mem _ (by rw [op_mem_max]; simp)
  · refine op_ker (Equiv.emptySum Empty (Fin a)) (Algebra.ofId O _) π (AlgHom.id O _) Function.surjective_id
      (fun s => s.elim) fun c hc t => ?_
    rw [← op_loc (Algebra.ofId O R)]
    refine hmin (fun t => algebraMap O R (c t)) ?_ t
    rw [Subsingleton.elim (π.comp _) (Algebra.ofId O R), pow_two] at hc
    simpa [hX, Algebra.smul_def] using hc

private theorem op_count (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R]
    (a : ℕ) (π : MvPowerSeries (Fin a) O →ₐ[O] R) (hπ : Function.Surjective π)
    (hk : RingHom.ker π ≤ (maximalIdeal O).map (Algebra.ofId O (MvPowerSeries (Fin a) O)) ⊔ maximalIdeal _ ^ 2) :
    Nat.card (R →ₐ[O] DualNumber (ResidueField O)) = Nat.card (ResidueField O) ^ a := by
  haveI : IsCO O (MvPowerSeries (Fin a) O) := co_mvps O O _
  haveI : IsCO O (DualNumber (ResidueField O)) := (co_res O).2
  have hm : ∀ x : DualNumber (ResidueField O),
      x ∈ maximalIdeal (DualNumber (ResidueField O)) ↔ x.fst = 0 := fun x => by
    rw [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not]
  have hsq : maximalIdeal (DualNumber (ResidueField O)) ^ 2 ≤ ⊥ := by
    rw [sq, Ideal.mul_le]
    intro x hx y hy
    rw [hm] at hx hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx, hy]
  have hev := fun v : Fin a → ResidueField O => co_ev O O (DualNumber (ResidueField O)) (Fin a) (Algebra.ofId O _)
    (fun s => TrivSqZeroExt.inr (v s)) fun s => (hm _).2 (by simp)
  have hb : Function.Bijective fun (f : R →ₐ[O] DualNumber (ResidueField O)) (s : Fin a) => (f (π (X s))).snd := by
    have hX : ∀ (f : R →ₐ[O] DualNumber (ResidueField O)) (s : Fin a),
        (f.comp π) (X s) = TrivSqZeroExt.inr (f (π (X s))).snd := fun f s => by
      refine TrivSqZeroExt.ext ?_ rfl
      exact (hm _).1 ((op_loc (f.comp π) _).2 (by rw [op_mem_max]; simp))
    refine ⟨fun f g hfg => ?_, fun v => ?_⟩
    · have : f.comp π = g.comp π := (hev fun s => (f (π (X s))).snd).unique
        ⟨fun x => AlgHom.commutes _ x, hX f⟩ ⟨fun x => AlgHom.commutes _ x, fun s => by
          rw [hX g]; exact congrArg _ (congrFun hfg s).symm⟩
      ext1 x
      obtain ⟨x, rfl⟩ := hπ x
      exact DFunLike.congr_fun this x
    · obtain ⟨F, ⟨-, hF⟩, -⟩ := hev v
      have hle : ∀ x ∈ RingHom.ker π, F x = 0 := fun x hx => by
        obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 (hk hx)
        have h1 : F w = 0 := hsq (op_loc_sq F hw)
        have h2 : (maximalIdeal O).map (Algebra.ofId O (MvPowerSeries (Fin a) O)) ≤ RingHom.ker F :=
          Ideal.map_le_iff_le_comap.2 fun c hc => by
            show F (algebraMap O _ c) = 0
            rw [F.commutes, IsScalarTower.algebraMap_apply O (ResidueField O), ResidueField.algebraMap_eq,
              (residue_eq_zero_iff c).2 hc, map_zero]
        rw [map_add, h1, add_zero]
        exact h2 hy
      refine ⟨AlgHom.liftOfSurjective π hπ F hle, funext fun s => ?_⟩
      show (AlgHom.liftOfSurjective π hπ F hle (π (X s))).snd = v s
      exact congrArg TrivSqZeroExt.snd ((AlgHom.liftOfSurjective_apply π hπ F hle _).trans (hF s))
  rw [Nat.card_eq_of_bijective _ hb, Nat.card_fun]
  simp

theorem UpperTheory.V.Alg.obs_pres :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (V : Type) [AddCommGroup V] [Module (ResidueField O) V] [Module.Finite (ResidueField O) V],
      (∀ (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (p : A →ₐ[O] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ →
        ∀ (κ : Type) [Fintype κ] (ε : κ → A), RingHom.ker p = Ideal.span (Set.range ε) → (∀ c : κ → O, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal O) →
        ∃ o : κ → V, ∀ c : κ → O, ∑ u, residue O (c u) • o u = 0 →
          ∀ (A' : Type) [CommRing A'] [Algebra O A'] [IsCO O A'] (p' : A →ₐ[O] A') (p'' : A' →ₐ[O] R) (η : A'), Function.Surjective p' → p''.comp p' = p → (∀ x ∈ maximalIdeal A', x * η = 0) → p'' η = 0 →
            (∀ u, p' (ε u) = c u • η) → ∃ s : R →ₐ[O] A', p''.comp s = AlgHom.id O R) →
      ∃ (a : ℕ) (π : MvPowerSeries (Fin a) O →ₐ[O] R) (f : Fin (Module.finrank (ResidueField O) V) → MvPowerSeries (Fin a) O), Function.Surjective π ∧ RingHom.ker π = Ideal.span (Set.range f) ∧
        Nat.card (R →ₐ[O] DualNumber (ResidueField O)) = Nat.card (ResidueField O) ^ a := by
  intro O _ _ _ _ _ R _ _ _ V _ _ _ H
  classical
  obtain ⟨a, π₀, hπ₀, hk⟩ := op_min_pres O R
  haveI : IsCO O (MvPowerSeries (Fin a) O) := co_mvps O O _
  obtain ⟨n, f, hf, hmin⟩ := op_min_fin (RingHom.ker π₀) ⊥ bot_le
  rw [bot_sup_eq] at hf hmin
  have bound : n ≤ Module.finrank (ResidueField O) V := by
    set N : Ideal (MvPowerSeries (Fin a) O) := maximalIdeal _ * RingHom.ker π₀ with hNdef
    have hNK : N ≤ RingHom.ker π₀ := Ideal.mul_le_right
    let π : MvPowerSeries (Fin a) O →ₐ[O] MvPowerSeries (Fin a) O ⧸ N := Ideal.Quotient.mkₐ O N
    have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
    have hπ0 : ∀ x, π x = 0 ↔ x ∈ N := fun x => Ideal.Quotient.eq_zero_iff_mem
    let p : (MvPowerSeries (Fin a) O ⧸ N) →ₐ[O] R := Ideal.Quotient.liftₐ N π₀ hNK
    have hpπ : ∀ x, p (π x) = π₀ x := fun x => rfl
    haveI : Nontrivial (MvPowerSeries (Fin a) O ⧸ N) := p.toRingHom.domain_nontrivial
    haveI : IsCO O (MvPowerSeries (Fin a) O ⧸ N) := co_quot O _ _ π hπ
    have hp : Function.Surjective p := fun x => by
      obtain ⟨y, rfl⟩ := hπ₀ x
      exact ⟨π y, rfl⟩
    have hm : maximalIdeal _ * RingHom.ker p = ⊥ := by
      rw [eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      obtain ⟨x, rfl⟩ := hπ x
      obtain ⟨y, rfl⟩ := hπ y
      rw [Ideal.mem_bot, ← map_mul, hπ0]
      exact Ideal.mul_mem_mul ((op_loc π x).1 hx) hy
    have hε0 : ∀ u, p (π (f u)) = 0 := fun u => by
      have : f u ∈ RingHom.ker π₀ := hf ▸ Ideal.subset_span ⟨u, rfl⟩
      exact this
    have hkp : RingHom.ker p = Ideal.span (Set.range fun u => π (f u)) := by
      refine le_antisymm (fun y hy => ?_) (Ideal.span_le.2 (by rintro _ ⟨u, rfl⟩; exact hε0 u))
      obtain ⟨y, rfl⟩ := hπ y
      have hy' : y ∈ RingHom.ker π₀ := hy
      rw [hf] at hy'
      obtain ⟨d, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hy'
      rw [map_sum]
      refine Ideal.sum_mem _ fun u _ => ?_
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨u, rfl⟩)
    have hind : ∀ c : Fin n → O, ∑ u, c u • π (f u) = 0 → ∀ u, c u ∈ maximalIdeal O := fun c hc u => by
      rw [← op_loc (Algebra.ofId O (MvPowerSeries (Fin a) O))]
      refine hmin (fun u => algebraMap O _ (c u)) ((hπ0 _).1 ?_) u
      rw [map_sum]
      simpa only [← Algebra.smul_def, map_smul] using hc
    have hker : RingHom.ker p ≤ (maximalIdeal O).map (Algebra.ofId O _) ⊔ maximalIdeal _ ^ 2 := by
      intro x hx
      obtain ⟨x, rfl⟩ := hπ x
      obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 (hk hx)
      rw [map_add]
      refine Submodule.add_mem_sup ?_ (op_loc_sq π hw)
      have h2 : (maximalIdeal O).map (Algebra.ofId O (MvPowerSeries (Fin a) O)) ≤
          ((maximalIdeal O).map (Algebra.ofId O (MvPowerSeries (Fin a) O ⧸ N))).comap π :=
        Ideal.map_le_iff_le_comap.2 fun c hc => Ideal.mem_map_of_mem (Algebra.ofId O _) hc
      exact h2 hy
    obtain ⟨o, ho⟩ := H _ p hp hm (Fin n) (fun u => π (f u)) hkp hind
    have hli : LinearIndependent (ResidueField O) o := by
      rw [Fintype.linearIndependent_iff]
      intro cb hcb
      choose c hc using fun u => residue_surjective (cb u)
      have h3 := op_detect (Algebra.ofId O _) p hm hker (fun u => π (f u)) hε0 hind c (by
        intro A' _ _ _ p' p'' η k1 k2 k3 k4 k5
        obtain ⟨s, hs⟩ := ho c (by simpa only [hc] using hcb) A' p' p'' η k1 k2 k3 k4 k5
        exact ⟨s, hs, Subsingleton.elim _ _⟩)
      intro u
      rw [← hc, residue_eq_zero_iff]
      exact h3 u
    simpa using hli.fintype_card_le_finrank
  refine ⟨a, π₀, fun u => if h : u.1 < n then f ⟨u, h⟩ else 0, hπ₀, ?_, op_count O R a π₀ hπ₀ hk⟩
  rw [hf]
  refine le_antisymm (Ideal.span_mono ?_) (Ideal.span_le.2 ?_)
  · rintro _ ⟨u, rfl⟩
    exact ⟨⟨u, u.2.trans_le bound⟩, dif_pos u.2⟩
  · rintro _ ⟨u, rfl⟩
    by_cases h : u.1 < n
    · simp only [dif_pos h]
      exact Ideal.subset_span ⟨_, rfl⟩
    · simp only [dif_neg h]
      exact zero_mem _
