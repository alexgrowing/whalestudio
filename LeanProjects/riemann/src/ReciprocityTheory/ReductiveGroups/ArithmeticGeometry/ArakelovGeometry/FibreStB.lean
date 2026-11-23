import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.FibreStA

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}

structure Gen.Good (G : Gen x e) (w : Fin (D + 1) → ℂ) : Prop where
  w0 : w 0 ≠ 0
  ker : ∀ m, deh (x ∘ e) 0 m = 0 → deh w 0 m = 0
  dd : deh w 0 G.dd ≠ 0
  cc : deh w 0 G.cc ≠ 0

theorem deh_eval₂_rename {S : Type*} [Field S] (v : ι → S) (e : Fin (D + 1) → ι)
    (Θ : MvPolynomial ι ℤ) (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)) :
    deh v (e 0) (H.eval₂ (rename e : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial ι ℤ).toRingHom Θ) =
      H.eval₂ (deh (v ∘ e) 0) (deh v (e 0) Θ) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [deh_apply]
  · intro i
    simp [deh_apply]

variable [DecidableEq ι] (G : Gen x e) {w : Fin (D + 1) → ℂ}

private theorem eval₂_deh_eq_zero_of_good_of_root (hw : G.Good w) {ρ : ℂ} (hρ : G.P.eval₂ (deh w 0) ρ = 0)
    (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ))
    (hH : H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0) : H.eval₂ (deh w 0) ρ = 0 := by
  have hP1 : G.P ≠ 1 := by
    intro h
    have h' := G.root
    rw [h, Polynomial.eval₂_one] at h'
    exact one_ne_zero h'
  have hsplit : H %ₘ G.P + G.P * (H /ₘ G.P) = H := by
    first
    | exact Polynomial.modByMonic_add_div H G.P
    | exact Polynomial.modByMonic_add_div H G.monic
  have hdeg : (H %ₘ G.P).natDegree < G.P.natDegree := by
    first
    | exact Polynomial.natDegree_modByMonic_lt H G.monic hP1
    | exact Polynomial.natDegree_modByMonic_lt H G.monic hP1
  have hrx : (H %ₘ G.P).eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0 := by
    have h2 := congrArg (fun p => p.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) hsplit
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, G.root, zero_mul, add_zero, hH] at h2
    exact h2
  have hc := G.min _ hdeg hrx
  have hrw : (H %ₘ G.P).map (deh w 0) = 0 := by
    ext j
    rw [Polynomial.coeff_map, hw.ker _ (hc j), Polynomial.coeff_zero]
  have hr : (H %ₘ G.P).eval₂ (deh w 0) ρ = 0 := by
    rw [← Polynomial.eval_map, hrw, Polynomial.eval_zero]
  have h3 := congrArg (fun p => p.eval₂ (deh w 0) ρ) hsplit
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, hr, hρ, zero_mul, add_zero] at h3
  exact h3.symm

theorem Gen.zOf_e (hw : G.Good w) {ρ : ℂ} (hρ : G.P.eval₂ (deh w 0) ρ = 0) (k : Fin (D + 1)) :
    G.zOf w ρ (e k) = w k := by
  have hH := eval₂_deh_eq_zero_of_good_of_root G hw hρ (G.Q (e k) - Polynomial.C (G.dd * X k)) (by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, ← G.hQ (e k), map_mul, sub_eq_zero, deh_X, deh_X]
    rfl)
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, map_mul, deh_X, sub_eq_zero] at hH
  have h0 := hw.w0
  have h1 := hw.dd
  simp only [Gen.zOf, Gen.evQ]
  rw [hH]
  first
  | (field_simp; done)
  | (field_simp; ring)

theorem Gen.deh_zOf (hw : G.Good w) {ρ : ℂ} (hρ : G.P.eval₂ (deh w 0) ρ = 0)
    (F : MvPolynomial ι ℤ) :
    deh (G.zOf w ρ) (e 0) F = MvPolynomial.eval₂ (Int.castRingHom ℂ) (G.evQ (deh w 0) ρ) F := by
  have h0 := hw.w0
  rw [deh_apply, G.zOf_e hw hρ 0]
  congr 1
  funext i
  simp only [Gen.zOf]
  first
  | (field_simp; done)
  | (field_simp; ring)

private theorem map_eval₂_X_mul_C_eq {K : Type*} [Field K] (φ : MvPolynomial (Fin (D + 1)) ℤ →+* K) (t : K)
    (f : MvPolynomial ι ℤ) :
    (MvPolynomial.eval₂ (Int.castRingHom (Polynomial (Polynomial (MvPolynomial (Fin (D + 1)) ℤ))))
        (fun i => Polynomial.X * Polynomial.C (G.Q i)) f).map (Polynomial.eval₂RingHom φ t) =
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial K))
        (fun i => Polynomial.X * Polynomial.C ((G.Q i).eval₂ φ t)) f := by
  have hk := MvPolynomial.eval₂_comp_left (Polynomial.mapRingHom (Polynomial.eval₂RingHom φ t))
    (Int.castRingHom _) (fun i => Polynomial.X * Polynomial.C (G.Q i)) f
  first
  | rw [Polynomial.coe_mapRingHom] at hk
  | skip
  rw [hk]
  congr 1
  · exact RingHom.ext_int _ _
  · funext i
    simp [Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C, Polynomial.coe_eval₂RingHom]

theorem Gen.zOf_mem (hx0 : x (e 0) ≠ 0) (hw : G.Good w) {ρ : ℂ}
    (hρ : G.P.eval₂ (deh w 0) ρ = 0) : G.zOf w ρ ∈ pts (coordIdeal ℤ x) := by
  show G.zOf w ρ ≠ 0 ∧ ∀ f ∈ coordIdeal ℤ x,
    MvPolynomial.eval (G.zOf w ρ) (MvPolynomial.map (Int.castRingHom ℂ) f) = 0
  refine ⟨fun h => hw.w0 ?_, fun f hf => ?_⟩
  · rw [← G.zOf_e hw hρ 0, h, Pi.zero_apply]
  have hcone := RingHom.mem_ker.mp (show f ∈ RingHom.ker (coneMap ℤ x) from hf)
  have hrel : MvPolynomial.eval₂ (Int.castRingHom (Polynomial Ω))
      (fun i => Polynomial.X * Polynomial.C ((G.Q i).eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ))) f =
      ((coneMap ℤ x) f).comp (Polynomial.C (deh (x ∘ e) 0 G.dd * (x (e 0))⁻¹) * Polynomial.X) := by
    have hk := MvPolynomial.eval₂_comp_left
      (Polynomial.compRingHom (Polynomial.C (deh (x ∘ e) 0 G.dd * (x (e 0))⁻¹) * Polynomial.X))
      (algebraMap ℤ (Polynomial Ω)) (fun i => Polynomial.C (x i) * Polynomial.X) f
    rw [coneMap, MvPolynomial.aeval_def, ← Polynomial.coe_compRingHom_apply, hk]
    congr 1
    · exact RingHom.ext_int _ _
    · funext i
      simp only [Function.comp_apply, Polynomial.coe_compRingHom_apply, Polynomial.mul_comp,
        Polynomial.C_comp, Polynomial.X_comp, ← G.hQ i, deh_X, div_eq_mul_inv, map_mul]
      ring
  have h2 := map_eval₂_X_mul_C_eq G (deh (x ∘ e) 0) (deh x (e 0) G.Θ) f
  rw [hrel, hcone, Polynomial.zero_comp] at h2
  have h3 : (MvPolynomial.eval₂ (Int.castRingHom (Polynomial (Polynomial (MvPolynomial (Fin (D + 1)) ℤ))))
        (fun i => Polynomial.X * Polynomial.C (G.Q i)) f).map (Polynomial.eval₂RingHom (deh w 0) ρ) = 0 := by
    ext d
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.coe_eval₂RingHom]
    apply eval₂_deh_eq_zero_of_good_of_root G hw hρ
    have h4 := Polynomial.ext_iff.mp h2 d
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.coe_eval₂RingHom] at h4
    exact h4
  rw [map_eval₂_X_mul_C_eq G (deh w 0) ρ f] at h3
  rw [MvPolynomial.eval_map]
  have h4 := congrArg (Polynomial.eval (w 0 / deh w 0 G.dd)) h3
  rw [Polynomial.eval_zero, ← Polynomial.coe_evalRingHom, MvPolynomial.eval₂_comp_left] at h4
  have e1 : (Polynomial.evalRingHom (w 0 / deh w 0 G.dd)).comp (Int.castRingHom (Polynomial ℂ)) =
      Int.castRingHom ℂ := RingHom.ext_int _ _
  have e2 : (⇑(Polynomial.evalRingHom (w 0 / deh w 0 G.dd)) ∘
      fun i => Polynomial.X * Polynomial.C ((G.Q i).eval₂ (deh w 0) ρ)) = G.zOf w ρ := by
    funext i
    simp only [Function.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, Gen.zOf, Gen.evQ]
    ring
  rw [e1, e2] at h4
  exact h4

private theorem sum_coeff_homogenize_eq_pow_mul_eval₂ {S : Type*} [Field S] (F : MvPolynomial ι ℤ) (v a : ι → S) (d : S)
    (hv : ∀ i, v i = a i / d) (hd : d ≠ 0) (N : ℕ) (hN : F.totalDegree ≤ N) :
    ∑ m ∈ F.support, ((MvPolynomial.coeff m F : ℤ) : S) * d ^ (N - ∑ i ∈ m.support, m i) *
      ∏ i ∈ m.support, a i ^ m i = d ^ N * MvPolynomial.eval₂ (Int.castRingHom S) v F := by
  rw [MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hs : ∑ i ∈ m.support, m i ≤ N := (MvPolynomial.le_totalDegree hm).trans hN
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  simp only [hv, div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, eq_intCast,
    Nat.add_sub_cancel_left, pow_add]
  first
  | (field_simp; done)
  | (field_simp; ring)
  | ring

private theorem map_homogenized_sub_dd_pow_X_eq {S : Type*} [Field S] (φ : MvPolynomial (Fin (D + 1)) ℤ →+* S) (t : S)
    (hd : φ G.dd ≠ 0) :
    Polynomial.eval₂ φ t ((∑ m ∈ G.Θ.support, Polynomial.C (MvPolynomial.C (MvPolynomial.coeff m G.Θ) *
        G.dd ^ (G.Θ.totalDegree - ∑ i ∈ m.support, m i)) * ∏ i ∈ m.support, G.Q i ^ m i) -
      Polynomial.C (G.dd ^ G.Θ.totalDegree) * Polynomial.X) =
      φ G.dd ^ G.Θ.totalDegree * (MvPolynomial.eval₂ (Int.castRingHom S) (G.evQ φ t) G.Θ - t) := by
  have hC : ∀ c : ℤ, φ (MvPolynomial.C c) = (c : S) := fun c => eq_intCast (φ.comp MvPolynomial.C) c
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.eval₂_finset_prod, Polynomial.eval₂_pow, map_mul, map_pow, hC]
  rw [mul_sub, ← sum_coeff_homogenize_eq_pow_mul_eval₂ G.Θ (G.evQ φ t) (fun i => (G.Q i).eval₂ φ t) (φ G.dd) (fun i => rfl) hd
    G.Θ.totalDegree le_rfl]

theorem Gen.deh_zOf_Θ (hw : G.Good w) {ρ : ℂ} (hρ : G.P.eval₂ (deh w 0) ρ = 0) :
    deh (G.zOf w ρ) (e 0) G.Θ = ρ := by
  have hx := map_homogenized_sub_dd_pow_X_eq G (deh (x ∘ e) 0) (deh x (e 0) G.Θ) G.dd_ne
  have hQx : MvPolynomial.eval₂ (Int.castRingHom Ω) (G.evQ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) G.Θ =
      deh x (e 0) G.Θ := by
    conv_rhs => rw [deh_apply]
    congr 1
    funext i
    simp only [Gen.evQ]
    rw [← G.hQ i, deh_X]
    first
    | exact mul_div_cancel_left₀ _ G.dd_ne
    | field_simp [G.dd_ne]
  rw [hQx, sub_self, mul_zero] at hx
  have hw' := eval₂_deh_eq_zero_of_good_of_root G hw hρ _ hx
  rw [map_homogenized_sub_dd_pow_X_eq G (deh w 0) ρ hw.dd] at hw'
  have h2 := (mul_eq_zero.mp hw').resolve_left (pow_ne_zero _ hw.dd)
  rw [G.deh_zOf hw hρ]
  exact sub_eq_zero.mp h2

private theorem deh_eq_zero_of_mem_pts_of_deh_eq_zero (hx0 : x (e 0) ≠ 0) (F : MvPolynomial ι ℤ) (hF : deh x (e 0) F = 0)
    {z : ι → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) (hz0 : z (e 0) ≠ 0) : deh z (e 0) F = 0 := by
  have hz' : z ≠ 0 ∧ ∀ f ∈ coordIdeal ℤ x,
      MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0 := hz
  have hmem : (∑ m ∈ F.support, MvPolynomial.C (MvPolynomial.coeff m F) *
      X (e 0) ^ (F.totalDegree - ∑ i ∈ m.support, m i) * ∏ i ∈ m.support, X i ^ m i) ∈ coordIdeal ℤ x := by
    show _ ∈ RingHom.ker (coneMap ℤ x)
    rw [RingHom.mem_ker, coneMap, map_sum]
    have h1 : ∀ m ∈ F.support, (aeval fun i => Polynomial.C (x i) * Polynomial.X)
        (MvPolynomial.C (MvPolynomial.coeff m F) * X (e 0) ^ (F.totalDegree - ∑ i ∈ m.support, m i) *
          ∏ i ∈ m.support, X i ^ m i) =
        Polynomial.C (((MvPolynomial.coeff m F : ℤ) : Ω) * x (e 0) ^ (F.totalDegree - ∑ i ∈ m.support, m i) *
          ∏ i ∈ m.support, x i ^ m i) * Polynomial.X ^ F.totalDegree := by
      intro m hm
      have hs : ∑ i ∈ m.support, m i ≤ F.totalDegree := MvPolynomial.le_totalDegree hm
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
      rw [hk, Nat.add_sub_cancel_left]
      simp only [map_mul, map_pow, map_prod, MvPolynomial.aeval_C, MvPolynomial.aeval_X, mul_pow,
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, algebraMap_int_eq, eq_intCast, map_intCast]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← map_sum Polynomial.C,
      sum_coeff_homogenize_eq_pow_mul_eval₂ F (fun i => x i / x (e 0)) x (x (e 0)) (fun i => rfl) hx0 _ le_rfl, ← deh_apply, hF,
      mul_zero, map_zero, zero_mul]
  have h2 := hz'.2 _ hmem
  rw [MvPolynomial.eval_map] at h2
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_prod, Int.coe_castRingHom] at h2
  rw [sum_coeff_homogenize_eq_pow_mul_eval₂ F (fun i => z i / z (e 0)) z (z (e 0)) (fun i => rfl) hz0 _ le_rfl, ← deh_apply] at h2
  exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ hz0)

private theorem deh_rename' {S : Type*} [Field S] (v : ι → S) (F : MvPolynomial (Fin (D + 1)) ℤ) :
    deh v (e 0) (rename e F) = deh (v ∘ e) 0 F := by
  rw [deh_apply, deh_apply, MvPolynomial.eval₂_rename]
  rfl

theorem Gen.of_mem (hx0 : x (e 0) ≠ 0) (hw : G.Good w) {z : ι → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) (hze : ∀ k, z (e k) = w k) :
    G.P.eval₂ (deh w 0) (deh z (e 0) G.Θ) = 0 ∧ G.zOf w (deh z (e 0) G.Θ) = z := by
  have hz0 : z (e 0) ≠ 0 := by
    rw [hze 0]
    exact hw.w0
  have hze' : z ∘ e = w := funext hze
  constructor
  · have h := deh_eq_zero_of_mem_pts_of_deh_eq_zero hx0
      (G.P.eval₂ (rename e : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial ι ℤ).toRingHom G.Θ)
      (by rw [deh_eval₂_rename]; exact G.root) hz hz0
    rw [deh_eval₂_rename, hze'] at h
    exact h
  · funext i
    have h := deh_eq_zero_of_mem_pts_of_deh_eq_zero hx0
      ((G.Q i).eval₂ (rename e : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial ι ℤ).toRingHom G.Θ -
        rename e G.dd * X i)
      (by rw [map_sub, deh_eval₂_rename, map_mul, deh_rename', ← G.hQ i, sub_self]) hz hz0
    rw [map_sub, deh_eval₂_rename, map_mul, deh_rename', hze', deh_X, sub_eq_zero] at h
    have h0 := hw.w0
    have h1 := hw.dd
    simp only [Gen.zOf, Gen.evQ]
    rw [h, hze 0]
    first
    | (field_simp; done)
    | (field_simp; ring)

theorem Gen.sep (hw : G.Good w) : (G.P.map (deh w 0)).Separable := by
  have h0 : (G.U * G.P + G.V * Polynomial.derivative G.P - Polynomial.C G.cc).map (deh w 0) = 0 := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    apply hw.ker
    rw [← Polynomial.coeff_map, G.hUV, Polynomial.coeff_zero]
  have h1 : G.U.map (deh w 0) * G.P.map (deh w 0) +
      G.V.map (deh w 0) * Polynomial.derivative (G.P.map (deh w 0)) =
      Polynomial.C (deh w 0 G.cc) := by
    rw [Polynomial.derivative_map, ← sub_eq_zero, ← h0]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
  rw [Polynomial.separable_def]
  refine ⟨Polynomial.C (deh w 0 G.cc)⁻¹ * G.U.map (deh w 0),
    Polynomial.C (deh w 0 G.cc)⁻¹ * G.V.map (deh w 0), ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, h1, ← Polynomial.C_mul, inv_mul_cancel₀ hw.cc, Polynomial.C_1]

theorem Gen.mem_roots {ρ : ℂ} :
    ρ ∈ (G.P.map (deh w 0)).roots ↔ G.P.eval₂ (deh w 0) ρ = 0 := by
  rw [Polynomial.mem_roots (G.monic.map _).ne_zero, Polynomial.IsRoot.def, Polynomial.eval_map]

theorem Gen.card_roots : (G.P.map (deh w 0)).roots.card = G.P.natDegree := by
  have hd : (G.P.map (deh w 0)).natDegree = G.P.natDegree := by
    first
    | exact G.monic.natDegree_map _
    | exact Polynomial.natDegree_map_of_monic G.monic _
  rw [← hd]
  first
  | exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
  | exact IsAlgClosed.card_roots_eq_natDegree
  | exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits _)).symm
  | simp

abbrev fib (x : ι → Ω) (e : Fin (D + 1) → ι) (w : Fin (D + 1) → ℂ) : Set (ι → ℂ) :=
  {z | z ∈ pts (coordIdeal ℤ x) ∧ ∀ k, z (e k) = w k}

theorem Gen.fib_eq (hx0 : x (e 0) ≠ 0) (hw : G.Good w) :
    fib x e w = G.zOf w '' {ρ | ρ ∈ (G.P.map (deh w 0)).roots} := by
  ext z
  constructor
  · rintro ⟨hz, hze⟩
    obtain ⟨h1, h2⟩ := G.of_mem hx0 hw hz hze
    exact ⟨_, G.mem_roots.2 h1, h2⟩
  · rintro ⟨ρ, hρ, rfl⟩
    have hρ' := G.mem_roots.1 hρ
    exact ⟨G.zOf_mem hx0 hw hρ', G.zOf_e hw hρ'⟩

theorem Gen.injOn (hw : G.Good w) :
    Set.InjOn (G.zOf w) {ρ | ρ ∈ (G.P.map (deh w 0)).roots} := by
  intro ρ₁ h₁ ρ₂ h₂ h
  calc ρ₁ = deh (G.zOf w ρ₁) (e 0) G.Θ := (G.deh_zOf_Θ hw (G.mem_roots.1 h₁)).symm
    _ = deh (G.zOf w ρ₂) (e 0) G.Θ := by rw [h]
    _ = ρ₂ := G.deh_zOf_Θ hw (G.mem_roots.1 h₂)

theorem Gen.roots_set (w : Fin (D + 1) → ℂ) :
    {ρ | ρ ∈ (G.P.map (deh w 0)).roots} = ((G.P.map (deh w 0)).roots.toFinset : Set ℂ) := by
  ext ρ
  simp

theorem Gen.fib_finite (hx0 : x (e 0) ≠ 0) (hw : G.Good w) : (fib x e w).Finite := by
  rw [G.fib_eq hx0 hw, G.roots_set]
  exact (Finset.finite_toSet _).image _

theorem Gen.fib_ncard (hx0 : x (e 0) ≠ 0) (hw : G.Good w) :
    (fib x e w).ncard = G.P.natDegree := by
  rw [G.fib_eq hx0 hw, Set.ncard_image_of_injOn (G.injOn hw), G.roots_set, Set.ncard_coe_finset,
    Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots (G.sep hw)), G.card_roots]

theorem Gen.finsum_fib (hx0 : x (e 0) ≠ 0) (hw : G.Good w) (f : (ι → ℂ) → ℂ) :
    ∑ᶠ z ∈ fib x e w, f z = ((G.P.map (deh w 0)).roots.map fun ρ => f (G.zOf w ρ)).sum := by
  rw [G.fib_eq hx0 hw, finsum_mem_image (G.injOn hw), G.roots_set, finsum_mem_coe_finset,
    Finset.sum_eq_multiset_sum, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr (Polynomial.nodup_roots (G.sep hw))]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem exists_implicit_section {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (f : E × ℂ → ℂ) (u : E × ℂ) (hf : ContDiffAt ℂ 1 f u) {c : ℂ} (hc : c ≠ 0)
    (hd : HasDerivAt (fun t => f (u.1, t)) c u.2) :
    ∃ (U : Set E) (τ : E → ℂ), IsOpen U ∧ u.1 ∈ U ∧ DifferentiableOn ℂ τ U ∧ τ u.1 = u.2 ∧
      ∀ w ∈ U, f (w, τ w) = f u := by
  have hfd : HasFDerivAt f (fderiv ℂ f u) u := (hf.differentiableAt one_ne_zero).hasFDerivAt
  have hi : HasFDerivAt (fun t : ℂ => (u.1, t)) (ContinuousLinearMap.inr ℂ E ℂ) u.2 := by
    first
    | exact hasFDerivAt_prodMk_right u.1 u.2
    | exact hasFDerivAt_prod_mk_right u.1 u.2
    | exact (hasFDerivAt_const u.1 u.2).prodMk (hasFDerivAt_id u.2)
    | exact (hasFDerivAt_const u.1 u.2).prod (hasFDerivAt_id u.2)
  have hcomp : HasFDerivAt (fun t : ℂ => f (u.1, t))
      ((fderiv ℂ f u).comp (ContinuousLinearMap.inr ℂ E ℂ)) u.2 := by
    have hfd' : HasFDerivAt f (fderiv ℂ f u) (u.1, u.2) := hfd
    exact hfd'.comp u.2 hi
  have heq : (fderiv ℂ f u).comp (ContinuousLinearMap.inr ℂ E ℂ) =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c := hcomp.unique hd.hasFDerivAt
  have hinv : ((fderiv ℂ f u).comp (ContinuousLinearMap.inr ℂ E ℂ)).IsInvertible := by
    rw [heq]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 c hc), ?_⟩
    first
    | (ext; simp)
    | (ext x; simp [mul_comm])
  have ev := IsContDiffImplicitAt.apply_implicitFunction hf one_ne_zero hinv
  have cd := IsContDiffImplicitAt.contDiffAt_implicitFunction hf one_ne_zero hinv
  have ev2 := IsContDiffImplicitAt.eventually_implicitFunction_apply_eq hf one_ne_zero hinv
  have hval : hf.implicitFunction one_ne_zero hinv u.1 = u.2 := (ev2.self_of_nhds).1 rfl
  have ecd : ∀ᶠ y in 𝓝 u.1, ContDiffAt ℂ 1 (hf.implicitFunction one_ne_zero hinv) y := by
    first
    | exact cd.eventually (by simp)
    | exact cd.eventually (by decide)
    | exact cd.eventually ENat.one_ne_top
  obtain ⟨U, hUsub, hUo, hUmem⟩ := eventually_nhds_iff.mp (ev.and ecd)
  exact ⟨U, hf.implicitFunction one_ne_zero hinv, hUo, hUmem,
    fun y hy => ((hUsub y hy).2.differentiableAt one_ne_zero).differentiableWithinAt, hval,
    fun y hy => (hUsub y hy).1⟩

theorem contDiffAt_eval₂ {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ι → ℂ) (e₀ : E) (hg : ∀ i, ContDiffAt ℂ 1 (fun e => g e i) e₀)
    (G : MvPolynomial ι ℤ) : ContDiffAt ℂ 1 (fun e => eval₂ (Int.castRingHom ℂ) (g e) G) e₀ := by
  induction G using MvPolynomial.induction_on
  next r =>
    simp only [eval₂_C]
    exact contDiffAt_const
  next p q hp hq =>
    simp only [eval₂_add]
    exact hp.add hq
  next p i hp =>
    simp only [eval₂_mul, eval₂_X]
    exact hp.mul (hg i)

theorem contDiffAt_deh {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ι → ℂ) (e₀ : E) (i₀ : ι) (hg : ∀ i, ContDiffAt ℂ 1 (fun e => g e i) e₀)
    (h0 : g e₀ i₀ ≠ 0) (G : MvPolynomial ι ℤ) : ContDiffAt ℂ 1 (fun e => deh (g e) i₀ G) e₀ := by
  simp only [deh_apply]
  exact contDiffAt_eval₂ (fun e i => g e i / g e i₀) e₀ (fun i => (hg i).div (hg i₀) h0) G

theorem contDiffAt_eval₂_deh {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ι → ℂ) (t : E → ℂ) (e₀ : E) (i₀ : ι) (hg : ∀ i, ContDiffAt ℂ 1 (fun e => g e i) e₀)
    (ht : ContDiffAt ℂ 1 t e₀) (h0 : g e₀ i₀ ≠ 0) (H : Polynomial (MvPolynomial ι ℤ)) :
    ContDiffAt ℂ 1 (fun e => H.eval₂ (deh (g e) i₀) (t e)) e₀ := by
  refine Polynomial.induction_on' H (fun p q hp hq => ?_) (fun n a => ?_)
  · simp only [Polynomial.eval₂_add]
    exact hp.add hq
  · simp only [Polynomial.eval₂_monomial]
    exact (contDiffAt_deh g e₀ i₀ hg h0 a).mul (ht.pow n)

theorem differentiableAt_eval₂_deh {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ι → ℂ) (t : E → ℂ) (e₀ : E) (i₀ : ι) (hg : ∀ i, ContDiffAt ℂ 1 (fun e => g e i) e₀)
    (ht : DifferentiableAt ℂ t e₀) (h0 : g e₀ i₀ ≠ 0) (H : Polynomial (MvPolynomial ι ℤ)) :
    DifferentiableAt ℂ (fun e => H.eval₂ (deh (g e) i₀) (t e)) e₀ := by
  refine Polynomial.induction_on' H (fun p q hp hq => ?_) (fun n a => ?_)
  · simp only [Polynomial.eval₂_add]
    exact hp.add hq
  · simp only [Polynomial.eval₂_monomial]
    exact ((contDiffAt_deh g e₀ i₀ hg h0 a).differentiableAt one_ne_zero).mul (ht.pow n)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω}
  {e : Fin (D + 1) → ι} (G : Gen x e)

theorem Gen.exists_section (hx0 : x (e 0) ≠ 0) {W : Set (Fin (D + 1) → ℂ)} (hWo : IsOpen W)
    (hgood : ∀ w ∈ W, G.Good w) {w : Fin (D + 1) → ℂ} (hw : w ∈ W) {z : ι → ℂ}
    (hz : z ∈ fib x e w) :
    ∃ (U : Set (Fin (D + 1) → ℂ)) (γ : (Fin (D + 1) → ℂ) → ι → ℂ),
      IsOpen U ∧ w ∈ U ∧ DifferentiableOn ℂ γ U ∧ γ w = z ∧ ∀ w' ∈ U, γ w' ∈ fib x e w' := by
  have hgw := hgood w hw
  obtain ⟨hroot, hzeq⟩ := G.of_mem hx0 hgw hz.1 hz.2
  generalize hρ : deh z (e 0) G.Θ = ρ at hroot hzeq
  have hp1 : ∀ i, ContDiffAt ℂ 1 (fun p : (Fin (D + 1) → ℂ) × ℂ => p.1 i) (w, ρ) := by
    intro i
    first
    | fun_prop
    | exact ((contDiff_apply ℂ ℂ i).comp contDiff_fst).contDiffAt
    | exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (D + 1) => ℂ) i).comp
        (ContinuousLinearMap.fst ℂ (Fin (D + 1) → ℂ) ℂ)).contDiff.contDiffAt
  have hcd : ContDiffAt ℂ 1 (fun p : (Fin (D + 1) → ℂ) × ℂ => G.P.eval₂ (deh p.1 0) p.2) (w, ρ) :=
    contDiffAt_eval₂_deh (fun p : (Fin (D + 1) → ℂ) × ℂ => p.1) (fun p => p.2) (w, ρ) 0 hp1
      contDiffAt_snd hgw.w0 G.P
  have hd0 := (G.P.map (deh w 0)).hasDerivAt ρ
  simp only [Polynomial.eval_map] at hd0
  have hsep := G.sep hgw
  rw [Polynomial.separable_def] at hsep
  obtain ⟨a, b, hab⟩ := hsep
  have hev := congrArg (Polynomial.eval ρ) hab
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_one,
    Polynomial.eval_map, hroot, mul_zero, zero_add] at hev
  have hc : Polynomial.eval ρ (Polynomial.derivative (G.P.map (deh w 0))) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hev
    exact zero_ne_one hev
  obtain ⟨U', τ, hU'o, hwU', hτd, hτw, hτf⟩ :=
    exists_implicit_section (fun p : (Fin (D + 1) → ℂ) × ℂ => G.P.eval₂ (deh p.1 0) p.2) (w, ρ) hcd hc hd0
  have hτw' : τ w = ρ := hτw
  have hproj : ∀ (v : Fin (D + 1) → ℂ) j, ContDiffAt ℂ 1 (fun u : Fin (D + 1) → ℂ => u j) v := by
    intro v j
    first
    | fun_prop
    | exact (contDiff_apply ℂ ℂ j).contDiffAt
    | exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (D + 1) => ℂ) j).contDiff.contDiffAt
  refine ⟨U' ∩ W, fun w' => G.zOf w' (τ w'), hU'o.inter hWo, ⟨hwU', hw⟩, ?_, ?_, ?_⟩
  · intro w' hw'
    have hg' := hgood w' hw'.2
    have hτa : DifferentiableAt ℂ τ w' := hτd.differentiableAt (hU'o.mem_nhds hw'.1)
    apply DifferentiableAt.differentiableWithinAt
    rw [differentiableAt_pi]
    intro i
    have hA := differentiableAt_eval₂_deh (fun u => u) τ w' 0 (hproj w') hτa hg'.w0 (G.Q i)
    have hB := (contDiffAt_deh (fun u => u) w' 0 (hproj w') hg'.w0 G.dd).differentiableAt one_ne_zero
    have hC := hA.mul (hB.inv hg'.dd)
    simp only [Gen.zOf, Gen.evQ, div_eq_mul_inv]
    exact ((hproj w' 0).differentiableAt one_ne_zero).mul hC
  · show G.zOf w (τ w) = z
    rw [hτw']
    exact hzeq
  · intro w' hw'
    have hg' := hgood w' hw'.2
    have hr : G.P.eval₂ (deh w' 0) (τ w') = 0 := (hτf w' hw'.1).trans hroot
    exact ⟨G.zOf_mem hx0 hg' hr, G.zOf_e hg' hr⟩

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
