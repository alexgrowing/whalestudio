import Development.EtaleCohomology.TateTwists.EtaleTensorCyclesLocallyLiftOfRowExactAndDescent

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.EtaleFoundations

local macro "TI " w:term:max : term => `({p : ℤ × ℤ // p.1 + p.2 = $w})

local macro "TF " C:term:max J:term:max U:term:max w:term:max : term =>
  `(fun q : {p : ℤ × ℤ // p.1 + p.2 = $w} => Sec (HomologicalComplex.X $C q.1.1) $U ⊗[ULift.{1} _] Sec (HomologicalComplex.X $J q.1.2) $U)

def stD {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w') :
    Tens C J U w →ₗ[ULift.{1} R] Tens C J U w' :=
  DirectSum.toModule _ _ _ fun p =>
    (DirectSum.lof (ULift.{1} R) (TI w') (TF C J U w') ⟨(p.1.1 + 1, p.1.2), by have := p.2; omega⟩) ∘ₗ
        TensorProduct.map ((C.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id +
      ((p.1.1.negOnePow : ℤ) • ((DirectSum.lof (ULift.{1} R) (TI w') (TF C J U w') ⟨(p.1.1, p.1.2 + 1), by have := p.2; omega⟩) ∘ₗ
        TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom))

theorem stD_lof {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w') (a b : ℤ) (hab : a + b = w)
    (v : Sec (C.X a) U ⊗[ULift.{1} R] Sec (J.X b) U) :
    stD C J U w w' h (DirectSum.lof (ULift.{1} R) (TI w) (TF C J U w) ⟨(a, b), hab⟩ v) =
      DirectSum.lof (ULift.{1} R) (TI w') (TF C J U w') ⟨(a + 1, b), by omega⟩
          (TensorProduct.map ((C.d a (a + 1)).hom.app (op U)).hom LinearMap.id v) +
        (a.negOnePow : ℤ) • DirectSum.lof (ULift.{1} R) (TI w') (TF C J U w') ⟨(a, b + 1), by omega⟩
          (TensorProduct.map LinearMap.id ((J.d b (b + 1)).hom.app (op U)).hom v) := by
  unfold stD
  rw [DirectSum.toModule_lof]
  rfl

theorem lift_lof {R : Type} [CommRing R] {C J T : Cx R} (τ : Pair C J T) (U : Scheme.{0}) (w : ℤ) (p : TI w)
    (v : Sec (C.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) : τ.lift U w (DirectSum.lof (ULift.{1} R) (TI w) (TF C J U w) p v) =
      TensorProduct.lift (τ.mul U p.1.1 p.1.2 w p.2) v := by
  unfold Pair.lift
  rw [DirectSum.toModule_lof]

theorem stD_lift {R : Type} [CommRing R] {C J T : Cx R} (τ : Pair C J T) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w')
    (y : Tens C J U w) : τ.lift U w' (stD C J U w w' h y) = Sec.map (T.d w w') (τ.lift U w y) := by
  subst h
  have key : (τ.lift U (w + 1)).comp (stD C J U w (w + 1) rfl) =
      ((T.d w (w + 1)).hom.app (op U)).hom.comp (τ.lift U w) := by
    refine DirectSum.linearMap_ext _ fun p => ?_
    obtain ⟨⟨a, b⟩, hab⟩ := p
    refine TensorProduct.ext' fun u v => ?_
    simp only [LinearMap.comp_apply]
    rw [stD_lof, map_add, map_zsmul, lift_lof, lift_lof, lift_lof]
    simp only [TensorProduct.map_tmul, TensorProduct.lift.tmul, LinearMap.id_apply]
    have := τ.leibniz U a b w hab u v
    rw [Units.smul_def] at this
    exact this.symm
  exact LinearMap.congr_fun key y

theorem stD_res {R : Type} [CommRing R] (C J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w w' : ℤ) (h : w + 1 = w')
    (y : Tens C J U w) : stD C J V w w' h (Tens.res g w y) = Tens.res g w' (stD C J U w w' h y) := by
  have key : (stD C J V w w' h).comp (Tens.res g w) = (Tens.res g w').comp (stD C J U w w' h) := by
    refine DirectSum.linearMap_ext _ fun p => ?_
    obtain ⟨⟨a, b⟩, hab⟩ := p
    refine TensorProduct.ext' fun u v => ?_
    have n1 := stair_map_res (C.d a (a + 1)) g u
    have n2 := stair_map_res (J.d b (b + 1)) g v
    simp only [Sec.map, Sec.res] at n1 n2
    simp only [LinearMap.comp_apply]
    rw [Tens.res, Tens.res, DirectSum.lmap_lof, stD_lof, stD_lof, map_add, map_zsmul, DirectSum.lmap_lof, DirectSum.lmap_lof]
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    rw [n1, n2]
  exact LinearMap.congr_fun key y

theorem lift_res {R : Type} [CommRing R] {C J T : Cx R} (τ : Pair C J T) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (y : Tens C J U w) : τ.lift V w (Tens.res g w y) = Sec.res g (τ.lift U w y) := by
  have key : (τ.lift V w).comp (Tens.res g w) = ((T.X w).obj.map g.op).hom.comp (τ.lift U w) := by
    refine DirectSum.linearMap_ext _ fun p => ?_
    refine TensorProduct.ext' fun u v => ?_
    simp only [LinearMap.comp_apply]
    rw [Tens.res, DirectSum.lmap_lof, lift_lof, lift_lof]
    simp only [TensorProduct.map_tmul, TensorProduct.lift.tmul]
    exact (τ.nat g _ _ _ p.2 u v).symm
  exact LinearMap.congr_fun key y

theorem lof_reidx {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w' a a' b : ℤ) (ha : a + 1 = a')
    (h1 : a + 1 + b = w') (h2 : a' + b = w') (v : Sec (C.X a) U ⊗[ULift.{1} R] Sec (J.X b) U) :
    DirectSum.lof (ULift.{1} R) (TI w') (TF C J U w') ⟨(a + 1, b), h1⟩
        (TensorProduct.map ((C.d a (a + 1)).hom.app (op U)).hom LinearMap.id v) =
      DirectSum.lof (ULift.{1} R) (TI w') (TF C J U w') ⟨(a', b), h2⟩
        (TensorProduct.map ((C.d a a').hom.app (op U)).hom LinearMap.id v) := by
  subst ha; rfl

theorem stD_low {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w') (n : ℤ)
    (y : Tens C J U w) (hy : ∀ p : TI w, n < p.1.1 → y p = 0) :
    ∀ q : TI w', n + 1 < q.1.1 → stD C J U w w' h y q = 0 := by
  classical
  intro q hq
  rw [← DirectSum.sum_support_of y, map_sum, DFinsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpn : p.1.1 ≤ n := by
    by_contra hc; exact (DFinsupp.mem_support_iff.1 hp) (hy p (by omega))
  obtain ⟨⟨a, b⟩, hab⟩ := p
  simp only at hpn
  rw [← DirectSum.lof_eq_of (ULift.{1} R), stD_lof, DFinsupp.add_apply, DFinsupp.smul_apply,
    DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, DirectSum.of_eq_of_ne, smul_zero, add_zero]
  · intro he; rw [he] at hq; simp only at hq; omega
  · intro he; rw [he] at hq; simp only at hq; omega

theorem stD_top {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w') (s : ℤ)
    (y : Tens C J U w) (hy : ∀ p : TI w, s < p.1.1 → y p = 0) (h0 : s + (w - s) = w) (h1 : s + 1 + (w - s) = w') :
    stD C J U w w' h y ⟨(s + 1, w - s), h1⟩ =
      TensorProduct.map ((C.d s (s + 1)).hom.app (op U)).hom LinearMap.id (y ⟨(s, w - s), h0⟩) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_of y]
  rw [map_sum, DFinsupp.finset_sum_apply]
  have hz : ∀ p ∈ DFinsupp.support y, p ≠ ⟨(s, w - s), h0⟩ →
      stD C J U w w' h (DirectSum.of (TF C J U w) p (y p)) ⟨(s + 1, w - s), h1⟩ = 0 := by
    intro p hp hne
    have hps : p.1.1 < s := by
      have hle : p.1.1 ≤ s := by
        by_contra hc; exact (DFinsupp.mem_support_iff.1 hp) (hy p (by omega))
      rcases lt_or_eq_of_le hle with h' | h'
      · exact h'
      · exact absurd (Subtype.ext (Prod.ext h' (by have := p.2; simp only at this ⊢; omega))) hne
    obtain ⟨⟨a, b⟩, hab⟩ := p
    simp only at hps
    rw [← DirectSum.lof_eq_of (ULift.{1} R), stD_lof, DFinsupp.add_apply, DFinsupp.smul_apply,
      DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, DirectSum.of_eq_of_ne, smul_zero, add_zero]
    · intro he; have := congrArg (fun q : TI w' => q.1.1) he; simp only at this; omega
    · intro he; have := congrArg (fun q : TI w' => q.1.1) he; simp only at this; omega
  by_cases hm : (⟨(s, w - s), h0⟩ : TI w) ∈ DFinsupp.support y
  · rw [Finset.sum_eq_single_of_mem _ hm hz]
    rw [← DirectSum.lof_eq_of (ULift.{1} R), stD_lof, DFinsupp.add_apply, DFinsupp.smul_apply,
      DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_same, DirectSum.of_eq_of_ne, smul_zero, add_zero]
    intro he; have := congrArg (fun q : TI w' => q.1.1) he; simp only at this; omega
  · rw [Finset.sum_eq_zero fun p hp => hz p hp (fun he => hm (he ▸ hp))]
    have : y ⟨(s, w - s), h0⟩ = 0 := by simpa [DFinsupp.mem_support_iff] using hm
    rw [this, map_zero]

theorem next_fix {R : Type} [CommRing R] (T : Cx R) (w : ℤ) {U : Scheme.{0}} (y : Sec (T.X w) U)
    (h : Sec.map (T.sc w).g y = 0) : Sec.map (T.d w (w + 1)) y = 0 := by
  change Sec.map (T.d w ((ComplexShape.up ℤ).next w)) y = 0 at h
  rwa [CochainComplex.next ℤ w] at h

theorem prev_fix {R : Type} [CommRing R] (T : Cx R) (w : ℤ) {V : Scheme.{0}} (z : Sec (T.X (w - 1)) V) :
    ∃ z' : Sec (T.sc w).X₁ V, Sec.map (T.sc w).f z' = Sec.map (T.d (w - 1) w) z := by
  change ∃ z' : Sec (T.X ((ComplexShape.up ℤ).prev w)) V, Sec.map (T.d ((ComplexShape.up ℤ).prev w) w) z' = _
  rw [CochainComplex.prev ℤ w]
  exact ⟨z, rfl⟩

theorem etale_tensor_cycle_locally_lowers_top_degree_of_row_exact : EtaleTensorCycleLocallyLowersTopDegree := by
  intro R _ C J T τ hτ hrow w s U x hx hc
  have hc' : τ.lift U (w + 1) (stD C J U w (w + 1) rfl x) = 0 := by
    rw [stD_lift]; exact next_fix T w _ hc
  refine stair_loc_bind U _ _ (hτ.2 U (w + 1) _ hc') ?_
  intro V g hV
  have hy : ∀ p : TI w, s < p.1.1 → Tens.res g w x p = 0 := by
    intro p hp; rw [Tens.res, DirectSum.lmap_apply, hx p hp, map_zero]
  have hrow0 : TensorProduct.map ((C.d s (s + 1)).hom.app (op V)).hom LinearMap.id
      (Tens.res g w x ⟨(s, w - s), by omega⟩) = 0 := by
    rw [← stD_top C J V w (w + 1) rfl s _ hy (by omega) (by omega), stD_res, hV]; rfl
  refine stair_loc_mono V _ _ (hrow s (w - s) V _ hrow0) ?_
  rintro W k ⟨e, he⟩
  have hlow : ∀ q : TI (w - 1), s - 1 < q.1.1 →
      (DirectSum.lof (ULift.{1} R) (TI (w - 1)) (TF C J W (w - 1)) ⟨(s - 1, w - s), by omega⟩ e) q = 0 := by
    intro q hq
    rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
    intro he'; rw [he'] at hq; simp only at hq; omega
  refine ⟨Tens.res k w (Tens.res g w x) - stD C J W (w - 1) w (by omega)
      (DirectSum.lof (ULift.{1} R) (TI (w - 1)) (TF C J W (w - 1)) ⟨(s - 1, w - s), by omega⟩ e), ?_, ?_⟩
  · intro p hp
    rw [DFinsupp.sub_apply]
    rcases lt_or_eq_of_le (show s ≤ p.1.1 by omega) with hps | hps
    · rw [stD_low C J W (w - 1) w (by omega) (s - 1) _ hlow p (by omega), sub_zero,
        show Tens.res k w (Tens.res g w x) p = TensorProduct.map ((C.X p.1.1).obj.map k.op).hom
          ((J.X p.1.2).obj.map k.op).hom (Tens.res g w x p) from DirectSum.lmap_apply _ _ _, hy p hps, map_zero]
    · obtain ⟨⟨a, b⟩, hab⟩ := p
      simp only at hps
      subst hps
      obtain rfl : b = w - s := by simp only at hab; omega
      rw [stD_lof, lof_reidx C J W w (s - 1) s (w - s) (by omega) _ (by omega), DFinsupp.add_apply, DFinsupp.smul_apply,
        DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_same, DirectSum.of_eq_of_ne, smul_zero, add_zero,
        sub_eq_zero]
      · exact he.symm
      · intro he'; have := congrArg (fun q : TI w => q.1.1) he'; simp only at this; omega
  · obtain ⟨z', hz'⟩ := prev_fix T w (τ.lift W (w - 1)
      (DirectSum.lof (ULift.{1} R) (TI (w - 1)) (TF C J W (w - 1)) ⟨(s - 1, w - s), by omega⟩ e))
    refine ⟨z', ?_⟩
    rw [map_sub, lift_res, lift_res, stair_res_res, stD_lift]
    exact congrArg (fun t => _ - t) hz'.symm

end LateralTheory.EtaleFoundations
