import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrSqz

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_mul {C : Type} [CommRing C] {n : ℕ} {M N : Matrix (Fin n) (Fin n) C} (hM : UpT M) (hN : UpT N) :
    UpT (M * N) := fun i j h => by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : c < i
  · rw [hM i c hc, zero_mul]
  · rw [hN c j (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]

theorem UpperTheory.V.Fr.pr_correct :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C) (D : SetLift p B) (μ : ResidueField O →+ C'), IsSq O μ → (∀ c, p (μ c) = 0) → ∀ (β : F.Γ → Matrix (Fin n) (Fin n) (ResidueField O)) (Y : F.V → Matrix (Fin n) (Fin n) (ResidueField O)) (a : ∀ v, F.Gv v → Matrix (Fin n) (Fin n) (ResidueField O)), IsLocallyConstant β → (∀ x, D.om x = (dOne (B.bar O).ad β x).map μ) → (∀ v s, D.a v s = (a v s).map μ) → (∀ v s, a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v)) ∈ (B.bar O).b v) → ∃ B' : Box F n C', B'.Cont (maximalIdeal C') ∧ B'.map (p : C' →+* C) = B ∧ ∀ s, (B'.r s).mat = (1 - (β s).map μ) * (D.r s : Matrix (Fin n) (Fin n) C') := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B D μ hμ hpμ β Y a hβ hom ha hb
  obtain ⟨e, he1, he2, he3, he4, he5⟩ := pr_sqz O C' n μ hμ
  have hres : ∀ z : C', res O C (p z) = res O C' z := fun z => res_map p z
  let x : F.Γ → GG n C' := fun s => SemidirectProduct.mk (D.r s) (F.del s)
  have hK1 : ∀ s, GG.map (res O C' : C' →+* ResidueField O) (x s) = (B.bar O).r s := by
    intro s
    apply SemidirectProduct.ext
    · ext i j
      simp [x, GG.map, Box.map, hres, ← D.r_map s]
    · simp [x, GG.map, Box.map, B.nu]
  have hdl : ∀ v (s : F.Gv v), F.del (F.loc v s) = 1 := fun v s => MonoidHom.mem_ker.1 (F.loc0 v s).2
  have hAd : ∀ v (s : F.Gv v) M, (B.bar O).ad (F.loc v s) M =
      (D.r (F.loc v s) : Matrix (Fin n) (Fin n) C').map (res O C') * M *
        (((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C') := by
    intro v s M
    show GG.adFun ((B.bar O).r (F.loc v s)) M = _
    rw [← hK1]
    clear hom ha hb he5 he4 he3 he2 he1 hβ hpμ hμ
    simp [GG.adFun, GG.mat, GG.map, x, hdl]
    congr 1
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.coe_units_inv]
    calc (((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C') *
          (D.r (F.loc v s) : Matrix (Fin n) (Fin n) C').map (res O C')
        = ((((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') *
            (D.r (F.loc v s) : Matrix (Fin n) (Fin n) C')).map (res O C') :=
          (Matrix.map_mul (f := (res O C').toRingHom)).symm
      _ = 1 := by
          rw [Units.inv_mul]
          exact Matrix.map_one _ (map_zero _) (map_one _)
  have hxmul : ∀ s t, x s * x t = GG.ofGL (e (dOne (B.bar O).ad β (s, t))) * x (s * t) := by
    intro s t
    have hu : D.r s * sgnAct n C' (F.del s) (D.r t) * (D.r (s * t))⁻¹ = e (dOne (B.bar O).ad β (s, t)) := by
      apply Units.ext
      rw [he1, ← hom (s, t)]
      simp [SetLift.om]
    apply SemidirectProduct.ext
    · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, ← hu]
      simp [x]
    · simp [x]
  have hcomm : ∀ s X, x s * GG.ofGL (e X) = GG.ofGL (e ((B.bar O).ad s X)) * x s := by
    intro s X
    rw [he5 (x s) X, hK1 s]
    rfl
  let R' : F.Γ → GG n C' := fun s => GG.ofGL (e (-β s)) * x s
  have hmul : ∀ s t, R' (s * t) = R' s * R' t := by
    intro s t
    symm
    calc R' s * R' t = GG.ofGL (e (-β s)) * (x s * GG.ofGL (e (-β t))) * x t := by
          simp only [R', mul_assoc]
      _ = GG.ofGL (e (-β s)) * GG.ofGL (e ((B.bar O).ad s (-β t))) * (x s * x t) := by
          rw [hcomm]
          simp only [mul_assoc]
      _ = GG.ofGL (e (-β s)) * GG.ofGL (e ((B.bar O).ad s (-β t))) *
            GG.ofGL (e (dOne (B.bar O).ad β (s, t))) * x (s * t) := by
          rw [hxmul]
          simp only [mul_assoc]
      _ = GG.ofGL (e (-β s + (B.bar O).ad s (-β t) + dOne (B.bar O).ad β (s, t))) * x (s * t) := by
          rw [he2, he2, map_mul, map_mul]
      _ = R' (s * t) := by
          simp only [R']
          congr 3
          simp only [dOne, map_neg]
          abel
  let rr : F.Γ →* GG n C' := MonoidHom.mk' R' hmul
  have hneg : ∀ Z : Matrix (Fin n) (Fin n) (ResidueField O), (-Z).map μ = -(Z.map μ) := by
    intro Z
    ext i j
    simp
  have hpe : ∀ X, GeneralLinearGroup.map (p : C' →+* C) (e X) = 1 := by
    intro X
    ext i j
    simp only [GeneralLinearGroup.map_apply, he1, Matrix.add_apply, Matrix.map_apply, Units.val_one, map_add]
    have h0 : (p : C' →+* C) (μ (X i j)) = 0 := hpμ _
    rw [h0, add_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hconj : ∀ (A : GL (Fin n) C') X, A * e X * A⁻¹ =
      e ((A : Matrix (Fin n) (Fin n) C').map (res O C') * X * ((A⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C')) := by
    intro A X
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, he1, he1, mul_add, mul_one, add_mul, Units.mul_inv, (he4 _ X).1, (he4 _ _).2]
  have hGbar : ∀ v, ((B.bar O).g v : Matrix (Fin n) (Fin n) (ResidueField O)) =
        (D.g v : Matrix (Fin n) (Fin n) C').map (res O C') ∧
      (((B.bar O).g v)⁻¹ : GL (Fin n) (ResidueField O)) =
        (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C') := by
    intro v
    constructor
    · ext i j
      simp [Box.map, ← D.g_map v, hres]
    · ext i j
      simp [Box.map, ← D.g_map v, hres, ← map_inv]
  refine ⟨{ r := rr, nu := ?_, g := fun v => D.g v * e (-(Y v)), tri := ?_ }, ?_, ?_, ?_⟩
  · intro s
    show (GG.ofGL (e (-β s)) * x s).right = F.del s
    simp [x]
  · intro v s
    show UpT ((↑(D.g v * e (-(Y v))) : Matrix (Fin n) (Fin n) C') * (R' (F.loc v s)).mat *
      (((D.g v * e (-(Y v)))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C'))
    have hr : D.r (F.loc v s) = e (a v s) * ((D.g v)⁻¹ * D.t v s * D.g v) := by
      rw [← mul_inv_eq_iff_eq_mul]
      apply Units.ext
      rw [he1, ← ha v s]
      simp [SetLift.a]
    have hmat : (R' (F.loc v s)).mat = ↑(e (-β (F.loc v s)) * D.r (F.loc v s)) := by
      simp [R', GG.mat, x]
    have h1 : D.r (F.loc v s) * e (Y v) * (D.r (F.loc v s))⁻¹ = e ((B.bar O).ad (F.loc v s) (Y v)) := by
      rw [hconj, hAd]
    have hX : e (a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v))) =
        e (-(Y v)) * e (-β (F.loc v s)) * e ((B.bar O).ad (F.loc v s) (Y v)) * e (a v s) := by
      rw [← he2, ← he2, ← he2]
      congr 1
      abel
    have key : D.g v * e (-(Y v)) * (e (-β (F.loc v s)) * D.r (F.loc v s)) * (D.g v * e (-(Y v)))⁻¹ =
        e ((D.g v : Matrix (Fin n) (Fin n) C').map (res O C') *
          (a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v))) *
          (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C')) * D.t v s := by
      rw [← hconj, hX]
      calc D.g v * e (-(Y v)) * (e (-β (F.loc v s)) * D.r (F.loc v s)) * (D.g v * e (-(Y v)))⁻¹
          = D.g v * e (-(Y v)) * e (-β (F.loc v s)) *
              (D.r (F.loc v s) * e (Y v) * (D.r (F.loc v s))⁻¹) * D.r (F.loc v s) * (D.g v)⁻¹ := by
            rw [_root_.mul_inv_rev, he3, neg_neg]
            group
        _ = D.g v * e (-(Y v)) * e (-β (F.loc v s)) * e ((B.bar O).ad (F.loc v s) (Y v)) *
              (e (a v s) * ((D.g v)⁻¹ * D.t v s * D.g v)) * (D.g v)⁻¹ := by
            rw [h1, ← hr]
        _ = D.g v * (e (-(Y v)) * e (-β (F.loc v s)) * e ((B.bar O).ad (F.loc v s) (Y v)) * e (a v s)) *
              (D.g v)⁻¹ * D.t v s := by
            group
    have hW : UpT ((D.g v : Matrix (Fin n) (Fin n) C').map (res O C') *
          (a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v))) *
          (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C')) := by
      rw [← (hGbar v).1, ← (hGbar v).2]
      exact hb v s
    rw [hmat, ← Units.val_mul, ← Units.val_mul, key, Units.val_mul, he1]
    apply upT_mul _ (D.t_tri v s)
    intro i j hij
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), Matrix.map_apply, hW i j hij, map_zero, add_zero]
  · intro i j N
    have hB : IsLocallyConstant fun s =>
        (D.r s : Matrix (Fin n) (Fin n) C').map (Ideal.Quotient.mk (maximalIdeal C' ^ N)) := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro s0
      have hall : ∀ᶠ s in nhds s0, ∀ a b,
          Ideal.Quotient.mk (maximalIdeal C' ^ N) ((D.r s : Matrix (Fin n) (Fin n) C') a b) =
            Ideal.Quotient.mk (maximalIdeal C' ^ N) ((D.r s0 : Matrix (Fin n) (Fin n) C') a b) :=
        Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b =>
          (IsLocallyConstant.iff_eventually_eq _).1 (D.r_cont a b N) s0
      filter_upwards [hall] with s hs
      ext a b
      exact hs a b
    have hA := hβ.comp (fun Z =>
      ((1 : Matrix (Fin n) (Fin n) C') + (-Z).map μ).map (Ideal.Quotient.mk (maximalIdeal C' ^ N)))
    have hM := (IsLocallyConstant.comp₂ hA hB (· * ·)).comp (fun M => M i j)
    convert hM using 1
    funext s
    simp only [Function.comp_apply]
    rw [← Matrix.map_mul, Matrix.map_apply]
    congr 1
    show (R' s).mat i j = _
    simp [R', GG.mat, x, he1]
  · apply Box.ext
    · apply MonoidHom.ext
      intro s
      apply SemidirectProduct.ext
      · show GeneralLinearGroup.map (p : C' →+* C) (R' s).left = (B.r s).left
        simp [R', x, hpe, D.r_map]
      · show (R' s).right = (B.r s).right
        simp [R', x, B.nu]
    · funext v
      show GeneralLinearGroup.map (p : C' →+* C) (D.g v * e (-(Y v))) = B.g v
      rw [map_mul, hpe, mul_one, D.g_map]
  · intro s
    show (R' s).mat = _
    simp [R', GG.mat, x, he1, hneg, sub_eq_add_neg]
