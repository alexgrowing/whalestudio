import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LcMatrix
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MapThetaLie

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_gl {C : Type} [CommRing C] {n : ℕ} (a b c : GL (Fin n) C)
    (ha : UpT (a : Matrix (Fin n) (Fin n) C)) (hb : UpT (b : Matrix (Fin n) (Fin n) C))
    (hc : UpT (c : Matrix (Fin n) (Fin n) C)) :
    UpT (((a * b * c⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) - 1) := by
  have ha' : (a : Matrix (Fin n) (Fin n) C).BlockTriangular id := fun i j h => ha i j h
  have hb' : (b : Matrix (Fin n) (Fin n) C).BlockTriangular id := fun i j h => hb i j h
  have hc' : (c : Matrix (Fin n) (Fin n) C).BlockTriangular id := fun i j h => hc i j h
  letI : Invertible (c : Matrix (Fin n) (Fin n) C) := c.invertible
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hc'
  rw [← Matrix.coe_units_inv] at hi
  intro i j h
  have h1 := ((ha'.mul hb').mul hi) (show id j < id i from h)
  rw [Matrix.sub_apply, Units.val_mul, Units.val_mul, h1, Matrix.one_apply_ne (ne_of_gt h), sub_zero]

private theorem ring_id {R : Type} [Ring R] (o c x a w : R) (h : (1 + o) * (1 + c) = (1 + x) * (1 + a) * (1 + w))
    (h1 : o * c = 0) (h2 : x * a = 0) (h3 : x * w = 0) (h4 : a * w = 0) : o - (x - c + a) = w := by
  have e1 : (1 + o) * (1 + c) = 1 + o + c + o * c := by noncomm_ring
  have e2 : (1 + x) * (1 + a) * (1 + w) = 1 + x + a + w + x * a + x * w + a * w + x * a * w := by noncomm_ring
  rw [e1, e2, h1, h2, h3, h4] at h
  simp only [add_zero, zero_mul] at h
  have : o = 1 + x + a + w - c - 1 := by rw [← h]; abel
  rw [this]; abel

theorem UpperTheory.V.Fr.pr_cocv :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C) (D : SetLift p B) (u : RingHom.ker p →ₗ[O] ResidueField O), maximalIdeal C' * RingHom.ker p = ⊥ → ∀ v s t, (D.co u).1 (F.loc v s, F.loc v t) - dOne ((B.bar O).ad.comp (F.loc v)) ((D.co u).2 v) (s, t) ∈ (B.bar O).b v := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B D u hK v s t
  obtain ⟨hom, ha, -, -⟩ := pr_omk hF O C' C p B D hK
  have hle : RingHom.ker p ≤ maximalIdeal C' := fun x hx => by
    rw [← res_eq_zero_iff O, ← res_map p, (RingHom.mem_ker).1 hx, map_zero]
  have ev := pr_evk O C' n (RingHom.ker p) u hK hle
  have hdel : ∀ s, F.del (F.loc v s) = 1 := fun s => (F.loc0 v s).2
  have hright : ∀ s, (B.r (F.loc v s)).right = 1 := fun s => (B.nu _).trans (hdel s)
  have hres : ∀ x : GL (Fin n) C', GeneralLinearGroup.map (res O C : C →+* ResidueField O)
      (GeneralLinearGroup.map (p : C' →+* C) x) = GeneralLinearGroup.map (res O C' : C' →+* ResidueField O) x := by
    intro x
    ext i j
    exact res_map p _
  have hval : ∀ x : GL (Fin n) C', (x : Matrix (Fin n) (Fin n) C').map (res O C') =
      ((GeneralLinearGroup.map (res O C' : C' →+* ResidueField O) x : GL (Fin n) (ResidueField O)) :
        Matrix (Fin n) (Fin n) (ResidueField O)) := fun x => rfl

  set T : Matrix (Fin n) (Fin n) C' :=
    ((D.t v s * D.t v t * (D.t v (s * t))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') - 1 with hT
  have hTup : UpT T := upT_gl _ _ _ (D.t_tri v s) (D.t_tri v t) (D.t_tri v _)
  have hTK : ∀ i j, T i j ∈ RingHom.ker p := by
    have e : GeneralLinearGroup.map (p : C' →+* C) (D.t v s * D.t v t * (D.t v (s * t))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, D.t_map, D.t_map, D.t_map, map_mul, map_mul, SemidirectProduct.mul_left,
        hright, sgnAct_one]
      group
    intro i j
    have e2 := congrArg (fun x : GL (Fin n) C => (x : Matrix (Fin n) (Fin n) C) i j) e
    rw [RingHom.mem_ker, hT, Matrix.sub_apply, map_sub]
    refine sub_eq_zero.2 (Eq.trans e2 ?_)
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  set gi : Matrix (Fin n) (Fin n) C' := (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hgi
  set g : Matrix (Fin n) (Fin n) C' := ((D.g v : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hg
  set ri : Matrix (Fin n) (Fin n) C' := (((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hri
  set r : Matrix (Fin n) (Fin n) C' := ((D.r (F.loc v s) : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hr
  have hW1 : ∀ i j, (gi * T) i j ∈ RingHom.ker p := fun i j => (((ev T hTK).2.1 gi).1 i j).1
  have hW : ∀ i j, (gi * T * g) i j ∈ RingHom.ker p := fun i j => (((ev _ hW1).2.1 g).1 i j).2
  have hX1 : ∀ i j, (r * D.a v t) i j ∈ RingHom.ker p := fun i j => (((ev _ (ha v t)).2.1 r).1 i j).1
  have hX : ∀ i j, (r * D.a v t * ri) i j ∈ RingHom.ker p := fun i j => (((ev _ hX1).2.1 ri).1 i j).2
  have key : D.om (F.loc v s, F.loc v t) - (r * D.a v t * ri - D.a v (s * t) + D.a v s) = gi * T * g := by
    refine ring_id _ _ _ _ _ ?_ ((ev _ (hom _)).1 _ (ha v _)).1 ((ev _ hX).1 _ (ha v _)).1
      ((ev _ hX).1 _ hW).1 ((ev _ (ha v _)).1 _ hW).1
    have e1 : 1 + r * D.a v t * ri = ((D.r (F.loc v s) * (D.r (F.loc v t) * ((D.g v)⁻¹ * D.t v t * D.g v)⁻¹) *
        (D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') := by
      rw [SetLift.a, mul_sub, sub_mul, mul_one, hr, hri, Units.mul_inv, add_sub_cancel]
      rfl
    have e2 : 1 + gi * T * g = (((D.g v)⁻¹ * (D.t v s * D.t v t * (D.t v (s * t))⁻¹) * D.g v : GL (Fin n) C') :
        Matrix (Fin n) (Fin n) C') := by
      rw [hT, mul_sub, sub_mul, mul_one, hg, hgi, Units.inv_mul, add_sub_cancel]
      rfl
    rw [e1, e2]
    simp only [SetLift.om, SetLift.a, add_sub_cancel, hdel, sgnAct_one, ← Units.val_mul, map_mul]
    congr 1
    group
  have hXc : ∀ i j, (r * D.a v t * ri - D.a v (s * t)) i j ∈ RingHom.ker p := fun i j =>
    sub_mem (hX i j) (ha v _ i j)
  have hXca : ∀ i j, (r * D.a v t * ri - D.a v (s * t) + D.a v s) i j ∈ RingHom.ker p := fun i j =>
    add_mem (hXc i j) (ha v _ i j)
  have k2 := congrArg (fun M : Matrix (Fin n) (Fin n) C' => M.map (evK (RingHom.ker p) u)) key
  rw [((ev _ (hom _)).1 _ hXca).2.2, ((ev _ hXc).1 _ (ha v _)).2.1, ((ev _ hX).1 _ (ha v _)).2.2,
    ((ev _ hX1).2.1 ri).2.2, ((ev _ (ha v t)).2.1 r).2.1, ((ev _ hW1).2.1 g).2.2, ((ev _ hTK).2.1 gi).2.1,
    hr, hri, hg, hgi, hval, hval, hval, hval, map_inv, map_inv, ← hres, ← hres (D.g v), D.r_map, D.g_map] at k2
  have k3 : (D.co u).1 (F.loc v s, F.loc v t) - dOne ((B.bar O).ad.comp (F.loc v)) ((D.co u).2 v) (s, t) =
      ((((B.bar O).g v)⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O)) *
        T.map (evK (RingHom.ker p) u) * ((B.bar O).g v : Matrix (Fin n) (Fin n) (ResidueField O)) := by
    refine Eq.trans ?_ k2
    have e : ((B.bar O).ad.comp (F.loc v)) s ((D.co u).2 v t) =
        ((B.bar O).r (F.loc v s)).adFun ((D.a v t).map (evK (RingHom.ker p) u)) := rfl
    have e' : ((B.bar O).r (F.loc v s)).right = 1 := hright s
    simp only [dOne]
    rw [e, GG.adFun, if_pos e', add_sub_assoc, add_comm]
    rfl
  rw [k3]
  intro i j h
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
    Matrix.mul_one, Matrix.map_apply, hTup i j h, evK_of_mem u (zero_mem _)]
  exact map_zero u
