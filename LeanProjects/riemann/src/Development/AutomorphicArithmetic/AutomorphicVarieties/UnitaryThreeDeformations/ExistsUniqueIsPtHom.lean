import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem gg_ext {R : Type} [CommRing R] {x y : GG 3 R} (h1 : x.right = y.right) (h2 : x.mat = y.mat) :
    x = y := SemidirectProduct.ext (Units.ext h2) h1

private theorem exists_weight_inv_det_left_mem_weight_piece {O R Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Group Γ] (u : Γ →* GG 3 R) (g : Γ) : ∃ j : ℤ, (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) ∈ wpart O u j := by
  have hth : ∀ {R' : Type} [CommRing R'] (k : GL (Fin 3) R'), GeneralLinearGroup.det (thetaAut 3 R' k) = (GeneralLinearGroup.det k)⁻¹ := by
    intro R' _ k
    have hJ : GeneralLinearGroup.det (Jgl R' 3) * GeneralLinearGroup.det (Jgl R' 3) = 1 := by
      rw [← map_mul]
      have : Jgl R' 3 * Jgl R' 3 = 1 := Units.ext (Jgl R' 3).val_inv
      rw [this, map_one]
    have hT : GeneralLinearGroup.det (trInv k) = (GeneralLinearGroup.det k)⁻¹ := by
      rw [← map_inv]
      apply Units.ext
      simp [GeneralLinearGroup.val_det_apply, trInv, Matrix.det_transpose]
    show GeneralLinearGroup.det (theta k) = _
    simp only [theta, map_mul, hT]
    rw [mul_right_comm, hJ, one_mul]
  have htor : ∀ {R' : Type} [CommRing R'] (t : R'ˣ), GeneralLinearGroup.det (tor R' t) = t ^ (wt1 0 + wt1 1 + wt1 2) := by
    intro R' _ t
    apply Units.ext
    simp [GeneralLinearGroup.val_det_apply, tor, torGL, Matrix.det_diagonal, Fin.prod_univ_three, _root_.zpow_add]
  refine ⟨if (u g).right = 1 then 0 else -(2 * (wt1 0 + wt1 1 + wt1 2)), ?_⟩
  intro R' _ _ _ f f' t h
  have hg := congrArg (fun φ => GeneralLinearGroup.det (φ g).left) h
  simp only [push, conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.inv_left, GG.ofGL, SemidirectProduct.left_inl, SemidirectProduct.right_inl, GG.map, SemidirectProduct.map_left, SemidirectProduct.map_right, map_mul, GeneralLinearGroup.map_det] at hg
  simp only [map_one, inv_one, MulAut.one_apply, SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.map_right, MonoidHom.id_apply, one_mul, map_inv, htor] at hg
  have key : (Units.map (f' : R →+* R')) (GeneralLinearGroup.det (u g).left)⁻¹ = t ^ (if (u g).right = 1 then 0 else -(2 * (wt1 0 + wt1 1 + wt1 2))) * (Units.map (f : R →+* R')) (GeneralLinearGroup.det (u g).left)⁻¹ := by
    rw [map_inv, map_inv]
    split_ifs with hs
    · rw [hs, map_one, MulAut.one_apply, GeneralLinearGroup.map_det, htor] at hg
      rw [hg, mul_right_comm, mul_inv_cancel, one_mul, zpow_zero, one_mul]
    · have : sgnAct 3 R' (u g).right = thetaAut 3 R' := by simp [sgnAct, hs]
      rw [this, hth, inv_inv, htor, GeneralLinearGroup.map_det] at hg
      rw [hg]
      generalize wt1 0 + wt1 1 + wt1 2 = w
      rw [show -(2 * w) = -w + -w by ring, _root_.zpow_add, _root_.zpow_neg]
      simp only [_root_.mul_inv_rev]
      ac_rfl
  have e : ∀ φ : R →ₐ[O] R', φ (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) = ((Units.map (φ : R →+* R') (GeneralLinearGroup.det (u g).left)⁻¹ : R'ˣ) : R') := fun φ => rfl
  rw [e f', e f, key, Units.val_mul]

theorem UpperTheory.V.UnitaryThreeInertia.existsUnique_isPtHom :
    ∀ {O R Γ K : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Group Γ] [CommRing K] [Algebra O K] (u : Γ →* GG 3 R) (ξ : Sring O u →ₐ[O] K), ∃! r, IsPtHom u ξ r := by
  intro O R Γ K _ _ _ _ _ _ _ u ξ
  have hmem : ∀ g a b, (u g).mat a b ∈ Sring O u := fun g a b => ptMat._proof_1 u g a b
  have hinv : ∀ g a b, (((u g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b ∈ Sring O u := by
    intro g a b
    obtain ⟨j, hj⟩ := exists_weight_inv_det_left_mem_weight_piece (O := O) u g
    have hd : (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) ∈ Sring O u := by
      show _ ∈ (⨆ j, wpart O u j)
      exact Submodule.mem_iSup_of_mem j hj
    let M' : Matrix (Fin 3) (Fin 3) (Sring O u) := fun a b => ⟨(u g).mat a b, hmem g a b⟩
    have hM : ((Sring O u).val : Sring O u →+* R).mapMatrix M' = ((u g).left : Matrix (Fin 3) (Fin 3) R) := by
      ext a b; rfl
    have hdet : ((u g).left : Matrix (Fin 3) (Fin 3) R).det = ((GeneralLinearGroup.det (u g).left : Rˣ) : R) :=
      (GeneralLinearGroup.val_det_apply _).symm
    rw [Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_unit, ← hM, ← RingHom.map_adjugate]
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (Sring O u).mul_mem hd (M'.adjugate a b).2
  have hinj : Function.Injective (((Sring O u).val : Sring O u →+* R).mapMatrix (m := Fin 3)) := by
    intro x y h
    ext a b
    exact congrFun (congrFun h a) b
  let large₂ : Γ → GL (Fin 3) (Sring O u) := fun g =>
    { val := Matrix.of fun a b => ⟨(u g).mat a b, hmem g a b⟩
      inv := Matrix.of fun a b => ⟨(((u g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b, hinv g a b⟩
      val_inv := by
        apply hinj
        rw [map_mul, map_one]
        convert (u g).left.val_inv using 2 <;> ext a b <;> rfl
      inv_val := by
        apply hinj
        rw [map_mul, map_one]
        convert (u g).left.inv_val using 2 <;> ext a b <;> rfl }
  have gmap_inj : Function.Injective (GG.map (m := 3) ((Sring O u).val : Sring O u →+* R)) := by
    intro x y h
    apply gg_ext
    · have := congrArg (fun z => z.right) h
      simpa [GG.map_right] using this
    · ext a b
      have := congrArg (fun z => z.mat a b) h
      simpa [GG.map_mat] using this
  let vf : Γ → GG 3 (Sring O u) := fun g => SemidirectProduct.mk (large₂ g) (u g).right
  have hv : ∀ g, GG.map ((Sring O u).val : Sring O u →+* R) (vf g) = u g := by
    intro g
    apply gg_ext
    · rw [GG.map_right]
    · ext a b
      rw [GG.map_mat]
      rfl
  let v : Γ →* GG 3 (Sring O u) :=
    { toFun := vf
      map_one' := gmap_inj (by rw [hv, map_one, map_one])
      map_mul' := fun x y => gmap_inj (by rw [map_mul, hv, hv, hv, map_mul]) }
  have h0 : IsPtHom u ξ ((GG.map (ξ : Sring O u →+* K)).comp v) := by
    intro g
    constructor
    · show (GG.map _ (vf g)).right = _
      rw [GG.map_right]
    · show (GG.map _ (vf g)).mat = _
      rw [GG.map_mat]
      ext a b
      rfl
  refine ⟨_, h0, fun r hr => MonoidHom.ext fun g => gg_ext ((hr g).1.trans (h0 g).1.symm) ((hr g).2.trans (h0 g).2.symm)⟩
