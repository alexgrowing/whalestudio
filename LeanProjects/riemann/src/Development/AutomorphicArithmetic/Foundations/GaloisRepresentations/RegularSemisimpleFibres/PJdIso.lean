import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Transport

variable {F F' : Type} [Field F] [Field F'] (r : F ≃+* F')

private theorem coe_phi {n : ℕ} (x : GL (Fin n) F) :
    ((Matrix.GeneralLinearGroup.map r.toRingHom x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      (x : Matrix (Fin n) (Fin n) F).map r := by
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

private def phiE (n : ℕ) : GL (Fin n) F ≃ GL (Fin n) F' where
  toFun := Matrix.GeneralLinearGroup.map r.toRingHom
  invFun := Matrix.GeneralLinearGroup.map r.symm.toRingHom
  left_inv x := by
    apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply]
  right_inv x := by
    apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply]

private theorem inPar_phi (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    InPar a (Matrix.GeneralLinearGroup.map r.toRingHom x) ↔ InPar a x := by
  unfold InPar
  simp only [coe_phi, Matrix.map_apply]
  constructor
  · intro h i j hj hi
    exact (map_eq_zero_iff r r.injective).1 (h i j hj hi)
  · intro h i j hj hi
    rw [h i j hj hi, map_zero]

private theorem ent_map {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : ℕ) :
    ent (M.map r) i j = r (ent M i j) := by
  unfold ent
  split_ifs
  · rfl
  · exact (map_zero r).symm

private theorem tl_map (a : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    tl a (M.map r) = (tl a M).map r := by
  ext i j
  simp [tl, ent_map]

private theorem br_map (a b : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    br a b (M.map r) = (br a b M).map r := by
  ext i j
  simp [br, ent_map]

private theorem isUnit_map {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    IsUnit (M.map r) ↔ IsUnit M := by
  have := isUnit_map_iff (r.mapMatrix (m := Fin n)) M
  simpa [RingEquiv.mapMatrix_apply] using this

private theorem coe_toG {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsUnit M) :
    ((toG M : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = M := by
  unfold toG
  rw [dif_pos h]
  rfl

private theorem toG_map {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    toG (M.map r) = Matrix.GeneralLinearGroup.map r.toRingHom (toG M) := by
  by_cases h : IsUnit M
  · apply Units.ext
    rw [coe_toG ((isUnit_map r M).2 h), coe_phi, coe_toG h]
  · have h' : ¬ IsUnit (M.map r) := fun k => h ((isUnit_map r M).1 k)
    unfold toG
    rw [dif_neg h, dif_neg h', map_one]

private theorem tlG_phi (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    tlG a (Matrix.GeneralLinearGroup.map r.toRingHom x) =
      Matrix.GeneralLinearGroup.map r.toRingHom (tlG a x) := by
  unfold tlG
  rw [coe_phi, tl_map, toG_map]

private theorem brG_phi (a b : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    brG a b (Matrix.GeneralLinearGroup.map r.toRingHom x) =
      Matrix.GeneralLinearGroup.map r.toRingHom (brG a b x) := by
  unfold brG
  rw [coe_phi, br_map, toG_map]

include r in
private theorem card_phi (a n : ℕ) :
    Nat.card {p : GL (Fin n) F' // InPar a p} = Nat.card {p : GL (Fin n) F // InPar a p} :=
  (Nat.card_congr ((phiE r n).subtypeEquiv fun x => (inPar_phi r a x).symm)).symm

private theorem gal_id {K : Type} [Field K] (n : ℕ) (y : GL (Fin n) K) : gal (RingHom.id K) n y = y := by
  apply Units.ext
  ext i j
  simp [gal, Matrix.GeneralLinearGroup.map_apply]

private theorem hc_phi (a b : ℕ) (α : GL (Fin a) F' → ℂ) (β : GL (Fin b) F' → ℂ) (n : ℕ)
    (g : GL (Fin n) F) :
    hc a b α β n (Matrix.GeneralLinearGroup.map r.toRingHom g) =
      hc a b (fun x => α (Matrix.GeneralLinearGroup.map r.toRingHom x))
        (fun x => β (Matrix.GeneralLinearGroup.map r.toRingHom x)) n g := by
  unfold hc hcTw
  simp only [gal_id]
  rw [card_phi r a n, ← finsum_comp_equiv (phiE r n)]
  congr 1
  refine finsum_congr fun y => ?_
  have e : (phiE r n y)⁻¹ * Matrix.GeneralLinearGroup.map r.toRingHom g * phiE r n y =
      Matrix.GeneralLinearGroup.map r.toRingHom (y⁻¹ * g * y) := by
    simp only [map_mul, map_inv]
    rfl
  rw [e]
  simp only [inPar_phi, tlG_phi, brG_phi]

private theorem detc_phi (j : AlgebraicClosure F ≃+* AlgebraicClosure F')
    (hj : ∀ x, j (algebraMap _ _ x) = algebraMap _ _ (r x)) (θ : AlgebraicClosure F' →* ℂ)
    (t k : ℕ) (x : GL (Fin t) F) :
    detc θ t k (Matrix.GeneralLinearGroup.map r.toRingHom x) = detc (θ.comp j.toMonoidHom) t k x := by
  unfold detc
  have e : ((x : Matrix (Fin t) (Fin t) F).map r).det = r (x : Matrix (Fin t) (Fin t) F).det :=
    (RingHom.map_det r.toRingHom _).symm
  rw [coe_phi, e, ← hj]
  rfl

end Transport

theorem UpperTheory.Gal.InertialTypesAlt.jdIso :
    CuspIso → JDIso := by
  intro hC F F' _ _ _ r j hj θ D L n g
  have hJ : ∀ (L : List (ℕ × ℕ)) (n : ℕ) (g : GL (Fin n) F),
      J θ L n (Matrix.GeneralLinearGroup.map r.toRingHom g) = J (θ.comp j.toMonoidHom) L n g := by
    intro L
    induction L with
    | nil => intro n g; rfl
    | cons p L ih =>
      intro n g
      rw [J_cons, J_cons, hc_phi]
      congr 1
      · funext x
        exact hC F F' r j hj θ p.1 p.2 x
      · funext x
        exact ih _ x
  induction D generalizing n g with
  | nil => exact hJ L n g
  | cons p D ih =>
    rw [JD_cons, JD_cons, hc_phi]
    congr 1
    · funext x
      exact detc_phi r j hj θ p.1 p.2 x
    · funext x
      exact ih _ x
