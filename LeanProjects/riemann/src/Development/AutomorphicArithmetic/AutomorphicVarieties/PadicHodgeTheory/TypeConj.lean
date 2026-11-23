import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc UpperTheory.V.U3

section Gen

variable {Q A V V' : Type} [Field Q] [CommRing A] [Algebra Q A] [AddCommGroup V] [Module A V] [Module Q V]
  [IsScalarTower Q A V] [AddCommGroup V'] [Module A V'] [Module Q V'] [IsScalarTower Q A V']

private noncomputable def tr (B : Type) [AddCommGroup B] [Module Q B] (e : V ≃ₗ[A] V') :
    V ⊗[Q] B ≃ₗ[A] V' ⊗[Q] B := AlgebraTensorModule.congr e (LinearEquiv.refl Q B)

variable {B B' : Type} [AddCommGroup B] [Module Q B] [AddCommGroup B'] [Module Q B'] (e : V ≃ₗ[A] V')

private theorem tr_map {f : V →ₗ[A] V} {f' : V' →ₗ[A] V'} (h : ∀ x, e (f x) = f' (e x)) (b : B →ₗ[Q] B')
    (x : V ⊗[Q] B) :
    tr B' e (AlgebraTensorModule.map f b x) = AlgebraTensorModule.map f' b (tr B e x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [tr, h]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem tr_range (b : B →ₗ[Q] B') (x : V ⊗[Q] B') :
    tr B' e x ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V' →ₗ[A] V') b) ↔
      x ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[A] V) b) := by
  rw [LinearMap.mem_range, LinearMap.mem_range, (tr B e).surjective.exists]
  refine exists_congr fun y => ?_
  rw [← tr_map e (f := LinearMap.id) (fun _ => rfl), (tr B' e).injective.eq_iff]

private theorem tr_smul {K : Type} [AddCommGroup K] [Module Q K] (s : K →ₗ[Q] Module.End Q B) (c : A ⊗[Q] K)
    (x : V ⊗[Q] B) :
    tr B e (((TensorProduct.homTensorHomMap (RingHom.id Q) V B V B).comp
      (TensorProduct.map (Algebra.lsmul Q Q V : A →ₐ[Q] Module.End Q V).toLinearMap s)) c x) =
    ((TensorProduct.homTensorHomMap (RingHom.id Q) V' B V' B).comp
      (TensorProduct.map (Algebra.lsmul Q Q V' : A →ₐ[Q] Module.End Q V').toLinearMap s)) c (tr B e x) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c d hc hd => simp only [map_add, LinearMap.add_apply, hc, hd]
  | tmul a k =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simp [tr]
    | add x y hx hy => simp only [map_add, hx, hy]

end Gen

section Per

variable {l : ℕ} [Fact l.Prime] {A V V' : Type} [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V']
  [IsScalarTower ℚ_[l] A V'] (e : V ≃ₗ[A] V')

private theorem tr_Dcr {G : Type} [Group G] (φ : G →* GQ l) {ρ : Representation A G V} {ρ' : Representation A G V'}
    (h : ∀ g x, e (ρ g x) = ρ' g (e x)) (x : V ⊗[ℚ_[l]] Bcr l) :
    tr (Bcr l) e x ∈ Dcr φ ρ' ↔ x ∈ Dcr φ ρ := by
  simp only [Dcr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun g => ?_
  rw [actC, actC, ← tr_map e (h g), (tr _ e).injective.eq_iff]

private theorem tr_FilD {G : Type} [Group G] (φ : G →* GQ l) {ρ : Representation A G V} {ρ' : Representation A G V'}
    (h : ∀ g x, e (ρ g x) = ρ' g (e x)) (i : ℤ) (x : V ⊗[ℚ_[l]] Bdr l) :
    tr (Bdr l) e x ∈ FilD φ ρ' i ↔ x ∈ FilD φ ρ i := by
  rw [FilD, FilD, Submodule.mem_inf, Submodule.mem_inf]
  refine and_congr ?_ (tr_range e _ x)
  simp only [Ddr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun g => ?_
  rw [UpperTheory.V.Loc.actD, UpperTheory.V.Loc.actD, ← tr_map e (h g), (tr _ e).injective.eq_iff]

private theorem tr_smulD (K : FinExt l) (c : A ⊗[ℚ_[l]] ↥K.1) (x : V ⊗[ℚ_[l]] Bdr l) :
    tr (Bdr l) e (smulD V K c x) = smulD V' K c (tr (Bdr l) e x) := tr_smul e _ c x

private theorem tr_smulC (K : FinExt l) (c : A ⊗[ℚ_[l]] ↥(K0 K)) (x : V ⊗[ℚ_[l]] Bcr l) :
    tr (Bcr l) e (smulC V K c x) = smulC V' K c (tr (Bcr l) e x) := tr_smul e _ c x

private theorem crys_equiv (K : FinExt l) {ρ : Representation A ↥(GK K) V} {ρ' : Representation A ↥(GK K) V'}
    (h : ∀ g x, e (ρ g x) = ρ' g (e x)) (hc : Crys K ρ) : Crys K ρ' := by
  unfold Crys IsCrys at hc ⊢
  rw [← (e.restrictScalars ℚ_[l]).finrank_eq, ← hc]
  symm
  refine ((tr (Bcr l) (e.restrictScalars ℚ_[l])).ofSubmodules _ _ ?_).finrank_eq
  ext x
  obtain ⟨y, rfl⟩ := (tr (Bcr l) (e.restrictScalars ℚ_[l])).surjective x
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun g => ?_
  rw [actVB, actVB, ← tr_map (e.restrictScalars ℚ_[l]) (f := resCoef ℚ_[l] ρ g)
    (f' := resCoef ℚ_[l] ρ' g) (h g), (tr _ _).injective.eq_iff]

theorem UpperTheory.V.Loc.potCrysType_equiv (K : FinExt l) {ρ : Representation A ↥(GK K) V}
    {ρ' : Representation A ↥(GK K) V'} (h : ∀ g x, e (ρ g x) = ρ' g (e x)) {n : ℕ} {m : ℤ → ℕ} {t : ↥(GK K) → A}
    (H : PotCrysType K ρ n m t) : PotCrysType K ρ' n m t := by
  obtain ⟨hH, L, hL, hn, hc, x, hx, hu, ht⟩ := H
  have h' : ∀ g x, e ((ρ.comp (incl hL) : Representation A _ V) g x) =
      (ρ'.comp (incl hL) : Representation A _ V') g (e x) := fun g x => h _ x
  refine ⟨fun i => ?_, L, hL, hn, crys_equiv e L h' hc, fun a => tr _ e (x a), fun a => (tr_Dcr e _ h' _).2 (hx a),
    fun y hy => ?_, fun γ hγ M hM => ht γ hγ M fun b => ?_⟩
  · obtain ⟨z, hz, hv⟩ := hH i
    refine ⟨fun a => tr _ e (z a), fun a => (tr_FilD e _ h i _).2 (hz a), fun y hy => ?_⟩
    obtain ⟨y, rfl⟩ := (tr (Bdr l) e).surjective y
    refine (existsUnique_congr fun c => ?_).1 (hv y ((tr_FilD e _ h i _).1 hy))
    rw [← tr_FilD e _ h, map_sub, map_sum]
    simp only [tr_smulD]
  · obtain ⟨y, rfl⟩ := (tr (Bcr l) e).surjective y
    refine (existsUnique_congr fun c => ?_).1 (hu y ((tr_Dcr e _ h' _).1 hy))
    rw [← (tr (Bcr l) e).injective.eq_iff, map_sum]
    simp only [tr_smulC]
  · apply (tr (Bcr l) e).injective
    rw [map_sum, actC, tr_map e (h γ)]
    simp only [tr_smulC]
    exact hM b

end Per

theorem UpperTheory.V.Loc.Dat3.IsType.conj {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    {D : Dat3 l O} {B : Type} [CommRing B] [Algebra O B] [Algebra ℚ_[l] B] {r : GQ l →* GG 3 B}
    (hm : HasMult D.η r) (h : GL (Fin 3) B) (H : D.IsType r) : D.IsType (conjBy h r) := by
  obtain ⟨ρ, hρ, H⟩ := H
  refine ⟨conjGL h ρ, fun g => ?_, potCrysType_equiv (Matrix.toLinearEquiv' (h : Matrix (Fin 3) (Fin 3) B) h.invertible)
    _ (fun g x => ?_) H⟩
  · have h1 : (r g).right = 1 := (hm g).trans ((D.η_ker g).2 g.2)
    have h2 : conjBy h r g = GG.ofGL h * r g * GG.ofGL h⁻¹ := by rw [map_inv]; rfl
    rw [h2, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.left_inl, SemidirectProduct.left_inl, SemidirectProduct.right_inl, h1, mul_one, sgnAct_one,
      sgnAct_one, ← hρ]
    rfl
  · simp [colRep, conjGL, Matrix.toLinearEquiv', Matrix.mul_assoc]
