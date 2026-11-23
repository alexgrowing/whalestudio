import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemSaturatedOrderIsoSubspaceSpanSymmApply

open TensorProduct

namespace GlobalTheory.Forms

abbrev Bil (Y A : Type*) [AddCommGroup Y] [AddCommGroup A] := Y →ₗ[ℤ] Y →ₗ[ℤ] A

section Symmetric

variable (S : Type*) [Semiring S] (Y : Type*) [AddCommGroup Y] (A : Type*) [AddCommGroup A]
  [Module S A]

def symForms : Submodule S (Bil Y A) where
  carrier := {b | ∀ y y', b y y' = b y' y}
  add_mem' {b c} hb hc y y' := by simp only [LinearMap.add_apply, hb y y', hc y y']
  zero_mem' _ _ := rfl
  smul_mem' s b hb y y' := by simp only [LinearMap.smul_apply, hb y y']

variable {S Y A}

theorem mem_symForms {b : Bil Y A} : b ∈ symForms S Y A ↔ ∀ y y', b y y' = b y' y := Iff.rfl

theorem mem_symForms_iff_flip {b : Bil Y A} : b ∈ symForms S Y A ↔ b.flip = b :=
  ⟨fun h => by ext y y'; exact h y' y, fun h y y' => by
    conv_lhs => rw [← h]
    rfl⟩

theorem mem_symForms_iff_isSymm {b : Bil Y ℤ} :
    b ∈ symForms ℤ Y ℤ ↔ LinearMap.BilinForm.IsSymm b :=
  ⟨fun h => ⟨h⟩, fun h => h.eq⟩

variable (Y) in

abbrev SymLattice : Type _ := symForms ℤ Y ℤ

instance [Module.Finite ℤ Y] [Module.Free ℤ Y] (L : Submodule ℤ (Bil Y ℤ)) : Module.Finite ℤ L :=
  Module.Finite.of_injective L.subtype L.injective_subtype

instance [Module.Finite ℤ Y] [Module.Free ℤ Y] (L : Submodule ℤ (Bil Y ℤ)) : Module.Free ℤ L :=
  Module.free_of_finite_type_torsion_free'

end Symmetric

section Pullback

variable (S : Type*) [Semiring S] {Y Y' Y'' : Type*} [AddCommGroup Y] [AddCommGroup Y']
  [AddCommGroup Y''] (A : Type*) [AddCommGroup A] [Module S A]

def pullback (f : Y →ₗ[ℤ] Y') : Bil Y' A →ₗ[S] Bil Y A where
  toFun b := b.compl₁₂ f f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {S A}

@[simp] theorem pullback_apply (f : Y →ₗ[ℤ] Y') (b : Bil Y' A) (y y' : Y) :
    pullback S A f b y y' = b (f y) (f y') := rfl

@[simp] theorem pullback_id : pullback S A (LinearMap.id : Y →ₗ[ℤ] Y) = LinearMap.id := rfl

theorem pullback_comp (f : Y →ₗ[ℤ] Y') (g : Y' →ₗ[ℤ] Y'') :
    pullback S A (g ∘ₗ f) = pullback S A f ∘ₗ pullback S A g := rfl

theorem pullback_injective {f : Y →ₗ[ℤ] Y'} (hf : Function.Surjective f) :
    Function.Injective (pullback S A f) := by
  intro b c h
  ext y y'
  obtain ⟨y, rfl⟩ := hf y
  obtain ⟨y', rfl⟩ := hf y'
  exact congr($h y y')

theorem pullback_mem_symForms (f : Y →ₗ[ℤ] Y') {b : Bil Y' A} (hb : b ∈ symForms S Y' A) :
    pullback S A f b ∈ symForms S Y A := fun _ _ => hb _ _

theorem pullback_mem_symForms_iff {f : Y →ₗ[ℤ] Y'} (hf : Function.Surjective f) {b : Bil Y' A} :
    pullback S A f b ∈ symForms S Y A ↔ b ∈ symForms S Y' A := by
  refine ⟨fun h y y' => ?_, pullback_mem_symForms f⟩
  obtain ⟨y, rfl⟩ := hf y
  obtain ⟨y', rfl⟩ := hf y'
  exact h y y'

theorem mem_range_pullback_iff {f : Y →ₗ[ℤ] Y'} (hf : Function.Surjective f) {b : Bil Y A}
    (hb : b ∈ symForms S Y A) :
    b ∈ LinearMap.range (pullback S A f) ↔ LinearMap.ker f ≤ LinearMap.ker b := by
  constructor
  · rintro ⟨c, rfl⟩ y hy
    rw [LinearMap.mem_ker] at hy ⊢
    ext y'
    simp [hy]
  · intro h
    obtain ⟨c, hc⟩ : ∃ c : Y' →ₗ[ℤ] Y →ₗ[ℤ] A, c ∘ₗ f = b :=
      ⟨(LinearMap.ker f).liftQ b h ∘ₗ (f.quotKerEquivOfSurjective hf).symm.toLinearMap, by
        ext y y'
        simp⟩
    have h' : LinearMap.ker f ≤ LinearMap.ker c.flip := by
      intro y hy
      rw [LinearMap.mem_ker]
      ext z
      obtain ⟨z, rfl⟩ := hf z
      have h1 : c (f z) y = b z y := congr($hc z y)
      have h2 : b y = 0 := h hy
      simp [h1, hb z y, h2]
    obtain ⟨d, hd⟩ : ∃ d : Y' →ₗ[ℤ] Y' →ₗ[ℤ] A, d ∘ₗ f = c.flip :=
      ⟨(LinearMap.ker f).liftQ c.flip h' ∘ₗ (f.quotKerEquivOfSurjective hf).symm.toLinearMap, by
        ext y y'
        simp⟩
    refine ⟨d.flip, ?_⟩
    ext y y'
    have h1 : d (f y') (f y) = c (f y) y' := congr($hd y' (f y))
    have h2 : c (f y) y' = b y y' := congr($hc y y')
    simp [h1, h2]

variable (S A) in

def symPullback (f : Y →ₗ[ℤ] Y') : symForms S Y' A →ₗ[S] symForms S Y A :=
  (pullback S A f).restrict fun _ hb => pullback_mem_symForms f hb

@[simp] theorem coe_symPullback (f : Y →ₗ[ℤ] Y') (b : symForms S Y' A) :
    (symPullback S A f b : Bil Y A) = pullback S A f b := rfl

theorem symPullback_injective {f : Y →ₗ[ℤ] Y'} (hf : Function.Surjective f) :
    Function.Injective (symPullback S A f) := fun _ _ h =>
  Subtype.ext (pullback_injective (S := S) hf (congrArg Subtype.val h))

variable (S Y A) in

def glAction : (Y ≃ₗ[ℤ] Y) →* (Bil Y A ≃ₗ[S] Bil Y A) where
  toFun g :=
    { pullback S A g.symm.toLinearMap with
      invFun := pullback S A g.toLinearMap
      left_inv := fun b => by ext y y'; simp
      right_inv := fun b => by ext y y'; simp }
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem glAction_apply (g : Y ≃ₗ[ℤ] Y) (b : Bil Y A) (y y' : Y) :
    glAction S Y A g b y y' = b (g.symm y) (g.symm y') := rfl

theorem glAction_eq_pullback (g : Y ≃ₗ[ℤ] Y) (b : Bil Y A) :
    glAction S Y A g b = pullback S A g.symm.toLinearMap b := rfl

def restrictAction {Γ : Type*} [Group Γ] (ρ : Γ →* (Y ≃ₗ[ℤ] Y)) (L : Submodule S (Bil Y A))
    (hL : ∀ γ, ∀ b ∈ L, glAction S Y A (ρ γ) b ∈ L) : Γ →* (L ≃ₗ[S] L) where
  toFun γ :=
    { (glAction S Y A (ρ γ)).toLinearMap.restrict (hL γ) with
      invFun := (glAction S Y A (ρ γ⁻¹)).toLinearMap.restrict (hL γ⁻¹)
      left_inv := fun b => Subtype.ext <| by
        change (glAction S Y A (ρ γ⁻¹) * glAction S Y A (ρ γ)) b.1 = b.1
        rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]; rfl
      right_inv := fun b => Subtype.ext <| by
        change (glAction S Y A (ρ γ) * glAction S Y A (ρ γ⁻¹)) b.1 = b.1
        rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]; rfl }
  map_one' := by
    ext b : 2
    change glAction S Y A (ρ 1) b.1 = b.1
    rw [map_one, map_one]; rfl
  map_mul' γ δ := by
    ext b : 2
    change glAction S Y A (ρ (γ * δ)) b.1 = (glAction S Y A (ρ γ) * glAction S Y A (ρ δ)) b.1
    rw [map_mul, map_mul]

@[simp] theorem coe_restrictAction {Γ : Type*} [Group Γ] (ρ : Γ →* (Y ≃ₗ[ℤ] Y))
    (L : Submodule S (Bil Y A)) (hL : ∀ γ, ∀ b ∈ L, glAction S Y A (ρ γ) b ∈ L) (γ : Γ) (b : L) :
    (restrictAction ρ L hL γ b : Bil Y A) = glAction S Y A (ρ γ) b := rfl

theorem glAction_mem_symForms (g : Y ≃ₗ[ℤ] Y) {b : Bil Y A} (hb : b ∈ symForms S Y A) :
    glAction S Y A g b ∈ symForms S Y A := fun _ _ => hb _ _

variable (S Y A) in

def symAction : (Y ≃ₗ[ℤ] Y) →* (symForms S Y A ≃ₗ[S] symForms S Y A) :=
  restrictAction (MonoidHom.id _) _ fun g _ hb => glAction_mem_symForms g hb

@[simp] theorem symAction_apply (g : Y ≃ₗ[ℤ] Y) (b : symForms S Y A) (y y' : Y) :
    (symAction S Y A g b : Bil Y A) y y' = (b : Bil Y A) (g.symm y) (g.symm y') := rfl

end Pullback

section SymSq

variable {S : Type*} [Semiring S] (Y : Type*) [AddCommGroup Y]

def symRel : AddSubgroup (Y ⊗[ℤ] Y) :=
  AddSubgroup.closure {x | ∃ y y' : Y, x = y ⊗ₜ y' - y' ⊗ₜ y}

def SymSq : Type _ := (Y ⊗[ℤ] Y) ⧸ symRel Y

instance : AddCommGroup (SymSq Y) := inferInstanceAs (AddCommGroup ((Y ⊗[ℤ] Y) ⧸ symRel Y))

namespace SymSq

def ofTensor : Y ⊗[ℤ] Y →+ SymSq Y := QuotientAddGroup.mk' (symRel Y)

theorem ofTensor_surjective : Function.Surjective (ofTensor Y) :=
  QuotientAddGroup.mk'_surjective _

theorem ker_ofTensor : (ofTensor Y).ker = symRel Y := QuotientAddGroup.ker_mk' _

variable {Y}

def mk : Bil Y (SymSq Y) :=
  LinearMap.mk₂ ℤ (fun y y' => ofTensor Y (y ⊗ₜ y'))
    (fun _ _ _ => by rw [add_tmul, map_add])
    (fun n y y' => by rw [← map_zsmul]; rfl)
    (fun _ _ _ => by rw [tmul_add, map_add])
    (fun n y y' => by rw [← map_zsmul, ← smul_tmul]; rfl)

theorem mk_apply (y y' : Y) : mk y y' = ofTensor Y (y ⊗ₜ y') := rfl

theorem mk_comm (y y' : Y) : mk y y' = mk y' y := by
  rw [mk_apply, mk_apply, ← sub_eq_zero, ← map_sub, ← AddMonoidHom.mem_ker, ker_ofTensor]
  exact AddSubgroup.subset_closure ⟨y, y', rfl⟩

@[ext high] theorem hom_ext {A : Type*} [AddCommGroup A] {f g : SymSq Y →ₗ[ℤ] A}
    (h : ∀ y y', f (mk y y') = g (mk y y')) : f = g := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := ofTensor_surjective Y x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul y y' => exact h y y'
  | add x y hx hy => simp only [map_add, hx, hy]

theorem span_mk : Submodule.span ℤ {x : SymSq Y | ∃ y y', x = mk y y'} = ⊤ := by
  rw [← Submodule.ker_mkQ (Submodule.span ℤ _), LinearMap.ker_eq_top]
  ext y y'
  exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨y, y', rfl⟩)

variable {A : Type*} [AddCommGroup A] [Module S A]

variable (S Y A) in

def lift : symForms S Y A ≃ₗ[S] (SymSq Y →ₗ[ℤ] A) where
  toFun b := AddMonoidHom.toIntLinearMap (M := SymSq Y) <|
    QuotientAddGroup.lift (symRel Y) (TensorProduct.lift b.1).toAddMonoidHom <|
      (AddSubgroup.closure_le _).2 <| by
        rintro _ ⟨y, y', rfl⟩
        rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub]
        exact sub_eq_zero.2 (b.2 y y')
  map_add' b c := by ext; rfl
  map_smul' s b := by ext; rfl
  invFun l := ⟨mk.compr₂ l, fun y y' => congrArg l (mk_comm y y')⟩
  left_inv b := by ext; rfl
  right_inv l := by ext; rfl

@[simp] theorem lift_mk (b : symForms S Y A) (y y' : Y) :
    lift S Y A b (mk y y') = (b : Bil Y A) y y' := rfl

@[simp] theorem lift_symm_apply (l : SymSq Y →ₗ[ℤ] A) (y y' : Y) :
    ((lift S Y A).symm l : Bil Y A) y y' = l (mk y y') := rfl

def map {Y' : Type*} [AddCommGroup Y'] (f : Y →ₗ[ℤ] Y') : SymSq Y →ₗ[ℤ] SymSq Y' :=
  lift ℤ Y (SymSq Y') ⟨pullback ℤ _ f mk, fun _ _ => mk_comm _ _⟩

@[simp] theorem map_mk {Y' : Type*} [AddCommGroup Y'] (f : Y →ₗ[ℤ] Y') (y y' : Y) :
    map f (mk y y') = mk (f y) (f y') := rfl

theorem lift_symPullback {Y' : Type*} [AddCommGroup Y'] (f : Y →ₗ[ℤ] Y') (b : symForms S Y' A) :
    lift S Y A (symPullback S A f b) = lift S Y' A b ∘ₗ map f := by
  ext; rfl

noncomputable def basis {ι : Type*} (e : Module.Basis ι ℤ Y) : Module.Basis (Sym2 ι) ℤ (SymSq Y) :=
  .ofRepr <| LinearEquiv.ofLinear
    (lift ℤ Y (Sym2 ι →₀ ℤ)
      ⟨e.constr ℤ fun i => e.constr ℤ fun j => Finsupp.single s(i, j) 1, by
        rw [mem_symForms_iff_flip]
        refine e.ext fun i => e.ext fun j => ?_
        simp only [LinearMap.flip_apply, Module.Basis.constr_basis, Sym2.eq_swap]⟩)
    (Finsupp.linearCombination ℤ (Sym2.lift ⟨fun i j => mk (e i) (e j), fun _ _ => mk_comm _ _⟩))
    (by
      refine Finsupp.lhom_ext' fun p => LinearMap.ext_ring ?_
      induction p using Sym2.ind with
      | h i j => simp)
    (by
      refine (lift ℤ Y (SymSq Y)).symm.injective (Subtype.ext ?_)
      refine e.ext fun i => e.ext fun j => ?_
      simp)

@[simp] theorem basis_apply {ι : Type*} (e : Module.Basis ι ℤ Y) (i j : ι) :
    basis e s(i, j) = mk (e i) (e j) := by
  simp [basis, Module.Basis.coe_ofRepr]

instance [Module.Free ℤ Y] : Module.Free ℤ (SymSq Y) :=
  .of_basis (basis (Module.Free.chooseBasis ℤ Y))

instance [Module.Finite ℤ Y] : Module.Finite ℤ (SymSq Y) :=
by
  have h : Module.Finite ℤ (Y ⊗[ℤ] Y) := by
    convert Module.Finite.tensorProduct ℤ Y Y using 0
    congr!
  exact Module.Finite.of_surjective (ofTensor Y).toIntLinearMap (ofTensor_surjective Y)

theorem finrank_eq [Module.Finite ℤ Y] [Module.Free ℤ Y] :
    Module.finrank ℤ (SymSq Y) = (Module.finrank ℤ Y + 1).choose 2 := by
  classical
  rw [Module.finrank_eq_card_basis (basis (Module.Free.chooseBasis ℤ Y)), Sym2.card,
    Module.finrank_eq_card_chooseBasisIndex]

variable (Y) in

noncomputable def dualEquiv [Module.Finite ℤ Y] [Module.Free ℤ Y] :
    SymSq Y ≃ₗ[ℤ] Module.Dual ℤ (SymLattice Y) :=
  Module.evalEquiv ℤ (SymSq Y) ≪≫ₗ (lift ℤ Y ℤ).dualMap

@[simp] theorem dualEquiv_apply [Module.Finite ℤ Y] [Module.Free ℤ Y] (x : SymSq Y)
    (b : SymLattice Y) : dualEquiv Y x b = lift ℤ Y ℤ b x := rfl

theorem dualEquiv_mk [Module.Finite ℤ Y] [Module.Free ℤ Y] (y y' : Y) (b : SymLattice Y) :
    dualEquiv Y (mk y y') b = (b : Bil Y ℤ) y y' := rfl

variable (Y) in

noncomputable def equivSymmetricPower : SymSq Y ≃+ Sym[ℤ]^2 Y :=
  let F : SymSq Y →+ Sym[ℤ]^2 Y := (lift ℤ Y (Sym[ℤ]^2 Y) ⟨
    (AddMonoidHom.mk' (fun y => (AddMonoidHom.mk' (fun y' => SymmetricPower.tprod ℤ ![y, y'])
      fun a b => by
        have := (SymmetricPower.tprod ℤ (ι := Fin 2) (M := Y)).map_update_add ![y, 0] 1 a b
        have h (c : Y) : Function.update ![y, 0] 1 c = ![y, c] := by
          ext i; fin_cases i <;> simp
        simpa only [h] using this).toIntLinearMap) fun a b => by
        ext y'
        have := (SymmetricPower.tprod ℤ (ι := Fin 2) (M := Y)).map_update_add ![0, y'] 0 a b
        have h (c : Y) : Function.update ![0, y'] 0 c = ![c, y'] := by
          ext i; fin_cases i <;> simp
        simp only [h] at this
        exact this).toIntLinearMap, fun y y' => by
      have := SymmetricPower.tprod_equiv (R := ℤ) (Equiv.swap (0 : Fin 2) 1) ![y', y]
      refine Eq.trans (congrArg (SymmetricPower.tprod ℤ) ?_) this
      ext i; fin_cases i <;> simp⟩).toAddMonoidHom
  let m : MultilinearMap ℤ (fun _ : Fin 2 => Y) (SymSq Y) :=
    { toFun := fun f => mk (f 0) (f 1)
      map_update_add' := fun f i a b => by
        fin_cases i <;> simp [Function.update_apply]
      map_update_smul' := fun f i a b => by
        fin_cases i <;> simp [Function.update_apply] }
  let G : Sym[ℤ]^2 Y →+ SymSq Y :=
    AddCon.lift _ (PiTensorProduct.lift m).toAddMonoidHom <| AddCon.addConGen_le.2 <| by
      rintro _ _ ⟨σ, f⟩
      rw [AddCon.ker_rel]
      refine (PiTensorProduct.lift.tprod (φ := m) f).trans
        (Eq.trans ?_ (PiTensorProduct.lift.tprod (φ := m) fun i => f (σ i)).symm)
      change mk (f 0) (f 1) = mk (f (σ 0)) (f (σ 1))
      have hσ : (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0) := by
        revert σ; decide
      rcases hσ with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · rw [h0, h1]
      · rw [h0, h1, mk_comm]
  have hG (f : Fin 2 → Y) : G (SymmetricPower.tprod ℤ f) = mk (f 0) (f 1) :=
    PiTensorProduct.lift.tprod (φ := m) f
  AddMonoidHom.toAddEquiv F G
    (by
      have : (G.comp F).toIntLinearMap = LinearMap.id := by
        ext y y'
        exact hG ![y, y']
      exact congrArg LinearMap.toAddMonoidHom this)
    (by
      ext x
      obtain ⟨x, rfl⟩ := LinearMap.range_eq_top.1 (SymmetricPower.range_mk ℤ (Fin 2) Y) x
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        have h1 : F (G (SymmetricPower.tprod ℤ f)) = SymmetricPower.tprod ℤ f := by
          rw [hG]
          change SymmetricPower.tprod ℤ ![f 0, f 1] = _
          congr 1
          ext i; fin_cases i <;> rfl
        have h2 := map_zsmul (SymmetricPower.mk ℤ (Fin 2) Y).toAddMonoidHom r
          (PiTensorProduct.tprod ℤ f)
        refine (congrArg (F.comp G) h2).trans (Eq.trans ?_ h2.symm)
        rw [map_zsmul]
        exact congrArg _ h1
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy])

@[simp] theorem equivSymmetricPower_mk (y y' : Y) :
    equivSymmetricPower Y (mk y y') = SymmetricPower.tprod ℤ ![y, y'] := rfl

end SymSq

theorem finrank_symLattice [Module.Finite ℤ Y] [Module.Free ℤ Y] :
    Module.finrank ℤ (SymLattice Y) = (Module.finrank ℤ Y + 1).choose 2 := by
  rw [(SymSq.lift ℤ Y ℤ).finrank_eq, ← SymSq.finrank_eq]
  exact Module.finrank_linearMap_self ℤ ℤ _

end SymSq

section Balanced

variable {S : Type*} [Semiring S] (O : Type*) [CommRing O] [StarRing O] {Y Y' : Type*} [AddCommGroup Y] [Module O Y]
  [AddCommGroup Y'] [Module O Y'] {A : Type*} [AddCommGroup A]

def IsBalanced (b : Bil Y A) : Prop := ∀ (a : O) (y y' : Y), b (a • y) y' = b y (star a • y')

variable {O}

theorem IsBalanced.right {b : Bil Y A} (hb : IsBalanced O b) (a : O) (y y' : Y) :
    b y (a • y') = b (star a • y) y' := by
  rw [hb, star_star]

theorem IsBalanced.smul_smul {b : Bil Y A} (hb : IsBalanced O b) (w : O) (y y' : Y) :
    b (w • y) (w • y') = b y ((w * star w) • y') := by
  rw [hb, _root_.smul_smul, mul_comm]

theorem IsBalanced.smul_smul_of_norm {b : Bil Y A} (hb : IsBalanced O b) {w : O} {n : ℤ}
    (hn : (n : O) = w * star w) (y y' : Y) : b (w • y) (w • y') = n • b y y' := by
  rw [hb.smul_smul, ← hn, Int.cast_smul_eq_zsmul, map_zsmul]

theorem IsBalanced.add_of_add_star {b : Bil Y A} (hb : IsBalanced O b) {w : O}
    (hw : w + star w = 1) (y y' : Y) : b y (w • y') + b (w • y) y' = b y y' := by
  rw [hb, ← map_add, ← add_smul, hw, one_smul]

theorem IsBalanced.smul_mem_ker {b : Bil Y A} (hb : IsBalanced O b) (a : O) {y : Y}
    (hy : y ∈ LinearMap.ker b) : a • y ∈ LinearMap.ker b := by
  rw [LinearMap.mem_ker] at hy ⊢
  ext y'
  rw [hb, hy]
  rfl

def IsBalanced.radical {b : Bil Y A} (hb : IsBalanced O b) : Submodule O Y where
  __ := (LinearMap.ker b).toAddSubmonoid
  smul_mem' a _ hy := hb.smul_mem_ker a hy

theorem IsBalanced.mem_radical {b : Bil Y A} (hb : IsBalanced O b) {y : Y} :
    y ∈ hb.radical ↔ b y = 0 := Iff.rfl

variable [Module S A]

variable (S O Y A) in

def balForms : Submodule S (Bil Y A) where
  carrier := {b | b ∈ symForms S Y A ∧ IsBalanced O b}
  add_mem' {b c} hb hc := ⟨add_mem hb.1 hc.1, fun a y y' => by
    simp only [LinearMap.add_apply, hb.2 a y y', hc.2 a y y']⟩
  zero_mem' := ⟨zero_mem _, fun _ _ _ => rfl⟩
  smul_mem' s b hb := ⟨Submodule.smul_mem _ s hb.1, fun a y y' => by
    simp only [LinearMap.smul_apply, hb.2 a y y']⟩

variable (O Y) in

abbrev BalLattice : Type _ := balForms ℤ O Y ℤ

theorem mem_balForms {b : Bil Y A} :
    b ∈ balForms S O Y A ↔ b ∈ symForms S Y A ∧ IsBalanced O b := Iff.rfl

variable (S O Y A) in
theorem balForms_le_symForms : balForms S O Y A ≤ symForms S Y A := fun _ hb => hb.1

theorem add_self_of_add_star {b : Bil Y A} (hb : b ∈ balForms S O Y A) {w : O}
    (hw : w + star w = 1) (y : Y) : b y (w • y) + b y (w • y) = b y y := by
  rw [← hb.2.add_of_add_star hw y y, hb.1 (w • y) y]

theorem smul_smul_self_of_norm {b : Bil Y A} (hb : b ∈ balForms S O Y A) {w : O} {n : ℤ}
    (hn : (n : O) = w * star w) (y : Y) : b (w • y) (w • y) = n • b y y :=
  hb.2.smul_smul_of_norm hn y y

theorem even_apply_self_of_add_star {b : Bil Y ℤ} (hb : b ∈ balForms ℤ O Y ℤ) {w : O}
    (hw : w + star w = 1) (y : Y) : Even (b y y) :=
  ⟨_, (add_self_of_add_star hb hw y).symm⟩

theorem balForms_int {Y : Type*} [AddCommGroup Y] : balForms S ℤ Y A = symForms S Y A :=
  le_antisymm (balForms_le_symForms S ℤ Y A) fun b hb => ⟨hb, fun a y y' => by simp⟩

def traceForm (t : O →ₗ[ℤ] A) : Bil O A :=
  LinearMap.mk₂ ℤ (fun x y => t (x * star y))
    (fun _ _ _ => by rw [add_mul, map_add])
    (fun _ _ _ => by rw [smul_mul_assoc, map_smul])
    (fun _ _ _ => by rw [star_add, mul_add, map_add])
    (fun _ _ _ => by rw [star_zsmul, mul_smul_comm, map_smul])

@[simp] theorem traceForm_apply (t : O →ₗ[ℤ] A) (x y : O) : traceForm t x y = t (x * star y) := rfl

theorem traceForm_mem_balForms {t : O →ₗ[ℤ] A} (ht : ∀ x, t (star x) = t x) :
    traceForm t ∈ balForms S O O A :=
  ⟨fun x y => by rw [traceForm_apply, traceForm_apply, ← ht, star_mul, star_star],
    fun a x y => by
      rw [traceForm_apply, traceForm_apply, smul_eq_mul, smul_eq_mul, star_mul, star_star]
      congr 1
      ring⟩

theorem mem_symForms_of_zsmul_mem [Module.IsTorsionFree ℤ A] {Y : Type*} [AddCommGroup Y]
    {b : Bil Y A} {n : ℤ} (hn : n ≠ 0) (hb : n • b ∈ symForms S Y A) : b ∈ symForms S Y A :=
  fun y y' => smul_right_injective A hn (hb y y')

theorem mem_balForms_of_zsmul_mem [Module.IsTorsionFree ℤ A] {b : Bil Y A} {n : ℤ} (hn : n ≠ 0)
    (hb : n • b ∈ balForms S O Y A) : b ∈ balForms S O Y A :=
  ⟨mem_symForms_of_zsmul_mem hn hb.1, fun a y y' => smul_right_injective A hn (hb.2 a y y')⟩

variable (O Y) in

def balInclusion : BalLattice O Y →ₗ[ℤ] SymLattice Y :=
  Submodule.inclusion (balForms_le_symForms ℤ O Y ℤ)

@[simp] theorem coe_balInclusion (b : BalLattice O Y) :
    (balInclusion O Y b : Bil Y ℤ) = b := rfl

variable (O Y) in
theorem balInclusion_injective : Function.Injective (balInclusion O Y) :=
  Submodule.inclusion_injective _

theorem mem_range_balInclusion {b : SymLattice Y} :
    b ∈ LinearMap.range (balInclusion O Y) ↔ IsBalanced O (b : Bil Y ℤ) :=
  ⟨by rintro ⟨c, rfl⟩; exact c.2.2, fun h => ⟨⟨b, b.2, h⟩, rfl⟩⟩

theorem isSaturated_symForms (Y : Type*) [AddCommGroup Y] :
    IsSaturatedSubmodule (symForms ℤ Y ℤ) :=
  isSaturatedSubmodule_iff.2 fun _ hn _ hb => mem_symForms_of_zsmul_mem hn hb

variable (O Y) in

theorem isSaturated_balForms : IsSaturatedSubmodule (balForms ℤ O Y ℤ) :=
  isSaturatedSubmodule_iff.2 fun _ hn _ hb => mem_balForms_of_zsmul_mem hn hb

variable (O Y) in

theorem isSaturated_range_balInclusion :
    IsSaturatedSubmodule (LinearMap.range (balInclusion O Y)) :=
  isSaturatedSubmodule_iff.2 fun n hn b hb => mem_range_balInclusion.2
    (mem_balForms_of_zsmul_mem (S := ℤ) hn ⟨(n • b).2, mem_range_balInclusion.1 hb⟩).2

instance : Module.IsTorsionFree ℤ (SymLattice Y ⧸ LinearMap.range (balInclusion O Y)) :=
  (isSaturated_range_balInclusion O Y).isTorsionFree_quotient

variable (O Y) in

theorem exists_isCompl_range_balInclusion [Module.Finite ℤ Y] [Module.Free ℤ Y] :
    ∃ Q : Submodule ℤ (SymLattice Y), IsCompl (LinearMap.range (balInclusion O Y)) Q := by
  have : Module.Free ℤ (SymLattice Y ⧸ LinearMap.range (balInclusion O Y)) :=
    Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (LinearMap.range (balInclusion O Y)).mkQ LinearMap.id (Submodule.mkQ_surjective _)
  refine ⟨LinearMap.range s, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨q, rfl⟩
    have h1 : q = 0 := by
      rw [← (Submodule.Quotient.mk_eq_zero _).2 hx]
      exact (congr($hs q)).symm
    rw [h1, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    refine Submodule.mem_sup.2 ⟨x - s (Submodule.Quotient.mk x), ?_, _, ⟨_, rfl⟩,
      sub_add_cancel _ _⟩
    rw [← Submodule.Quotient.eq]
    exact (congr($hs (Submodule.Quotient.mk x))).symm

theorem IsBalanced.pullback_of_semilinear {O' Z : Type*} [CommRing O'] [StarRing O']
    [AddCommGroup Z] [Module O' Z] (σ : O → O') (hσ : ∀ a, σ (star a) = star (σ a))
    (f : Y →ₗ[ℤ] Z) (hf : ∀ (a : O) y, f (a • y) = σ a • f y) {b : Bil Z A}
    (hb : IsBalanced O' b) : IsBalanced O (pullback S A f b) := fun a y y' => by
  rw [pullback_apply, pullback_apply, hf, hf, hσ, hb]

theorem pullback_mem_balForms (f : Y →ₗ[O] Y') {b : Bil Y' A} (hb : b ∈ balForms S O Y' A) :
    pullback S A (f.restrictScalars ℤ) b ∈ balForms S O Y A :=
  ⟨pullback_mem_symForms _ hb.1,
    hb.2.pullback_of_semilinear id (fun _ => rfl) _ fun a y => f.map_smul a y⟩

theorem pullback_mem_balForms_iff {f : Y →ₗ[O] Y'} (hf : Function.Surjective f) {b : Bil Y' A} :
    pullback S A (f.restrictScalars ℤ) b ∈ balForms S O Y A ↔ b ∈ balForms S O Y' A := by
  refine ⟨fun h => ⟨(pullback_mem_symForms_iff (f := f.restrictScalars ℤ) hf).1 h.1,
    fun a y y' => ?_⟩, pullback_mem_balForms f⟩
  obtain ⟨y, rfl⟩ := hf y
  obtain ⟨y', rfl⟩ := hf y'
  rw [← f.map_smul, ← f.map_smul]
  exact h.2 a y y'

variable (S A) in

def balPullback (f : Y →ₗ[O] Y') : balForms S O Y' A →ₗ[S] balForms S O Y A :=
  (pullback S A (f.restrictScalars ℤ)).restrict fun _ hb => pullback_mem_balForms f hb

@[simp] theorem balPullback_apply (f : Y →ₗ[O] Y') (b : balForms S O Y' A) (y y' : Y) :
    (balPullback S A f b : Bil Y A) y y' = (b : Bil Y' A) (f y) (f y') := rfl

theorem balPullback_injective {f : Y →ₗ[O] Y'} (hf : Function.Surjective f) :
    Function.Injective (balPullback S A f) := fun _ _ h =>
  Subtype.ext (pullback_injective (S := S) (f := f.restrictScalars ℤ) hf (congrArg Subtype.val h))

omit [StarRing O] in
variable (O Y) in

def autToGL : (Y ≃ₗ[O] Y) →* (Y ≃ₗ[ℤ] Y) where
  toFun g := g.restrictScalars ℤ
  map_one' := rfl
  map_mul' _ _ := rfl

omit [StarRing O] in
@[simp] theorem autToGL_apply (g : Y ≃ₗ[O] Y) (y : Y) : autToGL O Y g y = g y := rfl

omit [StarRing O] in
@[simp] theorem autToGL_symm_apply (g : Y ≃ₗ[O] Y) (y : Y) :
    (autToGL O Y g).symm y = g.symm y := rfl

theorem glAction_mem_balForms (g : Y ≃ₗ[O] Y) {b : Bil Y A} (hb : b ∈ balForms S O Y A) :
    glAction S Y A (autToGL O Y g) b ∈ balForms S O Y A :=
  pullback_mem_balForms g.symm.toLinearMap hb

theorem glAction_mem_balForms_of_semilinear (σ : O ≃+* O) (hσ : ∀ a, σ (star a) = star (σ a))
    (g : Y ≃ₗ[ℤ] Y) (hg : ∀ (a : O) y, g (a • y) = σ a • g y) {b : Bil Y A}
    (hb : b ∈ balForms S O Y A) : glAction S Y A g b ∈ balForms S O Y A := by
  refine ⟨glAction_mem_symForms g hb.1, hb.2.pullback_of_semilinear (S := S) σ.symm (fun a => ?_)
    g.symm.toLinearMap fun a y => ?_⟩
  · apply σ.injective
    rw [hσ, σ.apply_symm_apply, σ.apply_symm_apply]
  · apply g.injective
    simp [hg]

variable (S O Y A) in

def autAction : (Y ≃ₗ[O] Y) →* (balForms S O Y A ≃ₗ[S] balForms S O Y A) :=
  restrictAction (autToGL O Y) _ fun g _ hb => glAction_mem_balForms g hb

@[simp] theorem autAction_apply (g : Y ≃ₗ[O] Y) (b : balForms S O Y A) (y y' : Y) :
    (autAction S O Y A g b : Bil Y A) y y' = (b : Bil Y A) (g.symm y) (g.symm y') := rfl

theorem balInclusion_autAction (g : Y ≃ₗ[O] Y) (b : BalLattice O Y) :
    balInclusion O Y (autAction ℤ O Y ℤ g b) =
      symAction ℤ Y ℤ (autToGL O Y g) (balInclusion O Y b) := rfl

variable (O Y) in

def balRel : Submodule ℤ (SymSq Y) :=
  saturation (Submodule.span ℤ
    {x : SymSq Y | ∃ (a : O) (y y' : Y), x = SymSq.mk (a • y) y' - SymSq.mk y (star a • y')})

theorem mem_balRel {x : SymSq Y} : x ∈ balRel O Y ↔ ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ Submodule.span ℤ
    {x : SymSq Y | ∃ (a : O) (y y' : Y), x = SymSq.mk (a • y) y' - SymSq.mk y (star a • y')} :=
  mem_saturation_iff

variable (O Y) in

abbrev BalSq : Type _ := SymSq Y ⧸ balRel O Y

namespace BalSq

variable (O) in

def mk : Bil Y (BalSq O Y) := SymSq.mk.compr₂ (balRel O Y).mkQ

theorem mk_apply (y y' : Y) : mk O y y' = (balRel O Y).mkQ (SymSq.mk y y') := rfl

variable (O Y) in
theorem mk_mem_balForms : mk O ∈ balForms ℤ O Y (BalSq O Y) :=
  ⟨fun y y' => congrArg (balRel O Y).mkQ (SymSq.mk_comm y y'), fun a y y' =>
    (Submodule.Quotient.eq _).2 <| mem_balRel.2
      ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span ⟨a, y, y', rfl⟩⟩⟩

@[ext high] theorem hom_ext {f g : BalSq O Y →ₗ[ℤ] A}
    (h : ∀ y y', f (mk O y y') = g (mk O y y')) : f = g :=
  Submodule.linearMap_qext _ (SymSq.hom_ext h)

instance : Module.IsTorsionFree ℤ (BalSq O Y) := isTorsionFree_quotient_saturation _

instance [Module.Finite ℤ Y] : Module.Free ℤ (BalSq O Y) :=
  Module.free_of_finite_type_torsion_free'

variable (S O Y A) in

def lift [Module.IsTorsionFree ℤ A] : balForms S O Y A ≃ₗ[S] (BalSq O Y →ₗ[ℤ] A) where
  toFun b := (balRel O Y).liftQ (SymSq.lift S Y A ⟨b.1, b.2.1⟩) <| by
    intro x hx
    obtain ⟨n, hn, hx⟩ := mem_balRel.1 hx
    have h : n • x ∈ LinearMap.ker (SymSq.lift S Y A ⟨b.1, b.2.1⟩) := by
      refine Submodule.span_le.2 ?_ hx
      rintro _ ⟨a, y, y', rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.2 (b.2.2 a y y')
    rw [LinearMap.mem_ker, map_smul] at h
    exact (smul_eq_zero.1 h).resolve_left hn
  map_add' b c := by ext; rfl
  map_smul' s b := by ext; rfl
  invFun l := ⟨(mk O).compr₂ l, fun y y' => congrArg l ((mk_mem_balForms O Y).1 y y'),
    fun a y y' => congrArg l ((mk_mem_balForms O Y).2 a y y')⟩
  left_inv b := by ext; rfl
  right_inv l := by ext; rfl

@[simp] theorem lift_mk [Module.IsTorsionFree ℤ A] (b : balForms S O Y A) (y y' : Y) :
    lift S O Y A b (mk O y y') = (b : Bil Y A) y y' := rfl

@[simp] theorem lift_symm_apply [Module.IsTorsionFree ℤ A] (l : BalSq O Y →ₗ[ℤ] A) (y y' : Y) :
    ((lift S O Y A).symm l : Bil Y A) y y' = l (mk O y y') := rfl

variable (O Y) in

noncomputable def dualEquiv [Module.Finite ℤ Y] :
    BalSq O Y ≃ₗ[ℤ] Module.Dual ℤ (BalLattice O Y) :=
  Module.evalEquiv ℤ (BalSq O Y) ≪≫ₗ (lift ℤ O Y ℤ).dualMap

@[simp] theorem dualEquiv_apply [Module.Finite ℤ Y] (x : BalSq O Y) (b : BalLattice O Y) :
    dualEquiv O Y x b = lift ℤ O Y ℤ b x := rfl

theorem dualEquiv_mk [Module.Finite ℤ Y] (y y' : Y) (b : BalLattice O Y) :
    dualEquiv O Y (mk O y y') b = (b : Bil Y ℤ) y y' := rfl

theorem dualEquiv_mkQ [Module.Finite ℤ Y] [Module.Free ℤ Y] (x : SymSq Y) :
    dualEquiv O Y ((balRel O Y).mkQ x) = (balInclusion O Y).dualMap (SymSq.dualEquiv Y x) := rfl

end BalSq

variable (O Y) in

theorem dualMap_balInclusion_surjective [Module.Finite ℤ Y] [Module.Free ℤ Y] :
    Function.Surjective (balInclusion O Y).dualMap := by
  intro l
  obtain ⟨x, rfl⟩ := (BalSq.dualEquiv O Y).surjective l
  obtain ⟨x, rfl⟩ := (balRel O Y).mkQ_surjective x
  exact ⟨_, (BalSq.dualEquiv_mkQ x).symm⟩

end Balanced

section Level

variable {Y Y' : Type*} [AddCommGroup Y] [AddCommGroup Y']

def level (M : ℤ) (L : Submodule ℤ (Bil Y ℤ)) : Submodule ℤ (Bil Y ℤ) :=
  L.map (LinearMap.lsmul ℤ _ M)

theorem mem_level {M : ℤ} {L : Submodule ℤ (Bil Y ℤ)} {b : Bil Y ℤ} :
    b ∈ level M L ↔ ∃ c ∈ L, M • c = b := Iff.rfl

theorem smul_mem_level (M : ℤ) {L : Submodule ℤ (Bil Y ℤ)} {b : Bil Y ℤ} (hb : b ∈ L) :
    M • b ∈ level M L := ⟨b, hb, rfl⟩

theorem level_le (M : ℤ) (L : Submodule ℤ (Bil Y ℤ)) : level M L ≤ L := by
  rintro _ ⟨c, hc, rfl⟩
  exact L.smul_mem M hc

theorem level_mono (M : ℤ) {L L' : Submodule ℤ (Bil Y ℤ)} (h : L ≤ L') :
    level M L ≤ level M L' := Submodule.map_mono h

@[simp] theorem level_one (L : Submodule ℤ (Bil Y ℤ)) : level 1 L = L :=
  le_antisymm (level_le 1 L) fun b hb => ⟨b, hb, one_smul ℤ b⟩

theorem level_mul (M N : ℤ) (L : Submodule ℤ (Bil Y ℤ)) :
    level (M * N) L = level M (level N L) := by
  ext b
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨N • c, smul_mem_level N hc, (mul_smul M N c).symm⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, mul_smul M N c⟩

theorem level_le_level_of_dvd {M N : ℤ} (h : M ∣ N) (L : Submodule ℤ (Bil Y ℤ)) :
    level N L ≤ level M L := by
  obtain ⟨k, rfl⟩ := h
  rw [level_mul]
  exact level_mono M (level_le k L)

theorem mem_level_top {M : ℤ} {b : Bil Y ℤ} : b ∈ level M ⊤ ↔ ∀ y y', M ∣ b y y' := by
  constructor
  · rintro ⟨c, -, rfl⟩ y y'
    exact ⟨c y y', rfl⟩
  · intro h
    rcases eq_or_ne M 0 with rfl | hM
    · exact ⟨0, trivial, by ext y y'; exact (zero_dvd_iff.1 (h y y')).symm⟩
    · refine ⟨LinearMap.mk₂ ℤ (fun y y' => b y y' / M) (fun y z y' => ?_) (fun n y y' => ?_)
        (fun y y' z => ?_) (fun n y y' => ?_), trivial, ?_⟩
      · rw [map_add, LinearMap.add_apply, Int.add_ediv_of_dvd_left (h y y')]
      · rw [map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, Int.mul_ediv_assoc _ (h y y')]
      · rw [map_add, Int.add_ediv_of_dvd_left (h y y')]
      · rw [map_smul, smul_eq_mul, smul_eq_mul, Int.mul_ediv_assoc _ (h y y')]
      · ext y y'
        exact Int.mul_ediv_cancel' (h y y')

theorem mem_level_of_saturated {M : ℤ} {L : Submodule ℤ (Bil Y ℤ)}
    (hL : IsSaturatedSubmodule L) {b : Bil Y ℤ} :
    b ∈ level M L ↔ b ∈ L ∧ ∀ y y', M ∣ b y y' := by
  rw [← mem_level_top]
  refine ⟨fun h => ⟨level_le M L h, level_mono M le_top h⟩, ?_⟩
  rintro ⟨hb, c, -, rfl⟩
  rcases eq_or_ne M 0 with rfl | hM
  · exact ⟨0, L.zero_mem, by simp⟩
  · exact smul_mem_level M (hL.mem_of_smul_mem hM hb)

theorem mem_level_symForms {M : ℤ} {b : Bil Y ℤ} :
    b ∈ level M (symForms ℤ Y ℤ) ↔ b ∈ symForms ℤ Y ℤ ∧ ∀ y y', M ∣ b y y' :=
  mem_level_of_saturated (isSaturated_symForms Y)

theorem mem_level_balForms {O : Type*} [CommRing O] [StarRing O] [Module O Y] {M : ℤ}
    {b : Bil Y ℤ} :
    b ∈ level M (balForms ℤ O Y ℤ) ↔ b ∈ balForms ℤ O Y ℤ ∧ ∀ y y', M ∣ b y y' :=
  mem_level_of_saturated (isSaturated_balForms O Y)

theorem level_balForms (O : Type*) [CommRing O] [StarRing O] [Module O Y] (M : ℤ) :
    level M (balForms ℤ O Y ℤ) = level M (symForms ℤ Y ℤ) ⊓ balForms ℤ O Y ℤ := by
  ext b
  rw [Submodule.mem_inf, mem_level_balForms, mem_level_symForms]
  exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩

noncomputable def levelEquiv {M : ℤ} (hM : M ≠ 0) (L : Submodule ℤ (Bil Y ℤ)) :
    L ≃ₗ[ℤ] level M L :=
  Submodule.equivMapOfInjective _ (fun b c h => by
    ext y y'
    exact mul_left_cancel₀ hM congr($h y y')) L

@[simp] theorem coe_levelEquiv {M : ℤ} (hM : M ≠ 0) (L : Submodule ℤ (Bil Y ℤ)) (b : L) :
    (levelEquiv hM L b : Bil Y ℤ) = M • (b : Bil Y ℤ) := rfl

theorem relIndex_level [Module.Finite ℤ Y] [Module.Free ℤ Y] (M : ℕ)
    (L : Submodule ℤ (Bil Y ℤ)) :
    (level M L).toAddSubgroup.relIndex L.toAddSubgroup = M ^ Module.finrank ℤ L := by
  have : Module.Free ℤ L.toAddSubgroup.toIntSubmodule := inferInstance
  have : Module.Finite ℤ L.toAddSubgroup.toIntSubmodule := inferInstance
  have h := AddSubgroup.relIndex_map_nsmul M L.toAddSubgroup
  convert h using 2
  · ext b
    simp [mem_level]
  · rfl

theorem pullback_mem_level (f : Y →ₗ[ℤ] Y') {L : Submodule ℤ (Bil Y ℤ)}
    {L' : Submodule ℤ (Bil Y' ℤ)} (h : ∀ b ∈ L', pullback ℤ ℤ f b ∈ L) (M : ℤ) {b : Bil Y' ℤ}
    (hb : b ∈ level M L') : pullback ℤ ℤ f b ∈ level M L := by
  obtain ⟨c, hc, rfl⟩ := hb
  exact ⟨_, h c hc, rfl⟩

variable (Y) in

def symLevelAction (M : ℤ) :
    (Y ≃ₗ[ℤ] Y) →* (level M (symForms ℤ Y ℤ) ≃ₗ[ℤ] level M (symForms ℤ Y ℤ)) :=
  restrictAction (MonoidHom.id _) _ fun g _ hb =>
    pullback_mem_level g.symm.toLinearMap (fun _ h => glAction_mem_symForms g h) M hb

variable (Y) in

def balLevelAction (O : Type*) [CommRing O] [StarRing O] [Module O Y] (M : ℤ) :
    (Y ≃ₗ[O] Y) →* (level M (balForms ℤ O Y ℤ) ≃ₗ[ℤ] level M (balForms ℤ O Y ℤ)) :=
  restrictAction (autToGL O Y) _ fun g _ hb =>
    pullback_mem_level (autToGL O Y g).symm.toLinearMap
      (fun _ h => glAction_mem_balForms g h) M hb

end Level

end GlobalTheory.Forms
