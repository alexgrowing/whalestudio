import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.CommutingInverses.InvCommOfComm

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def adL (g : GL (Fin n) k) : Module.End k (Matrix (Fin n) (Fin n) k) :=
  LinearMap.mulLeft k g.val ∘ₗ LinearMap.mulRight k g⁻¹.val

theorem adL_apply (g : GL (Fin n) k) (y : Matrix (Fin n) (Fin n) k) : adL g y = g.val * y * g⁻¹.val := by
  simp [adL, mul_assoc]

def cA (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k) :
    Submodule k (Matrix (Fin n) (Fin n) k) where
  carrier := {a | a ∈ Bz Z ∧ a * x = x * a}
  add_mem' {a b} ha hb := ⟨fun z hz => by rw [mul_add, add_mul, ha.1 z hz, hb.1 z hz],
    by rw [add_mul, mul_add, ha.2, hb.2]⟩
  zero_mem' := ⟨fun z _ => by simp, by simp⟩
  smul_mem' c a ha := ⟨fun z hz => by rw [mul_smul_comm, smul_mul_assoc, ha.1 z hz],
    by rw [smul_mul_assoc, mul_smul_comm, ha.2]⟩

def cS (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k) (v : Fin n → k) :
    Submodule k (Matrix (Fin n) (Fin n) k) where
  carrier := {a | a ∈ cA Z x ∧ a *ᵥ v = 0}
  add_mem' {a b} ha hb := ⟨(cA Z x).add_mem ha.1 hb.1, by rw [add_mulVec, ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨(cA Z x).zero_mem, by simp⟩
  smul_mem' c a ha := ⟨(cA Z x).smul_mem c ha.1, by rw [Matrix.smul_mulVec, ha.2, smul_zero]⟩

def mulVecR (v : Fin n → k) : Matrix (Fin n) (Fin n) k →ₗ[k] (Fin n → k) where
  toFun a := a *ᵥ v
  map_add' a b := add_mulVec a b v
  map_smul' c a := Matrix.smul_mulVec c a v

def cAv (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k) (v : Fin n → k) :
    Submodule k (Fin n → k) :=
  (cA Z x).map (mulVecR v)

theorem cC_inv (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (g : GL (Fin n) k) (hg : g ∈ Gz Z) :
    ∀ a ∈ (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule,
      adL g a ∈ (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule := by
  intro a ha
  rw [adL_apply]
  exact PositivityTheory.RgUd.T.Desc.UniPf.conj_mem Z g hg a ha

theorem cA_inv (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k) (g : GL (Fin n) k)
    (hg : g ∈ Gz Z) (t : k) (ht : t ≠ 0) (hgx : g.val * x * g⁻¹.val = t • x) :
    ∀ a ∈ cA Z x, adL g a ∈ cA Z x := by
  intro a ha
  have hgi : g⁻¹.val * g.val = 1 := Units.inv_mul g
  have hB : a ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) := by
    rw [Subalgebra.mem_centralizer_iff]; intro z hz; exact ha.1 z hz
  have hc := PositivityTheory.RgUd.T.Desc.UniPf.conj_mem Z g hg a hB
  rw [Subalgebra.mem_centralizer_iff] at hc
  rw [adL_apply]
  refine ⟨fun z hz => hc z hz, ?_⟩
  apply smul_right_injective (Matrix (Fin n) (Fin n) k) ht
  simp only
  calc t • (g.val * a * g⁻¹.val * x) = g.val * a * g⁻¹.val * (t • x) := by rw [mul_smul_comm]
    _ = g.val * a * g⁻¹.val * (g.val * x * g⁻¹.val) := by rw [hgx]
    _ = g.val * (a * x) * g⁻¹.val := by
        simp only [mul_assoc]; rw [← mul_assoc g⁻¹.val g.val, hgi, one_mul]
    _ = g.val * (x * a) * g⁻¹.val := by rw [ha.2]
    _ = g.val * x * g⁻¹.val * (g.val * a * g⁻¹.val) := by
        simp only [mul_assoc]; rw [← mul_assoc g⁻¹.val g.val, hgi, one_mul]
    _ = (t • x) * (g.val * a * g⁻¹.val) := by rw [hgx]
    _ = t • (x * (g.val * a * g⁻¹.val)) := by rw [smul_mul_assoc]

theorem cS_inv (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k) (v : Fin n → k)
    (g : GL (Fin n) k) (hg : g ∈ Gz Z) (t : k) (ht : t ≠ 0) (hgx : g.val * x * g⁻¹.val = t • x)
    (hgv : g.val *ᵥ v = v) : ∀ a ∈ cS Z x v, adL g a ∈ cS Z x v := by
  intro a ha
  refine ⟨cA_inv Z x g hg t ht hgx a ha.1, ?_⟩
  have hv : g⁻¹.val *ᵥ v = v := by
    conv_lhs => rw [← hgv]
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  show adL g a *ᵥ v = 0
  rw [adL_apply, ← Matrix.mulVec_mulVec, hv, ← Matrix.mulVec_mulVec, ha.2, Matrix.mulVec_zero]

theorem cAv_inv (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k) (v : Fin n → k)
    (g : GL (Fin n) k) (hg : g ∈ Gz Z) (t : k) (ht : t ≠ 0) (hgx : g.val * x * g⁻¹.val = t • x)
    (hgv : g.val *ᵥ v = v) : ∀ y ∈ cAv Z x v, Matrix.toLin' g.val y ∈ cAv Z x v := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hy
  refine Submodule.mem_map.2 ⟨adL g a, cA_inv Z x g hg t ht hgx a ha, ?_⟩
  have hv : g⁻¹.val *ᵥ v = v := by
    conv_lhs => rw [← hgv]
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  show adL g a *ᵥ v = Matrix.toLin' g.val (a *ᵥ v)
  rw [Matrix.toLin'_apply, adL_apply, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_mulVec]

theorem det_C [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (g : GL (Fin n) k)
    (hg : g ∈ Gz Z) : LinearMap.det ((adL g).restrict (cC_inv Z g hg)) = 1 := by
  have h := PositivityTheory.RgUd.T.Desc.UniPf.det_conjL Z hZ g hg
  let e : (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule ≃ₗ[k]
      Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun y => ⟨y.1, y.2⟩, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have he : PositivityTheory.RgUd.T.Desc.UniPf.conjL Z g hg =
      (e : _ →ₗ[k] _) ∘ₗ (adL g).restrict (cC_inv Z g hg) ∘ₗ (e.symm : _ →ₗ[k] _) := by
    apply LinearMap.ext; intro y; apply Subtype.ext
    show g.val * (y : Matrix (Fin n) (Fin n) k) * g⁻¹.val = adL g (y : Matrix (Fin n) (Fin n) k)
    rw [adL_apply]
  rw [he, LinearMap.det_conj] at h
  exact h

theorem det_eq_of_surj {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (f : V →ₗ[K] V) (F : W →ₗ[K] W) (L : V →ₗ[K] W)
    (hL : Function.Surjective L) (h : ∀ v, L (f v) = F (L v))
    (hf : ∀ y ∈ LinearMap.ker L, f y ∈ LinearMap.ker L) :
    LinearMap.det f = LinearMap.det (f.restrict hf) * LinearMap.det F := by
  have he : LinearMap.ker L ≤ Submodule.comap f (LinearMap.ker L) := hf
  rw [LinearMap.det_eq_det_mul_det (LinearMap.ker L) f he]
  congr 1
  let e := L.quotKerEquivOfSurjective hL
  have key : (LinearMap.ker L).mapQ (LinearMap.ker L) f he =
      (e.symm : W →ₗ[K] _) ∘ₗ F ∘ₗ (e.symm.symm : _ →ₗ[K] W) := by
    apply Submodule.linearMap_qext
    ext v
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_symm]
    rw [LinearEquiv.eq_symm_apply]
    simpa [e] using h v
  rw [key, LinearMap.det_conj F e.symm]

theorem det_split (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k) (v : Fin n → k)
    (g : GL (Fin n) k) (hg : g ∈ Gz Z) (t : k) (ht : t ≠ 0) (hgx : g.val * x * g⁻¹.val = t • x)
    (hgv : g.val *ᵥ v = v) :
    LinearMap.det ((adL g).restrict (cA_inv Z x g hg t ht hgx)) =
      LinearMap.det ((adL g).restrict (cS_inv Z x v g hg t ht hgx hgv)) *
        LinearMap.det ((Matrix.toLin' g.val).restrict (cAv_inv Z x v g hg t ht hgx hgv)) := by
  have hv : g⁻¹.val *ᵥ v = v := by
    conv_lhs => rw [← hgv]
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  set f := (adL g).restrict (cA_inv Z x g hg t ht hgx)
  set F := (Matrix.toLin' g.val).restrict (cAv_inv Z x v g hg t ht hgx hgv)
  let L : cA Z x →ₗ[k] cAv Z x v := (mulVecR v).submoduleMap (cA Z x)
  have hL : Function.Surjective L := (mulVecR v).submoduleMap_surjective (cA Z x)
  have hLa : ∀ a : cA Z x, ((L a : cAv Z x v) : Fin n → k) = (a : Matrix (Fin n) (Fin n) k) *ᵥ v := fun a => rfl
  have hint : ∀ a, L (f a) = F (L a) := by
    intro a
    apply Subtype.ext
    rw [hLa]
    show adL g (a : Matrix (Fin n) (Fin n) k) *ᵥ v = Matrix.toLin' g.val ((L a : cAv Z x v) : Fin n → k)
    rw [hLa, Matrix.toLin'_apply, adL_apply, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_mulVec]
  have hker : ∀ a : cA Z x, a ∈ LinearMap.ker L ↔ (a : Matrix (Fin n) (Fin n) k) ∈ cS Z x v := by
    intro a
    rw [LinearMap.mem_ker]
    constructor
    · intro h0
      refine ⟨a.2, ?_⟩
      have := congrArg (fun y : cAv Z x v => (y : Fin n → k)) h0
      simpa [hLa] using this
    · intro h0
      apply Subtype.ext
      rw [hLa]
      exact h0.2
  have hf : ∀ y ∈ LinearMap.ker L, f y ∈ LinearMap.ker L := by
    intro y hy
    rw [hker] at hy ⊢
    exact cS_inv Z x v g hg t ht hgx hgv _ hy
  rw [det_eq_of_surj f F L hL hint hf]
  congr 1
  have hSA : cS Z x v ≤ cA Z x := fun a ha => ha.1
  have hP : LinearMap.ker L = Submodule.comap (cA Z x).subtype (cS Z x v) := by
    ext a
    rw [hker]
    rfl
  let e0 := Submodule.comapSubtypeEquivOfLe hSA
  let e : LinearMap.ker L ≃ₗ[k] cS Z x v := (LinearEquiv.ofEq _ _ hP).trans e0
  rw [← LinearMap.det_conj (f.restrict hf) e]
  congr 1

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
