import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep

noncomputable section

open Matrix Module

namespace PositivityTheory.RgUd.T.Desc.UniPf

open PositivityTheory.RgUd.T

theorem inv_comm_of_comm {n : ℕ} {k : Type} [Field k] (h : GL (Fin n) k) (a : Matrix (Fin n) (Fin n) k)
    (h1 : a * h.val = h.val * a) : a * h⁻¹.val = h⁻¹.val * a :=
  calc a * h⁻¹.val = (h⁻¹.val * h.val) * a * h⁻¹.val := by rw [Units.inv_mul, one_mul]
    _ = h⁻¹.val * (h.val * a) * h⁻¹.val := by simp only [mul_assoc]
    _ = h⁻¹.val * (a * h.val) * h⁻¹.val := by rw [h1]
    _ = h⁻¹.val * a := by rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]

theorem reg {n : ℕ} {k : Type} [Field k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z)
    (x : Matrix (Fin n) (Fin n) k)
    (hx : x ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) :
    ∃ g ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)), x * g * x = x := by
  classical
  obtain ⟨hc, hr⟩ := hZ
  let iC : CommRing Z := { (inferInstance : Ring Z) with mul_comm := fun a b => Subtype.ext (hc _ a.2 _ b.2) }
  have : IsArtinianRing Z := IsArtinianRing.of_finite k Z
  have : IsSemisimpleRing Z := IsArtinianRing.isSemisimpleRing_of_isReduced Z
  let ψ : Z →+* Module.End k (Fin n → k) :=
    ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp Z.val).toRingHom
  let iM : Module Z (Fin n → k) := Module.compHom (Fin n → k) ψ
  have hsm : ∀ (a : Z) (v : Fin n → k), a • v = (a : Matrix (Fin n) (Fin n) k).mulVec v := fun a v => rfl
  have : IsSemisimpleModule Z (Fin n → k) := inferInstance
  have hxc : ∀ a : Z, (a : Matrix (Fin n) (Fin n) k) * x = x * a := fun a =>
    (Subalgebra.mem_centralizer_iff k).1 hx a a.2
  let f : Module.End Z (Fin n → k) :=
    { toFun := fun v => x.mulVec v, map_add' := fun v w => Matrix.mulVec_add _ _ _
      map_smul' := fun a v => by
        show x *ᵥ ((a : Matrix (Fin n) (Fin n) k) *ᵥ v) = (a : Matrix (Fin n) (Fin n) k) *ᵥ (x *ᵥ v)
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hxc a] }
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property f.rangeRestrict f.surjective_rangeRestrict
    (LinearMap.id : LinearMap.range f →ₗ[Z] LinearMap.range f)
  obtain ⟨t, ht⟩ := IsSemisimpleModule.extension_property (LinearMap.range f).subtype
    (Submodule.injective_subtype _) s
  have hft : ∀ v, f (t (f v)) = f v := by
    intro v
    have e1 : t (f v) = s ⟨f v, LinearMap.mem_range_self f v⟩ :=
      congrArg (fun φ : LinearMap.range f →ₗ[Z] (Fin n → k) => φ ⟨f v, LinearMap.mem_range_self f v⟩) ht
    have e2 := congrArg (fun φ : LinearMap.range f →ₗ[Z] LinearMap.range f =>
      (φ ⟨f v, LinearMap.mem_range_self f v⟩ : Fin n → k)) hs
    rw [e1]; exact e2
  let tk : Module.End k (Fin n → k) :=
    { toFun := t, map_add' := t.map_add
      map_smul' := fun c w => by
        have h1 : t ((algebraMap k (Matrix (Fin n) (Fin n) k) c).mulVec w) =
            (algebraMap k (Matrix (Fin n) (Fin n) k) c).mulVec (t w) := t.map_smul (algebraMap k Z c) w
        have h2 : ∀ u : Fin n → k, (algebraMap k (Matrix (Fin n) (Fin n) k) c).mulVec u = c • u := fun u => by
          rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
        rw [h2, h2] at h1; exact h1 }
  set G := LinearMap.toMatrix' tk with hG
  have hGv : ∀ u, G.mulVec u = t u := fun u => by
    rw [← Matrix.toLin'_apply, hG, Matrix.toLin'_toMatrix']; rfl
  refine ⟨G, ?_, ?_⟩
  · rw [Subalgebra.mem_centralizer_iff]
    intro a ha
    apply Matrix.toLin'.injective
    apply LinearMap.ext; intro u
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, hGv]
    have := t.map_smul ⟨a, ha⟩ u
    change t (a.mulVec u) = a.mulVec (t u) at this
    exact this.symm
  · apply Matrix.toLin'.injective
    apply LinearMap.ext; intro u
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hGv]
    exact hft u

theorem nondeg {n : ℕ} {k : Type} [Field k] [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))
    (hZ : CR Z) (x : Matrix (Fin n) (Fin n) k)
    (hx : x ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)))
    (h0 : ∀ y ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)), trace (x * y) = 0) :
    x = 0 := by
  obtain ⟨g, hg, hxg⟩ := reg Z hZ x hx
  have hid : g * x * (g * x) = g * x := by
    calc g * x * (g * x) = g * (x * g * x) := by simp only [mul_assoc]
      _ = g * x := by rw [hxg]
  have he : IsIdempotentElem (Matrix.toLinAlgEquiv' (g * x)) := by
    show _ * _ = _
    rw [← map_mul, hid]
  have htr : LinearMap.trace k (Fin n → k) (Matrix.toLinAlgEquiv' (g * x)) = 0 := by
    rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n)), LinearMap.toMatrix_eq_toMatrix']
    show (LinearMap.toMatrix' (Matrix.toLin' (g * x))).trace = 0
    rw [LinearMap.toMatrix'_toLin', Matrix.trace_mul_comm]
    exact h0 g hg
  have h1 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero he htr
  have h2 : g * x = 0 := (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).injective (by rw [h1, map_zero])
  calc x = x * g * x := hxg.symm
    _ = x * (g * x) := by rw [mul_assoc]
    _ = 0 := by rw [h2, mul_zero]

theorem det_mulLeft_eq {n : ℕ} {k : Type} [Field k] [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))
    (hZ : CR Z) (a : Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) :
    LinearMap.det (LinearMap.mulLeft k a) = LinearMap.det (LinearMap.mulRight k a) := by
  let C := Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))
  let T : C →ₗ[k] k := (Matrix.traceLinearMap (Fin n) k k).comp C.val.toLinearMap
  let Φ : C →ₗ[k] Module.Dual k C := (LinearMap.mul k C).compr₂ T
  have hΦ : ∀ x y : C, Φ x y = trace ((x : Matrix (Fin n) (Fin n) k) * (y : Matrix (Fin n) (Fin n) k)) := fun x y => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    refine nondeg Z hZ x x.2 (fun y hy => ?_)
    have := LinearMap.congr_fun hx ⟨y, hy⟩
    rw [hΦ] at this
    exact this
  have hdim : finrank k C = finrank k (Module.Dual k C) := Subspace.dual_finrank_eq.symm
  let e := Φ.linearEquivOfInjective hinj hdim
  have hconj : (e : C →ₗ[k] Module.Dual k C) ∘ₗ LinearMap.mulLeft k a ∘ₗ (e.symm : Module.Dual k C →ₗ[k] C) =
      (LinearMap.mulRight k a).dualMap := by
    apply LinearMap.ext; intro φ
    obtain ⟨x, rfl⟩ := e.surjective φ
    apply LinearMap.ext; intro y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.dualMap_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    show Φ (a * x) y = Φ x (y * a)
    simp only [hΦ, MulMemClass.coe_mul]
    rw [mul_assoc, Matrix.trace_mul_comm, mul_assoc]
  rw [← LinearMap.det_conj (LinearMap.mulLeft k a) e, hconj, LinearMap.det_dualMap]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem conj_mem (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (h : GL (Fin n) k) (hh : h ∈ Gz Z)
    (x : Matrix (Fin n) (Fin n) k) (hx : x ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) :
    h.val * x * h⁻¹.val ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) := by
  rw [Subalgebra.mem_centralizer_iff] at hx ⊢
  intro a ha
  have h1 : a * h.val = h.val * a := hh a ha
  have h2 := inv_comm_of_comm h a h1
  calc a * (h.val * x * h⁻¹.val) = (a * h.val) * x * h⁻¹.val := by simp only [mul_assoc]
    _ = h.val * (a * x) * h⁻¹.val := by rw [h1]; simp only [mul_assoc]
    _ = h.val * x * (a * h⁻¹.val) := by rw [hx a ha]; simp only [mul_assoc]
    _ = h.val * x * h⁻¹.val * a := by rw [h2]; simp only [mul_assoc]

def conjL (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (h : GL (Fin n) k) (hh : h ∈ Gz Z) :
    Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) →ₗ[k]
      Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) where
  toFun x := ⟨h.val * x * h⁻¹.val, conj_mem Z h hh x x.2⟩
  map_add' x y := Subtype.ext (by simp [mul_add, add_mul])
  map_smul' c x := Subtype.ext (by simp)

theorem det_conjL [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (h : GL (Fin n) k)
    (hh : h ∈ Gz Z) : LinearMap.det (conjL Z h hh) = 1 := by
  have hm : h.val ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) := by
    rw [Subalgebra.mem_centralizer_iff]; intro a ha; exact hh a ha
  have hm' : h⁻¹.val ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) := by
    rw [Subalgebra.mem_centralizer_iff]; intro a ha; exact inv_comm_of_comm h a (hh a ha)
  set a : Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) := ⟨h.val, hm⟩
  set b : Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) := ⟨h⁻¹.val, hm'⟩
  have hab : b * a = 1 := Subtype.ext (Units.inv_mul h)
  have hsplit : conjL Z h hh = LinearMap.mulLeft k a ∘ₗ LinearMap.mulRight k b := by
    apply LinearMap.ext; intro x; apply Subtype.ext
    show h.val * x * h⁻¹.val = h.val * (x * h⁻¹.val)
    rw [mul_assoc]
  have hR : LinearMap.mulRight k a ∘ₗ LinearMap.mulRight k b = LinearMap.id := by
    apply LinearMap.ext; intro x
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.id_apply, mul_assoc, hab, mul_one]
  rw [hsplit, LinearMap.det_comp, det_mulLeft_eq Z hZ a, ← LinearMap.det_comp, hR, LinearMap.det_id]

end PositivityTheory.RgUd.T.Desc.UniPf
