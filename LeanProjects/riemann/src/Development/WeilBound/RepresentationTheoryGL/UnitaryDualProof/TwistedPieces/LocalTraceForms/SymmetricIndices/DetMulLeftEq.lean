import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.TraceForm
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.IsClosedGzS

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Loc.Uni

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF

variable {k : Type} [Field k] {n : ℕ}

theorem det_mulLeft_eq (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (τ : Matrix (Fin n) (Fin n) k →ₗ[k] k)
    (hsym : ∀ x ∈ Bz Z, ∀ y ∈ Bz Z, τ (x * y) = τ (y * x))
    (hnd : ∀ x ∈ Bz Z, (∀ y ∈ Bz Z, τ (x * y) = 0) → x = 0)
    (a : Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) :
    LinearMap.det (LinearMap.mulLeft k a) = LinearMap.det (LinearMap.mulRight k a) := by
  let A := Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))
  have memA : ∀ x : Matrix (Fin n) (Fin n) k, x ∈ A ↔ x ∈ Bz Z := by
    intro x
    exact Subalgebra.mem_centralizer_iff k
  let φ : A →ₗ[k] Module.Dual k A := (LinearMap.mul k A).compr₂ (τ ∘ₗ A.val.toLinearMap)
  have hφ : ∀ x y : A, φ x y = τ ((x : Matrix (Fin n) (Fin n) k) * y) := fun x y => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    refine hnd x ((memA x).1 x.2) ?_
    intro y hy
    have := LinearMap.congr_fun hx ⟨y, (memA y).2 hy⟩
    rw [hφ] at this
    simpa using this
  let e : A ≃ₗ[k] Module.Dual k A :=
    LinearMap.linearEquivOfInjective φ hinj (Subspace.dual_finrank_eq).symm
  have he : ∀ x, e x = φ x := fun x => rfl
  let D := (LinearMap.mulRight k a).dualMap
  have hD : D = (LinearMap.mulRight k a).dualMap := rfl
  have key : ∀ x, e (a * x) = D (e x) := by
    intro x
    apply LinearMap.ext
    intro y
    rw [hD, LinearMap.dualMap_apply, he, he, hφ, hφ]
    simp only [LinearMap.mulRight_apply, Subalgebra.coe_mul]
    have := hsym a ((memA a).1 a.2) ((x : Matrix (Fin n) (Fin n) k) * y)
      ((memA _).1 (A.mul_mem x.2 y.2))
    rw [Matrix.mul_assoc (a : Matrix (Fin n) (Fin n) k), this, Matrix.mul_assoc]
  have hconj : LinearMap.mulLeft k a = (e.symm : Module.Dual k A →ₗ[k] A) ∘ₗ D ∘ₗ (e : A →ₗ[k] Module.Dual k A) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.mulLeft_apply]
    rw [← key, LinearEquiv.symm_apply_apply]
  have h2 := LinearMap.det_conj D e.symm
  rw [LinearEquiv.symm_symm] at h2
  rw [hconj, h2, hD, LinearMap.det_dualMap]

theorem det_conjB (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (τ : Matrix (Fin n) (Fin n) k →ₗ[k] k)
    (hsym : ∀ x ∈ Bz Z, ∀ y ∈ Bz Z, τ (x * y) = τ (y * x))
    (hnd : ∀ x ∈ Bz Z, (∀ y ∈ Bz Z, τ (x * y) = 0) → x = 0)
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h : GL (Fin n) k) (hh : h ∈ Gz Z) : LinearMap.det (conjB Z h hh) = 1 := by
  let A := Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))
  have hu : (h : Matrix (Fin n) (Fin n) k) ∈ A := (Subalgebra.mem_centralizer_iff k).2 hh
  have hv : ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ A := by
    rw [Subalgebra.mem_centralizer_iff]
    intro a ha
    exact (Commute.units_inv_right (hh a ha)).eq
  let u : A := ⟨h, hu⟩
  let v : A := ⟨((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k), hv⟩
  have hc : conjB Z h hh = LinearMap.mulLeft k u ∘ₗ LinearMap.mulRight k v := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    show (h : Matrix (Fin n) (Fin n) k) * x * ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = _
    simp [u, v, Matrix.mul_assoc]
  have huv : u * v = 1 := by
    apply Subtype.ext
    simp [u, v]
  rw [hc, LinearMap.det_comp, ← det_mulLeft_eq Z τ hsym hnd v, ← LinearMap.det_comp,
    ← LinearMap.mulLeft_mul, huv, LinearMap.mulLeft_one, LinearMap.det_id]

end PositivityTheory.RgUd.TP.Loc.Uni
